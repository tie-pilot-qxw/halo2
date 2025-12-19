use halo2_proofs::plonk::jit::{make_env, JitConfig};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
use halo2curves::bn256::{Bn256, Fr, G1Affine};

use halo2_proofs::poly::kzg::{
    commitment::{KZGCommitmentScheme, ParamsKZG},
    multiopen::ProverSHPLONK,
    strategy::SingleStrategy,
};

use zkpoly_memory_pool::CpuMemoryPool;

use rand_core::OsRng;
use std::path::PathBuf;
use zkpoly_scheduler::scheduler::SchedulerConfig;

pub fn keygen<C: Circuit<Fr>>(
    k: u32,
    empty_circuit: &C,
) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params: ParamsKZG<Bn256> = ParamsKZG::setup(k, OsRng);
    let vk = keygen_vk(&params, empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, empty_circuit).expect("keygen_pk should not fail");
    (params, pk)
}

pub fn keygen_or_load<C: Circuit<Fr>>(
    k: u32,
    empty_circuit: &C,
) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
    let params_fname = PathBuf::from(format!("k{}.params", k));
    let pk_fname = PathBuf::from(format!("k{}.pk", k));

    let (params, pk) = if params_fname.exists() && pk_fname.exists() {
        println!("Load k{k} params and pk from {:?}", &pk_fname);

        let params = ParamsKZG::read_custom(
            &mut std::fs::File::open(params_fname).expect("open params file failed"),
            halo2_proofs::SerdeFormat::RawBytes,
        )
        .expect("read paras file failed");

        let pk = ProvingKey::read::<_, C>(
            &mut std::fs::File::open(pk_fname).expect("open params file failed"),
            halo2_proofs::SerdeFormat::RawBytes,
        )
        .expect("read paras file failed");

        (params, pk)
    } else {
        println!("Generating k{k} params and pk");

        let (params, pk) = keygen(k, empty_circuit);
        params
            .write(&mut std::fs::File::create(params_fname).expect("create params file failed"))
            .expect("write to params file failed");

        pk.write(
            &mut std::fs::File::create(pk_fname).expect("create params file failed"),
            halo2_proofs::SerdeFormat::RawBytes,
        )
        .expect("write to pk file failed");

        (params, pk)
    };

    println!(
        "Extended k = {}, Number of Instances = {}",
        pk.get_vk().get_domain().k(),
        pk.get_vk().cs().num_instance_columns()
    );

    (params, pk)
}

pub fn prover_cpu<C>(k: u32, params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>, circuit: C)
where
    C: Circuit<Fr> + Clone + Send + Sync + 'static,
{
    let rng = OsRng;

    use halo2_proofs::transcript::TranscriptWriterBuffer;
    let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
        _,
        _,
        halo2_proofs::transcript::Challenge255<G1Affine>,
    >::init(vec![]);
    halo2_proofs::plonk::create_proof_traced::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        _,
        _,
        _,
        _,
    >(
        params,
        pk,
        &[circuit.clone()],
        &[&[]],
        rng,
        &mut transcript,
        None,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    let strategy = SingleStrategy::new(params);
    use halo2_proofs::transcript::TranscriptReadBuffer;
    let mut transcript = halo2_proofs::transcript::Blake2bRead::<
        _,
        _,
        halo2_proofs::transcript::Challenge255<_>,
    >::init(&proof[..]);
    let verify_result = verify_proof::<_, VerifierSHPLONK<Bn256>, _, _, _>(
        params,
        pk.get_vk(),
        strategy,
        &[&[]],
        &mut transcript,
    );

    match verify_result {
        Ok(_) => println!("[Test] Verify Proof Success"),
        Err(e) => println!("[Test] Verify Proof Failed: {:?}", e),
    }
}

pub fn prover<C>(k: u32, params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>, circuit: C)
where
    C: Circuit<Fr> + Clone + Send + Sync + 'static,
{
    use halo2_proofs::transcript::TranscriptWriterBuffer;
    let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
        _,
        _,
        halo2_proofs::transcript::Challenge255<G1Affine>,
    >::init(vec![]);

    use zkpoly_compiler::driver;

    let options = driver::DebugOptions::all(PathBuf::from("/tmp"))
        .with_log(true)
        .with_type2_visualizer(driver::Type2DebugVisualizer::Cytoscape);

    let hd_info = driver::HardwareInfo::new(driver::MemoryInfo::new(10 * 2u64.pow(30)))
        .with_gpu(driver::MemoryInfo::new(4 * 2u64.pow(30)));

    let cpu_pool = CpuMemoryPool::new(30, std::mem::size_of::<u32>());
    let artifect_dir = "target/";

    let constant_pool = driver::ConstantPool::only_cpu(cpu_pool);

    let rebuild = std::env::args().any(|arg| arg == "--rebuild");

    let (mut jit, scheduler) = make_env(
        JitConfig::new(artifect_dir.into())
            .with_debug_options(options)
            .with_force_rebuild(rebuild)
            .with_artifect_versions_cpu_memory_divisions(vec![0])
            .with_compiler_config(
                driver::Config::default().with_sliceable_subgraph_on(
                    driver::SubgraphSlicingConfig::default()
                        .with_minimum_order(1)
                        .with_chunk_len(2u64.pow(k - 3)),
                ),
            ),
        SchedulerConfig::default(),
        hd_info.disk_allocator(2usize.pow(30)),
        constant_pool,
        hd_info.clone(),
    );

    // Create proof using JIT runner
    halo2_proofs::plonk::jit::create_proof_gpu::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<Bn256>,
        _,
        _,
        _,
    >(
        params,
        pk,
        &[circuit.clone()],
        &[&[]],
        &mut transcript,
        &mut jit,
        "shuffle",
    )
    .expect("proof generation should not fail");

    let proof = transcript.finalize();

    println!("[Test] Begin Verify Proof");
    let strategy = SingleStrategy::new(params);
    use halo2_proofs::transcript::TranscriptReadBuffer;
    let mut transcript = halo2_proofs::transcript::Blake2bRead::<
        _,
        _,
        halo2_proofs::transcript::Challenge255<_>,
    >::init(&proof[..]);
    let verify_result = verify_proof::<_, VerifierSHPLONK<Bn256>, _, _, _>(
        params,
        pk.get_vk(),
        strategy,
        &[&[]],
        &mut transcript,
    );

    match verify_result {
        Ok(_) => println!("[Test] Verify Proof Success"),
        Err(e) => println!("[Test] Verify Proof Failed: {:?}", e),
    }

    scheduler.shutdown();
}
