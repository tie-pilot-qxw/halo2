use group::ff::Field;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::jit::{JitConfig, JitProverEnv};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
use halo2_proofs::poly::{commitment::ParamsProver, Rotation};
use halo2curves::bn256::{Bn256, Fr, G1Affine};

use halo2_proofs::poly::kzg::{
    commitment::{KZGCommitmentScheme, ParamsKZG},
    multiopen::ProverSHPLONK,
    strategy::SingleStrategy,
};

use zkpoly_memory_pool::CpuMemoryPool;

use ff::PrimeField;
use std::marker::PhantomData;
use std::path::PathBuf;
use zkpoly_scheduler::scheduler::SchedulerConfig;

fn main() {
    #[derive(Clone, Default)]
    struct MyCircuit<F: Field> {
        _marker: PhantomData<F>,
    }

    #[derive(Clone)]
    struct MyConfig {
        selector: Selector,
        table: TableColumn,
        advice: Column<Advice>,
    }

    impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> MyConfig {
            let config = MyConfig {
                selector: meta.complex_selector(),
                table: meta.lookup_table_column(),
                advice: meta.advice_column(),
            };

            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(config.selector);
                let not_selector = Expression::Constant(F::ONE) - selector.clone();
                let advice = meta.query_advice(config.advice, Rotation::cur());
                vec![(selector * advice + not_selector, config.table)]
            });

            config
        }

        fn synthesize(
            &self,
            config: MyConfig,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "8-bit table",
                |mut table| {
                    for row in 0u64..(1 << 8) {
                        table.assign_cell(
                            || format!("row {row}"),
                            config.table,
                            row as usize,
                            || Value::known(F::from(row + 1)),
                        )?;
                    }

                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "assign values",
                |mut region| {
                    for offset in 0u64..(1 << 10) {
                        config.selector.enable(&mut region, offset as usize)?;
                        region.assign_advice(
                            || format!("offset {offset}"),
                            config.advice,
                            offset as usize,
                            || Value::known(F::from((offset % 256) + 1)),
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    fn keygen(k: u32) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
        let params: ParamsKZG<Bn256> = ParamsKZG::new(k);
        let empty_circuit: MyCircuit<Fr> = MyCircuit {
            _marker: PhantomData,
        };
        let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");
        (params, pk)
    }

    fn prover(_k: u32, params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>) {
        let circuit: MyCircuit<Fr> = MyCircuit {
            _marker: PhantomData,
        };

        println!("[Test] Begin Running Original Prover for Trace");
        use halo2_proofs::transcript::TranscriptWriterBuffer;
        let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
            _,
            _,
            halo2_proofs::transcript::Challenge255<G1Affine>,
        >::init(vec![]);

        use zkpoly_compiler::driver;

        let options = driver::DebugOptions::all(PathBuf::from("target/debug/transit"))
            .with_log(true)
            .with_type2_visualizer(driver::Type2DebugVisualizer::Cytoscape);
        let hd_info =
            driver::HardwareInfo::new(driver::MemoryInfo::new(300 * 2u64.pow(30), 2u64.pow(28)))
                .with_page_size(2u64.pow(24))
                .with_gpu(driver::MemoryInfo::new(2 * 2u64.pow(30), 2u64.pow(28)));

        let cpu_pool = CpuMemoryPool::new(30, std::mem::size_of::<u32>());
        let artifect_dir = "target/lookup";

        let constant_pool = driver::ConstantPool::only_cpu(cpu_pool);

        let rebuild = std::env::args().any(|arg| arg == "--rebuild");

        let mut jit = JitProverEnv::new(
            JitConfig::new(artifect_dir.into())
                .with_debug_options(options)
                .with_force_rebuild(rebuild),
            SchedulerConfig::default(),
            hd_info.disk_allocator(2usize.pow(30)),
            constant_pool,
            hd_info.clone(),
        );

        halo2_proofs::plonk::jit::create_proof::<
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
            "lookup-test",
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

        jit.shutdown();
    }

    let k = 14;

    print!("[Test] Keygen...");
    let (params, pk) = keygen(k);
    println!("Done");

    prover(k, &params, &pk);
}
