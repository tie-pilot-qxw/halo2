use group::ff::Field;
use halo2_proofs::circuit::{Cell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
use halo2_proofs::poly::{commitment::ParamsProver, Rotation};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;

use halo2_proofs::poly::kzg::{
    commitment::{KZGCommitmentScheme, ParamsKZG},
    multiopen::ProverSHPLONK,
    strategy::SingleStrategy,
};

use halo2_proofs::transcript::{self, TranscriptWriterBuffer};
use zkpoly_common::heap::Heap;
use zkpoly_compiler::driver::MemoryInfo;
use zkpoly_memory_pool::CpuMemoryPool;
use zkpoly_runtime::async_rng::AsyncRng;
use zkpoly_scheduler::scheduler::{make_scheduler, SchedulerConfig, SubmittedTask};

use std::marker::PhantomData;
use std::path::PathBuf;

fn main() {
    /// This represents an advice column at a certain row in the ConstraintSystem
    #[derive(Copy, Clone, Debug)]
    pub struct Variable(Column<Advice>, usize);

    #[derive(Clone)]
    struct PlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,

        sa: Column<Fixed>,
        sb: Column<Fixed>,
        sc: Column<Fixed>,
        sm: Column<Fixed>,
    }

    trait StandardCs<FF: Field> {
        fn raw_multiply<F>(
            &self,
            layouter: &mut impl Layouter<FF>,
            f: F,
        ) -> Result<(Cell, Cell, Cell), Error>
        where
            F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>;
        fn raw_add<F>(
            &self,
            layouter: &mut impl Layouter<FF>,
            f: F,
        ) -> Result<(Cell, Cell, Cell), Error>
        where
            F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>;
        fn copy(&self, layouter: &mut impl Layouter<FF>, a: Cell, b: Cell) -> Result<(), Error>;
    }

    #[derive(Clone)]
    struct MyCircuit<F: Field> {
        a: Value<F>,
        k: u32,
    }

    struct StandardPlonk<F: Field> {
        config: PlonkConfig,
        _marker: PhantomData<F>,
    }

    impl<FF: Field> StandardPlonk<FF> {
        fn new(config: PlonkConfig) -> Self {
            StandardPlonk {
                config,
                _marker: PhantomData,
            }
        }
    }

    impl<FF: Field> StandardCs<FF> for StandardPlonk<FF> {
        fn raw_multiply<F>(
            &self,
            layouter: &mut impl Layouter<FF>,
            mut f: F,
        ) -> Result<(Cell, Cell, Cell), Error>
        where
            F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>,
        {
            layouter.assign_region(
                || "raw_multiply",
                |mut region| {
                    let mut value = None;
                    let lhs = region.assign_advice(
                        || "lhs",
                        self.config.a,
                        0,
                        || {
                            value = Some(f());
                            value.unwrap().map(|v| v.0)
                        },
                    )?;
                    let rhs = region.assign_advice(
                        || "rhs",
                        self.config.b,
                        0,
                        || value.unwrap().map(|v| v.1),
                    )?;
                    let out = region.assign_advice(
                        || "out",
                        self.config.c,
                        0,
                        || value.unwrap().map(|v| v.2),
                    )?;

                    region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ZERO))?;
                    region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ZERO))?;
                    region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                    region.assign_fixed(|| "a * b", self.config.sm, 0, || Value::known(FF::ONE))?;
                    Ok((lhs.cell(), rhs.cell(), out.cell()))
                },
            )
        }
        fn raw_add<F>(
            &self,
            layouter: &mut impl Layouter<FF>,
            mut f: F,
        ) -> Result<(Cell, Cell, Cell), Error>
        where
            F: FnMut() -> Value<(Assigned<FF>, Assigned<FF>, Assigned<FF>)>,
        {
            layouter.assign_region(
                || "raw_add",
                |mut region| {
                    let mut value = None;
                    let lhs = region.assign_advice(
                        || "lhs",
                        self.config.a,
                        0,
                        || {
                            value = Some(f());
                            value.unwrap().map(|v| v.0)
                        },
                    )?;
                    let rhs = region.assign_advice(
                        || "rhs",
                        self.config.b,
                        0,
                        || value.unwrap().map(|v| v.1),
                    )?;
                    let out = region.assign_advice(
                        || "out",
                        self.config.c,
                        0,
                        || value.unwrap().map(|v| v.2),
                    )?;

                    region.assign_fixed(|| "a", self.config.sa, 0, || Value::known(FF::ONE))?;
                    region.assign_fixed(|| "b", self.config.sb, 0, || Value::known(FF::ONE))?;
                    region.assign_fixed(|| "c", self.config.sc, 0, || Value::known(FF::ONE))?;
                    region.assign_fixed(
                        || "a * b",
                        self.config.sm,
                        0,
                        || Value::known(FF::ZERO),
                    )?;
                    Ok((lhs.cell(), rhs.cell(), out.cell()))
                },
            )
        }
        fn copy(
            &self,
            layouter: &mut impl Layouter<FF>,
            left: Cell,
            right: Cell,
        ) -> Result<(), Error> {
            layouter.assign_region(|| "copy", |mut region| region.constrain_equal(left, right))
        }
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = PlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                a: Value::unknown(),
                k: self.k,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
            meta.set_minimum_degree(5);

            let a = meta.advice_column();
            let b = meta.advice_column();
            let c = meta.advice_column();

            meta.enable_equality(a);
            meta.enable_equality(b);
            meta.enable_equality(c);

            let sm = meta.fixed_column();
            let sa = meta.fixed_column();
            let sb = meta.fixed_column();
            let sc = meta.fixed_column();

            meta.create_gate("Combined add-mult", |meta| {
                let a = meta.query_advice(a, Rotation::cur());
                let b = meta.query_advice(b, Rotation::cur());
                let c = meta.query_advice(c, Rotation::cur());

                let sa = meta.query_fixed(sa, Rotation::cur());
                let sb = meta.query_fixed(sb, Rotation::cur());
                let sc = meta.query_fixed(sc, Rotation::cur());
                let sm = meta.query_fixed(sm, Rotation::cur());

                vec![a.clone() * sa + b.clone() * sb + a * b * sm - (c * sc)]
            });

            PlonkConfig {
                a,
                b,
                c,
                sa,
                sb,
                sc,
                sm,
            }
        }

        fn synthesize(
            &self,
            config: PlonkConfig,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let cs = StandardPlonk::new(config);

            for _ in 0..((1 << (self.k - 1)) - 3) {
                let a: Value<Assigned<_>> = self.a.into();
                let mut a_squared = Value::unknown();
                let (a0, _, c0) = cs.raw_multiply(&mut layouter, || {
                    a_squared = a.square();
                    a.zip(a_squared).map(|(a, a_squared)| (a, a, a_squared))
                })?;
                let (a1, b1, _) = cs.raw_add(&mut layouter, || {
                    let fin = a_squared + a;
                    a.zip(a_squared)
                        .zip(fin)
                        .map(|((a, a_squared), fin)| (a, a_squared, fin))
                })?;
                cs.copy(&mut layouter, a0, a1)?;
                cs.copy(&mut layouter, b1, c0)?;
            }

            Ok(())
        }
    }

    fn keygen(k: u32) -> (ParamsKZG<Bn256>, ProvingKey<G1Affine>) {
        let empty_circuit: MyCircuit<Fr> = MyCircuit {
            a: Value::unknown(),
            k,
        };

        let params_fname = format!("plonk-params-k{}.bin", k);
        let vk_fname = format!("plonk-vk-k{}.bin", k);
        let pk_fname = format!("plonk-pk-k{}.bin", k);

        let params: ParamsKZG<Bn256> = if let Ok(mut params_f) = std::fs::File::open(&params_fname)
        {
            ParamsKZG::read_custom(&mut params_f, halo2_proofs::SerdeFormat::RawBytes).unwrap()
        } else {
            println!("{} not opened, Generating new params", &params_fname);
            let params = ParamsKZG::new(k);
            let mut f = std::fs::File::create(&params_fname).unwrap();
            params
                .write_custom(&mut f, halo2_proofs::SerdeFormat::RawBytes)
                .unwrap();
            params
        };

        let vk = if let Ok(mut vk_f) = std::fs::File::open(&vk_fname) {
            VerifyingKey::read::<_, MyCircuit<_>>(&mut vk_f, halo2_proofs::SerdeFormat::RawBytes)
                .unwrap()
        } else {
            println!("{} not opened, Generating new vk", &vk_fname);
            let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
            let mut f = std::fs::File::create(&vk_fname).unwrap();
            vk.write(&mut f, halo2_proofs::SerdeFormat::RawBytes)
                .unwrap();
            vk
        };
        let pk = if let Ok(mut pk_f) = std::fs::File::open(&pk_fname) {
            ProvingKey::read::<_, MyCircuit<_>>(&mut pk_f, halo2_proofs::SerdeFormat::RawBytes)
                .unwrap()
        } else {
            println!("{} not opened, Generating new pk", &pk_fname);
            let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");
            let mut f = std::fs::File::create(&pk_fname).unwrap();
            pk.write(&mut f, halo2_proofs::SerdeFormat::RawBytes)
                .unwrap();
            pk
        };

        println!("Extended k = {}", pk.get_vk().get_domain().extended_k());

        (params, pk)
    }

    fn prover(k: u32, params: &ParamsKZG<Bn256>, pk: &ProvingKey<G1Affine>, rebuild: bool) {
        let rng = OsRng;

        let circuit: MyCircuit<Fr> = MyCircuit {
            a: Value::known(Fr::random(rng)),
            k,
        };

        type E = transcript::Challenge255<G1Affine>;
        type Tr = transcript::Blake2bWrite<Vec<u8>, G1Affine, E>;

        println!("[Test] Create Constant Pools");
        let allocator = CpuMemoryPool::new(30, std::mem::size_of::<u32>());
        let mut constant_pool = driver::ConstantPool::only_cpu(allocator);

        // let mut trace = Trace::default();

        // println!("[Test] Begin Running Original Prover for Trace");
        // use halo2_proofs::transcript::TranscriptWriterBuffer;
        // let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
        //     _,
        //     _,
        //     halo2_proofs::transcript::Challenge255<G1Affine>,
        // >::init(vec![]);
        // halo2_proofs::plonk::create_proof_traced::<
        //     KZGCommitmentScheme<Bn256>,
        //     ProverSHPLONK<Bn256>,
        //     _,
        //     _,
        //     _,
        //     _,
        // >(
        //     params,
        //     pk,
        //     &[circuit.clone()],
        //     &[&[]],
        //     rng,
        //     &mut transcript,
        //     Some(&mut trace),
        // )
        // .expect("proof generation should not fail");
        // transcript.finalize();
        // println!("[Test] End Running Original Prover for Trace");

        unsafe {
            backtrace_on_stack_overflow::enable();
        }

        println!("[Test] Begin Computation Graph Generation");
        let (cg_ret, cg_inputs_shape) = prover_gen::create_proof_validated::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<Bn256>,
            E,
            Tr,
            _,
        >(
            params,
            pk,
            vec![circuit],
            &vec![vec![]],
            &mut constant_pool,
            None,
        );
        println!("[Test] End Computation Graph Generation");

        use zkpoly_compiler::driver;

        let options = driver::DebugOptions::all(PathBuf::from("target/debug/transit"))
            .with_log(true)
            .with_type2_visualizer(driver::Type2DebugVisualizer::Graphviz);
        let hd_info = driver::HardwareInfo::new(MemoryInfo::new(2 * 2u64.pow(30), 2u64.pow(28)))
            .with_page_size(2 * 2u64.pow(20))
            .with_gpu(driver::MemoryInfo::new(4 * 2u64.pow(30), 2u64.pow(28)));

        let artifect_dir = "target/artifect";

        println!("[Test] Begin Compiling to Runtime Instructions");
        let pjh = driver::PanicJoinHandler::new();
        let type2_fresh = driver::FreshType2::from_ast(cg_ret, &options, &pjh).unwrap();

        let artifect = if rebuild || !std::path::Path::new(artifect_dir).exists() {
            let artifect = type2_fresh
                .to_semi_artifect(&options, &hd_info, &mut constant_pool, 0..=0, &pjh)
                .unwrap();
            artifect.dump(&artifect_dir, &mut constant_pool).unwrap();
            artifect.finish(&mut constant_pool)
        } else {
            println!("[Test] Loading Artifect from {}", &artifect_dir);
            type2_fresh
                .load_artifect(&artifect_dir, &mut constant_pool)
                .unwrap()
        };

        let sconfig = SchedulerConfig::default();
        let mut programs = Heap::new();
        let disk_pool = hd_info.disk_allocator(artifect.max_bs());
        let program = programs.push(artifect);
        let rng = AsyncRng::new(2usize.pow(20), OsRng);
        let (scheduler, submitter) = make_scheduler(hd_info, sconfig, rng, disk_pool, programs);
        let scheduler = scheduler.launch();

        println!("[Test] Launch VM");

        let results = (0..10)
            .into_iter()
            .map(|_| {
                let inputs = cg_inputs_shape.serialize(vec![vec![]], Tr::init(vec![]));
                submitter
                    .submit(SubmittedTask::new(program, inputs))
                    .expect("submit task failure")
            })
            .collect::<Vec<_>>();
        println!("[Test] VM Launched");

        for (i, res) in results.into_iter().enumerate() {
            println!("[Test] Waiting for result {}", i);
            let result = res.recv().unwrap();

            if i == 0 {
                let debug_log_f = std::fs::File::create("./runtime_debug.json").unwrap();
                serde_json::to_writer_pretty(debug_log_f, &result.log).unwrap();

                let mut f = std::fs::File::create("./runtime_debug.html").unwrap();
                result.log.waterfall().build(&mut f).unwrap();
            }

            let proof = result
                .ret_value
                .unwrap()
                .unwrap_transcript_move()
                .take()
                .finalize();
            println!("[Test] Begin Verify Proof {}", i);
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

        scheduler.shutdown();
        println!("[Test] VM Exited");
    }

    let k = 10;

    print!("[Test] Keygen...");
    let (params, pk) = keygen(k);
    println!("Done");

    let rebuild = std::env::args().any(|arg| arg == "--rebuild");

    prover(k, &params, &pk, rebuild);
}
