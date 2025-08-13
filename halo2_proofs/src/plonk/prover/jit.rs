//! Compile the create_proof computation graph if it has not been compiled, then running it.

use super::*;
use std::{
    path::PathBuf,
    sync::{Mutex, MutexGuard},
};

use rand_core::OsRng;
use zkpoly_compiler::driver::{self, Artifect, DebugOptions, HardwareInfo};
use zkpoly_memory_pool::buddy_disk_pool::DiskMemoryPool;
use zkpoly_runtime::{args::RuntimeType, async_rng::AsyncRng};
use zkpoly_scheduler::scheduler::{
    make_scheduler, ProgramToken, Programs, SubmittedTask, Submitter,
};

pub use zkpoly_scheduler::scheduler::{SchedulerConfig, SchedulerHandle};

#[derive(Debug, Clone)]
/// Configuratios for the Just-In-Time compiler.
pub struct JitConfig {
    assertions: bool,
    debug_options: DebugOptions,
    artifect_dir: PathBuf,
    force_rebuild: bool,
    artifect_versions_cpu_memory_divisions: Vec<u32>,
}

impl JitConfig {
    /// Default configuration, with compiled artifects and kernels put to `artifect_dir`.
    pub fn new(artifect_dir: PathBuf) -> Self {
        Self {
            assertions: false,
            debug_options: DebugOptions::none(artifect_dir.clone()),
            artifect_dir: artifect_dir,
            force_rebuild: false,
            artifect_versions_cpu_memory_divisions: vec![1, 2, 3],
        }
    }

    /// Enable asserations in computation graph, for debugging.
    pub fn with_assertions(self, x: bool) -> Self {
        Self {
            assertions: x,
            ..self
        }
    }

    /// Configure debug options for compiler.
    pub fn with_debug_options(self, x: DebugOptions) -> Self {
        Self {
            debug_options: x,
            ..self
        }
    }

    /// Always run the whole compilation process without loading from dumped artifects.
    pub fn with_force_rebuild(self, x: bool) -> Self {
        Self {
            force_rebuild: x,
            ..self
        }
    }

    /// Configure versions compiled for the artifect.
    /// See [`driver::UnfusedType2::fuse`] for details.
    pub fn with_artifect_versions_cpu_memory_divisions(self, x: Vec<u32>) -> Self {
        Self {
            artifect_versions_cpu_memory_divisions: x,
            ..self
        }
    }
}

/// The JIT compiler.
#[derive(Debug)]
pub struct Compiler {
    config: JitConfig,
    constant_pool: ConstantPool,
    hardware_info: HardwareInfo,
}

impl Compiler {
    pub fn new(config: JitConfig, constant_pool: ConstantPool, hd_info: HardwareInfo) -> Self {
        Self {
            config,
            constant_pool,
            hardware_info: hd_info,
        }
    }
}

/// This is a JIT Prover environment that can be used to run the gpu prover.
///
/// Let p be `config.artifect_dir`, then debug files will be dumped to p/id,
/// and artifect will be at p/id/'artifect',
/// where id is the `circuit_identifier` passed to `create_proof`.
#[derive(Debug, Clone)]
pub struct JitProverEnv<Rt: RuntimeType, CC> {
    compiler: Arc<Mutex<Compiler>>,
    submitter: Submitter<Rt>,
    artifect_registry:
        Arc<Mutex<HashMap<&'static str, (ProgramToken<Rt>, gen::InputsShape<Rt, CC>)>>>,
}

impl<Rt: RuntimeType, CC: Circuit<Rt::Field>> JitProverEnv<Rt, CC> {
    /// Assemble a [`JitProverEnv`] from compiler and scheduler submitter.
    pub fn assemble(compiler: Compiler, submitter: Submitter<Rt>) -> Self {
        Self {
            compiler: Arc::new(Mutex::new(compiler)),
            submitter,
            artifect_registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Clone a [`JitProverEnv`] that accepts requests for alternative [`RuntimeType`],
    /// but submits to the same scheduler.
    pub fn alternative_rt<Rt2: RuntimeType, CC2: Circuit<Rt2::Field>>(
        &self,
    ) -> JitProverEnv<Rt2, CC2> {
        JitProverEnv {
            compiler: self.compiler.clone(),
            submitter: self.submitter.alternative_rt(),
            artifect_registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

/// Make a [`JitProverEnv`], also returning the handle to the scheudler thread.
pub fn make_env<Rt: RuntimeType, CC: Circuit<Rt::Field>>(
    config: JitConfig,
    scheduler_config: SchedulerConfig,
    disk_pool: DiskMemoryPool,
    constant_pool: ConstantPool,
    hd_info: HardwareInfo,
) -> (JitProverEnv<Rt, CC>, SchedulerHandle) {
    let rng = AsyncRng::new(2usize.pow(24), OsRng);
    let (scheduler, submitter) = make_scheduler(
        hd_info.clone(),
        scheduler_config,
        rng,
        disk_pool,
        Programs::new(),
    );
    let scheduler = scheduler.launch();

    let compiler = Compiler::new(config, constant_pool, hd_info);
    let env = JitProverEnv::assemble(compiler, submitter);

    (env, scheduler)
}

impl<Rt: RuntimeType, CC: Circuit<Rt::Field>> JitProverEnv<Rt, CC> {
    pub fn compiler_lock<'a>(&'a self) -> MutexGuard<'a, Compiler> {
        self.compiler.lock().unwrap()
    }
}

impl Compiler {
    pub fn compile<
        's,
        'params,
        Scheme: CommitmentScheme + 'static,
        P: Prover<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve> + 'static,
        T: TranscriptWrite<Scheme::Curve, E> + std::fmt::Debug + 'static,
        ConcreteCircuit: Circuit<Scheme::Scalar> + Clone + Send + Sync + 'static,
    >(
        &mut self,
        params: &'params Scheme::ParamsProver,
        pk: &ProvingKey<Scheme::Curve>,
        circuits: &[ConcreteCircuit],
        instance_lengths: Vec<Vec<usize>>,
        trace: Option<&Trace<Scheme::Curve>>,
        circuit_identifier: &'static str,
    ) -> Result<
        (
            Artifect<gen::RtInstance<Scheme, E, T>>,
            gen::InputsShape<gen::RtInstance<Scheme, E, T>, ConcreteCircuit>,
        ),
        driver::Error<'s, gen::RtInstance<Scheme, E, T>>,
    >
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        std::thread::scope(|s| {
            let handler =
                std::thread::Builder::new()
                    .stack_size(64 * 1024 * 1024)
                    .spawn_scoped(s, || {
                        let cg_gen_start = start_timer!(|| "Generating Computation Graph");
                        let (cg_ret, cg_inputs_shape) =
                            gen::create_proof_validated::<Scheme, P, E, T, _>(
                                params,
                                &pk,
                                circuits,
                                &instance_lengths,
                                &mut self.constant_pool,
                                trace,
                            );
                        end_timer!(cg_gen_start);

                        let compile_start = start_timer!(|| "Compiling to Runtime Instructions");
                        use zkpoly_compiler::driver;

                        let name = circuit_identifier;

                        let options = self
                            .config
                            .debug_options
                            .clone()
                            .with_debug_dir(self.config.artifect_dir.join(name));

                        let pjh = driver::PanicJoinHandler::new();

                        let fresh_type2 =
                            driver::FreshType2::from_ast(cg_ret, &options, &pjh).unwrap();

                        let artifect_dir = self.config.artifect_dir.join(name).join("artifect");
                        let kerneld_dir = self.config.artifect_dir.join(name).join("kernels");

                        let artifect = if self.config.force_rebuild
                            || !std::path::Path::new(&artifect_dir).exists()
                        {
                            let processed_type2 = fresh_type2
                                .apply_passes(
                                    &options,
                                    &self.hardware_info,
                                    &mut self.constant_pool,
                                    &pjh,
                                )
                                .unwrap();

                            let artifect = processed_type2
                                .fuse(
                                    &options,
                                    &self.hardware_info,
                                    self.config
                                        .artifect_versions_cpu_memory_divisions
                                        .iter()
                                        .cloned(),
                                    &pjh,
                                )?
                                .to_type3(
                                    &options,
                                    &self.hardware_info,
                                    &mut self.constant_pool,
                                    &pjh,
                                )?
                                .apply_passes(&options)?
                                .to_artifect(&options, &self.hardware_info, kerneld_dir)?;

                            artifect
                                .dump(&artifect_dir, &mut self.constant_pool)
                                .expect("dump artifect failure");
                            artifect.finish(&mut self.constant_pool)
                        } else {
                            fresh_type2
                                .load_artifect(&artifect_dir, &mut self.constant_pool)
                                .expect("load artifect failure")
                        };

                        end_timer!(compile_start);

                        Ok((artifect, cg_inputs_shape))
                    })
                    .unwrap();

            handler.join().unwrap()
        })
    }
}
pub fn create_proof<
    'params,
    Scheme: CommitmentScheme + 'static,
    P: Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve> + 'static,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E> + std::fmt::Debug + 'static,
    ConcreteCircuit: Circuit<Scheme::Scalar> + Clone + Send + Sync + 'static,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
    rng: R,
    transcript: &mut T,
    env: Option<&mut JitProverEnv<gen::RtInstance<Scheme, E, T>, ConcreteCircuit>>,
    circuit_identifier: &'static str,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    if let Some(env) = env {
        create_proof_gpu::<Scheme, P, _, _, _>(
            params,
            pk,
            circuits,
            instances,
            transcript,
            env,
            circuit_identifier,
        )
    } else {
        super::create_proof::<Scheme, P, _, _, _, _>(
            params, pk, circuits, instances, rng, transcript,
        )
    }
}

/// Similar to [`super::create_proof`], but uses GPU and compiles artifects just-in-time.
///
/// The only differences are two extra arguments:
/// - `env` is the JIT env used.
/// - The `circuit_identifier` must be unique for each circuit and pk,vk.
///   If an artifect associated with `circuit_identifier` is already built, the compiler
///   won't compile again.
pub fn create_proof_gpu<
    'params,
    Scheme: CommitmentScheme + 'static,
    P: Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve> + 'static,
    T: TranscriptWrite<Scheme::Curve, E> + std::fmt::Debug + 'static,
    ConcreteCircuit: Circuit<Scheme::Scalar> + Clone + Send + Sync + 'static,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
    transcript: &mut T,
    env: &mut JitProverEnv<gen::RtInstance<Scheme, E, T>, ConcreteCircuit>,
    circuit_identifier: &'static str,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let mut artifect_registry = env.artifect_registry.lock().unwrap();

    let (program, inputs_shape) = if artifect_registry.get(circuit_identifier).is_some() {
        artifect_registry.get(circuit_identifier).cloned().unwrap()
    } else {
        let mut trace = Trace::default();
        let trace = if env.compiler_lock().config.assertions {
            println!("extended k = {}", pk.get_vk().get_domain().extended_k());

            let trace_start = start_timer!(|| "[Test] Begin Running Original Prover for Trace");
            let mut transcript = transcript.clone();
            create_proof_traced::<Scheme, P, E, _, T, ConcreteCircuit>(
                params,
                pk,
                circuits,
                instances,
                OsRng::default(), // traced prover does not use rng, this is just a placeholder
                &mut transcript,
                Some(&mut trace),
            )
            .expect("proof generation should not fail");
            end_timer!(trace_start);
            Some(&trace)
        } else {
            None
        };

        let instance_lengths = instances
            .iter()
            .map(|ins| ins.iter().map(|p| p.len()).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let (artifect, inputs_shape) = env
            .compiler_lock()
            .compile::<Scheme, P, E, T, ConcreteCircuit>(
                params,
                pk,
                circuits,
                instance_lengths,
                trace,
                circuit_identifier,
            )
            .expect("compile failure");

        let program = env
            .submitter
            .add_artifect(artifect)
            .expect("add artifect to scheduler failure");

        artifect_registry.insert(circuit_identifier, (program, inputs_shape.clone()));
        (program, inputs_shape)
    };

    drop(artifect_registry);

    let instances = instances
        .iter()
        .map(|ins| {
            ins.iter()
                .map(|ins| {
                    zkpoly_runtime::scalar::ScalarArray::from_vec(
                        &ins,
                        &mut env.compiler.lock().unwrap().constant_pool.cpu,
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let inputs = inputs_shape.serialize(instances, circuits.to_vec(), transcript.clone());

    let result_receiver = env
        .submitter
        .submit(SubmittedTask::new(program, inputs.clone()))
        .expect("submit to scheduler failure");

    let result = result_receiver
        .read()
        .expect("result pipe disconnected unexpectedly");

    env.compiler_lock().constant_pool.deallocate_inputs(inputs);

    let proof = result.ret_value.unwrap().unwrap_transcript_move().take();

    *transcript = proof;
    Ok(())
}
