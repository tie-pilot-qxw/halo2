use super::*;
use std::path::PathBuf;

use rand_core::OsRng;
use zkpoly_common::heap::Heap;
use zkpoly_compiler::driver::{self, Artifect, DebugOptions, HardwareInfo};
use zkpoly_memory_pool::buddy_disk_pool::DiskMemoryPool;
use zkpoly_runtime::{args::RuntimeType, async_rng::AsyncRng};
use zkpoly_scheduler::scheduler::{
    make_scheduler, ProgramId, SchedulerConfig, SchedulerHandle, SubmittedTask, Submitter,
};

#[derive(Debug, Clone)]
pub struct JitConfig {
    assertions: bool,
    debug_options: DebugOptions,
    artifect_dir: PathBuf,
    force_rebuild: bool,
}

impl JitConfig {
    pub fn new(artifect_dir: PathBuf) -> Self {
        Self {
            assertions: false,
            debug_options: DebugOptions::none(artifect_dir.clone()),
            artifect_dir: artifect_dir,
            force_rebuild: false,
        }
    }

    pub fn with_assertions(self, x: bool) -> Self {
        Self {
            assertions: x,
            ..self
        }
    }

    pub fn with_debug_options(self, x: DebugOptions) -> Self {
        Self {
            debug_options: x,
            ..self
        }
    }

    pub fn with_force_rebuild(self, x: bool) -> Self {
        Self {
            force_rebuild: x,
            ..self
        }
    }
}

/// This is a JIT Prover environment that can be used to run the gpu prover.
///
/// Let p be `config.artifect_dir`, then debug files will be dumped to p/id,
/// and artifect will be at p/id/'artifect',
/// where id is the `circuit_identifier` passed to `create_proof`.
#[derive(Debug)]
pub struct JitProverEnv<Rt: RuntimeType> {
    config: JitConfig,
    submitter: Submitter<Rt>,
    scheduler: SchedulerHandle,
    constant_pool: ConstantPool,
    hardware_info: HardwareInfo,
    artifect_registry: HashMap<&'static str, (ProgramId, gen::InputsShape)>,
}

impl<Rt: RuntimeType> JitProverEnv<Rt> {
    pub fn new(
        config: JitConfig,
        scheduler_config: SchedulerConfig,
        disk_pool: DiskMemoryPool,
        constant_pool: ConstantPool,
        hd_info: HardwareInfo,
    ) -> Self {
        let rng = AsyncRng::new(2usize.pow(20), OsRng);
        let (scheduler, submitter) = make_scheduler(
            hd_info.clone(),
            scheduler_config,
            rng,
            disk_pool,
            Heap::new(),
        );
        let scheduler = scheduler.launch();
        Self {
            config: config,
            submitter: submitter,
            scheduler,
            constant_pool,
            hardware_info: hd_info,
            artifect_registry: HashMap::new(),
        }
    }

    pub fn shutdown(self) {
        self.scheduler.shutdown();
    }
}

fn compile<
    's,
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
    instance_lengths: Vec<Vec<usize>>,
    env: &'s mut JitProverEnv<gen::RtInstance<Scheme, E, T>>,
    trace: Option<&Trace<Scheme::Curve>>,
    circuit_identifier: &'static str,
) -> Result<
    (Artifect<gen::RtInstance<Scheme, E, T>>, gen::InputsShape),
    driver::Error<'s, gen::RtInstance<Scheme, E, T>>,
>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    std::thread::scope(|s| {
        let handler = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn_scoped(s, || {
                let cg_gen_start = start_timer!(|| "Create proof");
                let (cg_ret, cg_inputs_shape) = gen::create_proof_validated::<Scheme, P, E, T, _>(
                    params,
                    &pk,
                    circuits.to_vec(),
                    &instance_lengths,
                    &mut env.constant_pool,
                    trace,
                );
                end_timer!(cg_gen_start);

                let compile_start =
                    start_timer!(|| "[Test] Begin Compiling to Runtime Instructions");
                use zkpoly_compiler::driver;

                let options = env
                    .config
                    .debug_options
                    .clone()
                    .with_debug_dir(env.config.artifect_dir.join("name"));

                let pjh = driver::PanicJoinHandler::new();

                let fresh_type2 = driver::FreshType2::from_ast(cg_ret, &options, &pjh).unwrap();

                let name = circuit_identifier;
                let artifect_dir = env.config.artifect_dir.join(name).join("artifect");

                let artifect = if env.config.force_rebuild
                    || !std::path::Path::new(&artifect_dir).exists()
                {
                    println!("[Test] Applying Type2 passes and lowering to Artifect");
                    let processed_type2 = fresh_type2
                        .apply_passes(&options, &env.hardware_info, &mut env.constant_pool, &pjh)
                        .unwrap();

                    let artifect = processed_type2
                        .fuse(&options, &env.hardware_info, 0..=2, &pjh)?
                        .to_type3(&options, &env.hardware_info, &mut env.constant_pool, &pjh)?
                        .apply_passes(&options)?
                        .to_artifect(&options, &env.hardware_info)?;

                    artifect
                        .dump(&artifect_dir, &mut env.constant_pool)
                        .expect("dump artifect failure");
                    artifect.finish(&mut env.constant_pool)
                } else {
                    fresh_type2
                        .load_artifect(&artifect_dir, &mut env.constant_pool)
                        .expect("load artifect failure")
                };

                end_timer!(compile_start);

                Ok((artifect, cg_inputs_shape))
            })
            .unwrap();

        handler.join().unwrap()
    })
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof<
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
    env: &mut JitProverEnv<gen::RtInstance<Scheme, E, T>>,
    circuit_identifier: &'static str,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let (program, inputs_shape) = if let Some(x) = env
        .artifect_registry
        .get(std::any::type_name::<ConcreteCircuit>())
        .cloned()
    {
        x
    } else {
        let mut trace = Trace::default();
        let trace = if env.config.assertions {
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

        let (artifect, inputs_shape) = compile::<Scheme, P, E, T, ConcreteCircuit>(
            params,
            pk,
            circuits,
            instance_lengths,
            env,
            trace,
            circuit_identifier,
        )
        .expect("compile failure");

        let program = env
            .submitter
            .add_artifect(artifect)
            .expect("add artifect to scheduler failure");

        env.artifect_registry
            .insert(circuit_identifier, (program, inputs_shape.clone()));
        (program, inputs_shape)
    };

    let instances = instances
        .iter()
        .map(|ins| {
            ins.iter()
                .map(|ins| {
                    zkpoly_runtime::scalar::ScalarArray::from_vec(&ins, &mut env.constant_pool.cpu)
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let inputs = inputs_shape.serialize(instances, transcript.clone());

    let result_receiver = env
        .submitter
        .submit(SubmittedTask::new(program, inputs))
        .expect("submit to scheduler failure");

    let result = result_receiver
        .recv()
        .expect("result pipe disconnected unexpectedly");

    let proof = result.ret_value.unwrap().unwrap_transcript_move().take();

    *transcript = proof;
    Ok(())
}
