//! Generator for [`create_proof`]
use super::*;
use ff::PrimeField;
use std::any;
use zkpoly_compiler::ast::{builder, Typ, Vertex};

mod user_functions {
    use super::*;
    use zkpoly_runtime::error::RuntimeError;
    use zkpoly_runtime::user_functions as uf;

    pub fn calculate_advices<
        'params,
        Scheme: CommitmentScheme,
        ConcreteCircuit: Circuit<Scheme::Scalar> + 'static,
    >(
        n: u64,
        k: u32,
        num_instance_columns: usize,
        current_phase: sealed::Phase,
        meta: &ConstraintSystem<Scheme::Scalar>,
        config: ConcreteCircuit::Config,
    ) -> uf::Function
    where
        ConcreteCircuit::Config: 'static,
    {
        #[derive(Clone)]
        struct AdviceSingle<C: CurveAffine, B: Basis> {
            pub advice_polys: Vec<Polynomial<C::Scalar, B>>,
            pub advice_blinds: Vec<Blind<C::Scalar>>,
        }

        struct WitnessCollection<'a, F: Field> {
            k: u32,
            current_phase: sealed::Phase,
            advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
            unblinded_advice: HashSet<usize>,
            challenges: &'a HashMap<usize, F>,
            instances: &'a [&'a [F]],
            usable_rows: RangeTo<usize>,
            _marker: std::marker::PhantomData<F>,
        }

        impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
            fn enter_region<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
                // Do nothing; we don't care about regions in this context.
            }

            fn exit_region(&mut self) {
                // Do nothing; we don't care about regions in this context.
            }

            fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
            where
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // We only care about advice columns here

                Ok(())
            }

            fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
            where
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // Do nothing
            }

            fn query_instance(
                &self,
                column: Column<Instance>,
                row: usize,
            ) -> Result<Value<F>, Error> {
                if !self.usable_rows.contains(&row) {
                    return Err(Error::not_enough_rows_available(self.k));
                }

                self.instances
                    .get(column.index())
                    .and_then(|column| column.get(row))
                    .map(|v| Value::known(*v))
                    .ok_or(Error::BoundsFailure)
            }

            fn assign_advice<V, VR, A, AR>(
                &mut self,
                _: A,
                column: Column<Advice>,
                row: usize,
                to: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<F>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // Ignore assignment of advice column in different phase than current one.
                if self.current_phase != column.column_type().phase {
                    return Ok(());
                }

                if !self.usable_rows.contains(&row) {
                    return Err(Error::not_enough_rows_available(self.k));
                }

                *self
                    .advice
                    .get_mut(column.index())
                    .and_then(|v| v.get_mut(row))
                    .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

                Ok(())
            }

            fn assign_fixed<V, VR, A, AR>(
                &mut self,
                _: A,
                _: Column<Fixed>,
                _: usize,
                _: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<F>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // We only care about advice columns here

                Ok(())
            }

            fn copy(
                &mut self,
                _: Column<Any>,
                _: usize,
                _: Column<Any>,
                _: usize,
            ) -> Result<(), Error> {
                // We only care about advice columns here

                Ok(())
            }

            fn fill_from_row(
                &mut self,
                _: Column<Fixed>,
                _: usize,
                _: Value<Assigned<F>>,
            ) -> Result<(), Error> {
                Ok(())
            }

            fn get_challenge(&self, challenge: Challenge) -> Value<F> {
                self.challenges
                    .get(&challenge.index())
                    .cloned()
                    .map(Value::known)
                    .unwrap_or_else(Value::unknown)
            }

            fn push_namespace<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
                // Do nothing; we don't care about namespaces in this context.
            }

            fn pop_namespace(&mut self, _: Option<String>) {
                // Do nothing; we don't care about namespaces in this context.
            }
        }

        let unusable_rows_start = n as usize - (meta.blinding_factors() + 1);
        let num_advice_columns = meta.num_advice_columns;
        let unblinded_advice_columns = meta.unblinded_advice_columns.clone();
        let constants = meta.constants.clone();

        let f = Box::new(move |args: Vec<&dyn any::Any>| {
            if args.len() != 3 {
                return Err(RuntimeError::ArgNumWrong);
            }

            let instances: &[&[Scheme::Scalar]] = unimplemented!();
            let challenges = unimplemented!();
            let circuit: ConcreteCircuit = unimplemented!();

            let mut witness = WitnessCollection {
                k,
                current_phase,
                advice: vec![Polynomial::empty_lagrange_assigned(n as usize); num_advice_columns],
                unblinded_advice: HashSet::from_iter(unblinded_advice_columns.iter().copied()),
                instances,
                challenges: challenges,
                // The prover will not be allowed to assign values to advice
                // cells that exist within inactive rows, which include some
                // number of blinding factors and an extra row for use in the
                // permutation argument.
                usable_rows: ..unusable_rows_start,
                _marker: std::marker::PhantomData,
            };

            // Synthesize the circuit to obtain the witness and other information.
            ConcreteCircuit::FloorPlanner::synthesize(&mut witness, &circuit, config, constants)
                .map_err(|e| RuntimeError::Other(format!("{:?}", e)))?;

            unimplemented!()
        });

        uf::Function::new_once(
            "calculate_advices".to_string(),
            f,
            (
                vec![
                    (
                        Typ::Array(Box::new(Typ::lagrange(n)), num_instance_columns),
                        uf::ParamMode::In,
                    ),
                    (
                        Typ::Any(
                            any::TypeId::of::<HashMap<usize, Scheme::Scalar>>(),
                            std::mem::size_of::<HashMap<usize, Scheme::Scalar>>(),
                        ),
                        uf::ParamMode::In,
                    ),
                    (
                        Typ::Any(
                            any::TypeId::of::<ConcreteCircuit>(),
                            std::mem::size_of::<ConcreteCircuit>(),
                        ),
                        uf::ParamMode::In,
                    ),
                ],
                Typ::Tuple(vec![
                    Typ::Array(Box::new(Typ::lagrange(n)), num_advice_columns),
                    Typ::Array(Box::new(Typ::lagrange(n)), num_advice_columns),
                ]),
            ),
        )
    }

    pub fn new_hash_dict<K: 'static, T: 'static>() -> uf::Function {
        let f = |args: Vec<&dyn any::Any>| -> Result<Box<dyn any::Any>, RuntimeError> {
            if args.len() != 0 {
                return Err(RuntimeError::ArgNumWrong);
            }

            let x: HashMap<K, T> = HashMap::new();
            Ok(Box::new(x))
        };

        uf::Function::new_mut(
            format!(
                "new_hash_dict::<{}, {}>",
                any::type_name::<K>(),
                any::type_name::<T>()
            ),
            Box::new(f),
            (
                vec![],
                Typ::Any(
                    any::TypeId::of::<HashMap<K, T>>(),
                    std::mem::size_of::<HashMap<K, T>>(),
                ),
            ),
        )
    }

    pub fn filter_accordingly(
        indices: BTreeSet<usize>,
        num_advice_columns: usize,
        n: u64,
    ) -> uf::Function {
        let f = |args: Vec<&dyn any::Any>| -> Result<Box<dyn any::Any>, RuntimeError> {
            if args.len() != 1 {
                return Err(RuntimeError::ArgNumWrong);
            }
            // Choose those polynomials in `args[0]` whose indices are those in `indices`
            unimplemented!()
        };

        uf::Function::new_mut(
            "filter_accordingly".to_string(),
            Box::new(f),
            (
                vec![(
                    Typ::Array(Box::new(Typ::lagrange(n)), num_advice_columns),
                    uf::ParamMode::In,
                )],
                Typ::Array(Box::new(Typ::lagrange(n)), indices.len()),
            ),
        )
    }

    pub fn hash_dict_insert<K: 'static, T: 'static>() -> uf::Function {
        let f = |args: Vec<&dyn any::Any>| -> Result<Box<dyn any::Any>, RuntimeError> {
            if args.len() != 3 {
                return Err(RuntimeError::ArgNumWrong);
            }
            // Insert `args[1]` into `args[0]`
            unimplemented!()
        };

        uf::Function::new_mut(
            format!(
                "hash_dict_insert::<{}, {}>",
                any::type_name::<K>(),
                any::type_name::<T>()
            ),
            Box::new(f),
            (
                vec![
                    (
                        Typ::Any(
                            any::TypeId::of::<HashMap<K, T>>(),
                            std::mem::size_of::<HashMap<K, T>>(),
                        ),
                        uf::ParamMode::InOut,
                    ),
                    (
                        Typ::Any(any::TypeId::of::<K>(), std::mem::size_of::<K>()),
                        uf::ParamMode::In,
                    ),
                    (
                        Typ::Any(any::TypeId::of::<T>(), std::mem::size_of::<T>()),
                        uf::ParamMode::In,
                    ),
                ],
                Typ::Any(
                    any::TypeId::of::<HashMap<K, T>>(),
                    std::mem::size_of::<HashMap<K, T>>(),
                ),
            ),
        )
    }

    pub fn collect_challenges<S: 'static + Clone>(num_challenges: usize) -> uf::Function {
        let f = move |args: Vec<&dyn any::Any>| -> Result<Box<dyn any::Any>, RuntimeError> {
            if args.len() != 1 {
                return Err(RuntimeError::ArgNumWrong);
            }
            if let Some(challenges) = args[0].downcast_ref::<HashMap<usize, S>>() {
                let result = (0..num_challenges)
                    .map(|index| challenges[&index].clone())
                    .collect::<Vec<_>>();
                // Gotta turn this vector to real runtime array type
                unimplemented!()
            } else {
                Err(RuntimeError::TypError)
            }
        };

        uf::Function::new_mut(
            "collect_challenges".to_string(),
            Box::new(f),
            (
                vec![(
                    Typ::Any(
                        any::TypeId::of::<HashMap<usize, S>>(),
                        std::mem::size_of::<HashMap<usize, S>>(),
                    ),
                    uf::ParamMode::In,
                )],
                Typ::Array(Box::new(Typ::Scalar), num_challenges),
            ),
        )
    }
}

fn kzg_commit_lagrange(
    builder: builder::Builder,
    poly: Vertex,
    points: Vertex,
    transcript: Vertex,
) -> Vertex {
    let point = builder.msm("".to_string(), poly, points);
    builder.hash_point(transcript, point)
}

/// The generator for [`super::create_proof`].
pub fn create_proof<
    'params,
    Scheme: CommitmentScheme,
    P: Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar> + 'static,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: Vec<ConcreteCircuit>,
) -> Vertex {
    let domain = &pk.vk.domain;
    let mut meta = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut meta, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut meta);

    let meta = &pk.vk.cs;

    assert!(P::QUERY_INSTANCE == false);

    let mut builder = builder::Builder::new();

    // Declare inputs
    let instances = (0..circuits.len())
        .map(|i| {
            (0..pk.vk.cs.num_instance_columns)
                .map(|j| builder.entry(format!("instance_{}_{}", i, j), Typ::lagrange(params.n())))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut transcript = builder.entry("transcript".to_string(), Typ::Transcript);

    // Where do our precomputed points come from?
    let lagrange_points: Vertex = unimplemented!();

    // Hash verfication key into transcript
    let vk_scalar = builder.constant_scaler("vk_scalar".to_string(), pk.vk.transcript_repr.clone());
    transcript = builder.hash_scalar(transcript, vk_scalar);

    let mut advices: Vec<Vec<Option<Vertex>>> =
        vec![vec![None; meta.num_advice_columns]; instances.len()];
    let mut challenges = builder.user_function(
        format!("challenges_0"),
        user_functions::new_hash_dict::<usize, Scheme::Scalar>(),
        vec![],
    );

    let circuits = circuits
        .into_iter()
        .enumerate()
        .map(|(i, circuit)| builder.constant(format!("circuit_{}", i), circuit))
        .collect::<Vec<_>>();

    let challenges_dict_insert =
        builder.add_user_function(user_functions::hash_dict_insert::<usize, Scheme::Scalar>());

    let unusable_rows_start = params.n() as usize - (meta.blinding_factors() + 1);
    for current_phase in pk.vk.cs.phases() {
        let column_indices = meta
            .advice_column_phase
            .iter()
            .enumerate()
            .filter_map(|(column_index, phase)| {
                if current_phase == *phase {
                    Some(column_index)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();

        for (i, ((circuit, advice), instance_values)) in circuits
            .iter()
            .zip(advices.iter_mut())
            .zip(instances.iter())
            .enumerate()
        {
            let advice_fixed = builder.user_function(
                format!("advice_{:?}_{}", current_phase, i),
                user_functions::calculate_advices::<Scheme, ConcreteCircuit>(
                    params.n(),
                    params.k(),
                    pk.vk.cs.num_instance_columns,
                    current_phase,
                    meta,
                    config.clone(),
                ),
                vec![
                    builder.array(
                        format!("instance_array_{}", i),
                        Typ::lagrange(params.n()),
                        instance_values.to_owned(),
                    ),
                    challenges.clone(),
                    circuit.clone(),
                ],
            );
            let (advice_numerator, advice_dominator) = builder.unpack_pair(
                format!("advice_numerator_{:?}_{}", current_phase, i),
                Typ::Array(
                    Box::new(Typ::lagrange(params.n())),
                    pk.vk.cs.num_advice_columns,
                ),
                format!("advice_dominator_{:?}_{}", current_phase, i),
                Typ::Array(
                    Box::new(Typ::lagrange(params.n())),
                    pk.vk.cs.num_advice_columns,
                ),
                advice_fixed,
            );

            let advice_numerator = builder.user_function(
                "advice_numerator_filtered".to_string(),
                user_functions::filter_accordingly(
                    column_indices.clone(),
                    pk.vk.cs.num_advice_columns,
                    params.n(),
                ),
                vec![advice_numerator],
            );
            let advice_dominator = builder.user_function(
                "advice_dominator_filtered".to_string(),
                user_functions::filter_accordingly(
                    column_indices.clone(),
                    pk.vk.cs.num_advice_columns,
                    params.n(),
                ),
                vec![advice_dominator],
            );

            let advice_values = advice_numerator / advice_dominator;

            let advice_values = column_indices
                .iter()
                .enumerate()
                .map(|(j, column_index)| {
                    let advice_poly = builder.array_get(
                        format!("advice_{:?}_{}_{}", current_phase, i, j),
                        advice_values.clone(),
                        j,
                    );
                    if meta.unblinded_advice_columns.contains(column_index) {
                        advice_poly
                    } else {
                        builder.blind(
                            format!("advice_blinded_{:?}_{}_{}", current_phase, i, j),
                            advice_poly,
                            unusable_rows_start,
                        )
                    }
                })
                .collect::<Vec<_>>();

            for advice_poly in advice_values.iter().cloned() {
                transcript = kzg_commit_lagrange(builder, advice_poly, lagrange_points, transcript);
            }

            for (i, p) in column_indices.into_iter().zip(advice_values.into_iter()) {
                advice[i] = Some(p);
            }
        }

        for (index, phase) in meta.challenge_phase.iter().enumerate() {
            if current_phase == *phase {
                let (transcript0, challenge_scalar) =
                    builder.squeeze_challenge_scalar(format!("challege_{:?}", phase), transcript);
                transcript = transcript0;
                let index = builder.constant("index".to_string(), index);
                challenges = builder.user_function_by_id(
                    format!("challenges_{:?}", phase),
                    challenges_dict_insert,
                    vec![challenges, index, challenge_scalar],
                );
            }
        }
    }

    let advices = advices
        .into_iter()
        .map(|advice| advice.into_iter().map(Option::unwrap).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let challenges = builder.user_function(
        "challenges".to_string(),
        user_functions::collect_challenges::<Scheme::Scalar>(meta.num_challenges),
        vec![challenges],
    );

    unimplemented!()
}
