/// Here we construct two circuits one for adding two vectors and one for multiplying and we check that their transcripts have the same inputs
/// by way of the unblinded inputs.
/// This is a simple example of how to use unblinded inputs to match up circuits that might be proved on different host machines.
use std::marker::PhantomData;

use ff::FromUniformBytes;
use halo2_debug::test_rng;
use halo2_proofs::{
    arithmetic::{CurveAffine, Field},
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::*,
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::{ProverIPA, VerifierIPA},
            strategy::AccumulatorStrategy,
        },
        Rotation,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};

// ANCHOR: instructions
trait NumericInstructions<F: Field>: Chip<F> {
    /// Variable representing a number.
    type Num;

    /// Loads a number into the circuit as an unblinded input this can be matched to inputs in other circuits !
    fn load_unblinded(
        &self,
        layouter: impl Layouter<F>,
        a: &[Value<F>],
    ) -> Result<Vec<Self::Num>, ErrorFront>;

    /// Returns `c = a * b`. The caller is responsible for ensuring that `a.len() == b.len()`.
    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: &[Self::Num],
        b: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront>;

    /// Returns `c = a + b`. The caller is responsible for ensuring that `a.len() == b.len()`.
    fn add(
        &self,
        layouter: impl Layouter<F>,
        a: &[Self::Num],
        b: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront>;

    /// Exposes a number as a public input to the circuit.
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: &Self::Num,
        row: usize,
    ) -> Result<(), ErrorFront>;
}
// ANCHOR_END: instructions

// ANCHOR: chip
/// The chip that will implement our instructions! Chips store their own
/// config, as well as type markers if necessary.
struct MultChip<F: Field> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

// ANCHOR: chip
/// The chip that will implement our instructions! Chips store their own
/// config, as well as type markers if necessary.
struct AddChip<F: Field> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}
// ANCHOR_END: chip

// ANCHOR: chip-config
/// Chip state is stored in a config struct. This is generated by the chip
/// during configuration, and then stored inside the chip.
#[derive(Clone, Debug)]
struct FieldConfig {
    advice: [Column<Advice>; 3],
    instance: Column<Instance>,
    s: Selector,
}

impl<F: Field> MultChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s = meta.selector();

        // Define our multiplication gate!
        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[2], Rotation::cur());
            let s_mul = meta.query_selector(s);

            vec![s_mul * (lhs * rhs - out)]
        });

        FieldConfig {
            advice,
            instance,
            s,
        }
    }
}

impl<F: Field> AddChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s = meta.selector();

        // Define our multiplication gate!
        meta.create_gate("add", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[2], Rotation::cur());
            let s_add = meta.query_selector(s);

            vec![s_add * (lhs + rhs - out)]
        });

        FieldConfig {
            advice,
            instance,
            s,
        }
    }
}
// ANCHOR_END: chip-config

// ANCHOR: chip-impl
impl<F: Field> Chip<F> for MultChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
// ANCHOR_END: chip-impl

// ANCHOR: chip-impl
impl<F: Field> Chip<F> for AddChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// ANCHOR: instructions-impl
/// A variable representing a number.
#[derive(Clone, Debug)]
struct Number<F: Field>(AssignedCell<F, F>);

impl<F: Field> NumericInstructions<F> for MultChip<F> {
    type Num = Number<F>;

    fn load_unblinded(
        &self,
        mut layouter: impl Layouter<F>,
        values: &[Value<F>],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        let config = self.config();

        layouter.assign_region(
            || "load unblinded",
            |mut region| {
                values
                    .iter()
                    .enumerate()
                    .map(|(i, value)| {
                        region
                            .assign_advice(|| "unblinded input", config.advice[0], i, || *value)
                            .map(Number)
                    })
                    .collect()
            },
        )
    }

    fn add(
        &self,
        _: impl Layouter<F>,
        _: &[Self::Num],
        _: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        panic!("Not implemented")
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: &[Self::Num],
        b: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        let config = self.config();
        assert_eq!(a.len(), b.len());

        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                a.iter()
                    .zip(b.iter())
                    .enumerate()
                    .map(|(i, (a, b))| {
                        config.s.enable(&mut region, i)?;

                        a.0.copy_advice(|| "lhs", &mut region, config.advice[0], i)?;
                        b.0.copy_advice(|| "rhs", &mut region, config.advice[1], i)?;

                        let value = a.0.value().copied() * b.0.value();

                        // Finally, we do the assignment to the output, returning a
                        // variable to be used in another part of the circuit.
                        region
                            .assign_advice(|| "lhs * rhs", config.advice[2], i, || value)
                            .map(Number)
                    })
                    .collect()
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: &Self::Num,
        row: usize,
    ) -> Result<(), ErrorFront> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}
// ANCHOR_END: instructions-impl

impl<F: Field> NumericInstructions<F> for AddChip<F> {
    type Num = Number<F>;

    fn load_unblinded(
        &self,
        mut layouter: impl Layouter<F>,
        values: &[Value<F>],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        let config = self.config();

        layouter.assign_region(
            || "load unblinded",
            |mut region| {
                values
                    .iter()
                    .enumerate()
                    .map(|(i, value)| {
                        region
                            .assign_advice(|| "unblinded input", config.advice[0], i, || *value)
                            .map(Number)
                    })
                    .collect()
            },
        )
    }

    fn mul(
        &self,
        _: impl Layouter<F>,
        _: &[Self::Num],
        _: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        panic!("Not implemented")
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: &[Self::Num],
        b: &[Self::Num],
    ) -> Result<Vec<Self::Num>, ErrorFront> {
        let config = self.config();
        assert_eq!(a.len(), b.len());

        layouter.assign_region(
            || "add",
            |mut region: Region<'_, F>| {
                a.iter()
                    .zip(b.iter())
                    .enumerate()
                    .map(|(i, (a, b))| {
                        config.s.enable(&mut region, i)?;

                        a.0.copy_advice(|| "lhs", &mut region, config.advice[0], i)?;
                        b.0.copy_advice(|| "rhs", &mut region, config.advice[1], i)?;

                        let value = a.0.value().copied() + b.0.value();

                        // Finally, we do the assignment to the output, returning a
                        // variable to be used in another part of the circuit.
                        region
                            .assign_advice(|| "lhs + rhs", config.advice[2], i, || value)
                            .map(Number)
                    })
                    .collect()
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: &Self::Num,
        row: usize,
    ) -> Result<(), ErrorFront> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}

#[derive(Default, Clone)]
struct MulCircuit<F: Field> {
    a: Vec<Value<F>>,
    b: Vec<Value<F>>,
}

impl<F: Field> Circuit<F> for MulCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the three advice columns that FieldChip uses for I/O.
        let advice = [
            meta.unblinded_advice_column(),
            meta.unblinded_advice_column(),
            meta.unblinded_advice_column(),
        ];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        MultChip::configure(meta, advice, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let field_chip = MultChip::<F>::construct(config);

        // Load our unblinded values into the circuit.
        let a = field_chip.load_unblinded(layouter.namespace(|| "load a"), &self.a)?;
        let b = field_chip.load_unblinded(layouter.namespace(|| "load b"), &self.b)?;

        let ab = field_chip.mul(layouter.namespace(|| "a * b"), &a, &b)?;

        for (i, c) in ab.iter().enumerate() {
            // Expose the result as a public input to the circuit.
            field_chip.expose_public(layouter.namespace(|| "expose c"), c, i)?;
        }
        Ok(())
    }
}
// ANCHOR_END: circuit

#[derive(Default, Clone)]
struct AddCircuit<F: Field> {
    a: Vec<Value<F>>,
    b: Vec<Value<F>>,
}

impl<F: Field> Circuit<F> for AddCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the three advice columns that FieldChip uses for I/O.
        let advice = [
            meta.unblinded_advice_column(),
            meta.unblinded_advice_column(),
            meta.unblinded_advice_column(),
        ];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        AddChip::configure(meta, advice, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let field_chip = AddChip::<F>::construct(config);

        // Load our unblinded values into the circuit.
        let a = field_chip.load_unblinded(layouter.namespace(|| "load a"), &self.a)?;
        let b = field_chip.load_unblinded(layouter.namespace(|| "load b"), &self.b)?;

        let ab = field_chip.add(layouter.namespace(|| "a + b"), &a, &b)?;

        for (i, c) in ab.iter().enumerate() {
            // Expose the result as a public input to the circuit.
            field_chip.expose_public(layouter.namespace(|| "expose c"), c, i)?;
        }
        Ok(())
    }
}
// ANCHOR_END: circuit

fn test_prover<C: CurveAffine>(
    k: u32,
    circuit: impl Circuit<C::Scalar>,
    expected: bool,
    instances: Vec<C::Scalar>,
) -> Vec<u8>
where
    C::Scalar: FromUniformBytes<64>,
{
    let rng = test_rng();

    let params = ParamsIPA::<C>::new(k);
    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk, &circuit).unwrap();

    let instances = vec![vec![instances]];
    let proof = {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        create_proof::<IPACommitmentScheme<C>, ProverIPA<C>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &instances,
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        transcript.finalize()
    };

    let accepted = {
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

        verify_proof::<IPACommitmentScheme<C>, VerifierIPA<C>, _, _, AccumulatorStrategy<_>>(
            &params,
            pk.get_vk(),
            &instances,
            &mut transcript,
        )
    };

    assert_eq!(accepted, expected);

    proof
}

#[test]
fn test_vector_ops_unbinded() {
    use halo2curves::pasta::Fp;

    const N: usize = 10;
    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 7;

    // Prepare the inputs to the circuit!
    let a = [Fp::from(2); N];
    let b = [Fp::from(3); N];
    let c_mul: Vec<Fp> = a.iter().zip(b).map(|(&a, b)| a * b).collect();
    let c_add: Vec<Fp> = a.iter().zip(b).map(|(&a, b)| a + b).collect();

    // Instantiate the mul circuit with the inputs.
    let mul_circuit = MulCircuit {
        a: a.iter().map(|&x| Value::known(x)).collect(),
        b: b.iter().map(|&x| Value::known(x)).collect(),
    };

    // Instantiate the add circuit with the inputs.
    let add_circuit = AddCircuit {
        a: a.iter().map(|&x| Value::known(x)).collect(),
        b: b.iter().map(|&x| Value::known(x)).collect(),
    };

    // the commitments will be the first columns of the proof transcript so we can compare them easily
    let proof_1 = halo2_debug::test_result(
        || test_prover::<halo2curves::pasta::EqAffine>(k, mul_circuit.clone(), true, c_mul.clone()),
        "1f726eaddd926057e6c2aa8a364d1b4192da27f53c38c9f21d8924ef3eb0f0ab",
    );

    // the commitments will be the first columns of the proof transcript so we can compare them easily
    let proof_2 = halo2_debug::test_result(
        || test_prover::<halo2curves::pasta::EqAffine>(k, add_circuit.clone(), true, c_add.clone()),
        "a42eb2f3e4761e6588bfd8db7e7035ead1cc1331017b6b09a7b75ddfbefefc58",
    );

    // the commitments will be the first columns of the proof transcript so we can compare them easily
    // here we compare the first 10 bytes of the commitments
    println!(
        "Commitments are equal: {:?}",
        proof_1[..10] == proof_2[..10]
    );
    // ANCHOR_END: test-circuit
}
