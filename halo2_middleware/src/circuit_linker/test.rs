use super::*;

use crate::{ff::Field, poly::Rotation};
use halo2_frontend::{
    circuit::{
        compile_circuit, AssignedCell, Layouter, Region, SimpleFloorPlanner, Value,
        WitnessCalculator,
    },
    dev::MockProver,
    plonk::{
        circuit::{Challenge, Column},
        Advice, Circuit, ConstraintSystem, Error as ErrorFront, Expression, FirstPhase, Fixed,
        Instance, SecondPhase, Selector,
    },
};

#[derive(Clone)]
struct CircuitAConfig {
    // A gate that uses selector, fixed, advice, has addition, multiplication and rotation
    // s_gate[0] * (a[0] - b[0] * c[0])
    s_mul: Column<Fixed>,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    s_not_zero: Column<Fixed>,
    x: Column<Advice>,
}

#[derive(Clone)]
struct CircuitBConfig {
    s_not_zero: Column<Fixed>,
    x: Column<Advice>,
    x_inv: Column<Advice>,
}

#[derive(Clone)]
struct CircuitB<F: Field> {
    k: u32,
    inputs: Vec<F>,
}

impl<F: Field + From<u64>> Circuit<F> for CircuitB<F> {
    type Config = CircuitBConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let s_not_zero = meta.fixed_column(); // Fixed 0
        let x = meta.advice_column(); // Advice 0
        let x_inv = meta.advice_column(); // Advice 1

        meta.create_gate("inverse", |meta| {
            let s_not_zero = meta.query_fixed(s_not_zero, Rotation::cur());
            let x = meta.query_advice(x, Rotation::cur());
            let x_inv = meta.query_advice(x_inv, Rotation::cur());

            vec![s_not_zero * (x * x_inv - Expression::Constant(F::from(1)))]
        });

        CircuitBConfig {
            s_not_zero,
            x,
            x_inv,
        }
    }

    fn synthesize(
        &self,
        config: CircuitBConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(
            || "inverses",
            |mut region| {
                let mut offset = 0;
                for x in &self.inputs {
                    region
                        .assign_advice(|| "", config.x, offset, || Value::known(*x))
                        .unwrap();
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}

#[test]
fn test_hello() {}
