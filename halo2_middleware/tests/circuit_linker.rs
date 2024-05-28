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
use halo2_middleware::{ff::Field, poly::Rotation};

#[derive(Clone)]
struct CircuitAConfig {
    // A gate that uses selector, fixed, advice, has addition, multiplication and rotation:
    // s_gate[0] * (a[0] - b[0] * c[0])
    s_mul: Column<Fixed>,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    // A gate that uses a lookup to constraint that c[0] is not zero by looking into a dynamic
    // table:
    // s_c_not_zero * c in tbl_s_not_zero * tbl_x
    s_c_not_zero: Column<Fixed>,
    // Dynamic table without constraints
    tbl_s_not_zero: Column<Fixed>,
    tbl_x: Column<Advice>,
}

#[derive(Clone)]
struct CircuitA<F: Field> {
    // k: u32,
    // Vector of (b, c, is_not_zero)
    inputs: Vec<(F, F, bool)>,
}

impl<F: Field + From<u64>> Circuit<F> for CircuitA<F> {
    type Config = CircuitAConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let s_mul = meta.fixed_column(); // Fixed 0
        let a = meta.advice_column(); // Advice 0
        let b = meta.advice_column(); // Advice 1
        let c = meta.advice_column(); // Advice 2
        let s_c_not_zero = meta.fixed_column(); // Fixed 1
        let tbl_s_not_zero = meta.fixed_column(); // Fixed 2
        let tbl_x = meta.advice_column(); // Advice 3

        meta.create_gate("mul", |meta| {
            let s_mul = meta.query_fixed(s_mul, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            vec![s_mul * (a - b * c)]
        });

        meta.lookup_any("not_zero", |meta| {
            let s_c_not_zero = meta.query_fixed(s_c_not_zero, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let tbl_s_not_zero = meta.query_fixed(tbl_s_not_zero, Rotation::cur());
            let tbl_x = meta.query_advice(tbl_x, Rotation::cur());

            let lhs = s_c_not_zero * c;
            let rhs = tbl_s_not_zero * tbl_x;
            vec![(lhs, rhs)]
        });

        CircuitAConfig {
            s_mul,
            a,
            b,
            c,
            s_c_not_zero,
            tbl_s_not_zero,
            tbl_x,
        }
    }

    fn synthesize(
        &self,
        config: CircuitAConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(
            || "mul",
            |mut region| {
                let mut offset = 0;
                for (b, c, is_not_zero) in &self.inputs {
                    region
                        .assign_advice(|| "", config.a, offset, || Value::known(*b * *c))
                        .unwrap();
                    region
                        .assign_advice(|| "", config.b, offset, || Value::known(*b))
                        .unwrap();
                    region
                        .assign_advice(|| "", config.c, offset, || Value::known(*c))
                        .unwrap();
                    if *is_not_zero {
                        region
                            .assign_fixed(
                                || "",
                                config.s_c_not_zero,
                                offset,
                                || Value::known(F::ONE),
                            )
                            .unwrap();
                    }
                    offset += 1;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "tbl_not_zero",
            |mut region| {
                let mut offset = 0;
                for (_, c, is_not_zero) in &self.inputs {
                    if *is_not_zero {
                        region
                            .assign_fixed(
                                || "",
                                config.s_c_not_zero,
                                offset,
                                || Value::known(F::ONE),
                            )
                            .unwrap();
                        region
                            .assign_advice(|| "", config.tbl_x, offset, || Value::known(*c))
                            .unwrap();
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

#[derive(Clone)]
struct CircuitBConfig {
    s_not_zero: Column<Fixed>,
    x: Column<Advice>,
    x_inv: Column<Advice>,
}

#[derive(Clone)]
struct CircuitB<F: Field> {
    // k: u32,
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

        meta.create_gate("not_zero", |meta| {
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
                        .assign_fixed(|| "", config.s_not_zero, offset, || Value::known(F::ONE))
                        .unwrap();
                    region
                        .assign_advice(|| "", config.x, offset, || Value::known(*x))
                        .unwrap();
                    let x_inv: Option<F> = x.invert().into();
                    region
                        .assign_advice(|| "", config.x_inv, offset, || Value::known(x_inv.unwrap()))
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
