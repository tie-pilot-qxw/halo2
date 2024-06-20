use halo2_debug::check_witness;
use halo2_frontend::{
    circuit::{compile_circuit, Layouter, SimpleFloorPlanner, Value, WitnessCalculator},
    plonk::{
        circuit::Column, Advice, Circuit, ConstraintSystem, Error as ErrorFront, Expression, Fixed,
    },
};
use halo2_middleware::circuit::{Any, ColumnMid};
use halo2_middleware::circuit_linker::{
    link_cs, link_preprocessing, link_witness, LinkConfig, MergeStrategy,
};
use halo2_middleware::{circuit::CompiledCircuit, ff::Field, poly::Rotation};
use std::collections::HashMap;

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
    // Dynamic table without constraints.  To be replaced by the columns of the circuit B which
    // applies constraints to the table.
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
        meta.annotate_column(s_mul, || "s_mul");
        meta.annotate_column(a, || "a");
        meta.annotate_column(b, || "b");
        meta.annotate_column(c, || "c");
        meta.annotate_column(s_c_not_zero, || "s_c_not_zero");
        meta.annotate_column(tbl_s_not_zero, || "tbl_s_not_zero");
        meta.annotate_column(tbl_x, || "tbl_x");

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

            let lhs = s_c_not_zero.clone() * c;
            let rhs = tbl_s_not_zero.clone() * tbl_x;
            vec![(s_c_not_zero, tbl_s_not_zero), (lhs, rhs)]
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
                        .assign_fixed(|| "", config.s_mul, offset, || Value::known(F::ONE))
                        .unwrap();
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
                                config.tbl_s_not_zero,
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
        meta.annotate_column(s_not_zero, || "s_not_zero");
        meta.annotate_column(x, || "x");
        meta.annotate_column(x_inv, || "x_inv");

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

use halo2_debug::display::{expr_disp_names, lookup_arg_disp_names};
use halo2curves::bn256::Fr;

fn f(v: u64) -> Fr {
    Fr::from(v)
}

#[test]
fn test_circuit_linker() {
    let circuit_a: CircuitA<Fr> = CircuitA {
        inputs: vec![
            (f(5), f(8), false),
            (f(3), f(10), true),
            (f(1), f(3), true),
            (f(7), f(0), false),
        ],
    };

    let circuit_b: CircuitB<Fr> = CircuitB {
        inputs: vec![f(1), f(2), f(3), f(4), f(5), f(10)],
    };

    let k = 6;
    let (compiled_circuit_a, config_a, cs_a) = compile_circuit(k, &circuit_a, false).unwrap();
    let (compiled_circuit_b, config_b, cs_b) = compile_circuit(k, &circuit_b, false).unwrap();

    let names_a = &compiled_circuit_a.cs.general_column_annotations;
    let names_b = &compiled_circuit_b.cs.general_column_annotations;

    const CIRCUIT_A: usize = 0;
    const CIRCUIT_B: usize = 1;
    const COL_TBL_X: usize = 3;
    const COL_TBL_S_NOT_ZERO: usize = 2;
    const COL_X: usize = 0;
    const COL_S_NOT_ZERO: usize = 0;
    assert_eq!(
        "tbl_x",
        names_a
            .get(&ColumnMid::new(Any::Advice, COL_TBL_X))
            .unwrap()
    );
    assert_eq!(
        "tbl_s_not_zero",
        names_a
            .get(&ColumnMid::new(Any::Fixed, COL_TBL_S_NOT_ZERO))
            .unwrap()
    );
    assert_eq!(
        "x",
        names_b.get(&ColumnMid::new(Any::Advice, COL_X)).unwrap()
    );
    assert_eq!(
        "s_not_zero",
        names_b
            .get(&ColumnMid::new(Any::Fixed, COL_S_NOT_ZERO))
            .unwrap()
    );

    let cfg = LinkConfig {
        shared_advice_columns: vec![vec![(CIRCUIT_A, COL_TBL_X), (CIRCUIT_B, COL_X)]],
        shared_fixed_columns: vec![vec![
            (CIRCUIT_A, COL_TBL_S_NOT_ZERO),
            (CIRCUIT_B, COL_S_NOT_ZERO),
        ]],
        shared_challenges: vec![],
        witness_merge_strategy: vec![MergeStrategy::Main(CIRCUIT_B, COL_X)],
        fixed_merge_strategy: vec![MergeStrategy::Main(CIRCUIT_B, COL_S_NOT_ZERO)],
    };
    {
        // CircuitA
        let cs_a = &compiled_circuit_a.cs;
        assert_eq!(
            "s_mul * (a - b * c)",
            format!("{}", expr_disp_names(&cs_a.gates[0].poly, names_a))
        );
        assert_eq!(
            "[s_c_not_zero, s_c_not_zero * c] in [tbl_s_not_zero, tbl_s_not_zero * tbl_x]",
            format!("{}", lookup_arg_disp_names(&cs_a.lookups[0], names_a))
        );

        // CircuitB
        let cs_b = &compiled_circuit_b.cs;
        assert_eq!(
            "s_not_zero * (x * x_inv - 1)",
            format!("{}", expr_disp_names(&cs_b.gates[0].poly, names_b))
        );
    }

    let (cs, map) = link_cs(&cfg, &[compiled_circuit_a.cs, compiled_circuit_b.cs]);

    // CircuitC
    let cs_c = &cs;
    let names_c = &cs.general_column_annotations;
    assert_eq!(
        "s_mul * (a - b * c)",
        format!("{}", expr_disp_names(&cs_c.gates[0].poly, names_c))
    );
    assert_eq!(
        "s_not_zero * (x * x_inv - 1)",
        format!("{}", expr_disp_names(&cs_c.gates[1].poly, names_c))
    );
    assert_eq!(
        "[s_c_not_zero, s_c_not_zero * c] in [s_not_zero, s_not_zero * x]",
        format!("{}", lookup_arg_disp_names(&cs_c.lookups[0], names_c))
    );

    let preprocessing = link_preprocessing(
        &cfg,
        &cs,
        &map,
        vec![
            compiled_circuit_a.preprocessing,
            compiled_circuit_b.preprocessing,
        ],
    );
    // println!("Comb");
    // print_fixed(&preprocessing.fixed);
    let compiled_circuit = CompiledCircuit { cs, preprocessing };

    let public: Vec<Vec<Fr>> = Vec::new();
    let mut witness_calc_a = WitnessCalculator::new(k, &circuit_a, &config_a, &cs_a, &public);
    let mut witness_calc_b = WitnessCalculator::new(k, &circuit_b, &config_b, &cs_b, &public);
    let challenges = HashMap::new();
    let mut witness: Vec<Vec<Fr>> = vec![vec![]; compiled_circuit.cs.num_advice_columns];
    for phase in 0..compiled_circuit.cs.phases() {
        let witness_a = witness_calc_a.calc(phase as u8, &challenges).unwrap();
        let witness_b = witness_calc_b.calc(phase as u8, &challenges).unwrap();
        let phase_witness =
            link_witness(&cfg, &compiled_circuit.cs, &map, vec![witness_a, witness_b]);
        for (i, witness_column) in phase_witness.into_iter().filter_map(|c| c).enumerate() {
            witness[i] = witness_column;
        }
    }

    let blinding_rows = 10;
    check_witness(&compiled_circuit, k, blinding_rows, &witness, &public);
}
