use ff::{Field, PrimeField};
use halo2_middleware::expression::{Expression, Variable};
use num_bigint::BigUint;
use std::fmt;

/// Wrapper type over `PrimeField` that implements Display with nice output.
/// - If the value is a power of two, format it as `2^k`
/// - If the value is smaller than 2^16, format it in decimal
/// - If the value is bigger than congruent -2^16, format it in decimal as the negative congruent
/// (between -2^16 and 0).
/// - Else format it in hex without leading zeros.
pub struct FDisp<'a, F: PrimeField>(pub &'a F);

impl<F: PrimeField> fmt::Display for FDisp<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v = (*self.0).to_repr();
        let v = v.as_ref();
        let v = BigUint::from_bytes_le(v.as_ref());
        let v_bits = v.bits();
        if v_bits >= 8 && v.count_ones() == 1 {
            write!(f, "2^{}", v.trailing_zeros().unwrap_or_default())
        } else if v_bits < 16 {
            write!(f, "{}", v)
        } else {
            let v_neg = (F::ZERO - self.0).to_repr();
            let v_neg = v_neg.as_ref();
            let v_neg = BigUint::from_bytes_le(v_neg.as_ref());
            let v_neg_bits = v_neg.bits();
            if v_neg_bits < 16 {
                write!(f, "-{}", v_neg)
            } else {
                write!(f, "0x{:x}", v)
            }
        }
    }
}

pub struct ExprDisp<'a, F: PrimeField, V: Variable>(pub &'a Expression<F, V>);

impl<F: PrimeField, V: Variable> fmt::Display for ExprDisp<'_, F, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let is_sum = |e: &Expression<F, V>| -> bool { matches!(e, Expression::Sum(_, _)) };
        let fmt_expr =
            |e: &Expression<F, V>, f: &mut fmt::Formatter<'_>, parens: bool| -> fmt::Result {
                if parens {
                    write!(f, "(")?;
                }
                write!(f, "{}", ExprDisp(e))?;
                if parens {
                    write!(f, ")")?;
                }
                Ok(())
            };

        match self.0 {
            Expression::Constant(c) => write!(f, "{}", FDisp(c)),
            Expression::Var(v) => write!(f, "{}", v),
            Expression::Negated(a) => {
                write!(f, "-")?;
                fmt_expr(&a, f, is_sum(&a))
            }
            Expression::Sum(a, b) => {
                fmt_expr(&a, f, false)?;
                if let Expression::Negated(neg) = &**b {
                    write!(f, " - ")?;
                    fmt_expr(&neg, f, is_sum(&neg))
                } else {
                    write!(f, " + ")?;
                    fmt_expr(&b, f, false)
                }
            }
            Expression::Product(a, b) => {
                fmt_expr(&a, f, is_sum(&a))?;
                write!(f, " * ")?;
                fmt_expr(&b, f, is_sum(&b))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_middleware::circuit::{Any, QueryMid, VarMid};
    use halo2_middleware::poly::Rotation;
    use halo2curves::bn256::Fr;

    #[test]
    fn test_expr_disp() {
        type E = Expression<Fr, VarMid>;
        let a0 = VarMid::Query(QueryMid {
            column_index: 0,
            column_type: Any::Advice,
            rotation: Rotation(0),
        });
        let a1 = VarMid::Query(QueryMid {
            column_index: 1,
            column_type: Any::Advice,
            rotation: Rotation(0),
        });
        let a0: E = Expression::Var(a0);
        let a1: E = Expression::Var(a1);

        let e = a0.clone() + a1.clone();
        assert_eq!("a0 + a1", format!("{}", ExprDisp(&e)));
        let e = a0.clone() + a1.clone() + a0.clone();
        assert_eq!("a0 + a1 + a0", format!("{}", ExprDisp(&e)));

        let e = a0.clone() * a1.clone();
        assert_eq!("a0 * a1", format!("{}", ExprDisp(&e)));
        let e = a0.clone() * a1.clone() * a0.clone();
        assert_eq!("a0 * a1 * a0", format!("{}", ExprDisp(&e)));

        let e = a0.clone() - a1.clone();
        assert_eq!("a0 - a1", format!("{}", ExprDisp(&e)));
        let e = (a0.clone() - a1.clone()) - a0.clone();
        assert_eq!("a0 - a1 - a0", format!("{}", ExprDisp(&e)));
        let e = a0.clone() - (a1.clone() - a0.clone());
        assert_eq!("a0 - (a1 - a0)", format!("{}", ExprDisp(&e)));

        let e = a0.clone() * a1.clone() + a0.clone();
        assert_eq!("a0 * a1 + a0", format!("{}", ExprDisp(&e)));
        let e = a0.clone() * (a1.clone() + a0.clone());
        assert_eq!("a0 * (a1 + a0)", format!("{}", ExprDisp(&e)));
    }

    #[test]
    fn test_f_disp() {
        let v = Fr::ZERO;
        assert_eq!("0", format!("{}", FDisp(&v)));

        let v = Fr::ONE;
        assert_eq!("1", format!("{}", FDisp(&v)));

        let v = Fr::from(12345u64);
        assert_eq!("12345", format!("{}", FDisp(&v)));

        let v = Fr::from(0x10000);
        assert_eq!("2^16", format!("{}", FDisp(&v)));

        let v = Fr::from(0x12345);
        assert_eq!("0x12345", format!("{}", FDisp(&v)));

        let v = Fr::from(-Fr::ONE);
        assert_eq!("-1", format!("{}", FDisp(&v)));

        let v = Fr::from(-Fr::from(12345u64));
        assert_eq!("-12345", format!("{}", FDisp(&v)));
    }
}
