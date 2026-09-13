//! Exterior Rust source release for a retained exact bilinear realization.
//!
//! The printer only serializes the returned factor circuit.  It does not infer a
//! new operator, expand the tensor image, or invoke a compiler/runtime.

use super::NativeSessionError;
use holonic_engine::exact_linear::BilinearRealization;
use num_rational::BigRational;
use num_traits::Zero;

/// Render a retained realization as an exact rational Rust function.
///
/// In linear mode the retained right port is the declared unit chart (one
/// coordinate).  The generated function therefore accepts only its left port.
/// Bilinear mode retains and checks both input ports.
pub fn rust_function(
    realization: &BilinearRealization,
    linear: bool,
) -> Result<String, NativeSessionError> {
    let left = realization.core().left_forms();
    let right = realization.core().right_forms();
    let receiver = &realization.receiver().particular;

    if left.columns() == 0 || right.columns() == 0 || receiver.columns() != left.rows() {
        return Err(invalid("retained realization has an invalid factor graph"));
    }
    if linear && right.columns() != 1 {
        return Err(invalid(
            "linear code release requires a one-coordinate unit right chart",
        ));
    }

    let mut out = String::new();
    out.push_str("// Generated from a retained exact Holonic factor graph.\n");
    out.push_str(&format!(
        "// domain: left [{}], right [{}]; output [{}]; products [{}]\n",
        left.columns(),
        right.columns(),
        receiver.rows(),
        left.rows()
    ));
    if linear {
        out.push_str(
            "pub fn holonic_apply(left: &[num_rational::BigRational]) -> Result<Vec<num_rational::BigRational>, &'static str> {\n",
        );
    } else {
        out.push_str(
            "pub fn holonic_apply(left: &[num_rational::BigRational], right: &[num_rational::BigRational]) -> Result<Vec<num_rational::BigRational>, &'static str> {\n",
        );
    }
    out.push_str(&format!(
        "    if left.len() != {} {{ return Err(\"left input extent mismatch\"); }}\n",
        left.columns()
    ));
    if !linear {
        out.push_str(&format!(
            "    if right.len() != {} {{ return Err(\"right input extent mismatch\"); }}\n",
            right.columns()
        ));
    }

    for p in 0..left.rows() {
        out.push_str(&format!(
            "    let left_{p} = {};\n",
            dot_expr(left.row(p).map_err(invalid)?, "left")
        ));
        if linear {
            out.push_str(&format!(
                "    let product_{p} = left_{p} * {};\n",
                rational_expr(right.get(p, 0).map_err(invalid)?)
            ));
        } else {
            out.push_str(&format!(
                "    let right_{p} = {};\n",
                dot_expr(right.row(p).map_err(invalid)?, "right")
            ));
            out.push_str(&format!("    let product_{p} = left_{p} * right_{p};\n"));
        }
    }

    out.push_str("    Ok(vec![\n");
    for row in receiver.to_rows() {
        let terms = row
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(p, coefficient)| format!("({}) * &product_{p}", rational_expr(coefficient)))
            .collect::<Vec<_>>();
        out.push_str("        ");
        if terms.is_empty() {
            out.push_str("num_rational::BigRational::from_integer(num_bigint::BigInt::from(0)),\n");
        } else {
            out.push_str(&terms.join(" + "));
            out.push_str(",\n");
        }
    }
    out.push_str("    ])\n}\n");
    Ok(out)
}

fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

fn rational_expr(value: &BigRational) -> String {
    // Parse integer digits exactly; no float or bounded machine-integer conversion
    // changes a retained coefficient, including arbitrarily large values.
    format!(
        "num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b\"{}\", 10).ok_or(\"invalid generated numerator\")?, num_bigint::BigInt::parse_bytes(b\"{}\", 10).ok_or(\"invalid generated denominator\")?)",
        value.numer(),
        value.denom()
    )
}

fn dot_expr(row: &[BigRational], input: &str) -> String {
    let terms = row
        .iter()
        .enumerate()
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .map(|(i, coefficient)| format!("({}) * &{input}[{i}]", rational_expr(coefficient)))
        .collect::<Vec<_>>();
    if terms.is_empty() {
        "num_rational::BigRational::from_integer(num_bigint::BigInt::from(0))".to_string()
    } else {
        terms.join(" + ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::exact_linear::{BilinearOperator, BilinearProductCore, ExactRatMatrix};
    use num_bigint::BigInt;
    use std::sync::Arc;

    fn q(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn linear_release_rejects_non_unit_right_chart() {
        let core = Arc::new(
            BilinearProductCore::new(
                ExactRatMatrix::new(vec![vec![q(1)]]).unwrap(),
                ExactRatMatrix::new(vec![vec![q(1), q(0)]]).unwrap(),
            )
            .unwrap(),
        );
        let target =
            BilinearOperator::new(1, 2, ExactRatMatrix::new(vec![vec![q(1), q(0)]]).unwrap())
                .unwrap();
        let realization = core.bind(&target).unwrap().unwrap();
        assert!(rust_function(&realization, true).is_err());
    }
}
