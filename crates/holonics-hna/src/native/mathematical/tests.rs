use super::*;

fn row(values: &[i64]) -> Vec<RationalWire> {
    values.iter().map(|v| RationalWire::integer(*v)).collect()
}
fn rows(values: &[&[i64]]) -> RationalMatrixWire {
    values.iter().map(|r| row(r)).collect()
}
fn construct() -> MathematicalRequest {
    MathematicalRequest::ConstructBilinear {
        target: BilinearTargetWire {
            left_extent: 2,
            right_extent: 2,
            coefficients: rows(&[&[1, 0, 0, -1], &[0, 1, 1, 0]]),
        },
        construction: BilinearConstructionWire::Search {
            left_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            right_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            min_products: 1,
            max_products: 3,
            max_candidates: 1000,
        },
    }
}
#[test]
fn mathematical_wire_keeps_exact_coefficients_and_refuses_extra_fields() {
    let request = construct();
    let value = serde_json::to_value(&request).unwrap();
    assert_eq!(
        serde_json::from_value::<MathematicalRequest>(value.clone()).unwrap(),
        request
    );
    let mut bad = value;
    bad["target"]["task_label"] = json!("expected answer");
    assert!(serde_json::from_value::<MathematicalRequest>(bad).is_err());
    assert!(matrix(&vec![row(&[1]), row(&[1, 2])]).is_err());
    assert!(matrix(&vec![vec![RationalWire {
        numerator: "1".into(),
        denominator: "0".into()
    }]])
    .is_err());
}
