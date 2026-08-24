use super::*;

use num_bigint::BigInt;

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn supported(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|value| rat(*value)).collect())
            .collect(),
    )
    .expect("supported rectangle")
}

fn testimony() -> OverlayTestimony {
    let source = |symbol: &str| {
        vec![SourceTestimony::Implementation {
            locator: "authenticated-w3-rest".to_owned(),
            symbol: symbol.to_owned(),
        }]
    };
    OverlayTestimony {
        input: source("W3Overlay.standing (inputs_embeds=)"),
        predecessor: source("W3Overlay.predecessor (y0)"),
        terminal_withdraw: vec![SourceTestimony::Intervention {
            statement: "withdraw rows [0, terminal)".to_owned(),
        }],
        v: source("W3Overlay.contract (v_weight)"),
        u: source("W3Overlay.contract (u_weight)"),
        re_entry: source("W3Overlay.re_entry (+)"),
    }
}

fn candidate(shape: OverlayShape, terminal_rows: usize) -> FactorizedCandidate {
    FactorizedCandidate::new(
        "delta.u.weight",
        "delta.v.weight",
        shape,
        1,
        terminal_rows,
        testimony(),
    )
}

fn receipt(
    defect: SparseDefect,
    left: SupportedFactor,
    right: SupportedFactor,
) -> RankDerivationReceipt {
    let zero = ExactRatMatrix::zero(defect.support_rows.len(), defect.support_columns.len())
        .expect("zero foil");
    RankDerivationReceipt {
        zero_rank_foil: SparseDefect {
            ambient_rows: defect.ambient_rows,
            ambient_columns: defect.ambient_columns,
            support_rows: defect.support_rows.clone(),
            support_columns: defect.support_columns.clone(),
            supported: zero,
        },
        separator: SeparatingReceiver {
            target: (1, 3),
            predecessor: rat(0),
            candidate: rat(6),
        },
        defect,
        left,
        right,
    }
}

fn valid_receipt() -> RankDerivationReceipt {
    receipt(
        SparseDefect {
            ambient_rows: 2,
            ambient_columns: 2_560,
            support_rows: vec![1],
            support_columns: vec![3, 7],
            supported: supported(&[&[6, 10]]),
        },
        SupportedFactor {
            ambient: 2,
            support: vec![1],
            values: vec![rat(2)],
        },
        SupportedFactor {
            ambient: 2_560,
            support: vec![3, 7],
            values: vec![rat(3), rat(5)],
        },
    )
}

#[test]
fn valid_sparse_rank_one_defect_is_admitted_and_terminal_quotient_precedes_contract() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        4,
    );
    let return_receipt = valid_receipt();
    let derivation = FactorDerivationReceipt::RankOne(return_receipt);
    let (complex, events) = factors
        .complex(Some(&derivation))
        .expect("valid candidate");
    assert_eq!(complex.dependency_span().expect("fronts"), 4);
    let fronts = complex.fronts().expect("fronts");
    let depth = |event| {
        fronts
            .iter()
            .position(|front| front.occurrences.contains(&event))
            .expect("event front")
    };
    assert!(depth(events.input) < depth(events.terminal));
    assert!(depth(events.terminal) < depth(events.factorized));
    assert_eq!(
        complex.shape.laws[&complex.shape.occurrences[&events.terminal].law].name,
        "phoenix.overlay.withdraw-terminal"
    );
    assert_eq!(
        complex.shape.laws[&complex.shape.occurrences[&events.factorized].law].name,
        FACTORIZED_LAW
    );
}

#[test]
fn false_supported_rank_refuses_without_dense_ambient_allocation() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        4,
    );
    let receipt = receipt(
        SparseDefect {
            ambient_rows: 2,
            ambient_columns: 2_560,
            support_rows: vec![0, 1],
            support_columns: vec![3, 7],
            supported: supported(&[&[1, 0], &[0, 1]]),
        },
        SupportedFactor {
            ambient: 2,
            support: vec![0, 1],
            values: vec![rat(1), rat(1)],
        },
        SupportedFactor {
            ambient: 2_560,
            support: vec![3, 7],
            values: vec![rat(1), rat(1)],
        },
    );
    let receipt = FactorDerivationReceipt::RankOne(receipt);
    assert!(matches!(
        factors.complex(Some(&receipt)),
        Err(CandidateRefusal::DefectRank { rank: 2 })
    ));
}

#[test]
fn wrong_supported_outer_product_refuses_exactly() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        4,
    );
    let mut receipt = valid_receipt();
    receipt.right.values[1] = rat(4);
    let receipt = FactorDerivationReceipt::RankOne(receipt);
    assert!(matches!(
        factors.complex(Some(&receipt)),
        Err(CandidateRefusal::ReconstructionMismatch)
    ));
}

#[test]
fn zero_supported_defect_refuses_as_zero_rank() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        4,
    );
    let mut receipt = valid_receipt();
    receipt.defect.supported = ExactRatMatrix::zero(1, 2).expect("zero supported defect");
    let receipt = FactorDerivationReceipt::RankOne(receipt);
    assert!(matches!(
        factors.complex(Some(&receipt)),
        Err(CandidateRefusal::DefectRank { rank: 0 })
    ));
}

#[test]
fn row_zero_refuses_before_terminal_quotient_construction() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        0,
    );
    assert!(matches!(
        factors.complex(Some(&FactorDerivationReceipt::RankOne(valid_receipt()))),
        Err(CandidateRefusal::FactorShape)
    ));
}

#[test]
fn structured_separator_must_match_exact_candidate_coordinate() {
    let factors = candidate(
        OverlayShape {
            rows: 2,
            input_width: 2_560,
        },
        4,
    );
    let mut receipt = valid_receipt();
    receipt.separator.candidate = rat(7);
    let receipt = FactorDerivationReceipt::RankOne(receipt);
    assert!(matches!(
        factors.complex(Some(&receipt)),
        Err(CandidateRefusal::ZeroRankFoilNotSeparated)
    ));
}
