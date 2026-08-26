use super::*;

use num_bigint::BigInt;

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|value| rat(*value)).collect())
            .collect(),
    )
    .expect("matrix")
}

fn section(address: &str, support: Vec<usize>, values: &[&[i64]]) -> SupportedDefectSection {
    let supported = matrix(values);
    SupportedDefectSection {
        address: address.to_owned(),
        parent_candidate: format!("candidate:{address}"),
        receiver: "graded-mathematical".to_owned(),
        successor_word: vec![format!("word:{address}")],
        chart: "control-chart".to_owned(),
        ambient_rows: 4,
        ambient_columns: 4,
        support_rows: support.clone(),
        support_columns: support,
        metrics: DefectMetrics {
            domain: ExactRatMatrix::identity(supported.columns()).expect("domain metric"),
            codomain: ExactRatMatrix::identity(supported.rows()).expect("codomain metric"),
        },
        supported,
    }
}

#[test]
fn zero_one_higher_and_singular_sections_return_complete_factor_fibres() {
    let zero = section("zero", vec![0, 1], &[&[0, 0], &[0, 0]])
        .derive()
        .expect("zero");
    assert_eq!(zero.disposition, FactorDisposition::NoChange);
    assert!(zero.factors.is_empty());
    assert_eq!(zero.radical_fibre.len(), 2);

    let rank_one = section("one", vec![0, 1], &[&[2, 4], &[3, 6]])
        .derive()
        .expect("one");
    assert_eq!(rank_one.derived_rank, 1);
    assert_eq!(rank_one.factors.len(), 1);
    assert_eq!(rank_one.reconstructed_defect, rank_one.section.supported);

    let rank_two_singular = section(
        "two-singular",
        vec![0, 1, 2],
        &[&[1, 0, 1], &[0, 1, 1], &[1, 1, 2]],
    )
    .derive()
    .expect("rank two");
    assert_eq!(rank_two_singular.derived_rank, 2);
    assert_eq!(rank_two_singular.factors.len(), 2);
    assert_eq!(rank_two_singular.radical_fibre.len(), 1);
    assert_eq!(rank_two_singular.open_exterior.len(), 1);
    let withdrawn = rank_two_singular.withdrawal_word.iter().fold(
        rank_two_singular.section.supported.clone(),
        |standing, step| standing.add(&step.delta).expect("withdraw"),
    );
    assert_eq!(
        withdrawn,
        ExactRatMatrix::zero(3, 3).expect("predecessor delta")
    );
}

#[test]
fn compatible_commuting_noncommuting_and_disjoint_overlaps_remain_distinct() {
    let compatible_left = section("compatible-left", vec![0, 1], &[&[1, 0], &[0, 2]]);
    let compatible_right = section("compatible-right", vec![1, 2], &[&[2, 0], &[0, 3]]);
    let commuting_left = section("commuting-left", vec![0, 1], &[&[1, 0], &[0, 2]]);
    let commuting_right = section("commuting-right", vec![0, 1], &[&[3, 0], &[0, 4]]);
    let noncommuting_left = section("noncommuting-left", vec![0, 1], &[&[0, 1], &[0, 0]]);
    let noncommuting_right = section("noncommuting-right", vec![0, 1], &[&[0, 0], &[1, 0]]);
    let disjoint_left = section("disjoint-left", vec![0], &[&[2]]);
    let disjoint_right = section("disjoint-right", vec![3], &[&[5]]);

    let compatible = compare_sections(&compatible_left, &compatible_right).expect("compatible");
    let OverlapKind::CompatibleGlue { glued } = compatible.kind else {
        panic!("compatible glue expected");
    };
    assert_eq!((glued.supported.rows(), glued.supported.columns()), (3, 3));
    assert_eq!(
        (glued.metrics.domain.rows(), glued.metrics.domain.columns()),
        (3, 3)
    );
    let commuting = compare_sections(&commuting_left, &commuting_right).expect("commuting");
    assert!(matches!(
        commuting.kind,
        OverlapKind::CommutingCocycle { .. }
    ));
    assert!(
        commuting
            .patch
            .expect("overlap")
            .cocycle
            .entries()
            .iter()
            .any(|entry| !entry.is_zero())
    );
    let noncommuting =
        compare_sections(&noncommuting_left, &noncommuting_right).expect("noncommuting");
    let OverlapKind::PathOrderedHolonomy { commutator, .. } = noncommuting.kind else {
        panic!("ordered overlap expected");
    };
    assert!(commutator.entries().iter().any(|entry| !entry.is_zero()));
    let disjoint = compare_sections(&disjoint_left, &disjoint_right).expect("disjoint");
    assert!(matches!(
        disjoint.kind,
        OverlapKind::DisjointInterchange { .. }
    ));
}

#[test]
fn a_nonidentity_metric_changes_the_returned_adjoint() {
    let mut section = section("metric", vec![0, 1], &[&[1, 2], &[0, 3]]);
    section.metrics = DefectMetrics {
        domain: matrix(&[&[2, 0], &[0, 5]]),
        codomain: matrix(&[&[3, 1], &[1, 4]]),
    };
    let bare = section.supported.transpose().expect("transpose");
    let receipt = section.derive().expect("metric return");
    assert_ne!(receipt.metric_adjoint, bare);
}

#[test]
fn a_column_disjoint_population_returns_one_exact_interchange_family() {
    let sections = (0..4)
        .map(|column| SupportedDefectSection {
            address: format!("local-{column}"),
            parent_candidate: format!("candidate-{column}"),
            receiver: "one-common-receiver-family".to_owned(),
            successor_word: vec!["generator-family".to_owned()],
            chart: "rectangular-free-module".to_owned(),
            ambient_rows: 3,
            ambient_columns: 4,
            support_rows: vec![0, 1],
            support_columns: vec![column],
            supported: matrix(&[&[-1], &[1]]),
            metrics: DefectMetrics {
                domain: ExactRatMatrix::identity(1).expect("domain metric"),
                codomain: ExactRatMatrix::identity(2).expect("codomain metric"),
            },
        })
        .collect();
    let cover = DerivedFactorCover::derive(sections).expect("compact cover");
    assert_eq!(cover.complete_pair_population, 6);
    assert!(cover.overlaps.is_empty());
    assert_eq!(cover.compact_interchange_families.len(), 1);
    let family = &cover.compact_interchange_families[0];
    assert_eq!(family.pair_population, 6);
    assert_eq!(family.disjoint_support_axis, "columns");
    assert_eq!(family.interchange_law, "additive-local-delta-interchange");
    cover.validate().expect("reopened compact cover");
}
