//! The invariant set of `presentation_cost`, mirroring
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PresentationCost.lean` theorem by
//! theorem. Each test names the Lean declaration it realizes.


use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use holonics::geometry::Rat;

use super::*;

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The all-ones weighting: `Rat` is not `Copy`, so the five entries are written out.
fn uniform_weighting() -> Weighting {
    Weighting::declare(
        "uniform",
        [
            integer(1),
            integer(1),
            integer(1),
            integer(1),
            integer(1),
        ],
    )
    .expect("the all-ones weighting is nonnegative")
}

fn receipt(name: &str, counts: [u64; 5]) -> CostReceipt {
    witness_receipt(name, counts)
}

fn point(name: &str, counts: [u64; 5]) -> ParetoPoint {
    ParetoPoint::new(name, receipt(name, counts))
}

// ---------------------------------------------------------------------------------------------
// Dominance is the product partial order.
// ---------------------------------------------------------------------------------------------

/// `PresentationCost.lean::dominates_refl`, `dominates_trans`, `dominates_antisymm_vector`.
#[test]
fn dominance_is_a_partial_order_on_the_cost_vector() {
    let family = [
        receipt("a", [1, 2, 3, 4, 5]),
        receipt("b", [2, 3, 4, 5, 6]),
        receipt("c", [3, 4, 5, 6, 7]),
        receipt("d", [9, 0, 3, 4, 5]),
    ];
    for left in &family {
        assert!(left.dominates(left), "dominates_refl at {}", left.presentation);
    }
    for left in &family {
        for middle in &family {
            for right in &family {
                if left.dominates(middle) && middle.dominates(right) {
                    assert!(
                        left.dominates(right),
                        "dominates_trans: {} <= {} <= {}",
                        left.presentation,
                        middle.presentation,
                        right.presentation
                    );
                }
            }
        }
    }
    for left in &family {
        for right in &family {
            if left.dominates(right) && right.dominates(left) {
                assert_eq!(
                    left.vector(),
                    right.vector(),
                    "dominates_antisymm_vector: {} and {} dominate each other",
                    left.presentation,
                    right.presentation
                );
            }
        }
    }
    // Strict dominance is irreflexive, asymmetric and transitive.
    for left in &family {
        assert!(!left.strictly_dominates(left));
        for right in &family {
            if left.strictly_dominates(right) {
                assert!(!right.strictly_dominates(left));
            }
        }
    }
}

/// `PresentationCost.lean::dominates_antisymm_fails_on_receipts`. Antisymmetry holds on the cost
/// vector and **not** on the receipt: a measured 12 and a supplier's declared 12 are one cost
/// vector and two receipts.
#[test]
fn dominance_antisymmetry_does_not_lift_to_the_receipt() {
    let measured = CostReceipt {
        presentation: "measured".into(),
        bytes: Counted::measured(12u64, "wc -c"),
        decode_work: Counted::measured(0u64, "wc -c"),
        update_work: Counted::measured(0u64, "wc -c"),
        certificate_work: Counted::measured(0u64, "wc -c"),
        residual: Counted::measured(0u64, "wc -c"),
    };
    let declared = CostReceipt {
        presentation: "declared".into(),
        bytes: Counted::declared(12u64, "vendor datasheet"),
        ..measured.clone()
    };
    assert!(measured.dominates(&declared));
    assert!(declared.dominates(&measured));
    assert_eq!(measured.vector(), declared.vector());
    assert_ne!(measured, declared);
    assert!(measured.is_accounted());
    assert!(!declared.is_accounted());
    assert!(!measured.strictly_dominates(&declared));
    assert!(!declared.strictly_dominates(&measured));
}

// ---------------------------------------------------------------------------------------------
// The frontier.
// ---------------------------------------------------------------------------------------------

/// `PresentationCost.lean::frontier_nonempty`, `exists_frontier_dominating`,
/// `frontier_isAntichain`.
#[test]
fn the_frontier_is_a_nonempty_dominating_antichain() {
    let family = vec![
        point("cheap-bytes", [1, 40, 9, 9, 0]),
        point("cheap-decode", [40, 1, 9, 9, 0]),
        point("balanced", [12, 12, 9, 9, 0]),
        point("dominated", [41, 41, 10, 10, 1]),
        point("also-dominated", [13, 13, 9, 9, 0]),
    ];
    let frontier = pareto_frontier(&family);
    assert!(!frontier.is_empty(), "frontier_nonempty");
    assert_eq!(
        frontier
            .iter()
            .map(|at| family[*at].label.as_str())
            .collect::<Vec<_>>(),
        vec!["cheap-bytes", "cheap-decode", "balanced"]
    );
    // frontier_isAntichain.
    for left in &frontier {
        for right in &frontier {
            assert!(
                !family[*left]
                    .receipt
                    .strictly_dominates(&family[*right].receipt),
                "the frontier is not an antichain at {} and {}",
                family[*left].label,
                family[*right].label
            );
        }
    }
    // exists_frontier_dominating.
    for at in 0..family.len() {
        let dominator = frontier_dominator(&family, at)
            .unwrap_or_else(|| panic!("{} has no frontier dominator", family[at].label));
        assert!(frontier.contains(&dominator));
        assert!(family[dominator].receipt.dominates(&family[at].receipt));
    }
    assert_eq!(frontier_dominator(&family, family.len()), None);
}

/// Two presentations with equal counts are two presentations: the frontier keeps both, because
/// equal vectors do not strictly dominate each other.
#[test]
fn the_frontier_keeps_every_copy_of_an_equal_cost_vector() {
    let family = vec![
        point("first", [3, 3, 3, 3, 3]),
        point("second", [3, 3, 3, 3, 3]),
        point("worse", [4, 4, 4, 4, 4]),
    ];
    assert_eq!(pareto_frontier(&family), vec![0, 1]);
}

/// An empty family has an empty frontier, and no minimizer. `frontier_nonempty` requires a
/// nonempty family and this is why.
#[test]
fn an_empty_family_returns_an_empty_frontier() {
    assert!(pareto_frontier(&[]).is_empty());
    assert!(scalar_minimizers(&[], &uniform_weighting()).is_empty());
}

// ---------------------------------------------------------------------------------------------
// The objective is one receiver of the receipt.
// ---------------------------------------------------------------------------------------------

/// `PresentationCost.lean::minimizer_isFrontierPoint`: every strictly positive weighting's
/// minimizer is on the frontier. Checked over a grid of strictly positive rational weightings.
#[test]
fn every_strictly_positive_weighting_minimizes_on_the_frontier() {
    let family = vec![
        point("cheap-bytes", [1, 40, 9, 9, 0]),
        point("cheap-decode", [40, 1, 9, 9, 0]),
        point("balanced", [12, 12, 9, 9, 0]),
        point("dominated", [41, 41, 10, 10, 1]),
    ];
    let frontier = pareto_frontier(&family);
    let mut checked = 0usize;
    for a in 1..=6i64 {
        for b in 1..=6i64 {
            for c in 1..=3i64 {
                let weighting = Weighting::declare(
                    format!("q({a}/{b}/{c})"),
                    [rat(a, 3), rat(b, 5), rat(c, 7), rat(1, 2), rat(1, 11)],
                )
                .expect("nonnegative weights are admitted");
                assert!(weighting.is_positive());
                for at in scalar_minimizers(&family, &weighting) {
                    assert!(
                        frontier.contains(&at),
                        "the minimizer {} of {} is off the frontier",
                        family[at].label,
                        weighting.receiver
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(checked >= 108, "the grid checked only {checked} minimizers");
}

/// `PresentationCost.lean::unsupported_not_minimizer`. The converse of the previous test fails:
/// `unsupported` is on the frontier and no weighting that puts weight on either varying axis ever
/// selects it. This is the formal reason a scalar score cannot stand in for the frontier.
#[test]
fn the_unsupported_frontier_point_is_selected_by_no_weighting() {
    let family = chord_family();
    let frontier = pareto_frontier(&family);
    assert_eq!(frontier, vec![0, 1, 2], "all three chord points are nondominated");
    assert_eq!(family[2].label, "unsupported");

    let mut swept = 0usize;
    for a in 0..=12i64 {
        for b in 0..=12i64 {
            if a == 0 && b == 0 {
                continue;
            }
            for extra in [0i64, 1, 5] {
                let weighting = Weighting::declare(
                    format!("q({a},{b},{extra})"),
                    [
                        rat(a, 4),
                        rat(b, 7),
                        integer(extra),
                        integer(extra),
                        integer(extra),
                    ],
                )
                .expect("nonnegative weights are admitted");
                let minimizers = scalar_minimizers(&family, &weighting);
                assert!(
                    !minimizers.contains(&2),
                    "{} selected the unsupported point, which is above the chord",
                    weighting.receiver
                );
                swept += 1;
            }
        }
    }
    assert_eq!(swept, 168 * 3);

    // The only weightings that "select" it are those blind to both varying axes, and they select
    // everything, so they select nothing in particular.
    let blind = Weighting::declare(
        "blind to both varying axes",
        [Rat::zero(), Rat::zero(), integer(3), integer(3), integer(3)],
    )
    .unwrap();
    assert_eq!(scalar_minimizers(&family, &blind), vec![0, 1, 2]);
}

/// A scalar score is a reading of the receipt and not the receipt. Two presentations with the same
/// objective under one weighting are separated by another, and the frontier never collapsed them.
#[test]
fn equal_scores_do_not_identify_presentations() {
    let left = receipt("left", [10, 0, 0, 0, 0]);
    let right = receipt("right", [0, 10, 0, 0, 0]);
    let uniform = uniform_weighting();
    assert_eq!(uniform.objective(&left), uniform.objective(&right));
    assert_ne!(left.vector(), right.vector());
    let byte_heavy = Weighting::declare(
        "byte-heavy",
        [integer(3), integer(1), integer(1), integer(1), integer(1)],
    )
    .unwrap();
    assert!(byte_heavy.objective(&right) < byte_heavy.objective(&left));
    assert!(left.incomparable_with(&right));
}

// ---------------------------------------------------------------------------------------------
// Reparameterization.
// ---------------------------------------------------------------------------------------------

fn square_decode() -> Reparameterization {
    Reparameterization::declare(
        "decode work reported in operation-pairs",
        [
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n * n),
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n.clone()),
        ],
    )
}

/// `PresentationCost.lean::frontier_reparameterization_invariant` against
/// `scalar_minimizer_not_reparameterization_invariant`: the frontier survives a strictly monotone
/// change of unit on one coordinate; the scalar minimizer does not.
#[test]
fn the_frontier_survives_a_unit_change_and_the_scalar_minimizer_does_not() {
    let family = vec![point("flatA", [0, 3, 0, 0, 0]), point("flatB", [2, 2, 0, 0, 0])];
    let unit_change = square_decode();
    let sample = (0u64..24).map(BigUint::from).collect::<Vec<_>>();
    assert_eq!(
        unit_change
            .check_strict_monotone_on(&sample)
            .expect("the declared unit change is strictly monotone on the sample"),
        5 * (sample.len() - 1)
    );

    let reparameterized = unit_change.apply_family(&family);
    assert_eq!(
        pareto_frontier(&family),
        pareto_frontier(&reparameterized),
        "frontier_reparameterization_invariant"
    );
    assert_eq!(pareto_frontier(&family), vec![0, 1]);

    let uniform = uniform_weighting();
    assert_eq!(scalar_minimizers(&family, &uniform), vec![0]);
    assert_eq!(scalar_minimizers(&reparameterized, &uniform), vec![1]);

    // The reparameterized coordinates are derived and say so; a unit change never passes itself
    // off as the original measurement.
    for axis in Axis::ALL {
        assert!(matches!(
            reparameterized[0].receipt.coordinate(axis).provenance,
            Provenance::Derived { .. }
        ));
    }
}

/// The frontier is invariant, but the *order* of the frontier's members by scalar score is not:
/// that is the whole content of the previous test, stated as the pair of readings.
#[test]
fn a_unit_change_that_reorders_is_refused() {
    let reversing = Reparameterization::declare(
        "a map that is not monotone",
        [
            Box::new(|n: &BigUint| if n > &BigUint::from(3u32) { BigUint::zero() } else { n.clone() }),
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n.clone()),
            Box::new(|n: &BigUint| n.clone()),
        ],
    );
    let sample = (0u64..8).map(BigUint::from).collect::<Vec<_>>();
    assert!(matches!(
        reversing.check_strict_monotone_on(&sample),
        Err(CostRefusal::ReparameterizationNotStrictlyMonotone { axis: Axis::Bytes, .. })
    ));
    let descending = vec![BigUint::from(4u32), BigUint::from(1u32)];
    assert!(matches!(
        square_decode().check_strict_monotone_on(&descending),
        Err(CostRefusal::SampleNotAscending { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// Composition, and the residual coordinate.
// ---------------------------------------------------------------------------------------------

/// `PresentationCost.lean::CostReceipt.compose_vector`, `compose_accounted`,
/// `compose_vector_comm`, `compose_vector_assoc`. The additivity law itself is
/// `ReceiverCodeCost.serial_boundary_balance`, cited in the derived provenance.
#[test]
fn receipts_compose_coordinatewise_and_name_the_law_that_licenses_it() {
    let first = receipt("first", [10, 20, 30, 40, 2]);
    let second = receipt("second", [1, 2, 3, 4, 3]);
    let composed = first.compose(&second);
    for (at, axis) in Axis::ALL.into_iter().enumerate() {
        assert_eq!(
            *composed.count(axis),
            first.count(axis) + second.count(axis),
            "compose_vector at {axis} (index {at})"
        );
    }
    assert!(composed.is_accounted(), "compose_accounted");
    for axis in Axis::ALL {
        match &composed.coordinate(axis).provenance {
            Provenance::Derived { rule } => assert!(
                rule.contains("serial_boundary_balance"),
                "the composed {axis} coordinate does not cite the owner of additivity"
            ),
            other => panic!("the composed {axis} coordinate is {other:?}, not derived"),
        }
    }
    assert_eq!(
        first.compose(&second).vector(),
        second.compose(&first).vector(),
        "compose_vector_comm"
    );
    let third = receipt("third", [5, 5, 5, 5, 5]);
    assert_eq!(
        first.compose(&second).compose(&third).vector(),
        first.compose(&second.compose(&third)).vector(),
        "compose_vector_assoc"
    );
}

/// `PresentationCost.lean::codeBits`, `codeBits_one`, `codeBits_mul_le` and
/// `codeBits_residual_comp_lt_witness`. `code_bits` is `Nat.clog 2` on the nose.
#[test]
fn code_bits_is_the_least_exponent_and_is_strictly_subadditive() {
    for (fibre, bits) in [
        (0u64, 0u64),
        (1, 0),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (8, 3),
        (9, 4),
        (15, 4),
        (16, 4),
        (17, 5),
        (1 << 20, 20),
        ((1u64 << 20) + 1, 21),
    ] {
        assert_eq!(
            code_bits(&BigUint::from(fibre)),
            BigUint::from(bits),
            "code_bits({fibre})"
        );
        // The defining property: the least k with fibre <= 2^k.
        if fibre > 1 {
            assert!(BigUint::from(fibre) <= BigUint::one() << bits as usize);
            assert!(BigUint::from(fibre) > BigUint::one() << (bits as usize - 1));
        }
    }
    // codeBits_mul_le over a grid.
    for a in 0u64..24 {
        for b in 0u64..24 {
            assert!(
                code_bits(&BigUint::from(a * b))
                    <= code_bits(&BigUint::from(a)) + code_bits(&BigUint::from(b)),
                "codeBits_mul_le at {a} * {b}"
            );
        }
    }
    // codeBits_residual_comp_lt_witness: composing residual fibres of 5 and 3 gives 15, which
    // codes in four bits where the two components code in three and two. The composed receipt's
    // residual coordinate is therefore an honest upper bound and not the composite's own.
    assert_eq!(code_bits(&BigUint::from(15u64)), BigUint::from(4u64));
    assert_eq!(
        code_bits(&BigUint::from(5u64)) + code_bits(&BigUint::from(3u64)),
        BigUint::from(5u64)
    );
    assert!(code_bits(&BigUint::from(15u64)) < code_bits(&BigUint::from(5u64)) + code_bits(&BigUint::from(3u64)));

    let second = receipt("second", [0, 0, 0, 0, 3]);
    let first = receipt("first", [0, 0, 0, 0, 2]);
    let composed = first.compose(&second);
    assert_eq!(*composed.count(Axis::Residual), BigUint::from(5u64));
    assert!(
        code_bits(&BigUint::from(15u64)) < *composed.count(Axis::Residual),
        "the composed residual coordinate bounds the composite's own residual, strictly here"
    );
}

// ---------------------------------------------------------------------------------------------
// `Migration.CostBoundedByRefinementRoute`.
// ---------------------------------------------------------------------------------------------

/// `PresentationCost.lean::costBoundedByRefinementRoute_of_route` and
/// `costBoundedByRefinementRoute_is_caller_decided` and `swapMigration_route_isEmpty`.
#[test]
fn the_route_comparison_holds_where_there_is_a_route_and_is_caller_decided_where_there_is_none() {
    let direct = receipt("direct restriction", [10, 10, 10, 10, 4]);
    let bounded = RouteComparison {
        direct: direct.clone(),
        route: vec![
            receipt("refine", [7, 6, 5, 6, 2]),
            receipt("restrict back", [4, 5, 6, 5, 2]),
        ],
    };
    assert_eq!(bounded.is_bounded(), Some(true));
    assert_eq!(
        bounded.route_receipt().map(|r| r.vector()),
        Some([11u64, 11, 11, 11, 4].map(BigUint::from))
    );

    let unbounded = RouteComparison {
        direct: direct.clone(),
        route: vec![receipt("one cheap step", [1, 1, 1, 1, 0])],
    };
    assert_eq!(unbounded.is_bounded(), Some(false));

    // swapMigration_route_isEmpty: no route, so nothing is compared. `None` is the honest return
    // and is a different return from "the route is free".
    let no_route = RouteComparison {
        direct: direct.clone(),
        route: Vec::new(),
    };
    assert_eq!(no_route.route_receipt(), None);
    assert_eq!(no_route.is_bounded(), None);

    // costBoundedByRefinementRoute_is_caller_decided: one direct receipt, two caller-supplied
    // route costs, opposite answers.
    let (holds, fails) = RouteComparison::is_caller_decided(&direct);
    assert_eq!(holds.is_bounded(), Some(true));
    assert_eq!(fails.is_bounded(), Some(false));
    assert_eq!(holds.direct, fails.direct);
}

// ---------------------------------------------------------------------------------------------
// Hostile input.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_negative_weight_is_refused_by_name() {
    let refusal = Weighting::declare(
        "a receiver that rewards cost",
        [integer(1), rat(-1, 2), integer(1), integer(1), integer(1)],
    )
    .expect_err("a negative weight is not a cost reading");
    assert!(matches!(
        refusal,
        CostRefusal::NegativeWeight {
            axis: Axis::DecodeWork,
            ..
        }
    ));
    // Zero is admitted: a receiver may be blind to an axis, and `is_positive` says so.
    let blind = Weighting::declare(
        "blind to bytes",
        [Rat::zero(), integer(1), integer(1), integer(1), integer(1)],
    )
    .expect("a zero weight is a lawful declaration");
    assert!(!blind.is_positive());
}

#[test]
fn a_declared_wire_extent_is_checked_and_never_allocated_from() {
    // Exact agreement is admitted.
    assert_eq!(
        decode_wire_record_count(52 * 3 + 11, 3, 11).expect("the declaration agrees"),
        3
    );
    // Disagreement is refused, not rounded.
    assert!(matches!(
        decode_wire_record_count(52 * 3 + 11, 4, 11),
        Err(CostRefusal::DeclaredExtentDisagrees { .. })
    ));
    // A declaration large enough to wrap the arithmetic is refused rather than wrapping, and no
    // buffer of that size is ever asked for.
    assert!(matches!(
        decode_wire_record_count(64, u64::MAX, 0),
        Err(CostRefusal::DeclaredExtentOverflows { .. })
    ));
    assert!(matches!(
        decode_wire_record_count(64, u64::MAX / 8, u64::MAX),
        Err(CostRefusal::DeclaredExtentOverflows { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// A costed tower, from the tower's own receipts.
// ---------------------------------------------------------------------------------------------

fn costed_residue_tower(base: u32) -> CostedResidueTower {
    CostedResidueTower::new(
        ResidueTower::new(BigUint::from(base)).expect("a base of at least two"),
        4096,
    )
}

/// `PresentationCost.lean::padicCostedTower`, `padicStepReceipt_route` and
/// `costBoundedByRefinementRoute_padic`. The `route_dominates` field is a theorem about this tower,
/// so the comparison is bounded at **every** triple, with both sides computed from the tower's own
/// restrictions and nothing supplied by a caller.
#[test]
fn the_costed_residue_tower_dominates_its_own_refinement_route_at_every_triple() {
    for base in [2u32, 3, 5] {
        let costed = costed_residue_tower(base);
        for coarse in 0u32..=6 {
            for middle in coarse..=6 {
                for fine in middle..=6 {
                    let comparison = costed
                        .route_comparison(coarse, middle, fine)
                        .expect("every chart of this sweep is under the declared aperture");
                    assert_eq!(
                        comparison.is_bounded(),
                        Some(true),
                        "route_dominates fails at base {base}, charts {coarse} <= {middle} <= {fine}"
                    );
                }
            }
        }
    }
}

/// `padicStepReceipt`: every coordinate is read off the tower, and the residual coordinate is
/// `code_bits` of the exact coset count `ResidueTower::split_fibre` returns — Lean's
/// `padicFibre_card`, which is `p ^ k` on the nose.
#[test]
fn the_costed_residue_towers_receipt_is_read_off_its_own_fibre_splitting() {
    let costed = costed_residue_tower(3);
    let step = costed
        .receipt(1, 3)
        .expect("chart 3 is under the declared aperture");
    // The fibre of the level-3 -> level-1 restriction has exactly 3^2 = 9 elements.
    let splitting = costed
        .tower()
        .split_fibre(1, 3, &BigUint::zero(), costed.ceiling_bits())
        .expect("under the aperture");
    assert_eq!(*splitting.coset_count(), BigUint::from(9u32));
    assert_eq!(*step.count(Axis::Residual), code_bits(splitting.coset_count()));
    assert_eq!(*step.count(Axis::Residual), BigUint::from(4u32));
    assert_eq!(*step.count(Axis::DecodeWork), BigUint::from(2u32));
    assert_eq!(*step.count(Axis::UpdateWork), BigUint::from(2u32));
    assert_eq!(*step.count(Axis::CertificateWork), BigUint::from(3u32));
    assert_eq!(
        *step.count(Axis::Bytes),
        BigUint::from(2u32) * costed.digit_octets()
    );
    assert!(step.is_accounted(), "no coordinate of it is merely declared");
}

/// `padicCostedTower_route_strict_at_residual` and
/// `padicCostedTower_route_strict_at_certificateWork`. The law is not an equality: at base 3 over
/// charts `0 <= 1 <= 3` the route pays six bits of residual where the direct restriction pays five,
/// and it checks one header more.
#[test]
fn the_direct_restriction_is_strictly_cheaper_than_the_route_on_two_axes() {
    let costed = costed_residue_tower(3);
    let comparison = costed
        .route_comparison(0, 1, 3)
        .expect("under the declared aperture");
    let route = comparison
        .route_receipt()
        .expect("a two-step route has a composed receipt");
    // residual: code_bits(27) = 5 against code_bits(9) + code_bits(3) = 4 + 2.
    assert_eq!(
        *comparison.direct.count(Axis::Residual),
        code_bits(&BigUint::from(27u32))
    );
    assert_eq!(*comparison.direct.count(Axis::Residual), BigUint::from(5u32));
    assert_eq!(*route.count(Axis::Residual), BigUint::from(6u32));
    assert!(comparison.direct.count(Axis::Residual) < route.count(Axis::Residual));
    // certificateWork: one header, against two.
    assert_eq!(
        *comparison.direct.count(Axis::CertificateWork),
        BigUint::from(4u32)
    );
    assert_eq!(*route.count(Axis::CertificateWork), BigUint::from(5u32));
    // The three step-counting axes are equal, which is `padicCostedTower_route_equality_on_step_axes`.
    for axis in [Axis::Bytes, Axis::DecodeWork, Axis::UpdateWork] {
        assert_eq!(
            comparison.direct.count(axis),
            route.count(axis),
            "the dropped digits are the same digits either way, at {axis}"
        );
    }
    assert_eq!(comparison.is_bounded(), Some(true));
}

/// `PresentationCost.lean::squaredGapReceipt_route_fails` and
/// `no_costedTower_with_squaredGapReceipt`. `route_dominates` is a real condition: this receipt
/// assignment is well formed on the same charts and fails the law at `0 <= 1 <= 2`, so no costed
/// tower carries it. Without that failure the field would be vacuous.
#[test]
fn the_squared_gap_receipts_are_no_costed_towers() {
    let comparison = RouteComparison {
        direct: squared_gap_receipt(0, 2),
        route: vec![squared_gap_receipt(1, 2), squared_gap_receipt(0, 1)],
    };
    let route = comparison
        .route_receipt()
        .expect("a two-step route has a composed receipt");
    assert_eq!(*comparison.direct.count(Axis::Bytes), BigUint::from(4u32));
    assert_eq!(*route.count(Axis::Bytes), BigUint::from(2u32));
    assert_eq!(
        comparison.is_bounded(),
        Some(false),
        "the square of the gap is superadditive, so the direct receipt is not dominated"
    );
    assert!(
        !comparison.direct.is_accounted(),
        "a billing rule is declared, never measured"
    );
    // The same triple on the real costed tower is bounded, so the failure is the assignment's and
    // not the charts'.
    assert_eq!(
        costed_residue_tower(2)
            .route_comparison(0, 1, 2)
            .expect("under the aperture")
            .is_bounded(),
        Some(true)
    );
}

/// Hostile input: a chart index whose carrier is wider than the declared aperture is refused by
/// name, before anything of that width is built.
#[test]
fn a_costed_chart_above_the_declared_aperture_is_refused_by_name() {
    let costed = CostedResidueTower::new(
        ResidueTower::new(BigUint::from(2u32)).expect("base two"),
        64,
    );
    assert!(
        costed.receipt(0, 32).is_ok(),
        "thirty-two charts of base two is exactly the declared 64-bit aperture, as \
         ResidueTower::modulus_bits measures it"
    );
    let refusal = costed
        .receipt(0, 1_000_000)
        .expect_err("a million-bit carrier is above the declared aperture");
    assert!(matches!(
        refusal,
        holonics::restriction::tower::SplittingRefusal::CarrierAboveCeiling { .. }
    ));
    let not_a_refinement = costed
        .receipt(5, 2)
        .expect_err("chart 2 does not refine chart 5");
    assert!(matches!(
        not_a_refinement,
        holonics::restriction::tower::SplittingRefusal::NotARefinement { coarse: 5, fine: 2 }
    ));
}

/// The positional lookups of [`Weighting::weight`] and [`Reparameterization::map`] go through
/// [`Axis::index`], an exhaustive match. This pins `index` against `Axis::ALL` so the two orderings
/// cannot drift; a new axis is a compile error in `index` rather than a silent `Bytes`.
#[test]
fn every_axis_reads_its_own_slot() {
    for (at, axis) in Axis::ALL.into_iter().enumerate() {
        assert_eq!(axis.index(), at, "{axis} is at slot {at} of Axis::ALL");
    }
    let weighting = Weighting::declare(
        "five distinct weights",
        [integer(1), integer(2), integer(3), integer(4), integer(5)],
    )
    .expect("nonnegative");
    for (at, axis) in Axis::ALL.into_iter().enumerate() {
        assert_eq!(
            *weighting.weight(axis),
            integer(at as i64 + 1),
            "the weight at {axis} is the one declared for it"
        );
    }
    let reparameterization = Reparameterization::declare(
        "five distinct unit changes",
        [
            Box::new(|count: &BigUint| count + BigUint::from(1u32)),
            Box::new(|count: &BigUint| count + BigUint::from(2u32)),
            Box::new(|count: &BigUint| count + BigUint::from(3u32)),
            Box::new(|count: &BigUint| count + BigUint::from(4u32)),
            Box::new(|count: &BigUint| count + BigUint::from(5u32)),
        ],
    );
    for (at, axis) in Axis::ALL.into_iter().enumerate() {
        assert_eq!(
            reparameterization.map(axis, &BigUint::zero()),
            BigUint::from(at as u32 + 1),
            "the unit change at {axis} is the one declared for it"
        );
    }
}
