//! Executable form of the witnesses proved in
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ContinuingTower.lean`.
//!
//! Each test names the Lean theorem it mirrors. A test is not a proof of that theorem; it is the
//! same statement asked of the executable owner over a declared finite aperture, so that the two
//! sides cannot drift apart silently.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::{
    ChartRoute, CoarseGrain, CompatibleSection, ComposedMigration, ComposedTransition,
    ComputableTower,
    EnumerableTower, ExactShift, GluingResult, HalvingMigration, IdentityMigration,
    MaterializedFace, Migration, MigrationOutcome, MigrationRefusal, NoResidual, ObservationFibre,
    RationalFloor, ResidualMigration, ResidueTower, ReversePassageReceipt, ShiftTower,
    SplittingRefusal, SwapMigration, Tower, TowerRefusal, TowerRestrictTransition, Transition,
    TwoChartTower, TwoCharts, UnitTower, carry_section, check_factors_through_restriction,
    check_index_routes, check_migration_naturality, check_migration_square_reopen,
    check_restriction_laws, check_reverse_passage, computable_section, glue_chain,
};

fn nat(value: u32) -> BigUint {
    BigUint::from(value)
}

/// The chart index of a residue tower *is* the exponent, so the caller owns the bound on it.
/// `modulus_bits` is the measurement it bounds against: it is an upper bound on the carrier
/// `modulus` actually allocates, and it returns without allocating that carrier.
#[test]
fn the_residue_chart_index_sizes_its_own_carrier_and_the_size_is_readable_without_building_it() {
    for base in [2u32, 3, 7, 10, 1_000_003] {
        let tower = ResidueTower::new(nat(base)).expect("a base of at least two is usable");
        assert_eq!(tower.modulus_bits(0), 0, "the level-zero modulus is 1");
        assert_eq!(tower.modulus(0), nat(1));
        for level in [1u32, 2, 7, 64, 513] {
            let allocated = u128::from(tower.modulus(level).bits());
            let reported = tower.modulus_bits(level);
            assert!(
                allocated <= reported,
                "base {base} level {level}: {allocated} bits allocated above the reported {reported}"
            );
            assert!(
                reported <= allocated + u128::from(level),
                "base {base} level {level}: the reported width is within one bit per level"
            );
        }
    }

    // The hostile chart index is measurable without being built: u32::MAX at base two is already
    // half a gigabyte of carrier, and this measurement neither allocates it nor overflows.
    let two = ResidueTower::new(nat(2)).expect("2 is a usable base");
    assert_eq!(
        two.modulus_bits(u32::MAX),
        u128::from(u32::MAX) * 2,
        "the measurement of the worst chart index is itself cheap and total"
    );
    assert_eq!(
        ResidueTower::new(nat(u32::MAX))
            .expect("a large base is usable")
            .modulus_bits(u32::MAX),
        u128::from(u32::MAX) * 32,
        "u32 * u64 cannot overflow the u128 product"
    );
}

/// Mirrors the `restrict_refl` and `restrict_trans` fields of `Tower`: the laws are checked over a
/// declared aperture and a receipt names what was checked.
#[test]
fn residue_tower_restriction_laws_return_a_receipt() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let charts = [0u32, 1, 2, 3];
    let faces: Vec<(u32, BigUint)> = (0u32..27).map(|value| (3u32, nat(value))).collect();

    let receipt = check_restriction_laws(&tower, &charts, &faces).expect("the laws hold");

    assert_eq!(receipt.faces_checked, 27);
    assert_eq!(receipt.reflexive_charts.len(), 27);
    // Every (coarse <= middle <= fine) triple over four charts.
    assert_eq!(receipt.transitive_triples.len(), 10);
}

/// Mirrors `Tower.restrict_refl`: a tower that moves a face when restricting a chart to itself is
/// refused by type, not by panic.
#[test]
fn a_broken_restrict_refl_is_a_typed_refusal() {
    struct BrokenRefl;

    impl Tower for BrokenRefl {
        type Index = u32;
        type Face = BigUint;

        fn refines(&self, coarse: &u32, fine: &u32) -> bool {
            coarse <= fine
        }

        fn carries(&self, _chart: &u32, _face: &BigUint) -> bool {
            true
        }

        fn restrict(
            &self,
            _coarse: &u32,
            _fine: &u32,
            face: &BigUint,
        ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
            Ok(face + BigUint::one())
        }
    }

    let refusal = check_restriction_laws(&BrokenRefl, &[0u32, 1], &[(0u32, nat(5))])
        .expect_err("restrict_refl must fail here");
    assert!(matches!(
        refusal,
        TowerRefusal::RestrictReflFailed { .. }
    ));
}

/// Mirrors `Tower.restrict_trans`: a tower whose two-step restriction disagrees with its one-step
/// restriction is refused by type, not by panic.
#[test]
fn a_broken_restrict_trans_is_a_typed_refusal() {
    struct BrokenTrans;

    impl Tower for BrokenTrans {
        type Index = u32;
        type Face = BigUint;

        fn refines(&self, coarse: &u32, fine: &u32) -> bool {
            coarse <= fine
        }

        fn carries(&self, _chart: &u32, _face: &BigUint) -> bool {
            true
        }

        fn restrict(
            &self,
            coarse: &u32,
            fine: &u32,
            face: &BigUint,
        ) -> Result<BigUint, TowerRefusal<u32, BigUint>> {
            // One step adds the gap; two steps would add it twice, so the laws disagree above a
            // gap of one.
            Ok(face + BigUint::from(fine - coarse) * BigUint::from(fine - coarse))
        }
    }

    let refusal = check_restriction_laws(&BrokenTrans, &[0u32, 1, 2], &[(2u32, nat(0))])
        .expect_err("restrict_trans must fail here");
    match refusal {
        TowerRefusal::RestrictTransFailed {
            two_step, one_step, ..
        } => {
            assert_eq!(two_step, nat(2));
            assert_eq!(one_step, nat(4));
        }
        other => panic!("expected a restrict_trans refusal, got {other:?}"),
    }
}

/// Mirrors `Tower.CompatibleSection.compatible`: an incompatible family is refused, never repaired.
#[test]
fn an_incompatible_witness_family_is_refused() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let mut witnesses = BTreeMap::new();
    witnesses.insert(0u32, nat(0));
    witnesses.insert(1u32, nat(1));
    witnesses.insert(2u32, nat(2)); // restricts to 0 at chart 1, not 1

    let refusal =
        CompatibleSection::check(&tower, witnesses).expect_err("this family is incompatible");
    assert!(matches!(
        refusal,
        TowerRefusal::IncompatibleWitness { .. }
    ));
}

/// Mirrors `unitTower_gluing`: the `unique` arm has an inhabitant.
#[test]
fn unit_tower_glues_uniquely() {
    let verdict = glue_chain(&UnitTower, &[0u32, 1, 2], ()).expect("the unit tower is lawful");
    match verdict {
        GluingResult::Unique(section) => {
            assert_eq!(section.charts(), vec![0u32, 1, 2]);
            assert_eq!(section.witness(&2), Some(&()));
        }
        other => panic!("expected a unique section, got {other:?}"),
    }
}

/// Mirrors `padicTower_plural` and `padicTower_gluing`: the `plural` arm has an inhabitant, and the
/// plurality is returned whole rather than collapsed to a representative.
#[test]
fn residue_tower_glues_plurally() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let verdict = glue_chain(&tower, &[0u32, 1, 2], nat(0)).expect("the residue tower is lawful");
    match verdict {
        GluingResult::Plural(sections) => {
            // 3 cosets from chart 0 to chart 1, 3 again from chart 1 to chart 2.
            assert_eq!(sections.len(), 9);
            let faces_at_two: Vec<BigUint> = sections
                .iter()
                .map(|section| section.witness(&2).expect("chart 2 is carried").clone())
                .collect();
            for value in 0u32..9 {
                assert!(faces_at_two.contains(&nat(value)), "missing face {value}");
            }
        }
        other => panic!("expected a plural return, got {other:?}"),
    }
}

/// Mirrors `padicSection_zero_ne_one_at_one`: the continuing objects of `0` and `1` already
/// separate at chart 1, which is why `padicTower_plural` holds.
#[test]
fn residue_sections_of_zero_and_one_separate_at_chart_one() {
    let tower = ResidueTower::new(nat(5)).expect("5 is a usable base");
    let charts = [0u32, 1, 2];
    let zero = computable_section(&tower, &BigUint::zero(), &charts).expect("0 is a section");
    let one = computable_section(&tower, &BigUint::one(), &charts).expect("1 is a section");

    assert_eq!(zero.witness(&0), one.witness(&0));
    assert_ne!(zero.witness(&1), one.witness(&1));
    assert_eq!(zero.witness(&1), Some(&nat(0)));
    assert_eq!(one.witness(&1), Some(&nat(1)));
}

/// Mirrors `ComputableTower.section`: materialization from one state is checked to be a compatible
/// section, and the declared cost is exact.
#[test]
fn computable_section_is_checked_and_costed() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let charts = [0u32, 1, 2, 3, 4];
    let state = nat(13);
    let section = computable_section(&tower, &state, &charts).expect("13 materializes lawfully");

    assert_eq!(section.witness(&0), Some(&nat(0)));
    assert_eq!(section.witness(&1), Some(&nat(1)));
    assert_eq!(section.witness(&2), Some(&nat(1)));
    assert_eq!(section.witness(&3), Some(&nat(5)));
    assert_eq!(section.witness(&4), Some(&nat(13)));
    assert_eq!(tower.cost(&state, &4), nat(4));
    // Every refining pair among five charts was checked.
    assert_eq!(section.receipt().checked_pairs.len(), 15);
}

/// Mirrors `Tower.ObservationFibre` and `Tower.MaterializedFace`: a face is admitted only with the
/// population retained behind it, and that population is plural.
#[test]
fn a_materialized_face_carries_its_plural_lineage() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let GluingResult::Plural(population) =
        glue_chain(&tower, &[0u32, 1, 2], nat(0)).expect("the residue tower is lawful")
    else {
        panic!("the residue tower is plural over this chain");
    };

    let fibre = ObservationFibre::over(1u32, nat(2), &population);
    assert_eq!(fibre.chart(), &1u32);
    assert_eq!(fibre.face(), &nat(2));
    // Three continuing objects sit over the face 2 at chart 1: 2, 5 and 8 at chart 2.
    assert_eq!(fibre.sections().len(), 3);
    assert!(!fibre.is_empty());

    let materialized = MaterializedFace::found(1u32, nat(2), fibre)
        .expect("the lineage belongs to the materialized face");
    assert_eq!(materialized.lineage().sections().len(), 3);

    let empty = ObservationFibre::over(1u32, nat(100), &population);
    assert!(empty.is_empty());
}

#[test]
fn a_materialized_face_rejects_lineage_from_another_observation() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let GluingResult::Plural(population) =
        glue_chain(&tower, &[0u32, 1, 2], nat(0)).expect("the residue tower is plural")
    else {
        panic!("the residue tower is plural over this chain");
    };
    let lineage = ObservationFibre::over(1u32, nat(2), &population);
    assert!(matches!(
        MaterializedFace::found(1u32, nat(1), lineage),
        Err(TowerRefusal::MaterializedLineageDisagrees { .. })
    ));
}

/// Mirrors `shiftTower_adjacent_not_surjective`: the adjacent fibre over the base face is empty, so
/// the `SuccessorWitnessSystem` hypothesis fails exactly here.
#[test]
fn shift_tower_adjacent_fibre_over_zero_is_empty() {
    let preimage = ShiftTower
        .adjacent_preimage(&0u32, &1u32, &BigUint::zero())
        .expect("the request is a refinement");
    assert!(preimage.is_empty());

    let over_one = ShiftTower
        .adjacent_preimage(&0u32, &1u32, &BigUint::one())
        .expect("the request is a refinement");
    assert_eq!(over_one, vec![BigUint::zero()]);
}

/// Mirrors `shiftTower_obstructed`, `shiftTower_gluing` and `shiftTower_obstruction_nonempty`: the
/// `obstructed` arm has an inhabitant, every chart is inhabited, and the search names the chart at
/// which extension dies.
#[test]
fn shift_tower_is_obstructed_at_a_named_chart() {
    // Every chart is inhabited: a face exists everywhere.
    for chart in 0u32..5 {
        assert!(ShiftTower.carries(&chart, &BigUint::zero()));
    }

    let verdict =
        glue_chain(&ShiftTower, &[0u32, 1, 2, 3], BigUint::zero()).expect("the shift tower is lawful");
    match verdict {
        GluingResult::Obstructed(obstruction) => {
            assert_eq!(obstruction.blocking_chart, 0);
            assert_eq!(obstruction.blocking_face, BigUint::zero());
            assert_eq!(obstruction.unreachable_chart, 1);
        }
        other => panic!("expected an obstruction, got {other:?}"),
    }

    // Starting higher only postpones it: the base witness would have to exceed every depth, which
    // is the content of `shiftTower_obstructed`.
    let verdict = glue_chain(&ShiftTower, &[0u32, 1, 2, 3], nat(2)).expect("the shift tower is lawful");
    match verdict {
        GluingResult::Obstructed(obstruction) => {
            assert_eq!(obstruction.blocking_chart, 2);
            assert_eq!(obstruction.unreachable_chart, 3);
        }
        other => panic!("expected an obstruction, got {other:?}"),
    }
}

/// Mirrors `Tower.gluingResult_total`: every tower and chain returns exactly one arm.
#[test]
fn the_gluing_return_is_total() {
    let residue = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let chain = [0u32, 1, 2];

    let arms = [
        matches!(
            glue_chain(&UnitTower, &chain, ()).expect("lawful"),
            GluingResult::Unique(_)
        ),
        matches!(
            glue_chain(&residue, &chain, nat(0)).expect("lawful"),
            GluingResult::Plural(_)
        ),
        matches!(
            glue_chain(&ShiftTower, &chain, BigUint::zero()).expect("lawful"),
            GluingResult::Obstructed(_)
        ),
    ];
    assert_eq!(arms, [true, true, true]);
}

/// Mirrors `Transition.reopen_apply`: the transported face plus the residual is exactly the source.
#[test]
fn coarse_graining_reopens_every_source() {
    let grain = CoarseGrain::new(nat(7)).expect("7 is a usable grain");
    for value in 0u32..50 {
        let receipt = grain
            .check_reopen(&nat(value))
            .expect("the residual reopens the source");
        assert_eq!(receipt.sources_reopened, 1);
    }
    assert_eq!(grain.apply(&nat(23)), nat(3));
    assert_eq!(grain.residual(&nat(23)), nat(2));
    assert!(CoarseGrain::new(BigUint::zero()).is_none());
}

/// Mirrors `coarseGrain_not_injective`: a coarse graining by more than one genuinely loses.
#[test]
fn coarse_graining_is_genuinely_lossy() {
    let grain = CoarseGrain::new(nat(4)).expect("4 is a usable grain");
    assert_eq!(grain.apply(&nat(0)), grain.apply(&nat(1)));
    assert_ne!(nat(0), nat(1));
}

/// Mirrors `Transition.residual_separates` and `Transition.residual_separates_insufficiency`: what
/// the transported face merged, the residual still separates.
#[test]
fn the_residual_separates_what_the_transported_face_merged() {
    let grain = CoarseGrain::new(nat(4)).expect("4 is a usable grain");
    let (left, right) = grain
        .separating_residuals(&nat(1), &nat(2))
        .expect("1 and 2 share a transported face");
    assert_ne!(left, right);
    assert_eq!(left, nat(1));
    assert_eq!(right, nat(2));

    // Distinct transported faces are not a merge, so there is nothing to separate.
    assert!(grain.separating_residuals(&nat(1), &nat(9)).is_none());
}

/// Mirrors `Transition.laterReceiverFactors`: an arbitrary later receiver is read off the
/// transported face together with the residual.
#[test]
fn a_later_receiver_is_reopened_from_the_residual() {
    let grain = CoarseGrain::new(nat(10)).expect("10 is a usable grain");
    // A finer receiver the transported face alone cannot see: the last decimal digit's parity.
    let finer = |source: &BigUint| -> bool { (source % nat(2)).is_zero() };

    for value in 0u32..40 {
        let source = nat(value);
        let recovered = grain.reopen_later_receiver(
            &grain.apply(&source),
            &grain.residual(&source),
            &finer,
        );
        assert_eq!(recovered, finer(&source));
    }
}

/// Mirrors `Transition.comp`, `Transition.comp_apply`, `coarseGrain_comp_apply`,
/// `coarseGrain_comp_residual_pair` and `coarseGrain_comp_residual_reassembles`: composition
/// composes residuals, and the paired residual reassembles the single one exactly.
#[test]
fn composition_composes_residuals() {
    let inner = CoarseGrain::new(nat(3)).expect("3 is a usable grain");
    let outer = CoarseGrain::new(nat(5)).expect("5 is a usable grain");
    let composed = ComposedTransition::new(outer.clone(), inner.clone());
    let product = CoarseGrain::new(nat(15)).expect("15 is a usable grain");

    for value in 0u32..120 {
        let source = nat(value);

        // `coarseGrain_comp_apply`: the composite transports along the product.
        assert_eq!(composed.apply(&source), product.apply(&source));

        // `coarseGrain_comp_residual_pair`: the composite residual is the pair.
        let (outer_part, inner_part) = composed.residual(&source);
        assert_eq!(outer_part, &inner.apply(&source) % outer.modulus());
        assert_eq!(inner_part, &source % inner.modulus());

        // `coarseGrain_comp_residual_reassembles`: n * r_outer + r_inner = the single residual.
        assert_eq!(
            inner.modulus() * &outer_part + &inner_part,
            product.residual(&source)
        );

        // `Transition.reopen_apply` for the composite.
        composed
            .check_reopen(&source)
            .expect("the paired residual reopens the source");
    }
}

/// Mirrors `Transition.ofEquiv` and `Transition.ofEquiv_residual_subsingleton`: an invertible
/// transition has zero residual, and the zero-ness is a fact about the type.
#[test]
fn an_invertible_transition_has_zero_residual() {
    let shift = ExactShift::new(BigInt::from(-17));
    for value in -5i32..5 {
        let source = BigInt::from(value);
        assert_eq!(shift.residual(&source), NoResidual);
        shift
            .check_reopen(&source)
            .expect("an invertible transition reopens trivially");
    }
    // Nothing is merged, so there is never a separating pair to report.
    assert!(
        shift
            .separating_residuals(&BigInt::from(1), &BigInt::from(2))
            .is_none()
    );
}

/// Mirrors `Transition` over an ordered field: the residual of the floor chart is an exact
/// rational, and no float participates.
#[test]
fn the_rational_floor_transition_is_exact() {
    let chart = RationalFloor;
    let source = Rat::new(BigInt::from(-22), BigInt::from(7));
    assert_eq!(chart.apply(&source), BigInt::from(-4));
    assert_eq!(
        chart.residual(&source),
        Rat::new(BigInt::from(6), BigInt::from(7))
    );
    chart
        .check_reopen(&source)
        .expect("the exact fraction reopens the rational");

    for numerator in -20i32..20 {
        let value = Rat::new(BigInt::from(numerator), BigInt::from(6));
        chart
            .check_reopen(&value)
            .expect("the exact fraction reopens the rational");
    }
}

/// Mirrors `Tower.restrictTransition` and `Tower.section_witness_reopened`: the coarse face of a
/// continuing object plus the restriction's residual returns its fine face exactly. The residual
/// here is the exact coset index the restriction drops.
#[test]
fn a_tower_restriction_reopens_the_fine_face_from_its_residual() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let charts = [0u32, 1, 2, 3];
    let section = computable_section(&tower, &nat(20), &charts).expect("20 materializes lawfully");

    let residual = tower
        .restriction_residual(&1, &3, section.witness(&3).expect("chart 3 is carried"))
        .expect("the residual exists");
    // 20 mod 27 is 20; 20 mod 3 is 2; the dropped digit block is 20 / 3 = 6.
    assert_eq!(residual, nat(6));

    let reopened = tower
        .restriction_reopen(
            &1,
            &3,
            section.witness(&1).expect("chart 1 is carried"),
            &residual,
        )
        .expect("the reopening exists");
    assert_eq!(&reopened, section.witness(&3).expect("chart 3 is carried"));

    let receipt = tower
        .check_section_reopen(&1, &3, &section)
        .expect("the section reopens");
    assert_eq!(receipt.sources_reopened, 1);
}

/// Mirrors `Tower.restrict_self_eq_id` and `Tower.restrict_roundTrip`: a tower's one-chart
/// restriction is the identity, which is why the loop obstruction of
/// `Millennium/HolonicDirectedPassage.lean` cannot be carried by a tower.
#[test]
fn a_one_chart_restriction_is_the_identity() {
    let tower = ResidueTower::new(nat(7)).expect("7 is a usable base");
    for value in 0u32..49 {
        let face = nat(value);
        assert_eq!(
            tower.restrict(&2, &2, &face).expect("a lawful restriction"),
            face
        );
    }
    for chart in 0u32..4 {
        assert_eq!(
            ShiftTower
                .restrict(&chart, &chart, &nat(11))
                .expect("a lawful restriction"),
            nat(11)
        );
    }
}

/// A request that is not a refinement is refused, not answered.
#[test]
fn a_non_refinement_is_refused() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let refusal = tower
        .restrict(&3, &1, &nat(1))
        .expect_err("3 does not refine 1");
    assert!(matches!(refusal, TowerRefusal::NotARefinement { .. }));
}

// ---------------------------------------------------------------------------------------------
// C2 — the exact fibre splitting
// ---------------------------------------------------------------------------------------------

/// Mirrors `padicFibre_card`: the fibre over a level-`m` face splits into exactly `base ^ k`
/// cosets at level `m + k`. The count is an exact `BigUint`, never an estimate.
#[test]
fn the_residue_fibre_splits_into_exactly_base_to_the_gap_cosets() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let splitting = tower
        .split_fibre(1, 4, &nat(2), 1_000)
        .expect("the splitting exists");

    assert_eq!(splitting.coarse_chart(), 1);
    assert_eq!(splitting.fine_chart(), 4);
    assert_eq!(splitting.coarse_face(), &nat(2));
    // 3^(4-1) = 27 cosets, each a translate of ker at the coarse chart by its modulus 3^1.
    assert_eq!(splitting.coset_count(), &nat(27));
    assert_eq!(splitting.coset_stride(), &nat(3));

    // Mirrors `padicAdjacentFibre_card`: one refinement step splits into exactly `base` cosets.
    for base in [2u32, 3, 5, 7] {
        let tower = ResidueTower::new(nat(base)).expect("a base of at least two is usable");
        for level in 0u32..4 {
            let splitting = tower
                .split_fibre(level, level + 1, &BigUint::zero(), 1_000)
                .expect("the splitting exists");
            assert_eq!(
                splitting.coset_count(),
                &nat(base),
                "base {base} level {level}: the adjacent step splits into exactly {base} cosets"
            );
        }
    }
}

/// Mirrors `padicFibreEquiv`'s two round trips, `padicDigitGap_reopenGap` and
/// `padicReopenGap_restrict`: the coset index and the representative are mutually inverse, and
/// every representative really restricts back to the face the fibre sits over.
#[test]
fn the_coset_index_and_the_representative_are_mutually_inverse() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let splitting = tower
        .split_fibre(2, 4, &nat(7), 1_000)
        .expect("the splitting exists");
    assert_eq!(splitting.coset_count(), &nat(9));

    // `padicDigitGap_reopenGap`: index(representative(d)) = d.
    let mut index = BigUint::zero();
    while &index < splitting.coset_count() {
        let representative = splitting
            .representative(&index)
            .expect("the index is in range");
        assert_eq!(
            splitting
                .coset_index(&representative)
                .expect("the representative is in the fibre"),
            index
        );
        // `padicRestrict_reopenGap`: it restricts back to the coarse face.
        assert_eq!(
            tower
                .restrict(&2, &4, &representative)
                .expect("a lawful restriction"),
            nat(7)
        );
        index += BigUint::one();
    }

    // `padicReopenGap_restrict`: representative(index(x)) = x for every x in the fibre.
    for value in 0u32..81 {
        let face = nat(value);
        if tower.restrict(&2, &4, &face).expect("a lawful restriction") != nat(7) {
            assert!(splitting.coset_index(&face).is_err());
            continue;
        }
        let recovered = splitting
            .coset_index(&face)
            .expect("the face is in the fibre");
        assert_eq!(
            splitting
                .representative(&recovered)
                .expect("a recovered index is in range"),
            face
        );
    }
}

/// The splitting and the enumerated adjacent preimage are the same population: C2's coset count and
/// the `glue_chain` search see one object, not two.
#[test]
fn the_splitting_agrees_with_the_enumerated_adjacent_preimage() {
    let tower = ResidueTower::new(nat(5)).expect("5 is a usable base");
    let preimage = tower
        .adjacent_preimage(&1, &3, &nat(4))
        .expect("the request is a refinement");
    let splitting = tower
        .split_fibre(1, 3, &nat(4), 1_000)
        .expect("the splitting exists");

    assert_eq!(BigUint::from(preimage.len()), *splitting.coset_count());
    assert_eq!(
        splitting.enumerate(1_000).expect("25 cosets fit"),
        preimage
    );
}

/// A hostile chart index is measured, not built: `coset_count_bits` allocates nothing, and
/// `split_fibre` refuses above the caller's declared ceiling before any carrier of that width
/// exists.
#[test]
fn a_hostile_chart_gap_is_refused_before_the_carrier_is_built() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");

    // The measurement is total and cheap even at the worst chart index.
    assert_eq!(
        tower
            .coset_count_bits(0, u32::MAX)
            .expect("0 refines u32::MAX"),
        u128::from(u32::MAX) * 2
    );

    let refusal = tower
        .split_fibre(0, u32::MAX, &BigUint::zero(), 1_000_000)
        .expect_err("a half-gigabyte carrier is above the declared ceiling");
    match refusal {
        SplittingRefusal::CarrierAboveCeiling {
            carrier_bits,
            ceiling_bits,
            ..
        } => {
            assert!(carrier_bits > ceiling_bits);
            assert_eq!(ceiling_bits, 1_000_000);
        }
        other => panic!("expected a carrier-ceiling refusal, got {other:?}"),
    }

    // A non-refinement and an uncarried face are refusals too, never panics.
    assert!(matches!(
        tower.coset_count_bits(3, 1),
        Err(SplittingRefusal::NotARefinement { .. })
    ));
    assert!(matches!(
        tower.split_fibre(3, 1, &BigUint::zero(), 1_000),
        Err(SplittingRefusal::NotARefinement { .. })
    ));
    assert!(matches!(
        tower.split_fibre(2, 4, &nat(9), 1_000),
        Err(SplittingRefusal::FaceNotCarried { .. })
    ));
}

/// A coset index outside the splitting, a fine face outside the fibre, and an enumeration above the
/// declared ceiling are all typed refusals.
#[test]
fn a_coset_index_outside_the_splitting_is_a_typed_refusal() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let splitting = tower
        .split_fibre(1, 3, &nat(1), 1_000)
        .expect("the splitting exists");
    assert_eq!(splitting.coset_count(), &nat(9));

    assert!(matches!(
        splitting.representative(&nat(9)),
        Err(SplittingRefusal::CosetIndexOutOfRange { .. })
    ));
    // 2 restricts to 2 at chart 1, not to 1, so it is not in this fibre.
    assert!(matches!(
        splitting.coset_index(&nat(2)),
        Err(SplittingRefusal::NotInFibre { .. })
    ));
    assert!(matches!(
        splitting.enumerate(4),
        Err(SplittingRefusal::EnumerationAboveCeiling { .. })
    ));
    assert_eq!(splitting.enumerate(9).expect("9 cosets fit").len(), 9);
}

// ---------------------------------------------------------------------------------------------
// C4 — `Migration`
// ---------------------------------------------------------------------------------------------

fn residue_faces(tower: &ResidueTower, chart: u32, count: u32) -> Vec<(u32, BigUint)> {
    (0u32..count)
        .map(|value| (chart, nat(value) % tower.modulus(chart)))
        .collect()
}

/// Mirrors `Migration.identity` and `rebaseMigration_residual_subsingleton`: the identity migration
/// is natural at every square and its residual is zero by type.
#[test]
fn the_identity_migration_is_natural_and_drops_nothing() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let migration = IdentityMigration::new(tower.clone());

    let mut faces = residue_faces(&tower, 0, 1);
    faces.extend(residue_faces(&tower, 1, 2));
    faces.extend(residue_faces(&tower, 2, 4));
    faces.extend(residue_faces(&tower, 3, 8));

    let receipt = check_migration_naturality(&migration, &[0u32, 1, 2, 3], &faces)
        .expect("the identity migration is natural");
    // Every (coarse <= fine) pair over four charts.
    assert_eq!(receipt.checked_squares.len(), 10);
    assert_eq!(receipt.faces_checked, faces.len());

    for (chart, face) in &faces {
        assert_eq!(migration.residual(chart, face).expect("total"), NoResidual);
        assert_eq!(
            migration
                .check_reopen(chart, face)
                .expect("zero residual reopens trivially")
                .sources_reopened,
            1
        );
    }
}

/// Mirrors `padicHalfMigration`: a genuinely lossy migration whose naturality square nevertheless
/// commutes at every checked pair, because naturality is `Tower.restrict_trans`.
#[test]
fn the_halving_migration_is_natural_over_a_declared_aperture() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let migration = HalvingMigration::new(tower.clone(), 4).expect("4 is below u32::MAX / 2");
    assert_eq!(migration.ceiling(), 4);
    assert_eq!(migration.index(&2), 4);

    // Source faces live at the image chart `2 * j`.
    let mut faces = residue_faces(&tower, 0, 1);
    faces.extend((0u32..9).map(|value| (1u32, nat(value))));
    faces.extend((0u32..81).map(|value| (2u32, nat(value))));

    let receipt = check_migration_naturality(&migration, &[0u32, 1, 2], &faces)
        .expect("the halving migration is natural");
    assert_eq!(receipt.checked_squares.len(), 6);

    // And it is genuinely lossy: `face` merges exactly `base ^ j` source faces at chart j.
    let splitting = tower
        .split_fibre(2, 4, &nat(5), 1_000)
        .expect("the splitting exists");
    assert_eq!(splitting.coset_count(), &nat(9));
    for index in 0u32..9 {
        let representative = splitting
            .representative(&nat(index))
            .expect("the index is in range");
        assert_eq!(
            migration
                .face(&2, &representative)
                .expect("chart 2 is inside the aperture"),
            nat(5),
            "all nine cosets present the same migrated face"
        );
    }
}

/// Mirrors `padicHalfMigration_carrySection`: the continuing object survives a migration whose every
/// face map is lossy. The object is the carrier; the faces are not.
#[test]
fn the_halving_migration_carries_the_continuing_object_unchanged() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let migration = HalvingMigration::new(tower.clone(), 4).expect("4 is below u32::MAX / 2");

    let state = nat(20);
    let saved = computable_section(&tower, &state, &[0u32, 2, 4]).expect("20 materializes lawfully");
    let read = carry_section(&migration, &saved, &[0u32, 1, 2]).expect("the object is readable");

    // The same continuing object, presented over the new chart family.
    let direct = computable_section(&tower, &state, &[0u32, 1, 2]).expect("20 materializes lawfully");
    for chart in [0u32, 1, 2] {
        assert_eq!(
            read.witness(&chart),
            direct.witness(&chart),
            "chart {chart} disagrees"
        );
    }
    assert_eq!(read.witness(&2), Some(&nat(2)));

    // A chart whose image the object does not carry is a typed refusal, not a guess.
    let partial = computable_section(&tower, &state, &[0u32, 2]).expect("20 materializes lawfully");
    assert!(matches!(
        carry_section(&migration, &partial, &[0u32, 1, 2]),
        Err(MigrationRefusal::SourceChartMissing { .. })
    ));
}

/// Mirrors `ResidualMigration.square_either_route_reopens`: one transported face, two retained
/// residual pairs, and each of them reconstructs the source face exactly.
#[test]
fn either_route_around_the_naturality_square_reopens_the_source() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let migration = HalvingMigration::new(tower.clone(), 4).expect("4 is below u32::MAX / 2");

    for value in 0u32..81 {
        let source_face = nat(value);
        let receipt = check_migration_square_reopen(&migration, &1, &2, &source_face)
            .expect("both routes reopen the source");
        assert_eq!(receipt.routes_reopened, 2);
        assert!(receipt.naturality_checked);
    }

    // The per-chart law on its own, which is `ResidualMigration.reopen_apply`.
    for value in 0u32..81 {
        assert_eq!(
            migration
                .check_reopen(&2, &nat(value))
                .expect("the residual reopens the source face")
                .sources_reopened,
            1
        );
    }
}

/// Mirrors `naturality_is_genuine_content`: a face family that is a perfectly good map at every
/// chart and still fails naturality is refused, by type, with both disagreeing faces named.
#[test]
fn a_broken_naturality_square_is_a_typed_refusal() {
    struct ShiftByChart {
        tower: ResidueTower,
    }

    impl Migration for ShiftByChart {
        type Source = ResidueTower;
        type Target = ResidueTower;

        fn source_tower(&self) -> &ResidueTower {
            &self.tower
        }

        fn target_tower(&self) -> &ResidueTower {
            &self.tower
        }

        fn index(&self, target_chart: &u32) -> u32 {
            *target_chart
        }

        fn face(&self, chart: &u32, face: &BigUint) -> MigrationOutcome<Self, BigUint> {
            Ok((face + BigUint::from(*chart)) % self.tower.modulus(*chart))
        }
    }

    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let migration = ShiftByChart {
        tower: tower.clone(),
    };
    let faces: Vec<(u32, BigUint)> = (0u32..9).map(|value| (2u32, nat(value))).collect();

    let refusal = check_migration_naturality(&migration, &[1u32, 2], &faces)
        .expect_err("shifting by the chart index is not natural");
    match refusal {
        MigrationRefusal::NaturalityFailed {
            coarse,
            fine,
            via_target_restriction,
            via_source_restriction,
            ..
        } => {
            assert_eq!((coarse, fine), (1, 2));
            assert_ne!(via_target_restriction, via_source_restriction);
        }
        other => panic!("expected a naturality refusal, got {other:?}"),
    }
}

/// Mirrors `Migration.index_mono`: an index map that reverses a refinement is refused before any
/// face is migrated.
#[test]
fn a_non_monotone_index_map_is_refused() {
    struct DescendingIndex {
        tower: ResidueTower,
    }

    impl Migration for DescendingIndex {
        type Source = ResidueTower;
        type Target = ResidueTower;

        fn source_tower(&self) -> &ResidueTower {
            &self.tower
        }

        fn target_tower(&self) -> &ResidueTower {
            &self.tower
        }

        fn index(&self, target_chart: &u32) -> u32 {
            5u32.saturating_sub(*target_chart)
        }

        fn face(&self, _chart: &u32, face: &BigUint) -> MigrationOutcome<Self, BigUint> {
            Ok(face.clone())
        }
    }

    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    let migration = DescendingIndex { tower };
    let refusal = check_migration_naturality(&migration, &[1u32, 2], &[])
        .expect_err("a descending index map is not a functor of index categories");
    match refusal {
        MigrationRefusal::IndexNotMonotone {
            coarse,
            fine,
            coarse_image,
            fine_image,
        } => {
            assert_eq!((coarse, fine), (1, 2));
            assert_eq!((coarse_image, fine_image), (4, 3));
        }
        other => panic!("expected an index-monotonicity refusal, got {other:?}"),
    }
}

/// Mirrors `Migration.carrySection_comp`: a schema **history** may be replayed step by step or
/// composed first, with the same continuing object either way.
#[test]
fn composed_migrations_carry_sections_functorially() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let first = HalvingMigration::new(tower.clone(), 8).expect("8 is below u32::MAX / 2");
    let second = HalvingMigration::new(tower.clone(), 8).expect("8 is below u32::MAX / 2");
    let composed = ComposedMigration::new(second, first);
    assert_eq!(composed.index(&2), 8);

    let state = nat(5_000);
    let saved = computable_section(&tower, &state, &[0u32, 4, 8]).expect("it materializes lawfully");

    let composed_once =
        carry_section(&composed, &saved, &[0u32, 1, 2]).expect("the composite reads the object");

    let middle = carry_section(&composed.first, &saved, &[0u32, 2, 4])
        .expect("the first migration reads the object");
    let replayed = carry_section(&composed.second, &middle, &[0u32, 1, 2])
        .expect("the second migration reads it again");

    for chart in [0u32, 1, 2] {
        assert_eq!(
            composed_once.witness(&chart),
            replayed.witness(&chart),
            "chart {chart} disagrees between the composite and the replay"
        );
    }

    // And the composite residual *is* the pair, exactly as `ComposedTransition`'s is.
    let source_face = nat(5_000) % tower.modulus(8);
    let (second_part, first_part) = composed
        .residual(&2, &source_face)
        .expect("the composite residual exists");
    assert_eq!(
        first_part,
        composed
            .first
            .residual(&4, &source_face)
            .expect("the first residual exists")
    );
    let middle_face = composed
        .first
        .face(&4, &source_face)
        .expect("the first migration transports");
    assert_eq!(
        second_part,
        composed
            .second
            .residual(&2, &middle_face)
            .expect("the second residual exists")
    );
    assert_eq!(
        composed
            .check_reopen(&2, &source_face)
            .expect("the paired residual reopens the source face")
            .sources_reopened,
        1
    );
}

/// Mirrors `residual_is_not_determined_by_the_face_map`: one face map carries two genuinely
/// different residuals, so a migration's residual is data a caller deposits and never a consequence
/// of the map.
#[test]
fn the_residual_is_supplied_and_not_derived_from_the_face_map() {
    struct TautologicalQuotient {
        modulus: BigUint,
    }

    impl Transition for TautologicalQuotient {
        type Source = BigUint;
        type Target = BigUint;
        type Residual = BigUint;

        fn apply(&self, source: &BigUint) -> BigUint {
            source / &self.modulus
        }

        fn residual(&self, source: &BigUint) -> BigUint {
            source.clone()
        }

        fn reopen(&self, _target: &BigUint, residual: &BigUint) -> BigUint {
            residual.clone()
        }
    }

    let exact = CoarseGrain::new(nat(4)).expect("4 is a usable grain");
    let tautological = TautologicalQuotient { modulus: nat(4) };

    for value in 0u32..40 {
        let source = nat(value);
        // The same transported face.
        assert_eq!(exact.apply(&source), tautological.apply(&source));
        // Both satisfy `reopen_apply`.
        exact.check_reopen(&source).expect("the exact residual reopens");
        tautological
            .check_reopen(&source)
            .expect("the tautological residual reopens");
    }

    // And they are genuinely different data: the exact remainder merges 4 and 0, the tautological
    // residual separates them.
    assert_eq!(exact.residual(&nat(4)), exact.residual(&nat(0)));
    assert_ne!(
        tautological.residual(&nat(4)),
        tautological.residual(&nat(0))
    );
}

/// A target chart above the migration's declared aperture, and a ceiling whose image chart does not
/// exist, are refused rather than overflowing the chart index.
#[test]
fn a_chart_above_the_declared_aperture_is_refused() {
    let tower = ResidueTower::new(nat(2)).expect("2 is a usable base");
    assert!(HalvingMigration::new(tower.clone(), u32::MAX).is_none());
    assert!(HalvingMigration::new(tower.clone(), u32::MAX / 2 + 1).is_none());

    let migration = HalvingMigration::new(tower, 2).expect("2 is below u32::MAX / 2");
    match migration.face(&5, &BigUint::zero()) {
        Err(MigrationRefusal::ChartAboveDeclaredAperture {
            target_chart,
            declared_ceiling,
        }) => {
            assert_eq!(target_chart, 5);
            assert_eq!(declared_ceiling, 2);
        }
        other => panic!("expected a declared-aperture refusal, got {other:?}"),
    }
    assert!(matches!(
        migration.residual(&5, &BigUint::zero()),
        Err(MigrationRefusal::ChartAboveDeclaredAperture { .. })
    ));
    assert!(matches!(
        migration.reopen(&5, &BigUint::zero(), &BigUint::zero()),
        Err(MigrationRefusal::ChartAboveDeclaredAperture { .. })
    ));
}

/// Mirrors `Migration.StaysAtItsChart`, `Migration.FollowsRefinement` and
/// `Migration.FactorsThroughRefinement`: the identity migration reads exactly the chart it writes,
/// and the halving migration reads a finer chart and *is* the tower's own restriction there. Both
/// add passage the tower did not already have — which is to say, neither does.
#[test]
fn the_identity_and_halving_migrations_both_factor_through_refinement() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let charts = [0u32, 1, 2];

    let identity = IdentityMigration::new(tower.clone());
    let identity_routes = check_index_routes(&identity, &charts);
    assert!(identity_routes.orders_agreed());
    assert!(identity_routes.stays_at_its_chart_everywhere());
    assert!(!identity_routes.connects_incomparable_charts());

    let halving = HalvingMigration::new(tower.clone(), 4).expect("4 is below u32::MAX / 2");
    let halving_routes = check_index_routes(&halving, &charts);
    assert!(halving_routes.follows_refinement_everywhere());
    assert!(!halving_routes.connects_incomparable_charts());
    assert_eq!(
        halving_routes.routes(),
        vec![
            (0u32, ChartRoute::SameChart),
            (1u32, ChartRoute::FollowsRefinement),
            (2u32, ChartRoute::FollowsRefinement),
        ]
    );

    // And the components really are the tower's own restrictions.
    let mut faces: Vec<(u32, BigUint)> = vec![(0u32, BigUint::zero())];
    faces.extend((0u32..9).map(|value| (1u32, nat(value))));
    faces.extend((0u32..81).map(|value| (2u32, nat(value))));

    let receipt = check_factors_through_restriction(&halving, &charts, &faces)
        .expect("the halving migration is checkable");
    assert!(receipt.factors_through_refinement());
    assert_eq!(receipt.restriction_charts, vec![0u32, 1, 2]);
    assert!(receipt.no_route_charts.is_empty());

    // The identity migration reads the chart it writes, so its faces are the ones carried there.
    let mut identity_faces = residue_faces(&tower, 0, 1);
    identity_faces.extend(residue_faces(&tower, 1, 3));
    identity_faces.extend(residue_faces(&tower, 2, 9));
    let receipt = check_factors_through_restriction(&identity, &charts, &identity_faces)
        .expect("the identity migration is checkable");
    assert!(receipt.factors_through_refinement());
}

/// Mirrors `swapMigration_connectsIncomparableCharts`,
/// `swapMigration_not_factorsThroughRefinement` and `twoCharts_no_common_refinement`: a lawful
/// migration that supplies passage between two charts the tower relates in no way at all. The
/// non-factoring condition is not vacuous.
#[test]
fn a_migration_can_connect_charts_the_tower_relates_in_no_way() {
    let swap = SwapMigration::new();
    let charts = [TwoCharts::Left, TwoCharts::Right];

    // It is a lawful migration: every naturality square commutes.
    let faces: Vec<(TwoCharts, BigUint)> = (0u32..4)
        .flat_map(|value| [(TwoCharts::Left, nat(value)), (TwoCharts::Right, nat(value))])
        .collect();
    let receipt =
        check_migration_naturality(&swap, &charts, &faces).expect("the swap migration is natural");
    // Only the two reflexive squares exist in a discrete order.
    assert_eq!(receipt.checked_squares.len(), 2);

    // And it connects charts the tower does not relate at all.
    let routes = check_index_routes(&swap, &charts);
    assert!(routes.connects_incomparable_charts());
    assert_eq!(
        routes.incomparable_charts(),
        vec![&TwoCharts::Left, &TwoCharts::Right]
    );

    // So it does not factor through refinement: there is no refinement route to factor through.
    let factorisation = check_factors_through_restriction(&swap, &charts, &faces)
        .expect("the swap migration is checkable");
    assert!(!factorisation.factors_through_refinement());
    assert_eq!(
        factorisation.no_route_charts,
        vec![TwoCharts::Left, TwoCharts::Right]
    );

    // The tower itself offers nothing: no chart refines both, and the restriction refuses.
    assert!(!TwoChartTower.has_common_refinement());
    assert!(matches!(
        TwoChartTower.restrict(&TwoCharts::Left, &TwoCharts::Right, &BigUint::zero()),
        Err(TowerRefusal::NotARefinement { .. })
    ));
}

/// Mirrors `Migration.ReversePassage`, `not_reversePassage_of_not_injective`,
/// `padicHalfMigration_no_reverse_passage` and
/// `padicHalfMigration_residual_restores_the_reverse_passage`: the migrated face alone is one-way at
/// a lossy chart, and the retained residual restores the return exactly.
#[test]
fn traversability_is_the_retained_residual() {
    let tower = ResidueTower::new(nat(3)).expect("3 is a usable base");
    let halving = HalvingMigration::new(tower.clone(), 4).expect("4 is below u32::MAX / 2");

    // Chart 0 reads chart 0, so its component is the identity and the passage is already two-way.
    let receipt = check_reverse_passage(&halving, &0, &[BigUint::zero()])
        .expect("chart 0 is inside the aperture");
    assert!(matches!(
        receipt,
        ReversePassageReceipt::FromTheFaceAlone { .. }
    ));

    // Chart 2 reads chart 4 and merges exactly 3^2 faces, so nothing carries the migrated face back.
    let population: Vec<BigUint> = (0u32..81).map(nat).collect();
    let receipt =
        check_reverse_passage(&halving, &2, &population).expect("chart 2 is inside the aperture");
    let (merged_left, merged_right) = match receipt {
        ReversePassageReceipt::OnlyWithTheResidual {
            merged_left,
            merged_right,
        } => (merged_left, merged_right),
        other => panic!("expected a one-way chart, got {other:?}"),
    };
    assert_ne!(merged_left, merged_right);
    assert_eq!(
        halving.face(&2, &merged_left).expect("chart 2 migrates"),
        halving.face(&2, &merged_right).expect("chart 2 migrates")
    );

    // And the retained residual restores the return, exactly, for every face of that chart.
    for source_face in &population {
        assert_eq!(
            halving
                .check_reopen(&2, source_face)
                .expect("the residual reopens the source face")
                .sources_reopened,
            1
        );
    }
    // The residuals of the merged pair are what separates them.
    assert_ne!(
        halving.residual(&2, &merged_left).expect("total"),
        halving.residual(&2, &merged_right).expect("total")
    );

    // A migration whose residual is `NoResidual` by type is two-way from the face alone.
    let swap = SwapMigration::new();
    let receipt = check_reverse_passage(&swap, &TwoCharts::Left, &population)
        .expect("the swap migration is total");
    assert!(matches!(
        receipt,
        ReversePassageReceipt::FromTheFaceAlone { .. }
    ));
}
