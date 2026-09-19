//! Tests for the fold owner. Every law is checked on synthetic exact data that needs no fixture;
//! the measured M5 return is `#[ignore]`d with pinned assertions and hard-fails by name when the
//! authenticated release is absent.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use crate::physical_constraint_complex::DistanceAperture;

// ---------------------------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------------------------

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn point(values: &[i64]) -> FoldPoint {
    FoldPoint::integers(values).expect("a declared point")
}

fn crease(normal: &[i64], offset: i64) -> Crease {
    Crease::declared(normal.iter().map(|entry| rat(*entry)).collect(), rat(offset))
        .expect("a declared crease")
}

fn aperture(squared: i64) -> DistanceAperture {
    DistanceAperture {
        lineage: "fold tests".to_owned(),
        squared: rat(squared),
    }
}

// ---------------------------------------------------------------------------------------------
// 1. the crease, the reflection and the fold
// ---------------------------------------------------------------------------------------------

/// `reflect` is an involution and an isometry, exactly, with no square root anywhere.
#[test]
fn the_reflection_is_an_involution_and_an_isometry() {
    let h = crease(&[1, 2, 2], 3);
    let left = point(&[5, -1, 4]);
    let right = point(&[0, 7, -2]);
    let mirrored_left = h.reflect(&left).expect("the reflection returns");
    let mirrored_right = h.reflect(&right).expect("the reflection returns");
    assert_eq!(
        h.reflect(&mirrored_left).expect("twice"),
        left,
        "Lean: Crease.reflect_involutive"
    );
    assert_eq!(
        squared_distance(mirrored_left.coordinates(), mirrored_right.coordinates())
            .expect("a squared distance"),
        squared_distance(left.coordinates(), right.coordinates()).expect("a squared distance"),
        "Lean: Crease.reflect_distSq"
    );
    assert_eq!(
        h.side_value(&mirrored_left).expect("a side"),
        -h.side_value(&left).expect("a side"),
        "Lean: Crease.side_reflect"
    );
}

/// The crease is fixed pointwise, and the fold fixes exactly the closed positive side.
#[test]
fn the_crease_is_fixed_and_the_fold_fixes_the_positive_side() {
    let h = crease(&[1, 1], 2);
    let on = point(&[1, 1]);
    assert_eq!(h.side(&on).expect("a side"), Side::OnCrease);
    assert_eq!(h.reflect(&on).expect("a reflection"), on);
    assert_eq!(h.fold(&on).expect("a fold"), on);

    let above = point(&[3, 3]);
    assert_eq!(h.side(&above).expect("a side"), Side::Positive);
    assert_eq!(h.fold(&above).expect("a fold"), above);

    let below = point(&[0, 0]);
    assert_eq!(h.side(&below).expect("a side"), Side::Negative);
    let folded = h.fold(&below).expect("a fold");
    assert_ne!(folded, below);
    assert!(
        !h.side_value(&folded).expect("a side").is_negative(),
        "Lean: Crease.fold_mem_positive_side"
    );
}

/// **The fold is a piecewise isometry and not an isometry.** Each half is rigid; across the crease
/// the squared distance drops by exactly `4 σ(x) σ(y) / ⟨n,n⟩`.
#[test]
fn the_fold_is_rigid_on_each_half_and_moves_the_two_halves_together() {
    let h = crease(&[0, 1], 0);
    let above_one = point(&[0, 3]);
    let above_two = point(&[4, 5]);
    let below_one = point(&[1, -2]);
    let below_two = point(&[6, -7]);

    for (left, right) in [(&above_one, &above_two), (&below_one, &below_two)] {
        assert_eq!(
            h.fold_defect(left, right).expect("a defect"),
            Rat::zero(),
            "Lean: Crease.fold_distSq_same_side"
        );
        let folded_left = h.fold(left).expect("a fold");
        let folded_right = h.fold(right).expect("a fold");
        assert_eq!(
            squared_distance(folded_left.coordinates(), folded_right.coordinates())
                .expect("a squared distance"),
            squared_distance(left.coordinates(), right.coordinates()).expect("a squared distance"),
        );
    }

    // σ(above_one) = 3, σ(below_one) = −2, ⟨n,n⟩ = 1, so the defect is 4·3·(−2)/1 = −24.
    let defect = h
        .fold_defect(&above_one, &below_one)
        .expect("the cross defect");
    assert_eq!(defect, rat(-24), "Lean: Crease.fold_distSq_opposite_side");
    let folded_above = h.fold(&above_one).expect("a fold");
    let folded_below = h.fold(&below_one).expect("a fold");
    let before =
        squared_distance(above_one.coordinates(), below_one.coordinates()).expect("before");
    let after = squared_distance(folded_above.coordinates(), folded_below.coordinates())
        .expect("after");
    assert_eq!(&after - &before, defect);
    assert!(
        after < before,
        "Lean: Crease.fold_brings_the_two_sides_together"
    );
}

/// The fold is two-to-one off the crease: folding in half is division by two, and the side bit is
/// the remainder.
#[test]
fn the_fold_fibre_has_two_elements_off_the_crease_and_one_on_it() {
    let h = crease(&[1, 0, 0], 0);
    let off = point(&[5, 1, 2]);
    assert_eq!(
        h.fold_fibre(&off).expect("a fibre").len(),
        2,
        "Lean: Crease.fold_fibre"
    );
    let on = point(&[0, 1, 2]);
    assert_eq!(h.fold_fibre(&on).expect("a fibre"), vec![on]);
}

/// Hostile input: a zero normal names no hyperplane, and the empty point is not a point.
#[test]
fn a_degenerate_crease_and_an_empty_point_are_refused() {
    assert_eq!(
        Crease::declared(vec![Rat::zero(), Rat::zero()], Rat::one()).unwrap_err(),
        FoldRefusal::DegenerateCrease
    );
    assert_eq!(
        Crease::declared(Vec::new(), Rat::one()).unwrap_err(),
        FoldRefusal::ZeroDimension
    );
    assert_eq!(
        FoldPoint::declared(Vec::new()).unwrap_err(),
        FoldRefusal::ZeroDimension
    );
    assert_eq!(
        FoldPoint::declared(vec![Rat::zero(); DIMENSION_CEILING + 1]).unwrap_err(),
        FoldRefusal::DimensionTooWide {
            supplied: DIMENSION_CEILING + 1,
            ceiling: DIMENSION_CEILING,
        }
    );
}

/// Hostile input: a point of another dimension is refused by name rather than read partially.
#[test]
fn a_point_of_another_dimension_is_refused() {
    let h = crease(&[1, 1], 0);
    let wide = point(&[1, 2, 3]);
    assert_eq!(
        h.side_value(&wide).unwrap_err(),
        FoldRefusal::DimensionDisagrees {
            expected: 2,
            supplied: 3
        }
    );
}

/// Constructor bypass: the wire route re-checks the crease and never carries `⟨n,n⟩`.
#[test]
fn the_wire_route_rechecks_the_crease_and_the_point() {
    let h = crease(&[3, 4], 5);
    let text = ron::to_string(&h).expect("the crease serializes");
    let remounted: Crease = ron::from_str(&text).expect("the crease remounts");
    assert_eq!(remounted, h);
    assert_eq!(remounted.normal_squared(), &rat(25));

    let degenerate = "(normal:[(0,1),(0,1)],offset:(1,1))";
    let refused: Result<Crease, _> = ron::from_str(degenerate);
    assert!(refused.is_err(), "a zero normal cannot remount");

    let empty = "(coordinates:[])";
    let refused_point: Result<FoldPoint, _> = ron::from_str(empty);
    assert!(refused_point.is_err(), "an empty point cannot remount");
}

// ---------------------------------------------------------------------------------------------
// 2. reversibility is the residual
// ---------------------------------------------------------------------------------------------

/// `reopen(fold(x), side(x)) = x`, exactly, on both sides and on the crease.
#[test]
fn the_fold_transition_reopens_exactly() {
    let transition = FoldTransition::of(crease(&[2, -1, 3], 4));
    for coordinates in [[0, 0, 0], [5, 5, 5], [1, -4, 2], [2, 1, 1]] {
        let source = point(&coordinates);
        let receipt = transition
            .check_reopen(&source)
            .expect("Lean: Crease.reopen_apply_fold");
        assert_eq!(receipt.sources_reopened, 1);
    }
}

/// Totality: `reopen` off the image returns the target unchanged and never panics.
#[test]
fn reopen_is_total_off_the_image() {
    let transition = FoldTransition::of(crease(&[1, 0], 0));
    let wrong_dimension = point(&[1, 2, 3]);
    assert_eq!(
        transition.reopen(&wrong_dimension, &Side::Negative),
        wrong_dimension,
        "off the image reopen is the identity, exactly as the Lean docstring says"
    );
    assert_eq!(
        transition.apply(&wrong_dimension),
        wrong_dimension,
        "apply is total too"
    );
    assert_eq!(transition.residual(&wrong_dimension), Side::OnCrease);
}

/// Two points merged by the fold are separated by their residuals, which is
/// `Transition.residual_separates`.
#[test]
fn the_residual_separates_the_two_points_the_fold_merges() {
    let transition = FoldTransition::of(crease(&[1, 0], 0));
    let above = point(&[3, 1]);
    let below = point(&[-3, 1]);
    assert_eq!(transition.apply(&above), transition.apply(&below));
    let (left, right) = transition
        .separating_residuals(&above, &below)
        .expect("the fold merges them");
    assert_eq!((left, right), (Side::Positive, Side::Negative));
}

/// `k` folds carry `k` bits and `2^k` layers, and the layer address is a bijection onto `Z/2^k`.
#[test]
fn k_folds_carry_k_bits_and_two_to_the_k_layers() {
    let word = FoldWord::declared(vec![
        crease(&[1, 0], 0),
        crease(&[0, 1], 0),
        crease(&[1, 1], 0),
    ])
    .expect("a declared word");
    assert_eq!(word.layer_count(), BigUint::from(8_u32));
    assert_eq!(word.residual_code_bits(), BigUint::from(3_u32));

    // Every one of the eight side words addresses a distinct layer of Z/2^3.
    let mut addresses = BTreeSet::new();
    for bits in 0..8_u32 {
        let residual: Vec<Side> = (0..3)
            .map(|at| {
                if bits & (1 << at) != 0 {
                    Side::Negative
                } else {
                    Side::Positive
                }
            })
            .collect();
        let address = word.dyadic_layer(&residual).expect("a layer address");
        assert_eq!(address, BigUint::from(bits));
        assert!(addresses.insert(address));
    }
    assert_eq!(addresses.len(), 8, "Lean: k_folds_branch_dyadically at p = 2");
}

/// The word reopens exactly through its retained `k` bits.
#[test]
fn a_word_of_folds_reopens_through_its_retained_bits() {
    let word = FoldWord::declared(vec![crease(&[1, 0], 1), crease(&[0, 1], 2)])
        .expect("a declared word");
    for coordinates in [[0, 0], [5, 5], [3, -1], [-2, 7]] {
        let source = point(&coordinates);
        let folded = word.apply(&source).expect("the word folds");
        let residual = word.residual(&source).expect("the word's residual");
        assert_eq!(residual.len(), 2);
        assert_eq!(
            word.reopen(&folded, &residual).expect("the word reopens"),
            source
        );
    }
}

/// An empty fold word is refused by name: a residual over no crease would be a certificate minted
/// from nothing.
#[test]
fn an_empty_fold_word_is_refused() {
    assert_eq!(
        FoldWord::declared(Vec::new()).unwrap_err(),
        FoldRefusal::EmptyFoldWord
    );
    let word = FoldWord::declared(vec![crease(&[1, 0], 0)]).expect("a word");
    assert_eq!(
        word.dyadic_layer(&[]).unwrap_err(),
        FoldRefusal::ResidualWidthDisagrees {
            expected: 1,
            supplied: 0
        }
    );
    assert_eq!(
        FoldWord::declared(vec![crease(&[1, 0], 0), crease(&[1, 0, 0], 0)]).unwrap_err(),
        FoldRefusal::DimensionDisagrees {
            expected: 2,
            supplied: 3
        }
    );
}

/// A plastic crease has no reverse passage from the folded face alone, and refuses an empty probe.
#[test]
fn a_plastic_crease_has_no_reverse_passage_from_the_face_alone() {
    let plastic = PlasticCrease::declared(crease(&[1, 0], 0), "heat set above the glass transition");
    let probe = vec![point(&[2, 1]), point(&[-2, 1]), point(&[0, 5])];
    match plastic.reverse_passage(&probe).expect("a receipt") {
        ReversePassageReceipt::OnlyWithTheResidual {
            merged_left,
            merged_right,
        } => {
            assert_eq!(merged_left, point(&[2, 1]));
            assert_eq!(merged_right, point(&[-2, 1]));
        }
        other => panic!("the plastic fold merges two faces, not {other:?}"),
    }
    assert_eq!(
        plastic.reverse_passage(&[]).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a plastic crease's reverse passage"
        },
        "a check over an empty probe is not a check"
    );

    // On a probe that lives entirely on one side nothing is merged, and the receipt says exactly
    // how many faces it rests on.
    let one_sided = vec![point(&[2, 1]), point(&[3, 4])];
    assert_eq!(
        plastic.reverse_passage(&one_sided).expect("a receipt"),
        ReversePassageReceipt::FromTheFaceAlone { faces_checked: 2 }
    );
}

// ---------------------------------------------------------------------------------------------
// 3. the bounce and the collision
// ---------------------------------------------------------------------------------------------

/// The billiard unfolding: the crossing is exactly rational, the tangential direction is fixed and
/// the normal component is negated. Equal angles, with no angle taken.
#[test]
fn the_bounce_is_the_reflected_path() {
    let h = crease(&[0, 1], 0);
    let from = point(&[0, 2]);
    let to = point(&[4, -2]);
    let reading = billiard_unfolding(&h, &from, &to).expect("the segment crosses");
    assert_eq!(reading.crossing_parameter, ratio(1, 2));
    assert_eq!(
        h.side_value(&reading.crossing_point).expect("a side"),
        Rat::zero(),
        "Lean: Crease.crossing_side_eq_zero"
    );
    assert_eq!(reading.crossing_point, point(&[2, 0]));
    assert!(reading.tangential_is_fixed, "Lean: linReflect_fixes_tangential");
    assert!(reading.normal_is_negated, "Lean: bounce_direction");
    assert_eq!(reading.outgoing_direction, vec![rat(4), rat(4)]);
    assert_eq!(reading.incoming_normal_pairing, rat(-4));
    assert_eq!(reading.outgoing_normal_pairing, rat(4));
}

/// A segment that does not change side is refused: a bounce needs a crossing.
#[test]
fn a_segment_that_does_not_cross_is_refused() {
    let h = crease(&[0, 1], 0);
    assert_eq!(
        billiard_unfolding(&h, &point(&[0, 2]), &point(&[4, 2])).unwrap_err(),
        FoldRefusal::SegmentDoesNotCrossTheCrease
    );
    assert_eq!(
        billiard_unfolding(&h, &point(&[0, 2]), &point(&[4, 1])).unwrap_err(),
        FoldRefusal::SegmentDoesNotCrossTheCrease,
        "a crossing outside the segment is not a bounce on it"
    );
}

/// The collision: after folding, the two layers stack and the contact law between them is the
/// existing three-valued reading, carried whole.
#[test]
fn the_folded_layers_stack_and_their_contact_stays_three_valued() {
    let h = crease(&[0, 1], 0);
    let lower = [point(&[0, 1]), point(&[10, 1])];
    let below = [point(&[0, -1]), point(&[10, -3])];
    let upper: Vec<FoldPoint> = below
        .iter()
        .map(|entry| h.fold(entry).expect("a fold"))
        .collect();
    assert_eq!(upper[0], point(&[0, 1]), "the fold stacks the layers");

    let reading = layer_contact(&upper, &lower, &aperture(1)).expect("a contact reading");
    assert_eq!(reading.readings.len(), 4);
    assert_eq!(reading.inside + reading.outside + reading.open, 4);
    assert_eq!(
        reading.touching,
        vec![(0, 0)],
        "the folded layer touches the one it landed on"
    );
    assert!(
        reading.open == 0 || !reading.undecided.is_empty(),
        "an open pair is carried in its own list"
    );
}

/// An `Open` layer pair is carried plural and never rounded into `Inside` or `Outside`.
#[test]
fn an_open_layer_contact_is_carried_and_never_rounded() {
    let upper = vec![point(&[0, 0])];
    let lower = vec![point(&[0, 2])];
    // With exact places the separation is a point, so the reading is two-valued in practice.
    let touching = layer_contact(&upper, &lower, &aperture(4)).expect("a reading");
    assert_eq!(touching.inside, 1);
    assert_eq!(touching.open, 0);
    assert!(touching.undecided.is_empty());
    let apart = layer_contact(&upper, &lower, &aperture(3)).expect("a reading");
    assert_eq!(apart.outside, 1);
    assert!(apart.touching.is_empty());

    // Under a declared squared-separation tolerance the aperture straddles the enclosure and the
    // pair is `Open`. It is counted and listed as undecided, and it is neither touching nor
    // outside: nothing rounds it.
    let undecided =
        layer_contact_within(&upper, &lower, &aperture(4), &rat(1)).expect("a reading");
    assert_eq!(undecided.open, 1);
    assert_eq!(undecided.inside, 0);
    assert_eq!(undecided.outside, 0);
    assert_eq!(undecided.undecided, vec![(0, 0)]);
    assert!(undecided.touching.is_empty());
    assert_eq!(undecided.readings[0].2, ContactClass::Open);

    assert_eq!(
        layer_contact_within(&upper, &lower, &aperture(4), &rat(-1)).unwrap_err(),
        FoldRefusal::NegativeTolerance
    );
}

/// A contact reading over an empty layer is refused: no non-penetration verdict is minted from
/// nothing.
#[test]
fn an_empty_layer_probe_is_refused() {
    assert_eq!(
        layer_contact(&[], &[point(&[0, 0])], &aperture(1)).unwrap_err(),
        FoldRefusal::EmptyLayerProbe { upper: 0, lower: 1 }
    );
    assert_eq!(
        layer_contact(&[point(&[0, 0])], &[], &aperture(1)).unwrap_err(),
        FoldRefusal::EmptyLayerProbe { upper: 1, lower: 0 }
    );
}

// ---------------------------------------------------------------------------------------------
// 4. division, shear, inversion
// ---------------------------------------------------------------------------------------------

/// **Rotation is two reflections**, exactly over `Q`: each reflection has determinant `−1` and the
/// composite has determinant `+1` and is orthogonal.
#[test]
fn rotation_is_two_reflections_exactly() {
    let first = GaussianRational::integers(1, 0);
    let second = GaussianRational::integers(0, 1);
    let reading = rotation_from_two_reflections(&first, &second).expect("a rotation");
    assert_eq!(reading.reflection_determinants.0, rat(-1));
    assert_eq!(reading.reflection_determinants.1, rat(-1));
    assert_eq!(reading.determinant, rat(1));
    assert!(reading.is_orthogonal);
    // Reflecting in the x axis then the y axis is the half turn: turn = i·1̄ = i, whose square is
    // −1, so the rotation is by π and is not the identity.
    assert_eq!(reading.turn, GaussianRational::integers(0, 1));
    assert!(!reading.is_identity);
    assert_eq!(reading.matrix[0][0], rat(-1));
    assert_eq!(reading.matrix[1][1], rat(-1));

    // Two equal reflections compose to the identity, exactly.
    let same = rotation_from_two_reflections(&first, &first).expect("a rotation");
    assert!(same.is_identity);
    assert_eq!(same.matrix[0][0], rat(1));
    assert_eq!(same.matrix[1][1], rat(1));
    assert_eq!(same.matrix[0][1], Rat::zero());

    // A direction with no rational angle still gives an exact rational rotation.
    let skew = GaussianRational::integers(3, 4);
    let mixed = rotation_from_two_reflections(&first, &skew).expect("a rotation");
    assert_eq!(mixed.determinant, rat(1));
    assert!(mixed.is_orthogonal);
    assert_eq!(mixed.turn, GaussianRational::integers(3, 4));
}

/// A line reflection is a reflection of a **line**, not a ray: rescaling the direction, including
/// by `−1`, leaves the matrix unchanged.
#[test]
fn a_line_reflection_does_not_see_the_direction_s_sign_or_length() {
    let direction = GaussianRational::integers(2, 3);
    let negated = GaussianRational::integers(-4, -6);
    assert_eq!(
        line_reflection_matrix(&direction).expect("a matrix"),
        line_reflection_matrix(&negated).expect("a matrix"),
        "Lean: lineReflect_cscale"
    );
    assert_eq!(
        line_reflection_matrix(&GaussianRational::integers(0, 0)).unwrap_err(),
        FoldRefusal::DegenerateCrease
    );
}

/// A shear changes a squared distance at every point and every scale, so it is not an isometry and
/// therefore not a composition of folds.
#[test]
fn a_shear_changes_a_squared_distance_at_every_scale() {
    for scale in [1_i64, -3, 7] {
        for coefficient in [1_i64, -2, 5] {
            let defect = shear_defect(&rat(coefficient), &rat(scale));
            assert!(
                !defect.is_zero(),
                "Lean: shear_changes_a_squared_distance_at_every_point_and_scale"
            );
            assert_eq!(defect, rat(coefficient * coefficient * scale * scale));
        }
    }
    assert!(shear_defect(&Rat::zero(), &rat(5)).is_zero());
}

/// Inversion satisfies the exact rational distance law, and the cross ratio is exactly invariant.
#[test]
fn inversion_satisfies_the_exact_distance_law_and_preserves_the_cross_ratio() {
    let inversion = Inversion::declared(rat(2)).expect("a declared inversion");
    let w = point(&[1, 0, 0]);
    let x = point(&[0, 1, 0]);
    let y = point(&[0, 0, 1]);
    let z = point(&[1, 1, 1]);

    for (left, right) in [(&w, &x), (&x, &y), (&w, &y), (&x, &z)] {
        let image_left = inversion.apply(left).expect("an image");
        let image_right = inversion.apply(right).expect("an image");
        assert_eq!(
            squared_distance(image_left.coordinates(), image_right.coordinates())
                .expect("a squared distance"),
            inversion.distance_law(left, right).expect("the law"),
            "Lean: inversion_distSq"
        );
    }

    let ratio_before = {
        let a = squared_distance(w.coordinates(), x.coordinates()).expect("wx");
        let b = squared_distance(y.coordinates(), z.coordinates()).expect("yz");
        let c = squared_distance(w.coordinates(), y.coordinates()).expect("wy");
        let d = squared_distance(x.coordinates(), z.coordinates()).expect("xz");
        (a * b) / (c * d)
    };
    let ratio_after = {
        let a = inversion.distance_law(&w, &x).expect("wx");
        let b = inversion.distance_law(&y, &z).expect("yz");
        let c = inversion.distance_law(&w, &y).expect("wy");
        let d = inversion.distance_law(&x, &z).expect("xz");
        (a * b) / (c * d)
    };
    assert_eq!(
        ratio_before, ratio_after,
        "Lean: inversion_preserves_cross_ratio"
    );
}

/// Inversion refuses its centre and the zero radius by name.
#[test]
fn inversion_refuses_the_centre_and_the_zero_radius() {
    assert_eq!(
        Inversion::declared(Rat::zero()).unwrap_err(),
        FoldRefusal::DegenerateInversion
    );
    let inversion = Inversion::declared(rat(1)).expect("a declared inversion");
    assert_eq!(
        inversion.apply(&point(&[0, 0, 0])).unwrap_err(),
        FoldRefusal::InversionAtTheCentre
    );
    assert_eq!(
        inversion
            .distance_law(&point(&[0, 0, 0]), &point(&[1, 0, 0]))
            .unwrap_err(),
        FoldRefusal::InversionAtTheCentre
    );
}

// ---------------------------------------------------------------------------------------------
// 5. fold against cut
// ---------------------------------------------------------------------------------------------

/// A square disc split into two triangles, symmetric about the line `x = 0`.
fn symmetric_disc() -> CellComplex {
    CellComplex::declared(
        "symmetric disc",
        4,
        vec![[0, 1], [0, 2], [1, 2], [1, 3], [2, 3]],
        vec![[0, 1, 2], [1, 2, 3]],
    )
    .expect("a declared complex")
}

/// A triangulated annulus: two concentric triangles joined by six triangles.
fn annulus() -> CellComplex {
    CellComplex::declared(
        "annulus",
        6,
        vec![
            [0, 1],
            [0, 2],
            [0, 3],
            [0, 5],
            [1, 2],
            [1, 3],
            [1, 4],
            [2, 4],
            [2, 5],
            [3, 4],
            [3, 5],
            [4, 5],
        ],
        vec![
            [0, 1, 3],
            [1, 3, 4],
            [1, 2, 4],
            [2, 4, 5],
            [0, 2, 5],
            [0, 3, 5],
        ],
    )
    .expect("a declared annulus")
}

/// A fold of a complex changes no Betti number and no edge length.
#[test]
fn a_cellular_fold_preserves_betti_and_every_edge_length() {
    let complex = symmetric_disc();
    assert_eq!(
        complex.betti(),
        Ok(vec![1, 0, 0]),
        "the square disc is contractible"
    );
    assert_eq!(complex.cell_euler_characteristic(), 1);

    // The realization is symmetric about `x = 0`, and the fold is the vertex map that swaps the
    // two vertices the crease separates.
    let places = vec![
        point(&[-1, 0]),
        point(&[0, -1]),
        point(&[0, 1]),
        point(&[1, 0]),
    ];
    let h = crease(&[1, 0], 0);
    assert_eq!(h.reflect(&places[0]).expect("a reflection"), places[3]);
    assert_eq!(h.reflect(&places[1]).expect("a reflection"), places[1]);

    let fold = CellularFold {
        image: vec![3, 1, 2, 0],
    };
    let reading = read_cellular_fold(&complex, &fold, Some(&places)).expect("a fold reading");
    assert!(
        reading.is_cellular_automorphism,
        "the crease lies along the skeleton, so the fold is a bijection on cells"
    );
    assert_eq!(
        reading.homology,
        FoldHomologyVerdict::Preserved,
        "Lean: ChainTwo.fold_preserves_betti"
    );
    assert_eq!(reading.betti_after, Some(reading.betti_before.clone()));
    assert!(
        reading.edge_lengths_preserved,
        "Lean: fold_preserves_intrinsic_length"
    );
    assert!(reading.moved_edges.is_empty());
}

/// A vertex map that is not a bijection on cells is named as such rather than reported as a fold.
#[test]
fn a_non_cellular_vertex_map_is_not_a_fold() {
    let complex = symmetric_disc();
    let collapse = CellularFold {
        image: vec![1, 1, 2, 3],
    };
    let reading = read_cellular_fold(&complex, &collapse, None).expect("a reading");
    assert!(!reading.is_cellular_automorphism);
    assert_eq!(
        reading.homology,
        FoldHomologyVerdict::NotAFold,
        "a map that is not a bijection on cells makes no homology claim"
    );
    assert_eq!(reading.betti_after, None);
}

/// **Cutting an annulus into a disc changes `b₁` from one to zero.**
#[test]
fn cutting_an_annulus_changes_the_first_betti_number() {
    let before = annulus();
    assert_eq!(before.betti(), Ok(vec![1, 1, 0]));
    assert_eq!(before.cell_euler_characteristic(), 0);

    // Cut along the radial edge {0,3}: vertex 0 becomes {0, 6} and vertex 3 becomes {3, 7}.
    let after = CellComplex::declared(
        "annulus cut to a disc",
        8,
        vec![
            [0, 1],
            [0, 3],
            [1, 2],
            [1, 3],
            [1, 4],
            [2, 4],
            [2, 5],
            [2, 6],
            [3, 4],
            [4, 5],
            [5, 6],
            [5, 7],
            [6, 7],
        ],
        vec![
            [0, 1, 3],
            [1, 3, 4],
            [1, 2, 4],
            [2, 4, 5],
            [2, 5, 6],
            [5, 6, 7],
        ],
    )
    .expect("the cut complex");
    assert_eq!(after.betti(), Ok(vec![1, 0, 0]));
    assert_eq!(after.cell_euler_characteristic(), 1);

    let gluing = vec![
        CutIdentification { left: 0, right: 6 },
        CutIdentification { left: 3, right: 7 },
    ];
    let reading = read_cut(&before, &after, &gluing).expect("a cut reading");
    assert!(reading.homology_changed);
    assert_eq!(reading.grades_that_moved, vec![1]);
    assert_eq!(reading.betti_before, vec![1, 1, 0]);
    assert_eq!(reading.betti_after, vec![1, 0, 0]);
    assert!(
        reading.regluing_is_exact,
        "the gluing data is exactly what reversing the cut needs"
    );
    assert!(
        reading.residual_is_strictly_larger_than_a_folds(),
        "Lean: residual_injective_on_fibre"
    );
    assert_eq!(reading.fold_residual_bits, BigUint::one());
    // Two identifications, each naming two of eight vertex addresses: 2 · 2 · 3 = 12 bits.
    assert_eq!(reading.cut_residual_bits, BigUint::from(12_u32));
    assert!(reading.receipt.residual.provenance.is_accounted());
}

/// **Cutting a disc in two changes `b₀` from one to two.**
#[test]
fn cutting_a_disc_in_two_changes_the_zeroth_betti_number() {
    let before = symmetric_disc();
    let after = CellComplex::declared(
        "the disc cut along its diagonal",
        6,
        vec![[0, 1], [0, 2], [1, 2], [3, 4], [3, 5], [4, 5]],
        vec![[0, 1, 2], [3, 4, 5]],
    )
    .expect("the cut complex");
    assert_eq!(after.betti(), Ok(vec![2, 0, 0]));

    let gluing = vec![
        CutIdentification { left: 1, right: 4 },
        CutIdentification { left: 2, right: 5 },
    ];
    let reading = read_cut(&before, &after, &gluing).expect("a cut reading");
    assert_eq!(reading.betti_before, vec![1, 0, 0]);
    assert_eq!(reading.betti_after, vec![2, 0, 0]);
    assert!(reading.homology_changed);
    assert_eq!(reading.grades_that_moved, vec![0]);
    assert!(reading.regluing_is_exact);
    assert!(reading.residual_is_strictly_larger_than_a_folds());

    // Regluing really returns the original complex, cell for cell.
    let reglued = reglue(&after, &gluing).expect("the reglue returns");
    assert_eq!(reglued.vertex_count(), before.vertex_count());
    assert_eq!(reglued.edges(), before.edges());
    assert_eq!(reglued.triangles(), before.triangles());
}

/// An empty gluing is refused: a cut that identified nothing is not a cut.
#[test]
fn an_empty_gluing_is_refused() {
    let complex = symmetric_disc();
    assert_eq!(
        read_cut(&complex, &complex, &[]).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a cut's gluing data"
        }
    );
}

/// Hostile input: a complex whose triangle has no declared face, a repeated cell, a collapsed cell
/// and a population above the ceiling are all refused by name.
#[test]
fn a_malformed_complex_is_refused_by_name() {
    assert_eq!(
        CellComplex::declared("open triangle", 3, vec![[0, 1], [1, 2]], vec![[0, 1, 2]])
            .unwrap_err(),
        FoldRefusal::TriangleFaceAbsent { face: [0, 2] }
    );
    assert_eq!(
        CellComplex::declared("repeat", 3, vec![[0, 1], [0, 1]], Vec::new()).unwrap_err(),
        FoldRefusal::RepeatedCell
    );
    assert_eq!(
        CellComplex::declared("loop", 2, vec![[1, 1]], Vec::new()).unwrap_err(),
        FoldRefusal::CollapsedCell
    );
    assert_eq!(
        CellComplex::declared("absent", 2, vec![[0, 5]], Vec::new()).unwrap_err(),
        FoldRefusal::CellAddressesAnAbsentVertex { vertex: 5 }
    );
    assert_eq!(
        CellComplex::declared("empty", 0, Vec::new(), Vec::new()).unwrap_err(),
        FoldRefusal::EmptyComplex
    );
    assert_eq!(
        CellComplex::declared("wide", CELL_CEILING + 1, Vec::new(), Vec::new()).unwrap_err(),
        FoldRefusal::CellPopulationTooWide {
            cells: CELL_CEILING + 1,
            ceiling: CELL_CEILING,
        }
    );
}

/// **A cut is a passage that breaks bonds**, and the delta is the existing B6 owner's.
#[test]
fn the_cut_breaks_bonds_through_the_existing_passage_delta() {
    use crate::physical_occurrence::ConstraintDelta;
    use crate::physical_occurrence::fixture::{complete_environment, synthetic_family};

    let environment = complete_environment("cut", "folded", "seed-1").expect("a complete environment");
    let before = synthetic_family(
        1,
        &environment,
        &[
            ContactClass::Inside,
            ContactClass::Inside,
            ContactClass::Outside,
        ],
    );
    let severed = BTreeSet::from([(1_u32, 1_u32), (1, 2)]);
    let after = severed_contact_family(&before, &severed).expect("the cut family");
    let delta = ConstraintDelta::between(&before, &after).expect("the delta");
    assert_eq!(delta.broken(), vec![(1, 1), (1, 2)]);
    assert_eq!(delta.formed(), Vec::<(u32, u32)>::new());
    assert!(delta.changed().len() == 2);

    assert_eq!(
        severed_contact_family(&before, &BTreeSet::new()).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a cut's severed contact set"
        }
    );
    assert_eq!(
        severed_contact_family(&before, &BTreeSet::from([(9_u32, 9_u32)])).unwrap_err(),
        FoldRefusal::SeveredPairIsNotAddressed { pair: (9, 9) }
    );
}

// ---------------------------------------------------------------------------------------------
// 6. crease patterns as hinge frameworks
// ---------------------------------------------------------------------------------------------

/// Two triangular panels hinged along one crease have exactly one folding motion.
#[test]
fn a_triangulated_crease_pattern_has_one_folding_motion_per_crease() {
    let pattern = CreasePattern {
        lineage: "two triangular panels, folded".to_owned(),
        places: vec![
            vec![rat(0), rat(0), rat(0)],
            vec![rat(0), rat(1), rat(0)],
            vec![rat(1), rat(0), rat(0)],
            vec![rat(0), rat(0), rat(1)],
        ],
        creases: vec![[0, 1]],
        panels: vec![vec![0, 1, 2], vec![0, 1, 3]],
    };
    let framing = hinge_framework(&pattern).expect("a framing");
    assert_eq!(framing.crease_bars, 1);
    assert_eq!(framing.reading.constraint_count, 5);
    assert_eq!(
        framing.folding_motions, 1,
        "the one folding motion is the dihedral about the crease"
    );
    assert!(!framing.locked);
    assert!(framing.planar_panels.is_empty());
    assert_eq!(framing.reading.trivial.dimension_of_span, 6);
}

/// **A completely braced planar quadrilateral panel is infinitesimally flexible in three
/// dimensions, and carries a self-stress.** The reading names it rather than counting it as a
/// folding motion.
#[test]
fn a_planar_panel_of_four_vertices_is_infinitesimally_flexible_and_locked() {
    let pattern = CreasePattern {
        lineage: "one planar quadrilateral panel".to_owned(),
        places: vec![
            vec![rat(0), rat(0), rat(0)],
            vec![rat(1), rat(0), rat(0)],
            vec![rat(1), rat(1), rat(0)],
            vec![rat(0), rat(1), rat(0)],
        ],
        creases: Vec::new(),
        panels: vec![vec![0, 1, 2, 3]],
    };
    let framing = hinge_framework(&pattern).expect("a framing");
    assert_eq!(framing.panel_bars, 6, "the complete bracing of four vertices");
    assert_eq!(framing.planar_panels, vec![0]);
    assert_eq!(
        framing.folding_motions, 1,
        "the out-of-plane infinitesimal flex of a coplanar complete graph"
    );
    assert!(
        framing.locked,
        "the same degeneracy is a self-stress: the count alone under-reports the motion space"
    );
    assert_eq!(framing.reading.self_stress_dimension, 1);
    assert!(framing.reading.maxwell.count_is_a_bound_only);
}

/// Hostile input: a panel below three vertices, above the ceiling, or naming an absent vertex.
#[test]
fn a_malformed_crease_pattern_is_refused_by_name() {
    let places = vec![vec![rat(0), rat(0), rat(0)], vec![rat(1), rat(0), rat(0)]];
    assert_eq!(
        hinge_framework(&CreasePattern {
            lineage: "edge panel".to_owned(),
            places: places.clone(),
            creases: Vec::new(),
            panels: vec![vec![0, 1]],
        })
        .unwrap_err(),
        FoldRefusal::PanelIsNotAPolygon { extent: 2 }
    );
    assert_eq!(
        hinge_framework(&CreasePattern {
            lineage: "absent".to_owned(),
            places: places.clone(),
            creases: Vec::new(),
            panels: vec![vec![0, 1, 9]],
        })
        .unwrap_err(),
        FoldRefusal::CellAddressesAnAbsentVertex { vertex: 9 }
    );
    assert_eq!(
        hinge_framework(&CreasePattern {
            lineage: "wide panel".to_owned(),
            places,
            creases: Vec::new(),
            panels: vec![(0..=PANEL_EXTENT_CEILING).collect()],
        })
        .unwrap_err(),
        FoldRefusal::PanelTooWide {
            extent: PANEL_EXTENT_CEILING + 1,
            ceiling: PANEL_EXTENT_CEILING,
        }
    );
}

/// **Kawasaki's law without an angle.** The coordinate-ray vertex folds flat; moving one ray to
/// `(1, −1)` breaks it, and the turn's imaginary part is the exact witness.
#[test]
fn kawasaki_holds_at_the_plus_vertex_and_fails_at_the_skew_one() {
    let plus = KawasakiVertex::declared(vec![
        GaussianRational::integers(1, 0),
        GaussianRational::integers(0, 1),
        GaussianRational::integers(-1, 0),
        GaussianRational::integers(0, -1),
    ])
    .expect("a declared vertex");
    assert_eq!(plus.turn(), GaussianRational::integers(-1, 0));
    assert!(plus.is_flat_foldable(), "Lean: plusVertexIsFlatFoldable");

    let skew = KawasakiVertex::declared(vec![
        GaussianRational::integers(1, 0),
        GaussianRational::integers(0, 1),
        GaussianRational::integers(-1, 0),
        GaussianRational::integers(1, -1),
    ])
    .expect("a declared vertex");
    assert_eq!(skew.turn(), GaussianRational::integers(-1, -1));
    assert!(
        !skew.is_flat_foldable(),
        "Lean: skewVertexIsNotFlatFoldable"
    );
}

/// Hostile input: an odd degree, a zero direction and an empty vertex are all refused.
#[test]
fn a_malformed_single_vertex_is_refused() {
    assert_eq!(
        KawasakiVertex::declared(Vec::new()).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a single-vertex crease pattern"
        }
    );
    assert_eq!(
        KawasakiVertex::declared(vec![
            GaussianRational::integers(1, 0),
            GaussianRational::integers(0, 1),
            GaussianRational::integers(-1, 0),
        ])
        .unwrap_err(),
        FoldRefusal::VertexDegreeIsOdd { degree: 3 }
    );
    assert_eq!(
        KawasakiVertex::declared(vec![
            GaussianRational::integers(1, 0),
            GaussianRational::integers(0, 0),
        ])
        .unwrap_err(),
        FoldRefusal::DegenerateCrease
    );
}

/// **Maekawa's law is the integer count law**, and the two forms agree on every degree-four
/// assignment.
#[test]
fn maekawa_is_the_integer_count_law() {
    for bits in 0..16_u32 {
        let creases: Vec<bool> = (0..4).map(|at| bits & (1 << at) != 0).collect();
        let assignment = MaekawaAssignment::declared(creases).expect("an assignment");
        assert_eq!(
            assignment.is_balanced(),
            assignment.mountain_count_form(),
            "Lean: maekawa_iff_mountain_count"
        );
        assert_eq!(assignment.mountains() + assignment.valleys(), 4);
    }
    let balanced: usize = (0..16_u32)
        .filter(|bits| {
            let creases: Vec<bool> = (0..4).map(|at| bits & (1 << at) != 0).collect();
            MaekawaAssignment::declared(creases)
                .expect("an assignment")
                .is_balanced()
        })
        .count();
    assert_eq!(balanced, 8, "Lean: maekawa_degree_four");

    assert_eq!(
        MaekawaAssignment::declared(vec![true, false, true]).unwrap_err(),
        FoldRefusal::VertexDegreeIsOdd { degree: 3 }
    );
    assert_eq!(
        MaekawaAssignment::declared(Vec::new()).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a mountain/valley assignment"
        }
    );
}

/// **Flat-foldability never affirms.** It refutes by a named local law, or returns its bound.
#[test]
fn flat_foldability_refutes_and_never_affirms() {
    let plus = KawasakiVertex::declared(vec![
        GaussianRational::integers(1, 0),
        GaussianRational::integers(0, 1),
        GaussianRational::integers(-1, 0),
        GaussianRational::integers(0, -1),
    ])
    .expect("a vertex");
    let skew = KawasakiVertex::declared(vec![
        GaussianRational::integers(1, 0),
        GaussianRational::integers(0, 1),
        GaussianRational::integers(-1, 0),
        GaussianRational::integers(1, -1),
    ])
    .expect("a vertex");
    let balanced =
        MaekawaAssignment::declared(vec![true, true, true, false]).expect("an assignment");
    let unbalanced =
        MaekawaAssignment::declared(vec![true, true, false, false]).expect("an assignment");

    match flat_foldability(&skew, &balanced, 32).expect("a verdict") {
        FlatFoldabilityVerdict::RefutedByKawasaki { turn_imaginary } => {
            assert_eq!(turn_imaginary, rat(-1));
        }
        other => panic!("the skew vertex is refuted by Kawasaki, not {other:?}"),
    }
    match flat_foldability(&plus, &unbalanced, 32).expect("a verdict") {
        FlatFoldabilityVerdict::RefutedByMaekawa {
            mountains,
            valleys,
            balance,
        } => {
            assert_eq!((mountains, valleys), (2, 2));
            assert_eq!(balance, BigInt::zero());
        }
        other => panic!("the balanced-free assignment is refuted by Maekawa, not {other:?}"),
    }
    match flat_foldability(&plus, &balanced, 32).expect("a verdict") {
        FlatFoldabilityVerdict::NotDecidedWithinBound {
            bound,
            orderings_total,
            ..
        } => {
            assert_eq!(bound, 32);
            assert_eq!(orderings_total, BigUint::from(24_u32));
        }
        other => panic!("nothing affirms flat-foldability; got {other:?}"),
    }
    assert_eq!(
        flat_foldability(&plus, &MaekawaAssignment::declared(vec![true; 6]).unwrap(), 4)
            .unwrap_err(),
        FoldRefusal::AssignmentDegreeDisagrees {
            vertex: 4,
            assignment: 6
        }
    );
}

// ---------------------------------------------------------------------------------------------
// 7. the fold catastrophe
// ---------------------------------------------------------------------------------------------

/// Two equilibria above the threshold, one at it, none below — counted exactly by the Sturm owner.
#[test]
fn the_fold_catastrophe_counts_its_equilibria_exactly() {
    let above = FoldCatastrophe::declared(rat(4)).equilibria().expect("above");
    assert_eq!(above.equilibria, 2, "Lean: foldEquilibria_two_of_pos");
    assert_eq!(above.stable, 1, "Lean: positiveRoot_is_stable");
    assert_eq!(above.unstable, 1, "Lean: negativeRoot_is_unstable");
    assert!(!above.degenerate);

    // An irrational pair of roots, counted without ever forming one.
    let irrational = FoldCatastrophe::declared(ratio(1, 3))
        .equilibria()
        .expect("an irrational pair");
    assert_eq!(irrational.equilibria, 2);
    assert_eq!((irrational.stable, irrational.unstable), (1, 1));

    let at = FoldCatastrophe::declared(Rat::zero())
        .equilibria()
        .expect("at");
    assert_eq!(at.equilibria, 1);
    assert!(at.degenerate, "V'' vanishes where the two roots merge");
    assert_eq!((at.stable, at.unstable), (0, 0));

    let below = FoldCatastrophe::declared(rat(-1))
        .equilibria()
        .expect("below");
    assert_eq!(below.equilibria, 0, "Lean: no_equilibrium_of_neg");
}

/// The declared crease model's threshold is exact, typed, and is the fold catastrophe's `a = 0`.
#[test]
fn the_crease_model_threshold_is_exact_and_typed() {
    let base = mechanical_base().expect("a mechanical base");
    let torque = torque_dimension(&base).expect("a torque dimension");
    let stiffness = Quantity::new(rat(8), torque.clone());
    // u0 = 1/2, so the threshold is 8 · 1/4 = 2.
    let model = CreaseModel::declared(
        stiffness.clone(),
        ratio(1, 2),
        Quantity::new(rat(1), torque.clone()),
    )
    .expect("a declared model");
    assert_eq!(model.threshold().expect("a threshold").parts().0, &rat(2));
    assert_eq!(model.reduced_parameter().expect("a"), ratio(1, 8));
    assert!(model.held_equilibrium_exists().expect("held"));
    let equilibria = model.equilibria().expect("the equilibria");
    assert_eq!(equilibria.equilibria, 2);
    assert_eq!(equilibria.stable, 1);

    // At the threshold exactly the two equilibria merge.
    let at = CreaseModel::declared(
        stiffness.clone(),
        ratio(1, 2),
        Quantity::new(rat(2), torque.clone()),
    )
    .expect("a declared model");
    assert_eq!(at.reduced_parameter().expect("a"), Rat::zero());
    assert!(at.held_equilibrium_exists().expect("held"));
    assert!(at.equilibria().expect("the equilibria").degenerate);

    // Above it the held state is gone.
    let beyond = CreaseModel::declared(stiffness, ratio(1, 2), Quantity::new(rat(3), torque))
        .expect("a declared model");
    assert!(!beyond.held_equilibrium_exists().expect("held"));
    assert_eq!(beyond.equilibria().expect("the equilibria").equilibria, 0);
}

/// The crease model refuses a load in the wrong units and a nonpositive stiffness.
#[test]
fn the_crease_model_refuses_units_that_do_not_compare() {
    let base = mechanical_base().expect("a base");
    let torque = torque_dimension(&base).expect("a torque");
    let length = base.unit("m").expect("a length");
    let refused = CreaseModel::declared(
        Quantity::new(rat(1), torque.clone()),
        Rat::one(),
        Quantity::new(rat(1), length),
    )
    .unwrap_err();
    assert!(matches!(
        refused,
        FoldRefusal::CreaseModelUnitsDisagree { .. }
    ));
    assert_eq!(
        CreaseModel::declared(
            Quantity::new(Rat::zero(), torque.clone()),
            Rat::one(),
            Quantity::new(rat(1), torque.clone()),
        )
        .unwrap_err(),
        FoldRefusal::NonpositiveStiffness
    );
    assert_eq!(
        CreaseModel::declared(
            Quantity::new(rat(-1), torque.clone()),
            Rat::one(),
            Quantity::new(rat(1), torque),
        )
        .unwrap_err(),
        FoldRefusal::NonpositiveStiffness
    );
}

/// **Brandon's lever arm.** The rational rotation is orthogonal exactly, and the squared
/// displacement scales as the square of the distance from the crease.
#[test]
fn the_lever_arm_scales_the_offset_linearly_with_distance() {
    for numerator in [-3_i64, -1, 0, 1, 2, 5] {
        for denominator in [1_i64, 2, 7] {
            let t = ratio(numerator, denominator);
            let (cosine, sine) = rational_rotation(&t);
            assert_eq!(
                &cosine * &cosine + &sine * &sine,
                Rat::one(),
                "Lean: rationalRotation_orthogonal"
            );
        }
    }
    let t = ratio(1, 3);
    let base = opening_displacement_squared(&rat(1), &t);
    // 4 ℓ² t² / (1 + t²) at ℓ = 1, t = 1/3 is (4/9)/(10/9) = 2/5.
    assert_eq!(base, ratio(2, 5));
    for factor in [2_i64, 3, 7] {
        assert_eq!(
            opening_displacement_squared(&rat(factor), &t),
            rat(factor * factor) * &base,
            "Lean: displacementSq_scales_with_lever"
        );
    }
    assert!(opening_displacement_squared(&rat(5), &Rat::zero()).is_zero());
}

// ---------------------------------------------------------------------------------------------
// 8. the protein backbone
// ---------------------------------------------------------------------------------------------

fn synthetic_backbone(residues: usize) -> BackboneChain {
    // A rational zig-zag in general position: every consecutive step changes two coordinates, so
    // no three atoms are collinear and no four are coplanar.
    let mut carried = Vec::with_capacity(residues);
    for at in 0..residues {
        let base = at as i64;
        carried.push(BackboneResidue {
            source_ordinal: at as i32 + 1,
            monomer: "ALA".to_owned(),
            nitrogen: vec![rat(3 * base), rat(0), rat(base)],
            alpha_carbon: vec![rat(3 * base + 1), rat(1), rat(0)],
            carbon: vec![rat(3 * base + 2), rat(0), rat(base + 2)],
        });
    }
    BackboneChain::declared("synthetic zig-zag", carried).expect("a declared chain")
}

/// **The backbone's bar itemization is `7r − 4` and its measured internal freedom is `2(r − 1)`.**
#[test]
fn the_synthetic_backbone_has_two_internal_freedoms_per_residue_step() {
    for residues in [2_usize, 3, 4, 5] {
        let chain = synthetic_backbone(residues);
        assert_eq!(chain.atom_count(), 3 * residues);
        assert_eq!(chain.bar_count(), 7 * residues as i64 - 4);
        let bars = chain.bars().expect("the bars");
        assert_eq!(bars.len() as i64, chain.bar_count());
        let framing = chain.framework(&BTreeMap::new()).expect("a framing");
        assert_eq!(framing.predicted_internal, 2 * residues as i64 - 2);
        assert_eq!(
            framing.measured_internal as i64, framing.predicted_internal,
            "Lean: backbone_internal_dof, measured and not assumed"
        );
        assert!(framing.prediction_holds);
        assert!(!framing.locked, "a free chain carries no self-stress");
        assert_eq!(framing.reading.trivial.dimension_of_span, 6);
    }
}

/// Adding contact bars removes dihedral motions: that is what holds a fold.
#[test]
fn contact_bars_remove_dihedral_motions() {
    let chain = synthetic_backbone(4);
    let free = chain.framework(&BTreeMap::new()).expect("the free framing");
    assert_eq!(free.measured_internal, 6);

    // A generous aperture over the whole window closes every remaining dihedral.
    let contacts = chain
        .contact_bars(2, &rat(10_000))
        .expect("the contact bars");
    assert!(!contacts.is_empty());
    let held = chain.framework(&contacts).expect("the held framing");
    assert!(
        held.measured_internal < free.measured_internal,
        "the contacts hold the fold: {} against {}",
        held.measured_internal,
        free.measured_internal
    );
    assert!(held.contact_bars > 0);
    assert!(!held.prediction_holds, "the prediction is for the free chain");
    assert!(
        held.locked,
        "a chain held by more contacts than it has freedoms is redundantly held"
    );
}

/// A sequence separation of one names the covalent step and is refused.
#[test]
fn a_covalent_separation_is_refused() {
    let chain = synthetic_backbone(3);
    assert_eq!(
        chain.contact_bars(1, &rat(100)).unwrap_err(),
        FoldRefusal::SeparationIsCovalent { separation: 1 }
    );
    assert_eq!(
        BackboneChain::declared("empty", Vec::new()).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a backbone chain"
        }
    );
}

/// **A dihedral is reported without an angle**: an exact rational `cos²θ` in `[0, 1]` and two
/// signs, and never a float.
#[test]
fn a_dihedral_is_reported_without_an_angle() {
    // A right-angle dihedral: the two normals are orthogonal, so cos²θ = 0.
    let right = exact_dihedral(
        &[rat(1), rat(0), rat(0)],
        &[rat(0), rat(0), rat(0)],
        &[rat(0), rat(1), rat(0)],
        &[rat(0), rat(1), rat(1)],
    )
    .expect("a dihedral");
    assert_eq!(right.cosine_squared, Rat::zero());
    assert_eq!(right.cosine_sign, 0);

    // A planar trans dihedral: cos θ = −1 exactly, so cos²θ = 1 and sin θ = 0.
    let trans = exact_dihedral(
        &[rat(1), rat(1), rat(0)],
        &[rat(0), rat(1), rat(0)],
        &[rat(0), rat(0), rat(0)],
        &[rat(1), rat(0), rat(0)],
    )
    .expect("a dihedral");
    assert_eq!(trans.cosine_squared, Rat::one());
    assert_eq!(trans.sine_sign, 0);

    let chain = synthetic_backbone(3);
    for residue in 0..3 {
        if residue > 0 {
            let phi = chain.phi(residue).expect("phi");
            assert!(
                !phi.cosine_squared.is_negative() && phi.cosine_squared <= Rat::one(),
                "Lean: dihedralCosSq_nonneg and dihedralCosSq_le_one"
            );
        }
        if residue + 1 < 3 {
            let psi = chain.psi(residue).expect("psi");
            assert!(psi.cosine_squared <= Rat::one());
            let omega = chain.omega(residue).expect("omega");
            assert!(omega.cosine_squared <= Rat::one());
        }
    }
    assert_eq!(
        chain.phi(0).unwrap_err(),
        FoldRefusal::DihedralAbsentAtTheTerminus { residue: 0 }
    );
    assert_eq!(
        chain.psi(2).unwrap_err(),
        FoldRefusal::DihedralAbsentAtTheTerminus { residue: 2 }
    );
    assert_eq!(
        exact_dihedral(
            &[rat(0), rat(0), rat(0)],
            &[rat(1), rat(0), rat(0)],
            &[rat(2), rat(0), rat(0)],
            &[rat(3), rat(0), rat(0)],
        )
        .unwrap_err(),
        FoldRefusal::DegenerateDihedral
    );
}

fn declared_chart() -> RamachandranChart {
    RamachandranChart::declared(
        "a declared four-quadrant partition of the (sign cos, sign sin) chart; it is a declaration \
         of this test and not a measurement of any Ramachandran distribution",
        vec![
            RamachandranRegion {
                name: "right-handed-helix-quadrant".to_owned(),
                phi_cosine_sign: -1,
                phi_sine_sign: -1,
                psi_cosine_sign: -1,
                psi_sine_sign: -1,
            },
            RamachandranRegion {
                name: "sheet-quadrant".to_owned(),
                phi_cosine_sign: -1,
                phi_sine_sign: -1,
                psi_cosine_sign: -1,
                psi_sine_sign: 1,
            },
        ],
    )
    .expect("a declared chart")
}

/// The chart is a **declaration** with a ground, refuses an empty partition and a repeated
/// quadrant, and never imputes a residue it does not cover.
#[test]
fn the_ramachandran_chart_is_declared_and_never_imputes() {
    let chart = declared_chart();
    assert!(chart.ground().contains("declaration"));
    assert_eq!(chart.regions().len(), 2);

    let inside = ExactDihedral {
        cosine_squared: ratio(1, 2),
        cosine_sign: -1,
        sine_sign: -1,
    };
    assert_eq!(
        chart.read(&inside, &inside),
        RamachandranReading::InRegion {
            name: "right-handed-helix-quadrant".to_owned()
        }
    );

    let elsewhere = ExactDihedral {
        cosine_squared: ratio(1, 4),
        cosine_sign: 1,
        sine_sign: 1,
    };
    assert_eq!(
        chart.read(&elsewhere, &inside),
        RamachandranReading::OutsideTheChart {
            phi_cosine_sign: 1,
            phi_sine_sign: 1,
            psi_cosine_sign: -1,
            psi_sine_sign: -1,
        },
        "a residue the declared partition does not cover is not imputed to the nearest region"
    );

    assert_eq!(
        RamachandranChart::declared("ground", Vec::new()).unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a Ramachandran chart's declared regions"
        }
    );
    let repeated = RamachandranChart::declared(
        "ground",
        vec![
            RamachandranRegion {
                name: "one".to_owned(),
                phi_cosine_sign: 1,
                phi_sine_sign: 1,
                psi_cosine_sign: 1,
                psi_sine_sign: 1,
            },
            RamachandranRegion {
                name: "two".to_owned(),
                phi_cosine_sign: 1,
                phi_sine_sign: 1,
                psi_cosine_sign: 1,
                psi_sine_sign: 1,
            },
        ],
    );
    assert!(matches!(
        repeated.unwrap_err(),
        FoldRefusal::RamachandranRegionsOverlap { .. }
    ));
}

/// **A pivot move is two reflections about a chain axis, and every bond length survives exactly.**
#[test]
fn a_pivot_is_two_reflections_and_preserves_every_bond() {
    let chain = synthetic_backbone(4);
    let places = chain.places();
    let bars = chain.bars().expect("the bars");

    // The axis is the CA–C bond of residue 1. Both creases contain it, so both of its atoms are
    // fixed and every bond crossing the pivot keeps its length.
    let ca = chain
        .atom_index(1, BackboneAtom::AlphaCarbon)
        .expect("an index");
    let carbon = chain.atom_index(1, BackboneAtom::Carbon).expect("an index");
    let axis_point = FoldPoint::declared(places[ca].clone()).expect("a point");
    let axis_other = FoldPoint::declared(places[carbon].clone()).expect("a point");
    let direction: Vec<Rat> = axis_other
        .coordinates()
        .iter()
        .zip(axis_point.coordinates())
        .map(|(a, b)| a - b)
        .collect();

    // Two independent normals orthogonal to the axis direction, exactly over Q.
    let first_normal = cross_product(&direction, &[rat(1), rat(0), rat(0)]).expect("a normal");
    let second_normal = cross_product(&direction, &first_normal).expect("a normal");
    let first = Crease::through(first_normal.to_vec(), &axis_point).expect("a crease");
    let second = Crease::through(second_normal.to_vec(), &axis_point).expect("a crease");
    assert_eq!(
        first.side_value(&axis_other).expect("a side"),
        Rat::zero(),
        "the axis lies in the first crease"
    );
    assert_eq!(
        second.side_value(&axis_other).expect("a side"),
        Rat::zero(),
        "and in the second"
    );

    let tail: BTreeSet<usize> = (carbon + 1..places.len()).collect();
    let move_ = PivotMove {
        first,
        second,
        moved: tail.clone(),
    };
    let reading = chain.pivot(&move_).expect("a pivot reading");
    assert!(
        reading.bond_lengths_preserved,
        "Lean: pivot_preserves_squared_lengths; moved {:?}",
        reading.moved_bars
    );
    assert!(
        reading.fixed_atoms.contains(&ca) && reading.fixed_atoms.contains(&carbon),
        "Lean: pivot_fixes_the_axis"
    );
    assert_ne!(
        reading.places, places,
        "the pivot actually moved the tail"
    );
    // Whether the tail is separated from the head by the first crease is a fact about the
    // configuration, not an assumption: the reading says which atoms disagree.
    assert_eq!(
        reading.is_a_half_space_fold,
        reading.half_space_disagreements.is_empty()
    );

    assert_eq!(
        PivotMove {
            first: crease(&[1, 0, 0], 0),
            second: crease(&[0, 1, 0], 0),
            moved: BTreeSet::new(),
        }
        .apply(&places, &bars)
        .unwrap_err(),
        FoldRefusal::EmptyProbe {
            what: "a pivot move's moved set"
        }
    );
}

// ---------------------------------------------------------------------------------------------
// the measured M5 return
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the backbone framework is measured on, declared here rather than inferred.
const WINDOW: usize = 12;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;

fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

/// The backbone `N`, `CA`, `C` of the RBX1 chain's first `WINDOW` residues, as exact rationals.
fn read_backbone(path: &Path, lineage: &'static str) -> Result<BackboneChain, String> {
    use crate::physical_intake::mmcif::StructurePresentation;
    let presentation = StructurePresentation::read(path).map_err(|error| error.to_string())?;
    let chain = presentation
        .chain_with_residue_count(RBX1_RESIDUES)
        .map_err(|error| error.to_string())?;
    let mut residues = Vec::with_capacity(WINDOW);
    for residue in chain.residues.iter().take(WINDOW) {
        let mut places = Vec::with_capacity(3);
        for label in ["N", "CA", "C"] {
            let at = residue
                .labelled_atom(label)
                .map_err(|error| error.to_string())?
                .ok_or_else(|| {
                    format!(
                        "residue {} of {lineage} carries no {label} atom",
                        residue.source_ordinal
                    )
                })?;
            let atom = &residue.atoms[at];
            places.push(vec![
                atom.x.exact_centre().map_err(|error| error.to_string())?,
                atom.y.exact_centre().map_err(|error| error.to_string())?,
                atom.z.exact_centre().map_err(|error| error.to_string())?,
            ]);
        }
        let carbon = places.pop().expect("three places");
        let alpha_carbon = places.pop().expect("three places");
        let nitrogen = places.pop().expect("three places");
        residues.push(BackboneResidue {
            source_ordinal: residue.source_ordinal,
            monomer: residue.monomer.clone(),
            nitrogen,
            alpha_carbon,
            carbon,
        });
    }
    BackboneChain::declared(lineage, residues).map_err(|error| error.to_string())
}

/// **The measured return on the authenticated M5 release.**
///
/// CPU only, `#[ignore]`d because the exact rational elimination over the deposited coordinates is
/// the expensive part of this module: the designed release carries three decimal places and the
/// two Protenix releases carry seven, so their Jacobians' entries are four decimal digits wider and
/// the unoptimized debug build's `BigInt` arithmetic is what the minutes go into. Every law it
/// exercises is checked without any fixture by the synthetic tests above, so nothing here is the
/// only check of anything.
#[test]
#[ignore = "reads the authenticated M5 release and runs an exact elimination over it"]
fn the_backbone_framework_measures_the_m5_structures() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured backbone reading \
         cannot be taken, and this test refuses to report success without taking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif.",
        root.display()
    );

    let chart = declared_chart();
    let structures = [
        ("designed-free", "designed-free-rbx1.cif"),
        ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
        ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
    ];
    for (lineage, file) in structures {
        let chain = read_backbone(&root.join(file), lineage)
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        assert_eq!(chain.residue_count(), WINDOW);
        assert_eq!(chain.atom_count(), 3 * WINDOW);

        // Pinned: the free backbone of a twelve-residue window has 7·12 − 4 = 80 bars, 108
        // coordinates and exactly 2·11 = 22 internal freedoms.
        let free = chain.framework(&BTreeMap::new()).expect("a free framing");
        assert_eq!(free.backbone_bars, 80);
        assert_eq!(free.reading.occurrences, 36);
        assert_eq!(free.reading.maxwell.coordinate_freedoms, 108);
        assert_eq!(free.predicted_internal, 22);
        assert_eq!(
            free.measured_internal, 22,
            "{lineage}: the deposited configuration realizes the predicted freedom"
        );
        assert!(free.prediction_holds);
        assert!(!free.locked);

        // Adding the within-window contacts at eight angstroms removes dihedral motions: that is
        // what holds the fold.
        let contacts = chain
            .contact_bars(3, &rat(CONTACT_SQUARED))
            .expect("the contact bars");
        let held = chain.framework(&contacts).expect("a held framing");
        assert!(held.contact_bars > 0, "{lineage}: the window carries contacts");
        assert!(
            held.measured_internal <= free.measured_internal,
            "{lineage}: contacts can only remove motions"
        );

        // Every dihedral is exact: a rational cos² in [0, 1] with two signs, and no float.
        let mut readings = Vec::new();
        for residue in 1..WINDOW - 1 {
            let phi = chain.phi(residue).expect("phi");
            let psi = chain.psi(residue).expect("psi");
            let omega = chain.omega(residue).expect("omega");
            assert!(!phi.cosine_squared.is_negative() && phi.cosine_squared <= Rat::one());
            assert!(!psi.cosine_squared.is_negative() && psi.cosine_squared <= Rat::one());
            assert!(
                omega.cosine_squared > ratio(9, 10),
                "{lineage}: residue {residue}'s omega is near planar, cos^2 = {}",
                omega.cosine_squared
            );
            readings.push((residue, chart.read(&phi, &psi)));
        }
        let covered = readings
            .iter()
            .filter(|(_, reading)| matches!(reading, RamachandranReading::InRegion { .. }))
            .count();
        let outside = readings.len() - covered;
        assert_eq!(
            covered + outside,
            readings.len(),
            "every residue is either in a declared region or explicitly outside the chart"
        );

        println!(
            "fold M5 | {lineage} | residues {} | backbone bars {} | free internal {} | \
             contact bars {} | held internal {} | held self-stress {} | \
             residues inside the declared chart {covered} | outside it {outside}",
            chain.residue_count(),
            free.backbone_bars,
            free.measured_internal,
            held.contact_bars,
            held.measured_internal,
            held.reading.self_stress_dimension,
        );
    }
}

/// **A pivot on the real backbone**, as a composition of two reflections about a chain axis, with
/// every bond length preserved exactly.
#[test]
#[ignore = "reads the authenticated M5 release"]
fn a_pivot_on_the_real_backbone_preserves_every_bond() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent; this test refuses to report success \
         without it. The same pivot law is checked without any fixture by \
         a_pivot_is_two_reflections_and_preserves_every_bond.",
        root.display()
    );
    let chain = read_backbone(&root.join("designed-free-rbx1.cif"), "designed-free")
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let places = chain.places();
    let ca = chain
        .atom_index(4, BackboneAtom::AlphaCarbon)
        .expect("an index");
    let carbon = chain.atom_index(4, BackboneAtom::Carbon).expect("an index");
    let axis_point = FoldPoint::declared(places[ca].clone()).expect("a point");
    let axis_other = FoldPoint::declared(places[carbon].clone()).expect("a point");
    let direction: Vec<Rat> = axis_other
        .coordinates()
        .iter()
        .zip(axis_point.coordinates())
        .map(|(a, b)| a - b)
        .collect();
    let first_normal = cross_product(&direction, &[rat(1), rat(0), rat(0)]).expect("a normal");
    let second_normal = cross_product(&direction, &first_normal).expect("a normal");
    let move_ = PivotMove {
        first: Crease::through(first_normal.to_vec(), &axis_point).expect("a crease"),
        second: Crease::through(second_normal.to_vec(), &axis_point).expect("a crease"),
        moved: (carbon + 1..places.len()).collect(),
    };
    let reading = chain.pivot(&move_).expect("a pivot reading");
    assert!(
        reading.bond_lengths_preserved,
        "the pivot moved {:?}",
        reading.moved_bars
    );
    assert!(reading.fixed_atoms.contains(&ca));
    assert!(reading.fixed_atoms.contains(&carbon));
    println!(
        "fold M5 pivot | designed-free | fixed atoms {} | the tail is a half-space fold: {} | \
         atoms where the pivot and the half-space fold disagree {}",
        reading.fixed_atoms.len(),
        reading.is_a_half_space_fold,
        reading.half_space_disagreements.len(),
    );
}

/// **No float carries or decides anything in this owner.** A real scan of the sources: comment
/// lines are excluded because the header names the forbidden words in the sentence forbidding
/// them, the tokens are assembled at run time so this test does not contain them, and the scanned
/// line count is asserted so the scan cannot pass by covering nothing.
#[test]
fn no_float_token_occurs_in_this_owners_sources() {
    let banned: Vec<String> = [32u8, 64u8]
        .iter()
        .map(|width| format!("{}{width}", 'f'))
        .collect();
    for (name, source) in [
        ("fold.rs", include_str!("../fold.rs")),
        ("fold/tests.rs", include_str!("tests.rs")),
    ] {
        let mut scanned = 0usize;
        for line in source.lines() {
            if line.trim_start().starts_with("//") {
                continue;
            }
            scanned += 1;
            for forbidden in &banned {
                assert!(
                    !line.contains(forbidden.as_str()),
                    "{name} line `{line}` names `{forbidden}`"
                );
            }
        }
        assert!(scanned > 200, "{name}: the scan covered only {scanned} lines");
    }
}
