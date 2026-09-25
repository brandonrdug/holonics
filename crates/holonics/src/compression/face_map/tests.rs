//! One test per law of Lean `Compression/Core/FaceMap` that this owner realizes, one per
//! counterexample of its ramp, and the sharper horizon bound.

use super::*;

use crate::ratio::integer;
use crate::ratio::linear::vector::{integer_matrix, ints};
use crate::receiver::standing::{
    FutureObservation, SourcePopulation, SufficiencyVerdict, sufficiency,
};

fn family(maps: Vec<ExactRatMatrix>) -> NavigatorFamily {
    let names = (0..maps.len()).map(|index| format!("T{index}")).collect();
    NavigatorFamily::declared("terrain", names, maps).unwrap()
}

fn reading(name: &str, rows: &[&[i64]]) -> ReceiverReading {
    ReceiverReading::declared(name, integer_matrix(rows).unwrap()).unwrap()
}

/// Lean `Ramp`: terrain `(a, b, c)`, one navigator `(a, b, c) ↦ (a + b, b, c)`, one receiver
/// reading `a`.
fn ramp() -> FaceMap {
    FaceMap::new(
        family(vec![
            integer_matrix(&[&[1, 1, 0], &[0, 1, 0], &[0, 0, 1]]).unwrap(),
        ]),
        vec![reading("a", &[&[1, 0, 0]])],
    )
    .unwrap()
}

/// Two noncommuting navigators on `ℚ⁴` read at `x₀`: `T₀` shifts `x₁ → x₀`, `x₂ → x₁`, and `T₁`
/// feeds `x₁` into `x₂`. The relevance kernel is `x₃` alone, reached in two steps.
fn braid() -> FaceMap {
    let shift =
        integer_matrix(&[&[0, 1, 0, 0], &[0, 0, 1, 0], &[0, 0, 0, 0], &[0, 0, 0, 1]]).unwrap();
    let feed =
        integer_matrix(&[&[1, 0, 0, 0], &[0, 1, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 2]]).unwrap();
    assert_ne!(
        shift.multiply(&feed).unwrap(),
        feed.multiply(&shift).unwrap()
    );
    FaceMap::new(
        family(vec![shift, feed]),
        vec![reading("x0", &[&[1, 0, 0, 0]])],
    )
    .unwrap()
}

/// The nilpotent shift on `ℚ⁴` read at `x₀`: each step reveals one more coordinate, so the
/// recursion needs exactly `dim X − 1 = 3` steps.
fn shift_chain() -> FaceMap {
    FaceMap::new(
        family(vec![
            integer_matrix(&[&[0, 1, 0, 0], &[0, 0, 1, 0], &[0, 0, 0, 1], &[0, 0, 0, 0]]).unwrap(),
        ]),
        vec![reading("x0", &[&[1, 0, 0, 0]])],
    )
    .unwrap()
}

/// Whether two families of vectors span one subspace.
fn same_span(left: &[Vec<Rat>], right: &[Vec<Rat>], extent: usize) -> bool {
    let rank = |rows: Vec<Vec<Rat>>| {
        if rows.is_empty() {
            0
        } else {
            ExactRatMatrix::shaped(rows.len(), extent, rows)
                .unwrap()
                .rank()
                .unwrap()
        }
    };
    let joint: Vec<Vec<Rat>> = left.iter().chain(right).cloned().collect();
    let joint_rank = rank(joint);
    rank(left.to_vec()) == joint_rank && rank(right.to_vec()) == joint_rank
}

fn transported(navigators: &NavigatorFamily, word: &[usize], state: &[Rat]) -> Vec<Rat> {
    let mut current = state.to_vec();
    for letter in word.iter().rev() {
        current = navigators.step(*letter, &current).unwrap();
    }
    current
}

/// Lean `ker_faceMap_eq_relevanceKernel`, `Ramp.relevanceKernel_eq_span`: the ramp's kernel is
/// spanned by the silent coordinate `(0, 0, 1)`, and every kernel member is invisible to the
/// receiver after every word.
#[test]
fn the_kernel_is_what_no_future_receiver_distinguishes() {
    let face_map = ramp();
    let kernel = face_map.kernel().unwrap();
    assert!(same_span(&kernel, &[ints(&[0, 0, 1])], 3));
    for member in &kernel {
        for word in face_map.navigators().words_within(6).unwrap() {
            let state = transported(face_map.navigators(), &word, member);
            let face = face_map.receivers()[0].face(&state).unwrap();
            assert!(face.iter().all(Zero::is_zero));
        }
    }
}

/// Lean `mem_horizonBlind_iff`, `ker_horizonFaceMap`, `horizonBlind_stable_forever`: the recursion's
/// `B_N` is exactly the kernel of the face map on the declared request set of horizon `N`, at every
/// horizon; the observed ranks rise strictly and then stay; and the stable blind subspace is the
/// kernel forever after.
#[test]
fn the_recursion_is_the_kernel_of_every_declared_request_set() {
    for face_map in [ramp(), braid(), shift_chain()] {
        let extent = face_map.terrain_extent();
        let ranks = face_map.observed_ranks();
        assert!(ranks.windows(2).all(|pair| pair[0] < pair[1]));
        for horizon in 0..=extent + 2 {
            let finite = face_map.at_horizon(horizon).unwrap();
            let enumerated = finite.matrix().kernel_basis().unwrap();
            let blind = face_map.blind(horizon).unwrap();
            assert!(same_span(&enumerated, &blind, extent));
            let ledger = finite.ledger().unwrap();
            assert_eq!(ledger.rank, ranks[horizon.min(face_map.stable_at())]);
            if horizon >= face_map.stable_at() {
                assert!(same_span(&blind, &face_map.kernel().unwrap(), extent));
            }
        }
    }
    let braid = braid();
    assert_eq!(braid.observed_ranks(), vec![1, 2, 3]);
    assert!(same_span(
        &braid.kernel().unwrap(),
        &[ints(&[0, 0, 0, 1])],
        4
    ));
}

/// Lean `exists_stable_le_finrank_pred`, `horizonBlind_finrank_pred_eq_ker`, `Shift.horizon_sharp`:
/// the recursion is stable by horizon `dim X − 1` for every family here, and the shift chain
/// attains it, so no smaller horizon suffices in general.
#[test]
fn words_up_to_one_less_than_the_terrain_dimension_read_the_kernel() {
    for face_map in [ramp(), braid(), shift_chain()] {
        assert!(face_map.stable_at() < face_map.terrain_extent());
    }
    let chain = shift_chain();
    assert_eq!(chain.stable_at(), 3);
    assert_eq!(chain.kernel().unwrap().len(), 0);
    assert_eq!(chain.blind(2).unwrap().len(), 1);
    let silent = FaceMap::new(
        family(vec![ExactRatMatrix::identity(2).unwrap()]),
        vec![reading("nothing", &[&[0, 0]])],
    )
    .unwrap();
    assert_eq!(silent.stable_at(), 0);
    assert_eq!(silent.kernel().unwrap().len(), 2);
}

/// Lean `rank_nullity_ledger`, `finrank_faces`, `cokernel_ledger` and `Ramp.ledger`: at horizon
/// `3` the ramp reads kernel `1`, rank `2`, faces `4`, cokernel `2`. The cokernel is relative to
/// its horizon: on the ramp's `N + 1` requests it is `N − 1`. The ledger closes at every horizon.
#[test]
fn the_ledger_closes_and_the_cokernel_grows_with_the_horizon() {
    let ramp = ramp();
    assert_eq!(
        ramp.at_horizon(3).unwrap().ledger().unwrap(),
        FaceLedger {
            horizon: 3,
            terrain: 3,
            requests: 4,
            faces: 4,
            rank: 2,
            kernel: 1,
            cokernel: 2,
        }
    );
    for horizon in 1..=8 {
        let cokernel = ramp.at_horizon(horizon).unwrap().cokernel().unwrap();
        assert_eq!(cokernel.horizon(), horizon);
        assert_eq!(cokernel.requests(), horizon + 1);
        assert_eq!(cokernel.dimension(), horizon - 1);
    }
    for face_map in [ramp, braid(), shift_chain()] {
        for horizon in 0..=face_map.terrain_extent() {
            let ledger = face_map.at_horizon(horizon).unwrap().ledger().unwrap();
            let words = face_map.navigators().words_within(horizon).unwrap().len();
            assert_eq!(ledger.rank + ledger.kernel, ledger.terrain);
            assert_eq!(ledger.requests, face_map.receivers().len() * words);
            assert_eq!(ledger.faces, ledger.requests);
            assert_eq!(ledger.cokernel, ledger.faces - ledger.rank);
        }
    }
}

/// Lean `kernelQuotient_is_coarsest_retention`, `kernelQuotient_eq_iff_futureAgreement`: the
/// kernel quotient is a lawful retention for every declared observation, its classes are exactly
/// future agreement, and dropping one retained coordinate is no longer sufficient.
#[test]
fn the_kernel_quotient_is_the_coarsest_lawful_retention() {
    let face_map = braid();
    let retention = face_map.quotient().unwrap();
    assert_eq!(retention.extent(), 3);
    let finite = face_map.at_horizon(face_map.terrain_extent() - 1).unwrap();
    let members = vec![
        ints(&[0, 0, 0, 0]),
        ints(&[0, 0, 0, 5]),
        ints(&[1, 2, 3, 4]),
        ints(&[1, 2, 3, -7]),
        ints(&[1, 2, 4, 4]),
        ints(&[0, 1, 0, 0]),
    ];
    for left in &members {
        for right in &members {
            assert_eq!(
                retention.retained(left).unwrap() == retention.retained(right).unwrap(),
                finite.face(left).unwrap() == finite.face(right).unwrap()
            );
        }
    }
    let population = SourcePopulation::declared("braid", members).unwrap();
    let observations: Vec<FutureObservation> = finite
        .requests()
        .iter()
        .map(|request| {
            FutureObservation::declared(
                request.word.clone(),
                face_map.receivers()[request.receiver].clone(),
            )
            .unwrap()
        })
        .collect();
    let standing = retention.standing("kernel quotient").unwrap();
    assert!(matches!(
        sufficiency(&standing, &population, face_map.navigators(), &observations).unwrap(),
        SufficiencyVerdict::Sufficient { pairs: 2, .. }
    ));
    let coarser_rows: Vec<Vec<Rat>> = retention.retain().to_rows()[..2].to_vec();
    let coarser =
        StandingLaw::declared("coarser", ExactRatMatrix::new(coarser_rows).unwrap()).unwrap();
    assert!(matches!(
        sufficiency(&coarser, &population, face_map.navigators(), &observations).unwrap(),
        SufficiencyVerdict::NotSufficient { .. }
    ));
}

/// Lean `kernelReceiverQuotient`, `ker_faceMap_invariant`, `descendedNavigator`,
/// `kernelClass_after_word`: every future face is read from the retained class alone, and the
/// class after any word is the descended word applied to the class.
#[test]
fn the_navigators_run_on_retention() {
    let face_map = braid();
    let retention = face_map.quotient().unwrap();
    let terrain = ints(&[3, -1, 2, 9]);
    let class = retention.retained(&terrain).unwrap();
    for word in face_map.navigators().words_within(5).unwrap() {
        let state = transported(face_map.navigators(), &word, &terrain);
        assert_eq!(
            retention.retained(&state).unwrap(),
            retention.transport_word(&word, &class).unwrap()
        );
        assert_eq!(
            retention.face(0, &word, &class).unwrap(),
            face_map.receivers()[0].face(&state).unwrap()
        );
    }
}

/// Lean `exact_sequence`, `reachable_iff_cokernelClass_zero`, `reachable_iff_cocycles_vanish`: the
/// kernel maps to zero, every cocycle annihilates the image, and a face is reached exactly when
/// its class is zero, exactly when it has an exact preimage fibre.
#[test]
fn a_face_is_reached_exactly_when_its_cokernel_class_is_zero() {
    let face_map = braid();
    let finite = face_map.at_horizon(2).unwrap();
    for member in face_map.blind(2).unwrap() {
        assert!(finite.face(&member).unwrap().iter().all(Zero::is_zero));
    }
    let cokernel = finite.cokernel().unwrap();
    let transpose = finite.matrix().transpose().unwrap();
    for cocycle in cokernel.cocycles() {
        assert!(transpose.apply(cocycle).unwrap().iter().all(Zero::is_zero));
    }
    let reached = finite.face(&ints(&[2, -3, 5, 1])).unwrap();
    assert!(finite.reachable(&reached).unwrap());
    for coordinate in 0..reached.len() {
        let mut face = reached.clone();
        face[coordinate] += integer(1);
        let reachable = finite.reachable(&face).unwrap();
        assert_eq!(
            reachable,
            finite.matrix().preimage_fibre(&face).unwrap().is_some()
        );
        assert_eq!(reachable, cokernel.obstruction(&face).unwrap().is_none());
    }
}

/// Lean `Ramp.dormant_direction_not_released`: `(0, 1, 0)` is blind to the present receiver, yet
/// one step makes it visible, so it is not in the kernel: the present-blind subspace `B₀` is
/// strictly larger than the relevance kernel, and it is not carried by the navigator.
#[test]
fn the_dormant_direction_is_not_released() {
    let face_map = ramp();
    let dormant = ints(&[0, 1, 0]);
    assert!(same_span(
        &face_map.blind(0).unwrap(),
        &[dormant.clone(), ints(&[0, 0, 1])],
        3
    ));
    let stepped = face_map.navigators().step(0, &dormant).unwrap();
    assert!(!face_map.receivers()[0].face(&stepped).unwrap()[0].is_zero());
    assert_eq!(face_map.kernel().unwrap().len(), 1);
    assert!(!same_span(
        &face_map.kernel().unwrap(),
        &face_map.blind(0).unwrap(),
        3
    ));
}

/// Lean `Ramp.released_pair_one_class`: `(0, 0, 0)` and `(0, 0, 1)` differ and share one retained
/// class; retention is a quotient, not an injection.
#[test]
fn the_released_pair_shares_one_class() {
    let retention = ramp().quotient().unwrap();
    let (rest, released) = (ints(&[0, 0, 0]), ints(&[0, 0, 1]));
    assert_ne!(rest, released);
    assert_eq!(
        retention.retained(&rest).unwrap(),
        retention.retained(&released).unwrap()
    );
}

/// Lean `Ramp.unreachable_face`: on the declared request set of horizon `3`, the face reading `1`
/// after the three-step word and `0` elsewhere is not reached; one cocycle certifies it, and it has
/// no preimage.
#[test]
fn the_late_face_of_the_ramp_is_unreachable() {
    let finite = ramp().at_horizon(3).unwrap();
    let late: Vec<Rat> = finite
        .requests()
        .iter()
        .map(|request| integer(i64::from(request.word.len() == 3)))
        .collect();
    assert_eq!(late, ints(&[0, 0, 0, 1]));
    assert!(!finite.reachable(&late).unwrap());
    let cokernel = finite.cokernel().unwrap();
    let cocycle = cokernel.obstruction(&late).unwrap().unwrap();
    assert!(!dot(&cocycle, &late).is_zero());
    assert_eq!(finite.matrix().preimage_fibre(&late).unwrap(), None);
}

/// A receiver reading another terrain, and an empty receiver family, are refused by name.
#[test]
fn a_receiver_of_another_terrain_is_refused() {
    let navigators = ramp().navigators().clone();
    assert_eq!(
        FaceMap::new(navigators.clone(), vec![reading("wide", &[&[1, 0, 0, 0]])]),
        Err(CompressionError::Extent {
            what: "receiver source",
            expected: 3,
            found: 4
        })
    );
    assert_eq!(
        FaceMap::new(navigators, Vec::new()),
        Err(CompressionError::EmptyReceiverFamily)
    );
}
