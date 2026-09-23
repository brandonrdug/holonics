//! Tests for **R6 — receiver width and release**.
//!
//! Every theorem of `Foundation/ReceiverRelease.lean` appears here as a test under the name the
//! module's correspondence table gives it, and every declared-size entry point has a hostile-input
//! test beside it. Nothing here needs a fixture.

use super::*;

use num_traits::One;

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(integer).collect())
            .collect(),
    )
    .expect("a rectangular matrix")
}

// ---------------------------------------------------------------------------------------------
// the readings used throughout
// ---------------------------------------------------------------------------------------------

/// One coordinate of the state, as a one-entry vector face.
#[derive(Clone, Debug)]
struct Coordinate {
    receiver: String,
    at: usize,
}

impl Reading for Coordinate {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        state
            .get(self.at)
            .map(|value| ExactFace::Vector(vec![value.clone()]))
            .ok_or(WidthRefusal::DimensionMismatch {
                declared: self.at,
                found: state.len(),
            })
    }
}

/// `min(value, cap)`: a declared non-expansive factor map.
#[derive(Clone, Debug)]
struct Clamp {
    cap: Rat,
}

impl FactorMap for Clamp {
    fn name(&self) -> &str {
        "clamp"
    }

    fn apply(&self, value: &Rat) -> Rat {
        if value > &self.cap {
            self.cap.clone()
        } else {
            value.clone()
        }
    }
}

/// An **owned** coarser reading: one coordinate clamped at a declared cap. `FactoredReading`
/// borrows its finer reading, which a `CoarseningStep`'s `Box<dyn Reading>` cannot hold, so the
/// tower tests use this owned equivalent. It is `Clamp ∘ Coordinate` by construction, so it
/// factors through `Coordinate` exactly as `coarser_receiver_factors` requires.
#[derive(Clone, Debug)]
struct OwnedClamped {
    receiver: String,
    at: usize,
    cap: Rat,
}

impl Reading for OwnedClamped {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let value = state
            .get(self.at)
            .ok_or(WidthRefusal::DimensionMismatch {
                declared: self.at,
                found: state.len(),
            })?;
        let clamped = if value > &self.cap {
            self.cap.clone()
        } else {
            value.clone()
        };
        Ok(ExactFace::Vector(vec![clamped]))
    }
}

/// `2 · value`: a declared **expansive** factor map. It is still a lawful coarsening — the
/// composite reading is a function of the finer face and of nothing else — and it still widens.
#[derive(Clone, Debug)]
struct Scale {
    by: Rat,
}

impl FactorMap for Scale {
    fn name(&self) -> &str {
        "scale"
    }

    fn apply(&self, value: &Rat) -> Rat {
        &self.by * value
    }
}

/// **The exact system whose event is future-stable while its timing is not.**
///
/// `x_{t+1} = 2 x_t` over `Q` — `Linearization` with `state = [[2]]` and a zero admitted input —
/// with the event "the trajectory reaches `1`". Both receivers below read the same fibre of
/// initial states through the same exact `h`-step map; they are `R ∘ Φ_h`, exactly as the Lean
/// owner says.
fn doubling() -> Linearization {
    Linearization::declared(
        "doubling",
        matrix(&[&[2]]),
        matrix(&[&[0]]),
        matrix(&[&[1]]),
        vec!["none".to_owned()],
        vec!["x".to_owned()],
    )
    .expect("a one-dimensional linearization")
}

/// The first step at or before the horizon at which the trajectory reaches the threshold, or
/// `horizon + 1` when it does not. The crossing is computed, not declared.
fn crossing_time(system: &Linearization, state: &[Rat], threshold: &Rat, horizon: usize) -> usize {
    let mut current = state.to_vec();
    for step in 0..=horizon {
        if &current[0] >= threshold {
            return step;
        }
        current = advance(system, &current, &[vec![Rat::zero()]]).expect("the step advances");
    }
    horizon + 1
}

/// The receiver **"the event occurs by the declared horizon"**.
#[derive(Clone, Debug)]
struct EventByHorizon {
    receiver: String,
    horizon: usize,
    threshold: Rat,
}

impl Reading for EventByHorizon {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let at = crossing_time(&doubling(), state, &self.threshold, self.horizon);
        Ok(ExactFace::Flag(at <= self.horizon))
    }
}

/// The receiver **"the time of the event"**.
#[derive(Clone, Debug)]
struct TimeOfEvent {
    receiver: String,
    horizon: usize,
    threshold: Rat,
}

impl Reading for TimeOfEvent {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let at = crossing_time(&doubling(), state, &self.threshold, self.horizon);
        Ok(ExactFace::Count(BigInt::from(at)))
    }
}

// ---------------------------------------------------------------------------------------------
// the three laws of the width
// ---------------------------------------------------------------------------------------------

/// Lean: `width_mono`. **A narrower fibre has no larger width.**
#[test]
fn the_width_is_monotone_under_fibre_inclusion() {
    let wide = CompatibleFamily::enumerated(
        "wide",
        vec![vec![integer(0)], vec![integer(3)], vec![integer(7)]],
    )
    .expect("a family");
    let narrow =
        CompatibleFamily::enumerated("narrow", vec![vec![integer(0)], vec![integer(3)]])
            .expect("a family");
    assert_eq!(narrow.is_subfamily_of(&wide), Some(true));
    let reading = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let wide_width = width_enumerated(&reading, &wide, DiameterNorm::Supremum).expect("a width");
    let narrow_width =
        width_enumerated(&reading, &narrow, DiameterNorm::Supremum).expect("a width");
    assert_eq!(wide_width.diameter(), &integer(7));
    assert_eq!(narrow_width.diameter(), &integer(3));
    assert!(narrow_width.diameter() <= wide_width.diameter());
    assert_eq!(
        wide_width.attaining(),
        &WidthWitness::Pair { left: 0, right: 2 }
    );
}

/// Lean: `width_eq_zero_iff`. **Width zero is exactly constancy on the fibre.**
#[test]
fn width_zero_is_constancy_on_the_fibre() {
    let reading = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let constant = CompatibleFamily::enumerated(
        "constant",
        vec![vec![integer(5)], vec![integer(5)], vec![integer(5)]],
    )
    .expect("a family");
    let plural =
        CompatibleFamily::enumerated("plural", vec![vec![integer(5)], vec![integer(6)]])
            .expect("a family");
    let flat = width_enumerated(&reading, &constant, DiameterNorm::Supremum).expect("a width");
    let spread = width_enumerated(&reading, &plural, DiameterNorm::Supremum).expect("a width");
    assert!(flat.is_zero());
    assert_eq!(flat.attaining(), &WidthWitness::Point);
    assert!(!spread.is_zero());
}

/// Lean: `releasable_at_every_tolerance_iff_width_zero`.
#[test]
fn width_zero_releases_at_every_tolerance() {
    let reading = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let constant =
        CompatibleFamily::enumerated("constant", vec![vec![integer(5)], vec![integer(5)]])
            .expect("a family");
    let flat = width_enumerated(&reading, &constant, DiameterNorm::Supremum).expect("a width");
    for tolerance in [Rat::zero(), ratio(1, 1000), integer(1), integer(1000)] {
        assert!(flat.releasable_at(&tolerance));
    }
    let plural =
        CompatibleFamily::enumerated("plural", vec![vec![integer(0)], vec![integer(4)]])
            .expect("a family");
    let spread = width_enumerated(&reading, &plural, DiameterNorm::Supremum).expect("a width");
    assert!(!spread.releasable_at(&integer(3)));
    assert!(spread.releasable_at(&integer(4)));
}

/// Lean: `width_nonExpansive_factor`. **A coarser receiver with a non-expansive factor map has no
/// larger width**, and the non-expansiveness is *checked* on the fibre actually read.
#[test]
fn a_non_expansive_coarser_receiver_has_no_larger_width() {
    let family = CompatibleFamily::enumerated(
        "fibre",
        vec![vec![integer(0)], vec![integer(3)], vec![integer(9)]],
    )
    .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let clamp = Clamp { cap: integer(4) };
    let coarse = FactoredReading {
        receiver: "clamped-x".to_owned(),
        fine: &fine,
        factor: &clamp,
    };
    coarse
        .verify_non_expansive(&family)
        .expect("clamping never increases a separation");
    let fine_width = width_enumerated(&fine, &family, DiameterNorm::Supremum).expect("a width");
    let coarse_width =
        width_enumerated(&coarse, &family, DiameterNorm::Supremum).expect("a width");
    assert_eq!(fine_width.diameter(), &integer(9));
    assert_eq!(coarse_width.diameter(), &integer(4));
    assert!(coarse_width.diameter() <= fine_width.diameter());
}

/// Lean: `expansive_factor_increases_width` and `doubling_factor_not_nonExpansive`. **The
/// hypothesis is needed**: `q ↦ 2q` is a lawful coarsening that strictly widens, and the library
/// says so by name rather than accepting it.
#[test]
fn an_expansive_factor_map_widens_the_reading() {
    let family = CompatibleFamily::enumerated("fibre", vec![vec![integer(0)], vec![integer(3)]])
        .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let scale = Scale { by: integer(2) };
    let coarse = FactoredReading {
        receiver: "doubled-x".to_owned(),
        fine: &fine,
        factor: &scale,
    };
    let fine_width = width_enumerated(&fine, &family, DiameterNorm::Supremum).expect("a width");
    let coarse_width =
        width_enumerated(&coarse, &family, DiameterNorm::Supremum).expect("a width");
    assert_eq!(fine_width.diameter(), &integer(3));
    assert_eq!(coarse_width.diameter(), &integer(6));
    assert!(coarse_width.diameter() > fine_width.diameter());
    let refusal = coarse
        .verify_non_expansive(&family)
        .expect_err("an expansive factor map is refused by name");
    assert!(matches!(
        refusal,
        WidthRefusal::FactorIsExpansive { ref factor, .. } if factor == "scale"
    ));
}

// ---------------------------------------------------------------------------------------------
// the event is future-stable while its timing is not
// ---------------------------------------------------------------------------------------------

/// Lean: `future_stable_event_with_unstable_timing`.
///
/// **One fibre, two receivers, two opposite verdicts.** On the exact doubling system with the
/// compatible fibre `{1/8, 1/4}` and horizon `3`, the receiver "the event occurs by horizon 3" has
/// width exactly `0` and is released at every tolerance; the receiver "the time of the event" has
/// width exactly `1` and is released at no tolerance below `1`. There is no scalar attached to the
/// fibre that could have produced both answers.
#[test]
fn an_event_is_future_stable_while_its_timing_is_not() {
    let fibre =
        CompatibleFamily::enumerated("doubling|fibre", vec![vec![ratio(1, 8)], vec![ratio(1, 4)]])
            .expect("a family");
    let event = EventByHorizon {
        receiver: "event-by-3".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };

    // The crossings are computed from the exact trajectory, so the receivers earn their names.
    let system = doubling();
    assert_eq!(
        crossing_time(&system, &[ratio(1, 8)], &Rat::one(), 3),
        3,
        "1/8 doubles to 1 in exactly three steps"
    );
    assert_eq!(crossing_time(&system, &[ratio(1, 4)], &Rat::one(), 3), 2);

    let event_width = width_enumerated(&event, &fibre, DiameterNorm::Supremum).expect("a width");
    let timing_width = width_enumerated(&timing, &fibre, DiameterNorm::Supremum).expect("a width");
    assert!(event_width.is_zero(), "the event is future-stable");
    assert_eq!(timing_width.diameter(), &integer(1), "the timing is not");
    for tolerance in [Rat::zero(), ratio(1, 2), integer(1)] {
        assert!(event_width.releasable_at(&tolerance));
    }
    assert!(!timing_width.releasable_at(&ratio(1, 2)));
    assert!(timing_width.releasable_at(&integer(1)));
}

/// Lean: `timingInsufficiency` and `no_transformer_from_the_released_coarse_face`. The released
/// coarse face does **not** determine the unreleased fine one: the two members of the fibre carry
/// the same event reading and different timings.
#[test]
fn the_coarse_event_reading_does_not_determine_the_timing() {
    let event = EventByHorizon {
        receiver: "event-by-3".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let eighth = vec![ratio(1, 8)];
    let quarter = vec![ratio(1, 4)];
    assert_eq!(
        event.read(&eighth).expect("a face"),
        event.read(&quarter).expect("a face"),
        "the coarse reading identifies them"
    );
    assert_ne!(
        timing.read(&eighth).expect("a face"),
        timing.read(&quarter).expect("a face"),
        "the fine reading separates them: an exact insufficiency witness"
    );
}

/// `ReleaseCoarser` finds the coarser invariant through the declared refinement order, and the
/// factoring is checked at every step rather than assumed.
#[test]
fn release_coarser_walks_the_declared_refinement_order() {
    let fibre =
        CompatibleFamily::enumerated("doubling|fibre", vec![vec![ratio(1, 8)], vec![ratio(1, 4)]])
            .expect("a family");
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let tower = CoarseningTower {
        lineage: "doubling|timing-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(EventByHorizon {
                receiver: "event-by-3".to_owned(),
                horizon: 3,
                threshold: Rat::one(),
            }),
        }],
    };
    let found = release_coarser(
        &timing,
        &tower,
        &fibre,
        &ratio(1, 2),
        DiameterNorm::Supremum,
    )
    .expect("the search returns")
    .expect("the event reading is inside tolerance");
    assert_eq!(found.receiver, "event-by-3");
    assert!(found.width.is_zero());
    assert_eq!(found.step, 0);
}

/// And a declared tower whose step does **not** factor through the finer reading is refused by
/// name, with the two members that refute it. A tower that is not a coarsening is not a tower.
#[test]
fn release_coarser_refuses_a_tower_that_does_not_factor() {
    // The finer reading is the event flag — constant on this fibre — and the declared "coarser"
    // step is the timing, which separates what the finer reading identified.
    let fibre =
        CompatibleFamily::enumerated("doubling|fibre", vec![vec![ratio(1, 8)], vec![ratio(1, 4)]])
            .expect("a family");
    let event = EventByHorizon {
        receiver: "event-by-3".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let tower = CoarseningTower {
        lineage: "doubling|not-a-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(TimeOfEvent {
                receiver: "time-of-event".to_owned(),
                horizon: 3,
                threshold: Rat::one(),
            }),
        }],
    };
    let refusal = release_coarser(&event, &tower, &fibre, &integer(10), DiameterNorm::Supremum)
        .expect_err("a step that separates what the finer reading identified is refused");
    assert!(matches!(
        refusal,
        WidthRefusal::CoarserDoesNotFactor { ref coarse, ref fine, left: 0, right: 1 }
            if coarse == "time-of-event" && fine == "event-by-3"
    ));
}

/// Phase 6: a coarsening tower is the core restriction's factor descent. The step that refuses in
/// `release_coarser` is the first descent that breaks, at the same two members; a step that
/// factors is a witness.
#[test]
fn the_coarsening_tower_is_the_core_factor_descent() {
    let fibre =
        CompatibleFamily::enumerated("doubling|fibre", vec![vec![ratio(1, 8)], vec![ratio(1, 4)]])
            .expect("a family");
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let event = EventByHorizon {
        receiver: "event-by-3".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let lawful = CoarseningTower {
        lineage: "doubling|timing-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(EventByHorizon {
                receiver: "event-by-3".to_owned(),
                horizon: 3,
                threshold: Rat::one(),
            }),
        }],
    };
    let descents = lawful
        .descent(&timing, &fibre)
        .expect("the descent is taken");
    assert_eq!(descents.len(), 1);
    assert!(descents[0].descends());
    assert!(
        release_coarser(
            &timing,
            &lawful,
            &fibre,
            &ratio(1, 2),
            DiameterNorm::Supremum
        )
        .expect("the search returns")
        .is_some()
    );

    let not_a_tower = CoarseningTower {
        lineage: "doubling|not-a-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(TimeOfEvent {
                receiver: "time-of-event".to_owned(),
                horizon: 3,
                threshold: Rat::one(),
            }),
        }],
    };
    let descents = not_a_tower
        .descent(&event, &fibre)
        .expect("the descent is taken");
    let breaks = descents
        .last()
        .and_then(|descent| descent.defect())
        .expect("the timing step does not factor through the event flag");
    let refusal = release_coarser(
        &event,
        &not_a_tower,
        &fibre,
        &integer(10),
        DiameterNorm::Supremum,
    )
    .expect_err("the same step is refused");
    let WidthRefusal::CoarserDoesNotFactor { left, right, .. } = refusal else {
        panic!("the refusal is the factoring refusal");
    };
    assert_eq!(breaks.first().pair(), (left, right));
    assert_eq!(descents.len(), 1);
}

/// Phase 6: a factor map is the induced coarse reading of a descent. A `FactoredReading` descends
/// through its finer reading (`Foundation/ReceiverRelease.lean::coarser_receiver_factors`), and the
/// witness's induced map `ρ̄` on the finer faces is the declared `FactorMap` applied entrywise.
#[test]
fn a_factor_map_is_the_induced_reading_of_a_descent() {
    let family = CompatibleFamily::enumerated(
        "fibre",
        vec![
            vec![integer(0)],
            vec![integer(3)],
            vec![integer(9)],
            vec![integer(3)],
        ],
    )
    .expect("a family");
    let members = family.members().expect("enumerated");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let clamp = Clamp { cap: integer(4) };
    let coarse = FactoredReading {
        receiver: "clamped-x".to_owned(),
        fine: &fine,
        factor: &clamp,
    };
    let quotient = super::FaceQuotient {
        faces: members
            .iter()
            .map(|m| fine.read(m).expect("a face"))
            .collect(),
    };
    let indices: Vec<usize> = (0..members.len()).collect();
    let descent = holonic_core::restriction::factor_descent(
        &quotient,
        |k: &usize| coarse.read(&members[*k]).expect("a face"),
        &indices,
    )
    .expect("a small family");
    let witness = descent
        .witness()
        .expect("a factored reading descends by construction");
    assert_eq!(witness.merged_pairs(), 1);
    assert_eq!(witness.factored().len(), 3);
    for (face, induced) in witness.factored() {
        let Some(ExactFace::Vector(values)) = face else {
            panic!("the coordinate reading is a vector face");
        };
        let mapped: Vec<Rat> = values.iter().map(|v| clamp.apply(v)).collect();
        assert_eq!(induced, &ExactFace::Vector(mapped));
    }
}

// ---------------------------------------------------------------------------------------------
// the exact enclosure and the exact h-step map
// ---------------------------------------------------------------------------------------------

/// The image of a box under an exact linear map is an exact zonotope, and its sup-norm diameter is
/// `2·max_i Σ_j |G_ij|`. Checked against the enumerated corner images.
#[test]
fn the_image_of_a_box_under_an_exact_linear_map_is_an_exact_zonotope() {
    let hull = ExactZonotope::box_hull(
        vec![integer(0), integer(0)],
        &[integer(1), integer(2)],
    )
    .expect("a box");
    let map = matrix(&[&[1, 1], &[1, -1]]);
    let image = hull.mapped(&map).expect("the image");
    assert_eq!(image.generators().len(), 2);
    // Row 0 of the image: |1| + |2| = 3, so the extent is 6. Row 1: |1| + |−2| = 3, also 6.
    let (diameter, coordinate) = image.supremum_diameter().expect("a diameter");
    assert_eq!(diameter, integer(6));
    assert_eq!(coordinate, 0);
    // The same number, read off the four corners of the box.
    let corners = [
        vec![integer(1), integer(2)],
        vec![integer(1), integer(-2)],
        vec![integer(-1), integer(2)],
        vec![integer(-1), integer(-2)],
    ];
    let images = corners
        .iter()
        .map(|corner| map.apply(corner).expect("the corner image"))
        .collect::<Vec<_>>();
    let mut widest = Rat::zero();
    for left in 0..images.len() {
        for right in (left + 1)..images.len() {
            let separation = ExactFace::Vector(images[left].clone())
                .separation(
                    &ExactFace::Vector(images[right].clone()),
                    DiameterNorm::Supremum,
                )
                .expect("a separation");
            if separation > widest {
                widest = separation;
            }
        }
    }
    assert_eq!(widest, diameter, "the enclosure is tight on this box");
}

/// The `h`-step image of a compatible box and an admitted-input box is exact, and it agrees with
/// the enumerated trajectories of the corners.
#[test]
fn the_horizon_image_is_exact() {
    // x' = 2x + u, compatible states in [−1, 1], admitted inputs in [−1, 1], horizon 2.
    // Φ₂(x, u₀, u₁) = 4x + 2u₀ + u₁, so the exact extent is 4 + 2 + 1 = 7 either side.
    let system = Linearization::declared(
        "doubling-with-input",
        matrix(&[&[2]]),
        matrix(&[&[1]]),
        matrix(&[&[1]]),
        vec!["u".to_owned()],
        vec!["x".to_owned()],
    )
    .expect("declared");
    let states = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    let inputs = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    let image = horizon_image(&system, &states, &inputs, 2).expect("the image");
    assert_eq!(image.generators().len(), 3);
    let (diameter, _) = image.supremum_diameter().expect("a diameter");
    assert_eq!(diameter, integer(14));

    // The extremal trajectory, advanced exactly.
    let top = advance(
        &system,
        &[integer(1)],
        &[vec![integer(1)], vec![integer(1)]],
    )
    .expect("the trajectory");
    assert_eq!(top, vec![integer(7)]);
    let bottom = advance(
        &system,
        &[integer(-1)],
        &[vec![integer(-1)], vec![integer(-1)]],
    )
    .expect("the trajectory");
    assert_eq!(bottom, vec![integer(-7)]);

    // Every generator names the source it came from: one compatible state coordinate and one
    // admitted input per step of the horizon.
    let sources = image
        .generators()
        .iter()
        .map(|generator| generator.source)
        .collect::<Vec<_>>();
    assert!(sources.contains(&GeneratorSource::CompatibleState { coordinate: 0 }));
    assert!(sources.contains(&GeneratorSource::AdmittedInput { step: 0, port: 0 }));
    assert!(sources.contains(&GeneratorSource::AdmittedInput { step: 1, port: 0 }));
}

/// The width of an exact linear reading over an enclosure, and the release verdict it supports.
#[test]
fn the_width_over_an_enclosure_is_exact() {
    let hull =
        ExactZonotope::box_hull(vec![integer(0), integer(0)], &[integer(1), ratio(1, 10)])
            .expect("a box");
    let family = CompatibleFamily::enclosed("hull", hull);
    // Read only the second coordinate: the width is 1/5, inside a tolerance of 1/4.
    let reading = LinearReading {
        receiver: "second-coordinate".to_owned(),
        matrix: matrix(&[&[0, 1]]),
    };
    let reading_width =
        width_enclosed(&reading, &family, DiameterNorm::Supremum).expect("a width");
    assert_eq!(reading_width.diameter(), &ratio(1, 5));
    assert!(reading_width.releasable_at(&ratio(1, 4)));
    // Read the first: the width is 2, outside it.
    let wide = LinearReading {
        receiver: "first-coordinate".to_owned(),
        matrix: matrix(&[&[1, 0]]),
    };
    let wide_width = width_enclosed(&wide, &family, DiameterNorm::Supremum).expect("a width");
    assert_eq!(wide_width.diameter(), &integer(2));
    assert!(!wide_width.releasable_at(&ratio(1, 4)));
}

// ---------------------------------------------------------------------------------------------
// `Ask`: the probe is computed
// ---------------------------------------------------------------------------------------------

/// **The probe direction maximally reducing the width, computed.** The reading sees the first
/// coordinate three times as strongly as the second, so the generator to ask for is the first
/// state coordinate — and the answer is returned with the exact width observing it would leave.
#[test]
fn the_narrowing_probe_names_the_generator_that_reduces_the_width_most() {
    let hull = ExactZonotope::box_hull(vec![integer(0), integer(0)], &[integer(3), integer(1)])
        .expect("a box");
    let reading = LinearReading {
        receiver: "sum".to_owned(),
        matrix: matrix(&[&[1, 1]]),
    };
    let probe = narrowing_probe(&reading, &hull)
        .expect("the search returns")
        .expect("there is something to ask for");
    assert_eq!(
        probe.source,
        GeneratorSource::CompatibleState { coordinate: 0 }
    );
    // Before: 2·(3 + 1) = 8. After observing the first coordinate exactly: 2·1 = 2.
    assert_eq!(probe.width_after, integer(2));
    assert_eq!(probe.reduction, integer(6));
    // And an enclosure with nothing unresolved has nothing to ask for.
    let point = ExactZonotope::box_hull(vec![integer(0), integer(0)], &[Rat::zero(), Rat::zero()])
        .expect("a point");
    assert_eq!(
        narrowing_probe(&reading, &point).expect("the search returns"),
        None
    );
}

/// **The declared observation maximally reducing the width, computed.** Over the enumerated fibre
/// the candidate whose level sets leave the smallest surviving width is returned by name.
#[test]
fn the_narrowing_observation_is_computed_over_the_declared_candidates() {
    // Four compatible states in the plane. The target reading is the first coordinate; observing
    // the first coordinate collapses it to zero, observing the second leaves it whole.
    let family = CompatibleFamily::enumerated(
        "plane",
        vec![
            vec![integer(0), integer(0)],
            vec![integer(0), integer(1)],
            vec![integer(5), integer(0)],
            vec![integer(5), integer(1)],
        ],
    )
    .expect("a family");
    let target = Coordinate {
        receiver: "first".to_owned(),
        at: 0,
    };
    let first = Coordinate {
        receiver: "observe-first".to_owned(),
        at: 0,
    };
    let second = Coordinate {
        receiver: "observe-second".to_owned(),
        at: 1,
    };
    let candidates: Vec<&dyn Reading> = vec![&second, &first];
    let probe = narrowing_observation(&target, &family, &candidates, DiameterNorm::Supremum)
        .expect("the search returns")
        .expect("a candidate narrows it");
    assert_eq!(probe.observation, "observe-first");
    assert!(probe.width_after.is_zero());
    assert_eq!(probe.reduction, integer(5));
}

// ---------------------------------------------------------------------------------------------
// the release law is the caller's
// ---------------------------------------------------------------------------------------------

struct HoldingLaw;

impl DecisionLaw for HoldingLaw {
    fn name(&self) -> &str {
        "holding"
    }

    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn {
        if options.inside_tolerance() {
            ReleaseReturn::Released {
                width: options.width().clone(),
                tolerance: options.tolerance().clone(),
            }
        } else {
            ReleaseReturn::Hold
        }
    }
}

struct AskingLaw;

impl DecisionLaw for AskingLaw {
    fn name(&self) -> &str {
        "asking"
    }

    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn {
        if options.inside_tolerance() {
            return ReleaseReturn::Released {
                width: options.width().clone(),
                tolerance: options.tolerance().clone(),
            };
        }
        match (options.ask(), options.coarser(), options.bridges()) {
            (Some(probe), _, _) => ReleaseReturn::Ask {
                probe: probe.clone(),
            },
            (None, Some(coarser), _) => ReleaseReturn::ReleaseCoarser {
                receiver: coarser.receiver().to_owned(),
                width: coarser.width().clone(),
            },
            (None, None, false) => ReleaseReturn::NoContinuationBridges {
                reason: "no admitted continuation reaches this receiver".to_owned(),
            },
            (None, None, true) => ReleaseReturn::Widen {
                tolerance: options.width().clone(),
            },
        }
    }
}

struct LyingLaw;

impl DecisionLaw for LyingLaw {
    fn name(&self) -> &str {
        "lying"
    }

    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn {
        ReleaseReturn::Released {
            width: options.width().clone(),
            tolerance: options.tolerance().clone(),
        }
    }
}

fn plural_options() -> LawfulOptions {
    let family = CompatibleFamily::enumerated("fibre", vec![vec![integer(0)], vec![integer(4)]])
        .expect("a family");
    let reading = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let measured = width_enumerated(&reading, &family, DiameterNorm::Supremum).expect("a width");
    LawfulOptions::assemble(&measured, integer(1), None, None, true).expect("coherent options")
}

/// Lean: `no_default_among_the_lawful_returns`. **Two lawful laws, one width, different arms.**
/// The library supplies no default; the decision is declared by the caller.
#[test]
fn two_lawful_laws_return_different_arms() {
    let options = plural_options();
    assert!(!options.inside_tolerance());
    let held = release(&HoldingLaw, &options).expect("a lawful return");
    let asked = release(&AskingLaw, &options).expect("a lawful return");
    assert_eq!(held, ReleaseReturn::Hold);
    assert_eq!(
        asked,
        ReleaseReturn::Widen {
            tolerance: integer(4)
        }
    );
    assert_ne!(held, asked);
}

/// Lean: `ReleaseLaw.sound`. **The one thing the library owns.** A law claiming release outside its
/// own declared tolerance is refused by name.
#[test]
fn a_law_releasing_outside_its_declared_tolerance_is_refused() {
    let options = plural_options();
    let refusal = release(&LyingLaw, &options).expect_err("the claim is refused");
    assert!(matches!(
        refusal,
        WidthRefusal::ReleasedOutsideTolerance(ref claim) if claim.law == "lying"
    ));
}

/// And a law naming a probe or a coarser receiver the library did not compute is refused: `Ask`
/// asks for something that exists.
#[test]
fn a_law_naming_an_uncomputed_probe_or_coarser_receiver_is_refused() {
    struct Inventing;
    impl DecisionLaw for Inventing {
        fn name(&self) -> &str {
            "inventing"
        }
        fn decide(&self, _options: &LawfulOptions) -> ReleaseReturn {
            ReleaseReturn::Ask {
                probe: AskProbe::Observation(ObservationProbe {
                    observation: "an-observation-nobody-computed".to_owned(),
                    width_after: Rat::zero(),
                    reduction: Rat::zero(),
                }),
            }
        }
    }
    struct Inventing2;
    impl DecisionLaw for Inventing2 {
        fn name(&self) -> &str {
            "inventing-coarser"
        }
        fn decide(&self, _options: &LawfulOptions) -> ReleaseReturn {
            ReleaseReturn::ReleaseCoarser {
                receiver: "a-receiver-nobody-declared".to_owned(),
                width: Rat::zero(),
            }
        }
    }
    let options = plural_options();
    assert!(matches!(
        release(&Inventing, &options).expect_err("refused"),
        WidthRefusal::ProbeNotOffered { .. }
    ));
    assert!(matches!(
        release(&Inventing2, &options).expect_err("refused"),
        WidthRefusal::CoarserNotOffered { .. }
    ));
}

/// The whole mechanism end to end: an unreleased fine receiver, a computed probe, a coarser
/// receiver inside tolerance, and a caller's law picking among them — with no default anywhere.
#[test]
fn the_release_mechanism_runs_end_to_end_on_the_doubling_system() {
    let fibre =
        CompatibleFamily::enumerated("doubling|fibre", vec![vec![ratio(1, 8)], vec![ratio(1, 4)]])
            .expect("a family");
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    let measured = width_enumerated(&timing, &fibre, DiameterNorm::Supremum).expect("a width");
    let tower = CoarseningTower {
        lineage: "doubling|timing-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(EventByHorizon {
                receiver: "event-by-3".to_owned(),
                horizon: 3,
                threshold: Rat::one(),
            }),
        }],
    };
    let coarser = release_coarser(
        &timing,
        &tower,
        &fibre,
        &ratio(1, 2),
        DiameterNorm::Supremum,
    )
    .expect("the search returns");
    let options = LawfulOptions::assemble(&measured, ratio(1, 2), None, coarser, true)
        .expect("the coarser release was searched at this very tolerance");
    assert!(!options.inside_tolerance());
    assert_eq!(
        release(&AskingLaw, &options).expect("a lawful return"),
        ReleaseReturn::ReleaseCoarser {
            receiver: "event-by-3".to_owned(),
            width: Rat::zero(),
        }
    );
    // The same options under a different declared law return a different arm. Release is
    // receiver-relative and caller-declared; there is no global gate.
    assert_eq!(
        release(&HoldingLaw, &options).expect("a lawful return"),
        ReleaseReturn::Hold
    );
}

// ---------------------------------------------------------------------------------------------
// hostile input
// ---------------------------------------------------------------------------------------------

/// A declared horizon cannot size an allocation: the generator count is formed with checked
/// arithmetic and compared with the ceiling before the first `Vec` is built.
#[test]
fn a_hostile_horizon_declaration_is_refused_before_allocation() {
    let system = Linearization::declared(
        "hostile",
        matrix(&[&[2]]),
        matrix(&[&[1]]),
        matrix(&[&[1]]),
        vec!["u".to_owned()],
        vec!["x".to_owned()],
    )
    .expect("declared");
    let states = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    let inputs = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    // One state generator plus one input generator per step: at `GENERATOR_CEILING` steps the
    // product is one past the generator ceiling while the horizon itself is still inside its own.
    let refusal = horizon_image(&system, &states, &inputs, GENERATOR_CEILING)
        .expect_err("a generator population past the ceiling is refused");
    assert!(matches!(
        refusal,
        WidthRefusal::GeneratorCeiling { ceiling, .. } if ceiling == GENERATOR_CEILING
    ));
    let overflow = horizon_image(&system, &states, &inputs, usize::MAX)
        .expect_err("a horizon that overflows the count is refused");
    assert!(matches!(
        overflow,
        WidthRefusal::GeneratorCountOverflows { .. }
            | WidthRefusal::GeneratorCeiling { .. }
            | WidthRefusal::HorizonCeiling { .. }
    ));

    // **The generator ceiling alone is not enough.** An admitted-input box with no width
    // contributes no generator at all, so the generator product stays at zero and a hostile
    // horizon would otherwise run one exact matrix multiplication per step. The horizon ceiling is
    // checked first, and this is the test that would catch its removal.
    let pointlike = ExactZonotope::box_hull(vec![Rat::zero()], &[Rat::zero()]).expect("a point");
    assert!(pointlike.generators().is_empty());
    let refusal = horizon_image(&system, &states, &pointlike, HORIZON_CEILING + 1)
        .expect_err("a horizon past the ceiling is refused even with a width-free input box");
    assert!(matches!(
        refusal,
        WidthRefusal::HorizonCeiling { ceiling, .. } if ceiling == HORIZON_CEILING
    ));
}

/// A law cannot buy a release with a forged `inside_tolerance` flag: `release` recomputes the
/// comparison from the options' own exact width and tolerance. Outside this module the flag is
/// no longer reachable at all — [`LawfulOptions`]'s fields are private and
/// [`LawfulOptions::assemble`] is the only constructor — so the forgery is written here, inside
/// the defining module, where it is still expressible.
#[test]
fn a_forged_inside_tolerance_flag_does_not_buy_a_release() {
    let mut options = plural_options();
    options.inside_tolerance = true;
    let refusal = release(&HoldingLaw, &options).expect_err("the recomputed comparison refuses");
    assert!(matches!(
        refusal,
        WidthRefusal::ReleasedOutsideTolerance(ref claim) if claim.law == "holding"
    ));
}

/// A declared family wider than the ceiling is refused, and an empty one has no diameter.
#[test]
fn a_hostile_family_declaration_is_refused() {
    assert!(matches!(
        CompatibleFamily::enumerated("empty", Vec::new()).expect_err("refused"),
        WidthRefusal::EmptyFamily
    ));
    let too_wide = vec![vec![Rat::zero()]; FAMILY_CEILING + 1];
    assert!(matches!(
        CompatibleFamily::enumerated("wide", too_wide).expect_err("refused"),
        WidthRefusal::FamilyCeiling { ceiling, .. } if ceiling == FAMILY_CEILING
    ));
    let ragged = vec![vec![Rat::zero()], vec![Rat::zero(), Rat::zero()]];
    assert!(matches!(
        CompatibleFamily::enumerated("ragged", ragged).expect_err("refused"),
        WidthRefusal::DimensionMismatch { .. }
    ));
}

/// A negative half-width is not an extent, and a zero-dimensional carrier carries no reading.
#[test]
fn a_hostile_enclosure_declaration_is_refused() {
    assert!(matches!(
        ExactZonotope::box_hull(vec![Rat::zero()], &[integer(-1)]).expect_err("refused"),
        WidthRefusal::NegativeHalfWidth { coordinate: 0 }
    ));
    assert!(matches!(
        ExactZonotope::box_hull(Vec::new(), &[]).expect_err("refused"),
        WidthRefusal::EmptyDimension
    ));
    assert!(matches!(
        ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1), integer(1)])
            .expect_err("refused"),
        WidthRefusal::DimensionMismatch { .. }
    ));
}

/// Two faces of different arms are incomparable and no separation is invented.
#[test]
fn faces_of_different_arms_are_incomparable() {
    let flag = ExactFace::Flag(true);
    let count = ExactFace::Count(BigInt::from(3));
    assert!(matches!(
        flag.separation(&count, DiameterNorm::Supremum)
            .expect_err("refused"),
        WidthRefusal::FacesIncomparable { .. }
    ));
    let short = ExactFace::Vector(vec![Rat::zero()]);
    let long = ExactFace::Vector(vec![Rat::zero(), Rat::zero()]);
    assert!(matches!(
        short
            .separation(&long, DiameterNorm::Supremum)
            .expect_err("refused"),
        WidthRefusal::VectorFacesDiffer { left: 1, right: 2 }
    ));
}

/// The squared-Euclidean diameter of a zonotope is not computed by enumerating `2^k` vertices: the
/// norm is refused on an enclosure by name, and it is exact on an enumerated family.
#[test]
fn the_squared_euclidean_norm_is_refused_on_an_enclosure_and_exact_on_a_family() {
    let hull = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    let family = CompatibleFamily::enclosed("hull", hull);
    let reading = LinearReading {
        receiver: "x".to_owned(),
        matrix: matrix(&[&[1]]),
    };
    assert!(matches!(
        width_enclosed(&reading, &family, DiameterNorm::SquaredEuclidean).expect_err("refused"),
        WidthRefusal::NormNotExactOnEnclosure {
            norm: "squared-euclidean"
        }
    ));
    let enumerated =
        CompatibleFamily::enumerated("pair", vec![vec![integer(0)], vec![integer(3)]])
            .expect("a family");
    let squared = width_enumerated(&reading, &enumerated, DiameterNorm::SquaredEuclidean)
        .expect("exact on an enumerated family");
    assert_eq!(squared.diameter(), &integer(9));
}

/// A declared non-linear reading over an enclosure is refused rather than sampled.
#[test]
fn a_declared_reading_over_an_enclosure_is_refused_rather_than_sampled() {
    let hull = ExactZonotope::box_hull(vec![Rat::zero()], &[integer(1)]).expect("a box");
    let family = CompatibleFamily::enclosed("hull", hull);
    let timing = TimeOfEvent {
        receiver: "time-of-event".to_owned(),
        horizon: 3,
        threshold: Rat::one(),
    };
    assert!(matches!(
        width(&timing, &family, DiameterNorm::Supremum).expect_err("refused"),
        WidthRefusal::DeclaredReadingNeedsEnumeratedFamily { .. }
    ));
}

/// `advance` is total off its image: a state or an input word of the wrong extent is a typed
/// refusal, never a panic and never a silent truncation.
#[test]
fn advance_refuses_a_mismatched_state_or_input() {
    let system = doubling();
    assert!(matches!(
        advance(&system, &[integer(1), integer(2)], &[]).expect_err("refused"),
        WidthRefusal::DimensionMismatch { .. }
    ));
    assert!(matches!(
        advance(&system, &[integer(1)], &[vec![integer(0), integer(0)]]).expect_err("refused"),
        WidthRefusal::DimensionMismatch { .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// R6 (e/f) — a coarser release cannot leave the tolerance it was searched under
// ---------------------------------------------------------------------------------------------

/// **The two-call escape, refused.** A coarser release searched under a wide tolerance cannot be
/// assembled against a narrow one. Before the fix both calls were ordinary public calls and the
/// resulting `ReleaseCoarser` was released, because `release` compared only `(receiver, width)`
/// against the offer and never compared the width to the tolerance.
///
/// Here the coarser reading is a *width-5* reading searched inside tolerance `10`, re-presented
/// against tolerance `1/2`.
#[test]
fn a_coarser_release_searched_under_a_wider_tolerance_is_refused() {
    let family = CompatibleFamily::enumerated(
        "fibre",
        vec![vec![integer(0)], vec![integer(5)], vec![integer(20)]],
    )
    .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let clamp = Clamp { cap: integer(5) };
    let tower = CoarseningTower {
        lineage: "clamping-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(OwnedClamped {
                receiver: "clamped-x".to_owned(),
                at: 0,
                cap: clamp.cap.clone(),
            }),
        }],
    };
    // Searched under tolerance 10: the clamped reading has width exactly 5 and is admitted.
    let coarser = release_coarser(&fine, &tower, &family, &integer(10), DiameterNorm::Supremum)
        .expect("the search returns")
        .expect("the clamped reading is inside tolerance 10");
    assert_eq!(coarser.width(), &integer(5));
    assert_eq!(coarser.searched_tolerance(), &integer(10));

    let measured = width_enumerated(&fine, &family, DiameterNorm::Supremum).expect("a width");
    // Assembling that answer against tolerance 1/2 is refused at the assembly.
    let refusal = LawfulOptions::assemble(
        &measured,
        ratio(1, 2),
        None,
        Some(coarser.clone()),
        true,
    )
    .expect_err("a release searched at 10 is not an answer about 1/2");
    assert!(matches!(
        refusal,
        WidthRefusal::CoarserSearchedAtAnotherTolerance(ref claim)
            if claim.receiver == "clamped-x" && claim.searched == integer(10)
                && claim.declared == ratio(1, 2)
    ));

    // Assembled against the tolerance it really was searched under, it is admitted and released.
    let options =
        LawfulOptions::assemble(&measured, integer(10), None, Some(coarser), true)
            .expect("the tolerances agree");
    assert_eq!(
        release(&AskingLaw, &options).expect("a lawful return"),
        ReleaseReturn::ReleaseCoarser {
            receiver: "clamped-x".to_owned(),
            width: integer(5),
        }
    );
}

/// **The `ReleaseCoarser` arm recomputes the inequality.** `assemble` already refuses a tolerance
/// mismatch, so outside this module the inconsistent options below are unconstructible; the
/// forgery is written inside the defining module, where the private fields are still reachable,
/// to exercise the arm's own guard. Before the fix the arm checked only `(receiver, width)`
/// against the offer and returned this release.
#[test]
fn the_coarser_arm_refuses_a_width_outside_the_options_tolerance() {
    let family = CompatibleFamily::enumerated(
        "fibre",
        vec![vec![integer(0)], vec![integer(5)], vec![integer(20)]],
    )
    .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let tower = CoarseningTower {
        lineage: "clamping-tower".to_owned(),
        steps: vec![CoarseningStep {
            reading: Box::new(OwnedClamped {
                receiver: "clamped-x".to_owned(),
                at: 0,
                cap: integer(5),
            }),
        }],
    };
    let coarser = release_coarser(&fine, &tower, &family, &integer(10), DiameterNorm::Supremum)
        .expect("the search returns")
        .expect("inside tolerance 10");
    let measured = width_enumerated(&fine, &family, DiameterNorm::Supremum).expect("a width");
    let mut options =
        LawfulOptions::assemble(&measured, integer(10), None, Some(coarser), true)
            .expect("the tolerances agree");
    // The forgery a private field still permits inside this module: narrow the tolerance after
    // the assembly checked it.
    options.tolerance = ratio(1, 2);
    let refusal = release(&AskingLaw, &options).expect_err("the arm recomputes the inequality");
    assert!(matches!(
        refusal,
        WidthRefusal::CoarserReleasedOutsideTolerance(ref claim)
            if claim.receiver == "clamped-x" && claim.width == integer(5)
    ));
}

/// `release_coarser` walks **past the first step**: the first coarsening is still outside
/// tolerance and the second one is inside it, and the returned step index says which. Every step
/// is checked to factor through the step before it, not merely through the finest reading.
#[test]
fn the_coarser_search_walks_past_the_first_tower_step() {
    let family = CompatibleFamily::enumerated(
        "fibre",
        vec![vec![integer(0)], vec![integer(4)], vec![integer(9)]],
    )
    .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let tower = CoarseningTower {
        lineage: "two-step-tower".to_owned(),
        steps: vec![
            CoarseningStep {
                reading: Box::new(OwnedClamped {
                    receiver: "clamped-at-6".to_owned(),
                    at: 0,
                    cap: integer(6),
                }),
            },
            CoarseningStep {
                reading: Box::new(OwnedClamped {
                    receiver: "clamped-at-2".to_owned(),
                    at: 0,
                    cap: integer(2),
                }),
            },
        ],
    };
    let coarser = release_coarser(&fine, &tower, &family, &integer(3), DiameterNorm::Supremum)
        .expect("the search returns")
        .expect("the second step is inside tolerance 3");
    assert_eq!(coarser.receiver(), "clamped-at-2");
    assert_eq!(coarser.step(), 1, "the first step, width 6, was outside 3");
    assert_eq!(coarser.width(), &integer(2));
    assert_eq!(coarser.searched_tolerance(), &integer(3));
    // No step of the tower is inside a tolerance below the coarsest width.
    assert!(
        release_coarser(&fine, &tower, &family, &integer(1), DiameterNorm::Supremum)
            .expect("the search returns")
            .is_none()
    );
}

// ---------------------------------------------------------------------------------------------
// declared-size ceilings
// ---------------------------------------------------------------------------------------------

/// A declared carrier extent, and the exact multiplications a horizon asks for at that extent, are
/// both bounded before the first matrix is formed.
#[test]
fn a_hostile_extent_or_multiplication_count_is_refused_before_any_product() {
    let wide = Linearization::declared(
        "wide",
        ExactRatMatrix::identity(EXTENT_CEILING + 1).expect("an identity"),
        ExactRatMatrix::identity(EXTENT_CEILING + 1).expect("an identity"),
        ExactRatMatrix::identity(EXTENT_CEILING + 1).expect("an identity"),
        (0..EXTENT_CEILING + 1).map(|i| format!("u{i}")).collect(),
        (0..EXTENT_CEILING + 1).map(|i| format!("x{i}")).collect(),
    )
    .expect("declared");
    let states = ExactZonotope::box_hull(
        vec![Rat::zero(); EXTENT_CEILING + 1],
        &vec![integer(1); EXTENT_CEILING + 1],
    )
    .expect("a box");
    let inputs = states.clone();
    assert!(matches!(
        horizon_image(&wide, &states, &inputs, 1).expect_err("refused"),
        WidthRefusal::ExtentCeiling { ceiling, .. } if ceiling == EXTENT_CEILING
    ));

    // Inside the extent ceiling, the *work* is still bounded: 128³ per step times 64 steps is
    // past the multiplication ceiling even though both axis ceilings are satisfied.
    let extent = 128usize;
    let system = Linearization::declared(
        "square",
        ExactRatMatrix::identity(extent).expect("an identity"),
        ExactRatMatrix::identity(extent).expect("an identity"),
        ExactRatMatrix::identity(extent).expect("an identity"),
        (0..extent).map(|i| format!("u{i}")).collect(),
        (0..extent).map(|i| format!("x{i}")).collect(),
    )
    .expect("declared");
    let box_hull =
        ExactZonotope::box_hull(vec![Rat::zero(); extent], &vec![Rat::zero(); extent])
            .expect("a box with no generator");
    assert!(matches!(
        horizon_image(&system, &box_hull, &box_hull, 64).expect_err("refused"),
        WidthRefusal::MultiplyWorkCeiling { ceiling, .. } if ceiling == MULTIPLY_WORK_CEILING
    ));
}

/// A declared coarsening tower and a declared candidate list are both bounded before the first
/// step or candidate is read.
#[test]
fn a_hostile_tower_or_candidate_declaration_is_refused_before_the_first_read() {
    let family = CompatibleFamily::enumerated("fibre", vec![vec![integer(0)], vec![integer(4)]])
        .expect("a family");
    let fine = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let tower = CoarseningTower {
        lineage: "tall".to_owned(),
        steps: (0..=TOWER_STEP_CEILING)
            .map(|step| CoarseningStep {
                reading: Box::new(OwnedClamped {
                    receiver: format!("clamped-{step}"),
                    at: 0,
                    cap: integer(1),
                }),
            })
            .collect(),
    };
    assert!(matches!(
        release_coarser(&fine, &tower, &family, &integer(1), DiameterNorm::Supremum)
            .expect_err("refused"),
        WidthRefusal::TowerStepCeiling { ceiling, .. } if ceiling == TOWER_STEP_CEILING
    ));

    let candidates: Vec<Coordinate> = (0..=CANDIDATE_CEILING)
        .map(|index| Coordinate {
            receiver: format!("candidate-{index}"),
            at: 0,
        })
        .collect();
    let borrowed: Vec<&dyn Reading> = candidates
        .iter()
        .map(|candidate| candidate as &dyn Reading)
        .collect();
    assert!(matches!(
        narrowing_observation(&fine, &family, &borrowed, DiameterNorm::Supremum)
            .expect_err("refused"),
        WidthRefusal::CandidateCeiling { ceiling, .. } if ceiling == CANDIDATE_CEILING
    ));
}

/// A remounted [`ReceiverWidth`] is re-checked structurally: the `Deserialize` route goes through
/// `TryFrom`, so a forged schema, a negative diameter or an attaining witness that does not index
/// the reading is refused rather than carried into [`LawfulOptions::assemble`].
#[test]
fn a_remounted_receiver_width_is_rechecked() {
    let family = CompatibleFamily::enumerated("fibre", vec![vec![integer(0)], vec![integer(4)]])
        .expect("a family");
    let reading = Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    };
    let honest = width_enumerated(&reading, &family, DiameterNorm::Supremum).expect("a width");
    let wire = serde_json::to_string(&honest).expect("serializes");
    let remounted: ReceiverWidth = serde_json::from_str(&wire).expect("a coherent width remounts");
    assert_eq!(remounted, honest);

    let mut forged: serde_json::Value = serde_json::from_str(&wire).expect("a json object");
    forged["schema"] = serde_json::Value::String("holonics.not-a-width.v1".to_owned());
    assert!(
        serde_json::from_value::<ReceiverWidth>(forged).is_err(),
        "a foreign schema is refused"
    );

    let mut forged: serde_json::Value = serde_json::from_str(&wire).expect("a json object");
    forged["attaining"]["right"] = serde_json::Value::from(99u64);
    assert!(
        serde_json::from_value::<ReceiverWidth>(forged).is_err(),
        "a witness that does not index the reading is refused"
    );

    let mut forged: serde_json::Value = serde_json::from_str(&wire).expect("a json object");
    forged["attaining"] = serde_json::json!({ "witness": "point" });
    assert!(
        serde_json::from_value::<ReceiverWidth>(forged).is_err(),
        "a point witness with a nonzero diameter is refused"
    );
}

// ---------------------------------------------------------------------------------------------
// T5 (a) — the horizon has two coordinates, and the width over already-read faces
// ---------------------------------------------------------------------------------------------

fn declared_horizon(longitudinal: usize, index: usize) -> Horizon {
    Horizon::declare(longitudinal, index).expect("a horizon inside both ceilings")
}

/// `Foundation/ReceiverRelease.lean::horizonWithin_is_not_total`: the two coordinates are a product
/// order and not one scale, so "how far into the horizon" is a pair and never a number.
#[test]
fn the_horizon_has_two_coordinates_that_are_not_one_scale() {
    let along = declared_horizon(2, 0);
    let across = declared_horizon(0, 2);
    assert!(!along.contains(&across));
    assert!(!across.contains(&along));
    assert!(!along.comparable(&across));
    assert!(declared_horizon(2, 2).contains(&along));
    assert!(declared_horizon(2, 2).contains(&across));
    assert!(along.is_longitudinal_only());
    assert!(!across.is_longitudinal_only());
    assert_eq!(
        Horizon::longitudinal_only(3).expect("inside the ceiling"),
        declared_horizon(3, 0)
    );
}

/// A declared horizon above either ceiling is a typed refusal, and the `Deserialize` route runs the
/// same checks: a forged horizon cannot be remounted.
#[test]
fn a_horizon_above_either_ceiling_is_refused_and_no_wire_bypasses_it() {
    assert!(matches!(
        Horizon::declare(usize::MAX, 0),
        Err(WidthRefusal::HorizonCeiling { .. })
    ));
    assert!(matches!(
        Horizon::declare(0, INDEX_HORIZON_CEILING + 1),
        Err(WidthRefusal::IndexHorizonCeiling { .. })
    ));
    let forged = format!(
        "{{\"longitudinal\":0,\"index\":{}}}",
        INDEX_HORIZON_CEILING + 1
    );
    let refused: Result<Horizon, _> = serde_json::from_str(&forged);
    assert!(
        refused.is_err(),
        "a wire horizon above the ceiling is refused by the validating TryFrom"
    );
    let admitted: Horizon =
        serde_json::from_str("{\"longitudinal\":2,\"index\":1}").expect("an admissible horizon");
    assert_eq!(admitted, declared_horizon(2, 1));
}

/// `width_over_readings` is `width_enumerated`'s diameter on faces that were read elsewhere — the
/// two-axis horizon of a tube is the first consumer — and the two agree exactly, witness included.
#[test]
fn the_width_over_readings_is_the_enumerated_width() {
    let family = CompatibleFamily::enumerated(
        "three compatible states",
        vec![
            vec![integer(1), integer(0)],
            vec![integer(4), integer(0)],
            vec![integer(2), integer(0)],
        ],
    )
    .expect("a family inside the ceiling");
    let reading = LinearReading {
        receiver: "the first coordinate".to_owned(),
        matrix: matrix(&[&[1, 0]]),
    };
    let enumerated =
        width_enumerated(&reading, &family, DiameterNorm::Supremum).expect("an exact width");
    let faces = vec![
        ExactFace::Vector(vec![integer(1)]),
        ExactFace::Vector(vec![integer(4)]),
        ExactFace::Vector(vec![integer(2)]),
    ];
    let over_readings = width_over_readings(
        "the first coordinate",
        "three compatible states",
        &faces,
        DiameterNorm::Supremum,
    )
    .expect("an exact width");
    assert_eq!(enumerated.diameter(), over_readings.diameter());
    assert_eq!(enumerated.diameter(), &integer(3));
    assert_eq!(enumerated.attaining(), over_readings.attaining());
    assert_eq!(enumerated.read(), over_readings.read());
    assert!(matches!(
        width_over_readings("r", "l", &[], DiameterNorm::Supremum),
        Err(WidthRefusal::EmptyFamily)
    ));
    let too_many: Vec<ExactFace> = (0..=(FAMILY_CEILING + 1))
        .map(|value| ExactFace::Count(BigInt::from(value as i64)))
        .collect();
    assert!(matches!(
        width_over_readings("r", "l", &too_many, DiameterNorm::Supremum),
        Err(WidthRefusal::FamilyCeiling { .. })
    ));
}
