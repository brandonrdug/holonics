//! Tests for **the one decision law**: the width laws it decides on, the threshold commit and its
//! refusals, the certified draw and its join to the law at tolerance zero.
//!
//! Every theorem of `Foundation/ReceiverRelease` the module's table names appears here under that
//! name, and the draw's receipts are the ones `population::sampling` carried before U3 moved the law
//! here (September 28), reproduced exactly.

use super::*;
use crate::receiver::face::{ExactFace, FAMILY_CEILING, Horizon, Reading, width_over_readings};
use num_bigint::BigInt;

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
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

fn x() -> Coordinate {
    Coordinate {
        receiver: "x".to_owned(),
        at: 0,
    }
}

/// The finite width of a reading over an enumerated compatible family: each member read, then the
/// diameter of the read faces (Lean `width`).
fn width_of(reading: &dyn Reading, members: &[Vec<Rat>], norm: DiameterNorm) -> ReceiverWidth {
    let faces = members
        .iter()
        .map(|member| reading.read(member).expect("a face"))
        .collect::<Vec<_>>();
    width_over_readings(reading.name(), "the enumerated fibre", &faces, norm).expect("a width")
}

fn states(values: &[Rat]) -> Vec<Vec<Rat>> {
    values.iter().map(|value| vec![value.clone()]).collect()
}

/// A factor map `g` composed with the coordinate reading: the coarser receiver `g ∘ R`.
fn factored(members: &[Vec<Rat>], g: impl Fn(&Rat) -> Rat) -> ReceiverWidth {
    let faces = members
        .iter()
        .map(|member| ExactFace::Vector(vec![g(&member[0])]))
        .collect::<Vec<_>>();
    width_over_readings("g ∘ x", "the enumerated fibre", &faces, DiameterNorm::Supremum)
        .expect("a width")
}

/// **The exact system whose event is future-stable while its timing is not**: the doubling
/// recurrence `x ↦ 2x` over `Q` (Lean `doubling`), with the event "the trajectory reaches `1`".
fn crossing_time(state: &Rat, threshold: &Rat, horizon: usize) -> usize {
    let mut current = state.clone();
    for step in 0..=horizon {
        if &current >= threshold {
            return step;
        }
        current = &current * integer(2);
    }
    horizon + 1
}

/// The receiver **"the event occurs by the declared horizon"**.
struct EventByHorizon {
    horizon: usize,
}

impl Reading for EventByHorizon {
    fn name(&self) -> &str {
        "event-by-horizon"
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let at = crossing_time(&state[0], &Rat::one(), self.horizon);
        Ok(ExactFace::Flag(at <= self.horizon))
    }
}

/// The receiver **"the time of the event"**.
struct TimeOfEvent {
    horizon: usize,
}

impl Reading for TimeOfEvent {
    fn name(&self) -> &str {
        "time-of-event"
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let at = crossing_time(&state[0], &Rat::one(), self.horizon);
        Ok(ExactFace::Count(BigInt::from(at)))
    }
}

// ---------------------------------------------------------------------------------------------
// the laws of the width
// ---------------------------------------------------------------------------------------------

/// Lean: `width_mono`. **A narrower fibre has no larger width.**
#[test]
fn the_width_is_monotone_under_fibre_inclusion() {
    let wide = width_of(
        &x(),
        &states(&[integer(0), integer(3), integer(7)]),
        DiameterNorm::Supremum,
    );
    let narrow = width_of(
        &x(),
        &states(&[integer(0), integer(3)]),
        DiameterNorm::Supremum,
    );
    assert_eq!(wide.diameter(), &integer(7));
    assert_eq!(narrow.diameter(), &integer(3));
    assert!(narrow.diameter() <= wide.diameter());
    assert_eq!(wide.attaining(), &WidthWitness::Pair { left: 0, right: 2 });
}

/// Lean: `width_eq_zero_iff`. **Width zero is exactly constancy on the fibre.**
#[test]
fn width_zero_is_constancy_on_the_fibre() {
    let flat = width_of(
        &x(),
        &states(&[integer(5), integer(5), integer(5)]),
        DiameterNorm::Supremum,
    );
    let spread = width_of(
        &x(),
        &states(&[integer(5), integer(6)]),
        DiameterNorm::Supremum,
    );
    assert!(flat.is_zero());
    assert_eq!(flat.attaining(), &WidthWitness::Point);
    assert!(!spread.is_zero());
}

/// Lean: `releasable_at_every_tolerance_iff_width_zero`.
#[test]
fn width_zero_releases_at_every_tolerance() {
    let flat = width_of(
        &x(),
        &states(&[integer(5), integer(5)]),
        DiameterNorm::Supremum,
    );
    for tolerance in [Rat::zero(), ratio(1, 1000), integer(1), integer(1000)] {
        assert!(flat.releasable_at(&tolerance));
    }
    let spread = width_of(
        &x(),
        &states(&[integer(0), integer(4)]),
        DiameterNorm::Supremum,
    );
    assert!(!spread.releasable_at(&integer(3)));
    assert!(spread.releasable_at(&integer(4)));
}

/// Lean: `width_nonExpansive_factor`. **A coarser receiver `g ∘ R` with `g` non-expansive has no
/// larger width**: clamping at `4` never increases a separation.
#[test]
fn a_non_expansive_coarser_reading_has_no_larger_width() {
    let members = states(&[integer(0), integer(3), integer(9)]);
    let fine = width_of(&x(), &members, DiameterNorm::Supremum);
    let cap = integer(4);
    let clamped = factored(&members, |value| value.min(&cap).clone());
    assert_eq!(fine.diameter(), &integer(9));
    assert_eq!(clamped.diameter(), &integer(4));
    assert!(clamped.diameter() <= fine.diameter());
}

/// Lean: `expansive_factor_increases_width` and `doubling_factor_not_nonExpansive`. **The
/// hypothesis is needed**: `q ↦ 2q` is a lawful coarsening (a function of the finer face) that
/// strictly widens.
#[test]
fn an_expansive_factor_widens_the_reading() {
    let members = states(&[integer(0), integer(3)]);
    let fine = width_of(&x(), &members, DiameterNorm::Supremum);
    let doubled = factored(&members, |value| value * integer(2));
    assert_eq!(fine.diameter(), &integer(3));
    assert_eq!(doubled.diameter(), &integer(6));
    assert!(doubled.diameter() > fine.diameter());
}

/// The squared-Euclidean norm is exact over read faces.
#[test]
fn the_squared_euclidean_norm_is_exact_over_read_faces() {
    let squared = width_of(
        &x(),
        &states(&[integer(0), integer(3)]),
        DiameterNorm::SquaredEuclidean,
    );
    assert_eq!(squared.diameter(), &integer(9));
}

// ---------------------------------------------------------------------------------------------
// the event is future-stable while its timing is not
// ---------------------------------------------------------------------------------------------

/// Lean: `future_stable_event_with_unstable_timing`. **One fibre, two receivers, two opposite
/// verdicts.** On the doubling system with the compatible fibre `{1/8, 1/4} = {2⁻³, 2⁻²}` and
/// horizon `3`, "the event occurs by horizon 3" has width `0` and releases at every tolerance;
/// "the time of the event" has width `1` and releases at no tolerance below `1`.
#[test]
fn an_event_is_future_stable_while_its_timing_is_not() {
    let fibre = states(&[ratio(1, 8), ratio(1, 4)]);
    assert_eq!(crossing_time(&ratio(1, 8), &Rat::one(), 3), 3);
    assert_eq!(crossing_time(&ratio(1, 4), &Rat::one(), 3), 2);
    let event = width_of(
        &EventByHorizon { horizon: 3 },
        &fibre,
        DiameterNorm::Supremum,
    );
    let timing = width_of(&TimeOfEvent { horizon: 3 }, &fibre, DiameterNorm::Supremum);
    assert!(event.is_zero(), "the event is future-stable");
    assert_eq!(timing.diameter(), &integer(1), "the timing is not");
    for tolerance in [Rat::zero(), ratio(1, 2), integer(1)] {
        assert!(event.releasable_at(&tolerance));
    }
    assert!(!timing.releasable_at(&ratio(1, 2)));
    assert!(timing.releasable_at(&integer(1)));
}

/// Lean: `timingInsufficiency` and `no_transformer_from_the_released_coarse_face`. The released
/// coarse face does **not** determine the fine one.
#[test]
fn the_coarse_event_reading_does_not_determine_the_timing() {
    let event = EventByHorizon { horizon: 3 };
    let timing = TimeOfEvent { horizon: 3 };
    let eighth = vec![ratio(1, 8)];
    let quarter = vec![ratio(1, 4)];
    assert_eq!(event.read(&eighth).unwrap(), event.read(&quarter).unwrap());
    assert_ne!(timing.read(&eighth).unwrap(), timing.read(&quarter).unwrap());
}

// ---------------------------------------------------------------------------------------------
// the threshold commit: the law is the caller's
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
        match (options.ask(), options.bridges()) {
            (Some(probe), _) => ReleaseReturn::Ask {
                probe: probe.clone(),
            },
            (None, false) => ReleaseReturn::NoContinuationBridges {
                reason: "no admitted continuation reaches this receiver".to_owned(),
            },
            (None, true) => ReleaseReturn::Widen {
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

fn plural_options(ask: Option<ObservationProbe>, bridges: bool) -> LawfulOptions {
    let measured = width_of(
        &x(),
        &states(&[integer(0), integer(4)]),
        DiameterNorm::Supremum,
    );
    LawfulOptions::assemble(&measured, integer(1), ask, bridges).expect("coherent options")
}

fn probe() -> ObservationProbe {
    ObservationProbe {
        observation: "observe-x".to_owned(),
        partition: ProbePartition::new(vec![1, 1], vec![2]).expect("a separating partition"),
    }
}

/// Lean: `no_default_among_the_lawful_returns`. **Two lawful laws, one width, different arms.**
#[test]
fn two_lawful_laws_return_different_arms() {
    let options = plural_options(None, true);
    assert!(!options.inside_tolerance());
    let held = release(&HoldingLaw, &options).expect("a lawful return");
    let widened = release(&AskingLaw, &options).expect("a lawful return");
    assert_eq!(held, ReleaseReturn::Hold);
    assert_eq!(
        widened,
        ReleaseReturn::Widen {
            tolerance: integer(4)
        }
    );
    assert_ne!(held, widened);
    // An offered probe is asked for; an unbridged gap is reported.
    assert_eq!(
        release(&AskingLaw, &plural_options(Some(probe()), true)).expect("lawful"),
        ReleaseReturn::Ask { probe: probe() }
    );
    assert_eq!(
        release(&AskingLaw, &plural_options(None, false)).expect("lawful"),
        ReleaseReturn::NoContinuationBridges {
            reason: "no admitted continuation reaches this receiver".to_owned()
        }
    );
}

/// Rebuild step 4 addition 8 (Lean `ReleaseLaw.sound`): **the decision as data.** A declared
/// [`DecisionRule`] releases inside its tolerance and takes its declared arm beyond it; every
/// return passes [`release`], a widening too narrow is refused like any law's, an offer the
/// options do not carry falls back to holding, and two rules on one width return different arms.
#[test]
fn a_decision_rule_is_a_declared_law_as_data() {
    let options = plural_options(None, true);
    let narrow = LawfulOptions::assemble(
        &width_of(
            &x(),
            &states(&[integer(0), ratio(1, 2)]),
            DiameterNorm::Supremum,
        ),
        integer(1),
        None,
        true,
    )
    .expect("coherent options");
    let releasing = DecisionRule::new(
        "release, else widen to 4",
        WithinTolerance::Release,
        BeyondTolerance::Widen(integer(4)),
    );
    assert_eq!(releasing.name(), "release, else widen to 4");
    assert_eq!(
        release(&releasing, &narrow).expect("lawful"),
        ReleaseReturn::Released {
            width: ratio(1, 2),
            tolerance: integer(1)
        }
    );
    assert_eq!(
        release(&releasing, &options).expect("lawful"),
        ReleaseReturn::Widen {
            tolerance: integer(4)
        }
    );
    let too_narrow = DecisionRule::new(
        "widen to 2",
        WithinTolerance::Hold,
        BeyondTolerance::Widen(integer(2)),
    );
    assert!(matches!(
        release(&too_narrow, &options),
        Err(WidthRefusal::WidenTooNarrow(_))
    ));
    assert_eq!(
        release(&too_narrow, &narrow).expect("lawful"),
        ReleaseReturn::Hold
    );
    for beyond in [
        BeyondTolerance::Ask,
        BeyondTolerance::NoContinuation("bridged".to_owned()),
        BeyondTolerance::Hold,
    ] {
        let rule = DecisionRule::new("offer-bound", WithinTolerance::Release, beyond);
        assert_eq!(
            release(&rule, &options).expect("lawful"),
            ReleaseReturn::Hold
        );
    }
    let asking = DecisionRule::new("ask", WithinTolerance::Release, BeyondTolerance::Ask);
    assert_eq!(
        release(&asking, &plural_options(Some(probe()), true)).expect("lawful"),
        ReleaseReturn::Ask { probe: probe() }
    );
    let reporting = DecisionRule::new(
        "report",
        WithinTolerance::Release,
        BeyondTolerance::NoContinuation("no admitted continuation".to_owned()),
    );
    assert_eq!(
        release(&reporting, &plural_options(None, false)).expect("lawful"),
        ReleaseReturn::NoContinuationBridges {
            reason: "no admitted continuation".to_owned()
        }
    );
}

/// Lean: `ReleaseLaw.sound`. A law claiming release outside its own declared tolerance is refused.
#[test]
fn a_law_releasing_outside_its_declared_tolerance_is_refused() {
    let refusal = release(&LyingLaw, &plural_options(None, true)).expect_err("refused");
    assert!(matches!(
        refusal,
        WidthRefusal::ReleasedOutsideTolerance(ref claim) if claim.law == "lying"
    ));
}

/// Lean: `ReleaseLaw.widenSound`. A named tolerance must actually contain the measured width.
#[test]
fn a_widening_proposal_below_the_measured_width_is_refused() {
    struct TooNarrow;
    impl DecisionLaw for TooNarrow {
        fn name(&self) -> &str {
            "too-narrow-widening"
        }

        fn decide(&self, _options: &LawfulOptions) -> ReleaseReturn {
            ReleaseReturn::Widen {
                tolerance: integer(3),
            }
        }
    }

    let refusal = release(&TooNarrow, &plural_options(None, true)).expect_err("4 is not inside 3");
    assert!(matches!(
        refusal,
        WidthRefusal::WidenTooNarrow(ref claim)
            if claim.law == "too-narrow-widening"
                && claim.width == integer(4)
                && claim.tolerance == integer(3)
    ));
}

/// A law naming a probe the owner did not offer is refused, and so is a width law that returns a
/// draw: the separating term between a width decision and a draw is the key.
#[test]
fn a_law_naming_an_unoffered_probe_or_a_draw_is_refused() {
    struct Inventing;
    impl DecisionLaw for Inventing {
        fn name(&self) -> &str {
            "inventing"
        }
        fn decide(&self, _options: &LawfulOptions) -> ReleaseReturn {
            ReleaseReturn::Ask {
                probe: ObservationProbe {
                    observation: "an-observation-nobody-computed".to_owned(),
                    partition: ProbePartition::new(vec![1, 1], vec![2])
                        .expect("a separating partition"),
                },
            }
        }
    }
    struct Drawing;
    impl DecisionLaw for Drawing {
        fn name(&self) -> &str {
            "drawing"
        }
        fn decide(&self, _options: &LawfulOptions) -> ReleaseReturn {
            ReleaseReturn::Drawn(CertifiedDraw {
                key: Rat::zero(),
                class: 0,
                prior_upper: Rat::zero(),
                through_lower: Rat::one(),
            })
        }
    }
    let options = plural_options(Some(probe()), true);
    assert!(matches!(
        release(&Inventing, &options).expect_err("refused"),
        WidthRefusal::ProbeNotOffered { .. }
    ));
    assert!(matches!(
        release(&Drawing, &options).expect_err("refused"),
        WidthRefusal::DrawNotOffered { ref law } if law == "drawing"
    ));
}

// ---------------------------------------------------------------------------------------------
// the probe's criterion
// ---------------------------------------------------------------------------------------------

/// Lean: `Population.partitionInformation_lt_iff`. **The probe's criterion is information, read
/// exactly as `∏_c |c|^|c|`.** Over a fibre of four, `{2, 2}` carries one bit and `{3, 1}` less
/// (`2 − ¾ log₂ 3`): `2²·2² = 16 < 3³·1¹ = 27`. `{2, 1, 1}` carries three halves and `{4}` none:
/// `4 < 256`. Equal products carry equal information and offer nothing; a partition of another
/// fibre, an empty class or no class at all is not a comparison.
#[test]
fn the_probe_partition_compares_information_by_its_product() {
    let halves = ProbePartition::new(vec![2, 2], vec![3, 1]).expect("one bit against less");
    assert_eq!(halves.fibre(), 4);
    assert_eq!(
        (halves.product(), halves.against_product()),
        (BigUint::from(16u32), BigUint::from(27u32))
    );
    let split = ProbePartition::new(vec![2, 1, 1], vec![4]).expect("three halves against none");
    assert_eq!(
        (split.product(), split.against_product()),
        (BigUint::from(4u32), BigUint::from(256u32))
    );
    assert_eq!(partition_product(&[]), BigUint::from(1u32));
    assert!(matches!(
        ProbePartition::new(vec![3, 1], vec![2, 2]),
        Err(WidthRefusal::ProbeNotInformative { ref product, ref against })
            if product == "27" && against == "16"
    ));
    assert!(matches!(
        ProbePartition::new(vec![1, 2], vec![2, 1]),
        Err(WidthRefusal::ProbeNotInformative { .. })
    ));
    for (classes, against) in [
        (vec![1, 1], vec![3]),
        (vec![0, 2], vec![2]),
        (vec![], vec![]),
    ] {
        assert!(matches!(
            ProbePartition::new(classes, against),
            Err(WidthRefusal::ProbeClasses { .. })
        ));
    }
}

/// **The chaser's rule is the one law on a discrete reading** (THE_REBUILD U3, the second loop):
/// `DecisionRule(Release, Ask)` at tolerance zero over the capture-within-`m` reading. Width zero
/// (the basin certifies every member) releases even while a probe is offered; width one (the
/// discrete band) asks the offered probe, and holds where none is offered. No other arm is lawful
/// here.
#[test]
fn a_certified_capture_releases_at_zero_and_an_uncertified_one_asks_or_holds() {
    let rule = DecisionRule::new("capture", WithinTolerance::Release, BeyondTolerance::Ask);
    let reading = |diameter: i64| {
        let attaining = if diameter == 0 {
            WidthWitness::Point
        } else {
            WidthWitness::Coordinate { coordinate: 0 }
        };
        ReceiverWidth::declared(
            "capture within m",
            "the selected fibre",
            DiameterNorm::Supremum,
            integer(diameter),
            attaining,
            4,
        )
        .expect("a declared width")
    };
    let decide = |diameter: i64, ask: Option<ObservationProbe>| {
        let options = LawfulOptions::assemble(&reading(diameter), Rat::zero(), ask, true)
            .expect("coherent options");
        release(&rule, &options).expect("a lawful return")
    };
    assert_eq!(
        decide(0, Some(probe())),
        ReleaseReturn::Released {
            width: Rat::zero(),
            tolerance: Rat::zero()
        }
    );
    assert_eq!(decide(1, Some(probe())), ReleaseReturn::Ask { probe: probe() });
    assert_eq!(decide(1, None), ReleaseReturn::Hold);
}

// ---------------------------------------------------------------------------------------------
// the certified draw (the receipts `population::sampling` and `population::family_release`
// carried, reproduced through the one law)
// ---------------------------------------------------------------------------------------------

fn drawn(returned: ReleaseReturn) -> CertifiedDraw {
    match returned {
        ReleaseReturn::Drawn(certified) => certified,
        other => panic!("expected a certified draw, got {other:?}"),
    }
}

fn unresolved(returned: ReleaseReturn) -> UnresolvedDraw {
    match returned {
        ReleaseReturn::Unresolved(unresolved) => unresolved,
        other => panic!("expected an unresolved draw, got {other:?}"),
    }
}

/// A point face draws the inverse-CDF class with its exact cell.
#[test]
fn point_face_selects_the_inverse_cdf_class_with_exact_bounds() {
    let face = vec![
        ExactInterval::point(ratio(1, 4)),
        ExactInterval::point(ratio(1, 2)),
        ExactInterval::point(ratio(1, 4)),
    ];
    let selected = drawn(draw(&face, &ratio(1, 4)).unwrap());
    assert_eq!(selected.class, 1);
    assert_eq!(selected.key, ratio(1, 4));
    assert_eq!(selected.prior_upper, ratio(1, 4));
    assert_eq!(selected.through_lower, ratio(3, 4));
}

/// An overlapping face leaves the key plural: it is held, with every crossing's exact bounds, and
/// its draw mass stays unresolved.
#[test]
fn overlapping_face_is_held_with_exact_crossing_bounds() {
    let face = vec![
        ExactInterval::new(ratio(0, 1), ratio(3, 4)).unwrap(),
        ExactInterval::new(ratio(1, 4), ratio(1, 1)).unwrap(),
    ];
    let held = unresolved(draw(&face, &ratio(1, 2)).unwrap());
    assert_eq!(held.key, ratio(1, 2));
    assert_eq!(held.crossings.len(), 2);
    assert_eq!(held.crossings[0].class, 0);
    assert_eq!(held.crossings[0].prior_upper, ratio(0, 1));
    assert_eq!(held.crossings[0].through_lower, ratio(0, 1));
    assert_eq!(held.crossings[1].class, 1);
    assert_eq!(held.crossings[1].prior_upper, ratio(3, 4));
    assert_eq!(held.crossings[1].through_lower, ratio(1, 4));
}

/// Bounds that enclose no normalized face are refused as content, not decided.
#[test]
fn invalid_normalization_is_refused() {
    let face = vec![
        ExactInterval::point(ratio(1, 4)),
        ExactInterval::point(ratio(1, 4)),
    ];
    assert_eq!(
        draw(&face, &ratio(1, 8)),
        Err(DrawRefusal::InvalidNormalization {
            lower_total: ratio(1, 2),
            upper_total: ratio(1, 2),
        })
    );
    assert_eq!(draw(&[], &ratio(1, 8)), Err(DrawRefusal::EmptyFace));
    assert_eq!(
        draw(&face, &Rat::one()),
        Err(DrawRefusal::KeyOutOfRange { key: Rat::one() })
    );
}

/// A reversed class interval, built past `ExactInterval::new` through its public fields, is refused
/// before the inverse CDF reads it: unchecked, `[3/4, 1/4], [0, 3/4]` at key `1/2` drew class 0,
/// whose interval holds no mass.
#[test]
fn reversed_mass_bounds_are_refused() {
    let face = vec![
        ExactInterval { lower: ratio(3, 4), upper: ratio(1, 4) },
        ExactInterval::new(ratio(0, 1), ratio(3, 4)).unwrap(),
    ];
    assert_eq!(
        draw(&face, &ratio(1, 2)),
        Err(DrawRefusal::ReversedMass {
            class: 0,
            lower: ratio(3, 4),
            upper: ratio(1, 4),
        })
    );
}

/// The stop class of the curated section chart (268 classes) is drawable.
#[test]
fn stop_class_is_selectable_in_a_268_class_chart() {
    let mut face = vec![ExactInterval::point(ratio(0, 1)); 268];
    face[267] = ExactInterval::point(ratio(1, 1));
    let selected = drawn(draw(&face, &ratio(999, 1000)).unwrap());
    assert_eq!(selected.class, 267);
    assert_eq!(selected.prior_upper, ratio(0, 1));
    assert_eq!(selected.through_lower, ratio(1, 1));
}

/// An exact family face is checked nonnegative and normalized, then drawn through its point
/// enclosure.
#[test]
fn exact_family_class_selection_validates_and_returns_the_cell() {
    let selected = drawn(draw_exact(&[ratio(1, 4), ratio(3, 4)], &ratio(1, 4)).unwrap());
    assert_eq!(selected.class, 1);
    assert_eq!(selected.prior_upper, ratio(1, 4));
    assert_eq!(selected.through_lower, Rat::one());
    assert!(matches!(
        draw_exact(&[ratio(-1, 4), ratio(5, 4)], &ratio(0, 1)),
        Err(DrawRefusal::NegativeMass { class: 0, .. })
    ));
    assert_eq!(
        draw_exact(&[ratio(1, 4), ratio(1, 4)], &ratio(0, 1)),
        Err(DrawRefusal::NotNormalized { total: ratio(1, 2) })
    );
}

/// **The join** (Lean `certified_draw_is_released_at_zero_tolerance`, `plural_draw_is_held`):
/// the draw's arm is the holding law's at tolerance zero on the key's class reading. On a face
/// whose certified cells and crossings are both present, every key in a certified cell is `Drawn`
/// exactly when the tolerance-zero holding rule releases a zero width, every other key is
/// `Unresolved` exactly when it holds a width of one, and a point face leaves no key unresolved.
#[test]
fn a_draw_is_the_holding_law_at_tolerance_zero() {
    let rule = DecisionRule::new(
        CERTIFIED_DRAW_RULE,
        WithinTolerance::Release,
        BeyondTolerance::Hold,
    );
    let decided = |diameter: Rat| {
        let attaining = if diameter.is_zero() {
            WidthWitness::Point
        } else {
            WidthWitness::Coordinate { coordinate: 0 }
        };
        let width = ReceiverWidth::declared(
            "the key's class",
            "the enclosure",
            DiameterNorm::Supremum,
            diameter,
            attaining,
            3,
        )
        .unwrap();
        release(
            &rule,
            &LawfulOptions::assemble(&width, Rat::zero(), None, false).unwrap(),
        )
        .unwrap()
    };
    let interval = vec![
        ExactInterval::new(ratio(1, 8), ratio(1, 4)).unwrap(),
        ExactInterval::point(ratio(1, 2)),
        ExactInterval::new(ratio(1, 4), ratio(3, 8)).unwrap(),
    ];
    let point = vec![
        ExactInterval::point(ratio(1, 4)),
        ExactInterval::point(ratio(1, 2)),
        ExactInterval::point(ratio(1, 4)),
    ];
    let (mut certified, mut plural) = (0usize, 0usize);
    for numerator in 0..64 {
        let key = ratio(numerator, 64);
        match draw(&interval, &key).unwrap() {
            ReleaseReturn::Drawn(cell) => {
                certified += 1;
                assert!(cell.prior_upper <= key && key < cell.through_lower);
                assert!(matches!(
                    decided(Rat::zero()),
                    ReleaseReturn::Released { .. }
                ));
            }
            ReleaseReturn::Unresolved(held) => {
                plural += 1;
                assert!(!held.crossings.is_empty());
                assert_eq!(decided(Rat::one()), ReleaseReturn::Hold);
            }
            other => panic!("a draw returns only its two arms, got {other:?}"),
        }
        assert!(matches!(
            draw(&point, &key).unwrap(),
            ReleaseReturn::Drawn(_)
        ));
    }
    // The certified cells are [0, 1/8), [1/4, 5/8) and [3/4, 7/8): 8 + 24 + 8 of 64 keys. The 24
    // keys of [1/8, 1/4) ∪ [5/8, 3/4) ∪ [7/8, 1) are unresolved draw mass `3/8 = 3/2³`; on
    // [7/8, 1) normalization already fixes class 2, so that part is the certificate's
    // sufficiency, not a plural fibre.
    assert_eq!(certified, 40);
    assert_eq!(plural, 24);
}

/// A face that covers the whole simplex never certifies a class: every key is held.
#[test]
fn a_simplex_covering_face_holds_every_key() {
    let face = vec![ExactInterval::new(Rat::zero(), Rat::one()).unwrap(); 2];
    for numerator in 0..8 {
        assert!(matches!(
            draw(&face, &ratio(numerator, 8)).unwrap(),
            ReleaseReturn::Unresolved(_)
        ));
    }
}

// ---------------------------------------------------------------------------------------------
// the faces the width is taken over
// ---------------------------------------------------------------------------------------------

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

fn declared_horizon(longitudinal: usize, index: usize) -> Horizon {
    Horizon::declare(longitudinal, index).expect("a horizon inside both ceilings")
}

/// `Foundation/ReceiverRelease.horizonWithin_is_not_total`: the two coordinates are a product
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

/// The finite width over read faces refuses an empty family and one past the ceiling.
#[test]
fn the_width_over_readings_refuses_empty_and_oversized_families() {
    let faces = vec![
        ExactFace::Vector(vec![integer(1)]),
        ExactFace::Vector(vec![integer(4)]),
        ExactFace::Vector(vec![integer(2)]),
    ];
    let over_readings =
        width_over_readings("the first coordinate", "three", &faces, DiameterNorm::Supremum)
            .expect("an exact width");
    assert_eq!(over_readings.diameter(), &integer(3));
    assert_eq!(
        over_readings.attaining(),
        &WidthWitness::Pair { left: 0, right: 1 }
    );
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
