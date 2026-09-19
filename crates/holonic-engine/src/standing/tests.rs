//! Tests for **T2 — standing, memory and extinction**.
//!
//! Every theorem of `Foundation/Standing.lean` appears here under the name the module's
//! correspondence table gives it, and every declared-size entry point has a hostile-input test
//! beside it. Nothing here needs a fixture, and no `f32`/`f64` appears.
//!
//! The instances are neutral throughout: a wave and the medium it inscribes, a song and a later
//! listener, a text and a later reader.

use super::*;

use crate::receiver_release::{CompatibleFamily, DiameterNorm, width_enumerated};

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// A matrix from exact rational entries given as `(numerator, denominator)` pairs.
fn matrix(rows: &[&[(i64, i64)]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| {
                row.iter()
                    .map(|(numerator, denominator)| rat(*numerator, *denominator))
                    .collect()
            })
            .collect(),
    )
    .expect("a rectangular matrix")
}

fn state(values: &[(i64, i64)]) -> Vec<Rat> {
    values
        .iter()
        .map(|(numerator, denominator)| rat(*numerator, *denominator))
        .collect()
}

// ---------------------------------------------------------------------------------------------
// 1. Standing is the retained residue of passages
// ---------------------------------------------------------------------------------------------

/// A two-coordinate carrier: the occurrence's own state, and the medium a later receiver reads.
/// `scale-state` doubles the state and leaves the medium; `scale-medium` doubles the medium and
/// leaves the state. Both are exactly linear.
fn medium_generators() -> GeneratorFamily {
    GeneratorFamily::declared(
        "wave-and-medium",
        vec!["scale-state".to_owned(), "scale-medium".to_owned()],
        vec![
            matrix(&[&[(2, 1), (0, 1)], &[(0, 1), (1, 1)]]),
            matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (2, 1)]]),
        ],
    )
    .expect("a declared generator family")
}

/// The receiver that reads the medium and nothing else.
fn medium_reading() -> ReceiverReading {
    ReceiverReading::declared("medium", matrix(&[&[(0, 1), (1, 1)]]))
        .expect("a declared reading")
}

/// The receiver that reads the occurrence's own state and nothing else.
fn state_reading() -> ReceiverReading {
    ReceiverReading::declared("state", matrix(&[&[(1, 1), (0, 1)]])).expect("a declared reading")
}

/// **Lean: `standingLaw_exists_iff_future_factors`.** A quotient is a lawful standing exactly when
/// every admitted future observation factors through it. The medium quotient is sufficient for
/// the medium receiver; the state quotient is not sufficient for a receiver that survives an
/// exchange.
#[test]
fn a_quotient_is_a_standing_exactly_when_the_future_factors_through_it() {
    let generators = medium_generators();
    let population = SourcePopulation::declared(
        "two-presents",
        vec![state(&[(2, 1), (1, 1)]), state(&[(4, 1), (1, 1)])],
    )
    .expect("a declared population");
    let standing =
        StandingLaw::declared("medium-standing", matrix(&[&[(0, 1), (1, 1)]])).expect("a standing");

    let observations = vec![
        FutureObservation::declared(vec![], medium_reading()).expect("an observation"),
        FutureObservation::declared(vec![0], medium_reading()).expect("an observation"),
        FutureObservation::declared(vec![1], medium_reading()).expect("an observation"),
        FutureObservation::declared(vec![0, 1, 0], medium_reading()).expect("an observation"),
    ];
    let verdict = sufficiency(&standing, &population, &generators, &observations)
        .expect("the check runs");
    assert_eq!(
        verdict,
        SufficiencyVerdict::Sufficient {
            pairs: 1,
            observations: 4
        },
        "the medium quotient carries every admitted future observation of the medium receiver"
    );

    // The same quotient is not sufficient for a receiver that reads the state.
    let state_observations =
        vec![FutureObservation::declared(vec![], state_reading()).expect("an observation")];
    let refuted = sufficiency(&standing, &population, &generators, &state_observations)
        .expect("the check runs");
    match refuted {
        SufficiencyVerdict::NotSufficient {
            left,
            right,
            ref receiver,
            ref word,
            ..
        } => {
            assert_eq!((left, right), (0, 1));
            assert_eq!(receiver, "state");
            assert!(word.is_empty());
        }
        other => panic!("the state receiver must refute the medium standing, got {other:?}"),
    }
}

/// **Lean: `two_histories_leave_one_standing`.** One doubling of the state and two reach distinct
/// presents carrying the same standing, so the passage history is not recoverable from standing
/// and none is owed.
#[test]
fn two_histories_leave_one_standing() {
    let generators = medium_generators();
    let origin = state(&[(1, 1), (1, 1)]);
    let one_step = generators
        .transport_word(&[0], &origin)
        .expect("one admitted passage");
    let two_steps = generators
        .transport_word(&[0, 0], &origin)
        .expect("two admitted passages");
    assert_ne!(one_step, two_steps, "the two presents are distinct occurrences");
    assert_eq!(one_step, state(&[(2, 1), (1, 1)]));
    assert_eq!(two_steps, state(&[(4, 1), (1, 1)]));

    let standing =
        StandingLaw::declared("medium-standing", matrix(&[&[(0, 1), (1, 1)]])).expect("a standing");
    assert_eq!(
        standing.retained(&one_step).expect("a standing"),
        standing.retained(&two_steps).expect("a standing"),
        "the two histories leave one standing"
    );
}

/// **Lean: `one_present_face_two_standings_separated_later`.** Two presents agree at the present
/// receiver and are separated by the same receiver after one exchange, so their standing differs.
#[test]
fn one_present_face_two_standings_separated_later() {
    let exchange = GeneratorFamily::declared(
        "exchange",
        vec!["exchange".to_owned()],
        vec![matrix(&[&[(0, 1), (1, 1)], &[(1, 1), (0, 1)]])],
    )
    .expect("a declared generator family");
    let population = SourcePopulation::declared(
        "one-present-face",
        vec![state(&[(0, 1), (0, 1)]), state(&[(0, 1), (1, 1)])],
    )
    .expect("a declared population");

    let present = state_reading();
    assert_eq!(
        present.face(&population.members()[0]).expect("a face"),
        present.face(&population.members()[1]).expect("a face"),
        "the present receiver cannot tell them apart"
    );

    // The proposed standing is the present face. One admitted successor refutes it.
    let proposed = StandingLaw::declared("present-face", matrix(&[&[(1, 1), (0, 1)]]))
        .expect("a standing");
    let observations = vec![
        FutureObservation::declared(vec![], state_reading()).expect("an observation"),
        FutureObservation::declared(vec![0], state_reading()).expect("an observation"),
    ];
    let verdict =
        sufficiency(&proposed, &population, &exchange, &observations).expect("the check runs");
    match verdict {
        SufficiencyVerdict::NotSufficient {
            ref word,
            ref left_face,
            ref right_face,
            ..
        } => {
            assert_eq!(word, &vec![0], "one exchange separates them");
            assert_eq!(left_face, &state(&[(0, 1)]));
            assert_eq!(right_face, &state(&[(1, 1)]));
        }
        other => panic!("one exchange must refute the present-face standing, got {other:?}"),
    }

    // The complete present is a lawful standing for the same family.
    let complete = StandingLaw::declared(
        "complete-present",
        matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]),
    )
    .expect("a standing");
    assert_eq!(
        sufficiency(&complete, &population, &exchange, &observations).expect("the check runs"),
        SufficiencyVerdict::Sufficient {
            pairs: 0,
            observations: 2
        }
    );
}

// ---------------------------------------------------------------------------------------------
// 2. Memory is a generator, not a retrieval
// ---------------------------------------------------------------------------------------------

/// The song's reconstruction: the retained melody, and the present listener's timbre, which this
/// law carries as `7`. It is total and returns a definite face for every standing.
fn song_memory(present: usize) -> MemoryLaw {
    MemoryLaw::declared(
        present,
        matrix(&[&[(1, 1)], &[(0, 1)]]),
        matrix(&[&[(0, 1)], &[(1, 1)]]),
    )
    .expect("a declared reconstruction")
}

/// **Lean: `the_remembered_face_is_a_new_occurrence`.** The reconstruction occurs now, not at the
/// original's time. In Lean the time is part of the type and the two faces cannot be compared at
/// all; here it is carried as data and `occurs_at` separates them.
#[test]
fn the_remembered_face_is_a_new_occurrence() {
    let law = song_memory(5);
    let remembered = law
        .remember(&state(&[(3, 1)]), &state(&[(7, 1)]))
        .expect("a reconstruction");
    let original = TimedFace::declared(0, state(&[(3, 1), (1, 1)])).expect("the original's face");
    assert_eq!(remembered.occurs_at(), 5);
    assert_eq!(original.occurs_at(), 0);
    assert_ne!(
        remembered.occurs_at(),
        original.occurs_at(),
        "the remembered face is a new occurrence at the present time"
    );
    assert_eq!(
        remembered.value(),
        state(&[(3, 1), (7, 1)]).as_slice(),
        "it carries the retained melody and the present listener's timbre"
    );
}

/// **Lean: `one_standing_two_contexts_two_faces`.** The reconstruction depends on the present,
/// which is what makes it a generation and not a retrieval.
#[test]
fn one_standing_two_contexts_two_faces() {
    let law = song_memory(5);
    let standing = state(&[(3, 1)]);
    let quiet = law
        .remember(&standing, &state(&[(0, 1)]))
        .expect("a reconstruction");
    let loud = law
        .remember(&standing, &state(&[(1, 1)]))
        .expect("a reconstruction");
    assert_ne!(quiet.value(), loud.value());
    assert_eq!(quiet.value(), state(&[(3, 1), (0, 1)]).as_slice());
    assert_eq!(loud.value(), state(&[(3, 1), (1, 1)]).as_slice());
}

/// **Lean: `one_original_two_standings_two_reconstructions`.** The two standings are the medium
/// standing of one original after two different intervening histories. Reinterpretation is the
/// standing changing under later passages, not the original changing.
#[test]
fn one_original_two_standings_two_reconstructions() {
    let generators = medium_generators();
    let original = state(&[(1, 1), (1, 1)]);
    let standing =
        StandingLaw::declared("medium-standing", matrix(&[&[(0, 1), (1, 1)]])).expect("a standing");

    let after_one = standing
        .retained(
            &generators
                .transport_word(&[1], &original)
                .expect("one deposit"),
        )
        .expect("a standing");
    let after_two = standing
        .retained(
            &generators
                .transport_word(&[1, 1], &original)
                .expect("two deposits"),
        )
        .expect("a standing");
    assert_eq!(after_one, state(&[(2, 1)]));
    assert_eq!(after_two, state(&[(4, 1)]));

    let law = song_memory(9);
    let context = state(&[(7, 1)]);
    let first = law.remember(&after_one, &context).expect("a reconstruction");
    let second = law.remember(&after_two, &context).expect("a reconstruction");
    assert_ne!(
        first.value(),
        second.value(),
        "the same original under two later standings returns two reconstructions"
    );
}

/// **Lean: `the_unretained_receiver_is_reconstructed_confidently_and_wrongly`.**
///
/// The melody factors through the standing, so a faithful reconstruction exists. The timbre does
/// not, and the two lineage members that refute the factoring are returned. The reconstruction
/// nevertheless returns a **definite** timbre for the original — exactly `7` where the original
/// carried `1`. The face is constituted and originful, and it is wrong.
#[test]
fn the_unretained_receiver_is_reconstructed_confidently_and_wrongly() {
    let population = SourcePopulation::declared(
        "one-song-two-performances",
        vec![
            state(&[(0, 1), (0, 1)]),
            state(&[(0, 1), (1, 1)]),
            state(&[(2, 1), (3, 1)]),
        ],
    )
    .expect("a declared population");
    let standing =
        StandingLaw::declared("melody-standing", matrix(&[&[(1, 1), (0, 1)]])).expect("a standing");

    let melody = ReceiverReading::declared("melody", matrix(&[&[(1, 1), (0, 1)]]))
        .expect("a declared reading");
    let timbre = ReceiverReading::declared("timbre", matrix(&[&[(0, 1), (1, 1)]]))
        .expect("a declared reading");

    assert_eq!(
        fidelity(&standing, &melody, &population).expect("the check runs"),
        Fidelity::Faithful {
            receiver: "melody".to_owned(),
            checked: 1
        },
        "the melody factors through the standing"
    );

    match fidelity(&standing, &timbre, &population).expect("the check runs") {
        Fidelity::NotRetained {
            ref receiver,
            left,
            right,
            ref left_face,
            ref right_face,
        } => {
            assert_eq!(receiver, "timbre");
            assert_eq!((left, right), (0, 1));
            assert_eq!(left_face, &state(&[(0, 1)]));
            assert_eq!(right_face, &state(&[(1, 1)]));
        }
        other => panic!("the timbre cannot be faithful, got {other:?}"),
    }

    // And the reconstruction still returns a definite, wrong timbre for the second performance.
    let original = &population.members()[1];
    let law = song_memory(5);
    let remembered = law
        .remember(
            &standing.retained(original).expect("a standing"),
            &state(&[(7, 1)]),
        )
        .expect("a reconstruction");
    assert_eq!(
        timbre.face(remembered.value()).expect("a face"),
        state(&[(7, 1)]),
        "the reconstruction is confident: it returns a definite timbre"
    );
    assert_eq!(
        timbre.face(original).expect("a face"),
        state(&[(1, 1)]),
        "and the original carried a different one"
    );
    assert_eq!(
        melody.face(remembered.value()).expect("a face"),
        melody.face(original).expect("a face"),
        "while the retained melody is exactly right"
    );
}

// ---------------------------------------------------------------------------------------------
// 3. The receiver keeps changing after the source stops
// ---------------------------------------------------------------------------------------------

fn text_chain() -> ApertureChain {
    ApertureChain::declared("a text and its later readers", 4).expect("a declared chain")
}

/// **Lean: `aperture_comp_of_le`.** A coarser aperture reads a finer aperture's face and returns
/// its own, which is the zero changing-receiver defect of `Transport/ChangingReceiver.lean`.
#[test]
fn a_coarser_aperture_reads_a_finer_face_and_returns_its_own() {
    let chain = text_chain();
    let source = state(&[(1, 1), (2, 1), (3, 1), (4, 1)]);
    for coarse in 0..=4 {
        for fine in coarse..=4 {
            let finer = chain.face(fine, &source).expect("a face");
            assert_eq!(
                chain.face(coarse, &finer).expect("a face"),
                chain.face(coarse, &source).expect("a face"),
                "the link law fails at ({coarse}, {fine})"
            );
        }
    }
}

/// **Lean: `the_available_face_changes_while_the_source_does_not`.** The source is fixed; the
/// available face changes at every step of the chain.
#[test]
fn the_available_face_changes_while_the_source_does_not() {
    let chain = text_chain();
    let fixed = state(&[(1, 1), (1, 1), (1, 1), (1, 1)]);
    for step in 0..4 {
        assert_ne!(
            chain.face(step, &fixed).expect("a face"),
            chain.face(step + 1, &fixed).expect("a face"),
            "the face at step {step} must differ from the face at step {}",
            step + 1
        );
    }
}

/// **Lean: `compatibleFibre_antitone`.** Understanding narrows the fibre and never widens it.
#[test]
fn the_compatible_fibre_is_antitone_in_the_step() {
    let chain = text_chain();
    let reference = state(&[(1, 1), (1, 1), (1, 1), (1, 1)]);
    let candidate = state(&[(1, 1), (1, 1), (0, 1), (1, 1)]);
    for coarse in 0..=4 {
        for fine in coarse..=4 {
            if chain
                .compatible(fine, &candidate, &reference)
                .expect("the check runs")
            {
                assert!(
                    chain
                        .compatible(coarse, &candidate, &reference)
                        .expect("the check runs"),
                    "membership at step {fine} must imply membership at step {coarse}"
                );
            }
        }
    }
}

/// **Lean: `the_fibre_is_never_a_singleton_and_a_later_step_separates`.** What one step cannot
/// separate a later step can, and the step that does it is returned.
#[test]
fn what_one_step_cannot_separate_a_later_step_can() {
    let chain = text_chain();
    let reference = state(&[(1, 1), (1, 1), (1, 1), (1, 1)]);
    let candidate = state(&[(1, 1), (1, 1), (0, 1), (1, 1)]);
    assert!(
        chain
            .compatible(2, &candidate, &reference)
            .expect("the check runs"),
        "the first two coordinates agree, so step 2 cannot separate them"
    );
    assert!(
        !chain
            .compatible(3, &candidate, &reference)
            .expect("the check runs"),
        "step 3 reads the coordinate they differ in"
    );
    assert_eq!(
        chain
            .first_separating_step(&candidate, &reference)
            .expect("the check runs"),
        Some(3)
    );

    // And a source the chain never reads is never separated: the fibre is not a singleton.
    let unread = state(&[(1, 1), (1, 1), (1, 1), (1, 1)]);
    assert_eq!(
        chain
            .first_separating_step(&unread, &reference)
            .expect("the check runs"),
        None
    );
}

// ---------------------------------------------------------------------------------------------
// 4. Effective extinction, the fossil, and the nondissipative control
// ---------------------------------------------------------------------------------------------

/// The fossil instance. Coordinates are `(a, e, m)`: the wave's amplitude, its declared quadratic
/// energy `e = a²`, and the medium's inscription. The step is exactly
///
/// ```text
/// a ↦ a/2,   e ↦ e/4,   m ↦ m + e/4
/// ```
///
/// so three quarters of the declared energy leave the wave chart at every step, of which the
/// medium captures a third and the rest dissipates.
fn fossil_generators() -> GeneratorFamily {
    GeneratorFamily::declared(
        "a damped wave and the medium it inscribes",
        vec!["settle".to_owned()],
        vec![matrix(&[
            &[(1, 2), (0, 1), (0, 1)],
            &[(0, 1), (1, 4), (0, 1)],
            &[(0, 1), (1, 4), (1, 1)],
        ])],
    )
    .expect("a declared generator family")
}

fn fossil_origin() -> Vec<Rat> {
    state(&[(1, 1), (1, 1), (0, 1)])
}

fn fossil_rest() -> Vec<Rat> {
    state(&[(0, 1), (0, 1), (0, 1)])
}

fn amplitude_reading() -> ReceiverReading {
    ReceiverReading::declared("amplitude", matrix(&[&[(1, 1), (0, 1), (0, 1)]]))
        .expect("a declared reading")
}

fn energy_reading() -> ReceiverReading {
    ReceiverReading::declared("energy", matrix(&[&[(0, 1), (1, 1), (0, 1)]]))
        .expect("a declared reading")
}

fn medium_inscription_reading() -> ReceiverReading {
    ReceiverReading::declared("medium", matrix(&[&[(0, 1), (0, 1), (1, 1)]]))
        .expect("a declared reading")
}

/// The wave chart `{a, e}` contracts by exactly `1/2` and is invariant.
fn wave_chart() -> ContractionCertificate {
    ContractionCertificate::declared(vec![0, 1], rat(1, 2), 3).expect("a declared certificate")
}

fn fossil_state(step: usize) -> Vec<Rat> {
    fossil_generators()
        .transport_word(&vec![0usize; step], &fossil_origin())
        .expect("the trajectory advances")
}

/// **Lean: `fossilState_step`, `the_energy_is_the_square_of_the_amplitude`.** The exact
/// trajectory, checked against its closed form for the first seven stations.
#[test]
fn the_fossil_instance_has_exact_numbers() {
    let expected = [
        state(&[(1, 1), (1, 1), (0, 1)]),
        state(&[(1, 2), (1, 4), (1, 4)]),
        state(&[(1, 4), (1, 16), (5, 16)]),
        state(&[(1, 8), (1, 64), (21, 64)]),
        state(&[(1, 16), (1, 256), (85, 256)]),
        state(&[(1, 32), (1, 1024), (341, 1024)]),
        state(&[(1, 64), (1, 4096), (1365, 4096)]),
    ];
    for (step, want) in expected.iter().enumerate() {
        let got = fossil_state(step);
        assert_eq!(&got, want, "the trajectory at step {step}");
        // `e = a²` exactly, at every station.
        assert_eq!(
            got[1],
            &got[0] * &got[0],
            "the declared energy is the square of the amplitude at step {step}"
        );
        // `m = (1 − 4^{−t})/3` exactly, and it never reaches its limit.
        assert!(
            got[2] < rat(1, 3),
            "the inscription stays below its limit at step {step}"
        );
    }
}

/// **Lean: `the_energy_that_left_the_wave_is_accounted_for`.** The declared quadratic energy that
/// left the wave chart equals what the medium holds plus what dissipated — exact rational
/// bookkeeping, with the dissipation computed from the constitutive law rather than defined as a
/// residual.
#[test]
fn the_energy_that_left_the_wave_is_accounted_for() {
    let origin = fossil_origin();
    for step in 0..=6 {
        let now = fossil_state(step);
        // The dissipation is the half of each step's outgoing energy the medium did not capture:
        // `Σ_{k<t} e_k/2`, summed over the exact trajectory rather than assumed.
        let mut dissipated = integer(0);
        for earlier in 0..step {
            dissipated += &fossil_state(earlier)[1] / integer(2);
        }
        assert_eq!(
            &origin[1] - &now[1],
            &now[2] + &dissipated,
            "the ledger must close at step {step}"
        );
        // And the closed form of that dissipation is `2(1 − 4^{−t})/3`.
        let closed = integer(2) * (integer(1) - &now[1]) / integer(3);
        assert_eq!(dissipated, closed, "the closed form at step {step}");
    }
}

/// **Lean: `the_wave_is_extinct_at_horizon_three`.** At horizon 3 the wave chart is extinct at
/// tolerance `1/8`, and the verdict is certificate-backed: it holds for every admitted future
/// word, not only the ones enumerated.
#[test]
fn the_wave_chart_is_extinct_at_horizon_three() {
    let generators = fossil_generators();
    let certificate = wave_chart();
    certificate
        .verify(&generators)
        .expect("the wave chart is invariant and contracts by 1/2");

    let receivers = vec![amplitude_reading(), energy_reading()];
    let verdict = extinction(
        &generators,
        &receivers,
        &fossil_state(3),
        &fossil_rest(),
        4,
        &rat(1, 8),
        Some(&certificate),
    )
    .expect("the check runs");
    match verdict {
        ExtinctionVerdict::Extinct {
            ref tolerance,
            ref bound,
            ref chart,
            ref factor,
        } => {
            assert_eq!(tolerance, &rat(1, 8));
            assert_eq!(bound, &rat(1, 8), "the gain is 1 and the chart separation is 1/8");
            assert_eq!(chart, &vec![0usize, 1]);
            assert_eq!(factor, &rat(1, 2));
        }
        other => panic!("the wave chart must be extinct at 1/8, got {other:?}"),
    }
}

/// **Lean: `the_medium_separates_what_the_wave_chart_declared_extinct`.** Extinct at `(R, ε)` and
/// separated at a richer `(R', ε)` — the *same* tolerance. The separator is returned: the medium
/// receiver, the empty word, exact width `21/64`.
#[test]
fn the_medium_separates_what_the_wave_chart_declared_extinct() {
    let generators = fossil_generators();
    let receivers = vec![
        amplitude_reading(),
        energy_reading(),
        medium_inscription_reading(),
    ];
    let verdict = extinction(
        &generators,
        &receivers,
        &fossil_state(3),
        &fossil_rest(),
        4,
        &rat(1, 8),
        Some(&wave_chart()),
    )
    .expect("the check runs");
    match verdict {
        ExtinctionVerdict::Separated {
            ref receiver,
            ref word,
            ref width,
            ref tolerance,
        } => {
            assert_eq!(receiver, "medium");
            assert!(word.is_empty(), "the fossil is visible at once");
            assert_eq!(width, &rat(21, 64));
            assert_eq!(tolerance, &rat(1, 8));
        }
        other => panic!("the medium must separate at 1/8, got {other:?}"),
    }
}

/// **Lean: `extinct_iff_release_width_inside_tolerance`.** The width the verdict carries is
/// `receiver_release`'s own width over the two-point family `{T_w x, T_w 0}`, not a second
/// diameter.
#[test]
fn the_extinction_width_is_the_release_owners_width() {
    let family = CompatibleFamily::enumerated(
        "the fossil against its rest",
        vec![fossil_state(3), fossil_rest()],
    )
    .expect("a two-point family");
    let width = width_enumerated(
        &medium_inscription_reading(),
        &family,
        DiameterNorm::Supremum,
    )
    .expect("the release owner's width");
    assert_eq!(width.diameter(), &rat(21, 64));
    assert!(!width.releasable_at(&rat(1, 8)));
    assert!(width.releasable_at(&rat(1, 2)));
}

/// **Lean: `the_fossil_is_durable`.** Every admitted future word still reads at least `21/64` on
/// the medium: the inscription is a durable boundary record, not a momentarily visible residue.
#[test]
fn the_fossil_is_durable() {
    let generators = fossil_generators();
    let reading = medium_inscription_reading();
    let start = fossil_state(3);
    for word in generators.words_within(5).expect("the admitted words") {
        let advanced = generators
            .transport_word(&word, &start)
            .expect("the trajectory advances");
        let face = reading.face(&advanced).expect("a face");
        assert!(
            face[0] >= rat(21, 64),
            "the inscription fell below 21/64 after {word:?}"
        );
        assert!(face[0] < rat(1, 3), "and it never reaches its limit");
    }
}

/// **Lean: `extinct_mono_tolerance`.** A wider tolerance keeps an extinct perturbation extinct.
#[test]
fn extinction_is_monotone_in_the_tolerance() {
    let generators = fossil_generators();
    let receivers = vec![amplitude_reading(), energy_reading()];
    for (numerator, denominator) in [(1i64, 8i64), (1, 4), (1, 2), (1, 1)] {
        let verdict = extinction(
            &generators,
            &receivers,
            &fossil_state(3),
            &fossil_rest(),
            3,
            &rat(numerator, denominator),
            Some(&wave_chart()),
        )
        .expect("the check runs");
        assert!(
            matches!(verdict, ExtinctionVerdict::Extinct { .. }),
            "a tolerance of {numerator}/{denominator} must keep it extinct, got {verdict:?}"
        );
    }
}

/// **Lean: `extinct_mono_receivers`.** A subfamily of a receiver family that declared extinction
/// still declares it; the richer family is the one that can separate.
#[test]
fn extinction_is_monotone_in_the_receiver_family() {
    let generators = fossil_generators();
    let certificate = wave_chart();
    for receivers in [
        vec![amplitude_reading()],
        vec![energy_reading()],
        vec![amplitude_reading(), energy_reading()],
    ] {
        let verdict = extinction(
            &generators,
            &receivers,
            &fossil_state(3),
            &fossil_rest(),
            3,
            &rat(1, 8),
            Some(&certificate),
        )
        .expect("the check runs");
        assert!(
            matches!(verdict, ExtinctionVerdict::Extinct { .. }),
            "a subfamily must stay extinct, got {verdict:?}"
        );
    }
}

/// A search that reaches its horizon without a separator and without a covering certificate
/// returns the third value, naming the horizon, the words read and why the certificate route did
/// not decide. It never reports extinction it did not prove.
#[test]
fn a_search_without_a_certificate_returns_not_decided_rather_than_extinct() {
    let generators = fossil_generators();
    let receivers = vec![medium_inscription_reading()];
    let verdict = extinction(
        &generators,
        &receivers,
        &fossil_state(3),
        &fossil_rest(),
        3,
        &integer(1),
        None,
    )
    .expect("the check runs");
    match verdict {
        ExtinctionVerdict::NotDecidedWithinBound {
            horizon,
            words,
            ref widest,
            ref receiver,
            ref reason,
        } => {
            assert_eq!(horizon, 3);
            assert_eq!(words, 4, "one generator and a horizon of 3 names four words");
            assert_eq!(receiver, "medium");
            assert!(widest > &rat(21, 64));
            assert!(reason.contains("no contraction certificate"), "reason: {reason}");
        }
        other => panic!("the search must return NotDecidedWithinBound, got {other:?}"),
    }
}

/// A certificate that does not cover a declared receiver decides nothing, and the fall-through
/// says which receiver it did not cover. It does not quietly grant extinction.
#[test]
fn a_certificate_that_does_not_cover_a_receiver_decides_nothing() {
    let generators = fossil_generators();
    let receivers = vec![medium_inscription_reading()];
    let verdict = extinction(
        &generators,
        &receivers,
        &fossil_state(3),
        &fossil_rest(),
        3,
        &integer(1),
        Some(&wave_chart()),
    )
    .expect("the check runs");
    match verdict {
        ExtinctionVerdict::NotDecidedWithinBound { ref reason, .. } => {
            assert!(reason.contains("medium"), "reason: {reason}");
            assert!(reason.contains("chart"), "reason: {reason}");
        }
        other => panic!("an uncovered receiver must not buy extinction, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// The nondissipative control: the exact 3-4-5 rotation
// ---------------------------------------------------------------------------------------------

fn rotation_generators() -> GeneratorFamily {
    GeneratorFamily::declared(
        "an exact rational rotation",
        vec!["turn".to_owned()],
        vec![matrix(&[&[(3, 5), (-4, 5)], &[(4, 5), (3, 5)]])],
    )
    .expect("a declared generator family")
}

/// **Lean: `rotate_preserves_energy_along_every_word`,
/// `the_difference_is_redistributed_not_removed`.** The declared quadratic energy is conserved
/// exactly along every admitted history: the difference is redistributed between the two
/// coordinates and never leaves.
#[test]
fn the_rotation_conserves_the_declared_energy_exactly() {
    let generators = rotation_generators();
    let origin = state(&[(1, 1), (0, 1)]);
    let expected = [
        state(&[(1, 1), (0, 1)]),
        state(&[(3, 5), (4, 5)]),
        state(&[(-7, 25), (24, 25)]),
    ];
    for (steps, want) in expected.iter().enumerate() {
        let now = generators
            .transport_word(&vec![0usize; steps], &origin)
            .expect("the rotation advances");
        assert_eq!(&now, want, "the exact station at step {steps}");
    }
    for word in generators.words_within(8).expect("the admitted words") {
        let now = generators
            .transport_word(&word, &origin)
            .expect("the rotation advances");
        let energy = &now[0] * &now[0] + &now[1] * &now[1];
        assert_eq!(energy, integer(1), "the energy after {word:?}");
        // Both coordinates can never be small at once: `2·max² ≥ 1`, so `max > 1/2` exactly.
        let widest = if now[0].abs() > now[1].abs() {
            now[0].abs()
        } else {
            now[1].abs()
        };
        assert!(
            integer(2) * &widest * &widest >= integer(1),
            "both coordinates went small after {word:?}"
        );
    }
}

/// **Lean: `no_horizon_releases_the_energy_receiver`, `nothing_nonzero_is_extinct_at_zero_
/// tolerance`.** In the nondissipative system no horizon and no tolerance below `1/2` ever
/// declares the rotation's difference extinct for the coordinate family.
#[test]
fn no_horizon_releases_the_energy_receiver() {
    let generators = rotation_generators();
    let receivers = vec![
        ReceiverReading::declared("first", matrix(&[&[(1, 1), (0, 1)]])).expect("a reading"),
        ReceiverReading::declared("second", matrix(&[&[(0, 1), (1, 1)]])).expect("a reading"),
    ];
    let rest = state(&[(0, 1), (0, 1)]);
    for horizon in 0..=6usize {
        let start = generators
            .transport_word(&vec![0usize; horizon], &state(&[(1, 1), (0, 1)]))
            .expect("the rotation advances");
        for (numerator, denominator) in [(0i64, 1i64), (1, 4), (2, 5)] {
            let verdict = extinction(
                &generators,
                &receivers,
                &start,
                &rest,
                4,
                &rat(numerator, denominator),
                None,
            )
            .expect("the check runs");
            assert!(
                matches!(verdict, ExtinctionVerdict::Separated { .. }),
                "horizon {horizon} at tolerance {numerator}/{denominator} must separate, got \
                 {verdict:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Hostile input
// ---------------------------------------------------------------------------------------------

#[test]
fn a_horizon_naming_more_words_than_the_ceiling_is_refused() {
    let generators = medium_generators();
    let refusal = generators
        .words_within(WORD_LENGTH_CEILING)
        .expect_err("two generators over a horizon of 32 name 2^33 words");
    assert!(
        matches!(refusal, StandingRefusal::WordCountCeiling { .. }),
        "got {refusal:?}"
    );
    // And the refusal precedes every allocation: the same family at a modest horizon is fine.
    assert_eq!(
        generators
            .words_within(3)
            .expect("a modest horizon is admitted")
            .len(),
        1 + 2 + 4 + 8
    );
}

#[test]
fn a_word_longer_than_the_ceiling_is_refused() {
    let generators = medium_generators();
    let word = vec![0usize; WORD_LENGTH_CEILING + 1];
    let refusal = generators
        .transport_word(&word, &state(&[(1, 1), (1, 1)]))
        .expect_err("a word past the ceiling is refused");
    assert!(
        matches!(refusal, StandingRefusal::WordLengthCeiling { .. }),
        "got {refusal:?}"
    );
}

#[test]
fn a_generator_that_is_not_square_is_refused() {
    let refusal = GeneratorFamily::declared(
        "not a transport",
        vec!["oblong".to_owned()],
        vec![matrix(&[&[(1, 1), (0, 1), (0, 1)], &[(0, 1), (1, 1), (0, 1)]])],
    )
    .expect_err("a non-square generator is refused");
    assert!(
        matches!(refusal, StandingRefusal::GeneratorShape { .. }),
        "got {refusal:?}"
    );
}

#[test]
fn a_generator_family_whose_names_and_maps_disagree_is_refused() {
    let refusal = GeneratorFamily::declared(
        "mislabelled",
        vec!["one".to_owned(), "two".to_owned()],
        vec![matrix(&[&[(1, 1)]])],
    )
    .expect_err("two names for one map is refused");
    assert!(
        matches!(refusal, StandingRefusal::GeneratorNameCount { .. }),
        "got {refusal:?}"
    );
}

#[test]
fn a_certificate_whose_chart_is_not_invariant_is_refused() {
    // The medium leaks into the wave: `a ↦ a/2 + m`.
    let leaking = GeneratorFamily::declared(
        "a leaking chart",
        vec!["settle".to_owned()],
        vec![matrix(&[
            &[(1, 2), (0, 1), (1, 1)],
            &[(0, 1), (1, 4), (0, 1)],
            &[(0, 1), (1, 4), (1, 1)],
        ])],
    )
    .expect("a declared generator family");
    let refusal = wave_chart()
        .verify(&leaking)
        .expect_err("a chart that is not invariant is refused");
    match refusal {
        StandingRefusal::ChartNotInvariant { row, column, .. } => {
            assert_eq!((row, column), (0, 2));
        }
        other => panic!("got {other:?}"),
    }
}

#[test]
fn a_certificate_that_does_not_contract_is_refused() {
    let generators = fossil_generators();
    let too_tight =
        ContractionCertificate::declared(vec![0, 1], rat(1, 4), 3).expect("a declared certificate");
    let refusal = too_tight
        .verify(&generators)
        .expect_err("the amplitude row sums to 1/2, not 1/4");
    match refusal {
        StandingRefusal::ChartDoesNotContract { row, ref sum, .. } => {
            assert_eq!(row, 0);
            assert_eq!(sum, "1/2");
        }
        other => panic!("got {other:?}"),
    }
}

#[test]
fn a_factor_outside_the_unit_interval_is_refused() {
    for (numerator, denominator) in [(-1i64, 2i64), (3, 2)] {
        let refusal = ContractionCertificate::declared(vec![0], rat(numerator, denominator), 3)
            .expect_err("a factor outside [0, 1] is refused");
        assert!(
            matches!(refusal, StandingRefusal::FactorOutsideUnitInterval { .. }),
            "got {refusal:?}"
        );
    }
}

#[test]
fn a_chart_naming_a_coordinate_outside_the_extent_is_refused() {
    let refusal = ContractionCertificate::declared(vec![0, 7], rat(1, 2), 3)
        .expect_err("coordinate 7 is outside an extent of 3");
    assert!(
        matches!(refusal, StandingRefusal::ChartOutsideExtent { .. }),
        "got {refusal:?}"
    );
    let repeated = ContractionCertificate::declared(vec![1, 1], rat(1, 2), 3)
        .expect_err("a repeated coordinate is refused");
    assert!(
        matches!(repeated, StandingRefusal::ChartRepeatsCoordinate { .. }),
        "got {repeated:?}"
    );
}

#[test]
fn a_negative_tolerance_is_refused() {
    let generators = fossil_generators();
    let refusal = extinction(
        &generators,
        &[amplitude_reading()],
        &fossil_state(3),
        &fossil_rest(),
        1,
        &rat(-1, 8),
        None,
    )
    .expect_err("a negative tolerance is not a tolerance");
    assert!(
        matches!(refusal, StandingRefusal::NegativeTolerance { .. }),
        "got {refusal:?}"
    );
}

/// The search performs one exact width per (word, receiver) pair. That product is what a hostile
/// pair of declarations buys, and it is refused before the first word is transported.
#[test]
fn a_search_product_past_the_work_ceiling_is_refused() {
    let generators = medium_generators();
    // 16383 words over 32 receivers is 524256 exact widths, past the ceiling of 262144.
    let receivers = vec![state_reading(); 32];
    let refusal = extinction(
        &generators,
        &receivers,
        &state(&[(1, 1), (1, 1)]),
        &state(&[(0, 1), (0, 1)]),
        13,
        &integer(1),
        None,
    )
    .expect_err("16383 words over 32 receivers is past the search work ceiling");
    assert!(
        matches!(refusal, StandingRefusal::SearchWorkCeiling { .. }),
        "got {refusal:?}"
    );
    // And a search inside the ceiling still runs.
    assert!(
        extinction(
            &generators,
            &receivers,
            &state(&[(1, 1), (1, 1)]),
            &state(&[(0, 1), (0, 1)]),
            2,
            &integer(64),
            None,
        )
        .is_ok()
    );
}

#[test]
fn an_empty_receiver_family_is_refused() {
    let generators = fossil_generators();
    let refusal = extinction(
        &generators,
        &[],
        &fossil_state(3),
        &fossil_rest(),
        1,
        &integer(1),
        None,
    )
    .expect_err("an empty receiver family declares nothing extinct");
    assert!(
        matches!(refusal, StandingRefusal::EmptyReceiverFamily),
        "got {refusal:?}"
    );
}

#[test]
fn an_extent_mismatch_between_a_standing_and_its_population_is_refused() {
    let population =
        SourcePopulation::declared("three wide", vec![state(&[(1, 1), (1, 1), (1, 1)])])
            .expect("a declared population");
    let standing =
        StandingLaw::declared("two wide", matrix(&[&[(1, 1), (0, 1)]])).expect("a standing");
    let refusal = fidelity(&standing, &state_reading(), &population)
        .expect_err("a two-wide standing cannot read a three-wide lineage");
    assert!(
        matches!(refusal, StandingRefusal::ExtentMismatch { .. }),
        "got {refusal:?}"
    );
}

#[test]
fn a_population_with_ragged_members_is_refused() {
    let refusal = SourcePopulation::declared(
        "ragged",
        vec![state(&[(1, 1), (1, 1)]), state(&[(1, 1)])],
    )
    .expect_err("members of different extents are refused");
    assert!(
        matches!(refusal, StandingRefusal::ExtentMismatch { .. }),
        "got {refusal:?}"
    );
}

#[test]
fn a_word_naming_an_absent_generator_is_refused() {
    let generators = fossil_generators();
    let refusal = generators
        .transport_word(&[3], &fossil_origin())
        .expect_err("generator 3 is absent from a family of one");
    assert!(
        matches!(refusal, StandingRefusal::GeneratorAbsent { .. }),
        "got {refusal:?}"
    );
}
