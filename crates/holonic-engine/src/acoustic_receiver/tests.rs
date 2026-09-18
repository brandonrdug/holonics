//! The acoustic receiver's own checks.
//!
//! Every law the Lean owner states — the exact Cayley law and its totality, stability preservation,
//! causality, superposition through the bank, the two ordering counterexamples, the declared
//! energy's monotonicity, the rate-form tie, the exact pole factor, and the two separations that
//! make colour and timbre two receivers of one source — is checked here on exact synthetic banks
//! that need no fixture and run everywhere. Hostile declarations get their own tests. The measured
//! M5 reading comes last: it refuses rather than passes when the authenticated release is absent,
//! and it is marked and ignored by default because the exact spectral isolation behind it costs
//! seconds per structure.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::EventId;
use crate::algebraic::{CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex};
use crate::hodge_receiver::{
    BoundaryCondition, DEFAULT_ISOLATION_DEPTH, ExactHodgeSpectrum, HodgeOperator,
    MetricDeclaration, exact_hodge_spectrum, refine_spectral_gap,
};
use crate::inertia::inertia;

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(integer(real), integer(imaginary))
}

fn mode(id: u64) -> DimensionalWaveModeId {
    DimensionalWaveModeId(id)
}

fn population(entries: &[(u64, i64, i64)]) -> ExactReceiverPhasePopulation {
    let mut carried = ExactReceiverPhasePopulation::default();
    for (id, real, imaginary) in entries {
        carried.receive(mode(*id), &current(*real, *imaginary));
    }
    carried
}

fn exact_source(source: &str) -> RateProvenance {
    RateProvenance::Exact {
        source: source.to_owned(),
    }
}

/// Two bands consuming two declared modes, one dissipating and one exactly on the axis.
///
/// Band `low` has `γ = 1/2`, `Ω = 1`; band `axis` has `γ = 0`, `Ω = 2` and is the conservative
/// control. Band `low` consumes mode `1` only, band `axis` consumes mode `2` only, so the two
/// modes are separated by the coupling in exactly the way the colour law cannot separate them.
fn worked_bank() -> ResonatorBank {
    let bands = vec![
        Resonator::declared(
            "low",
            ratio(1, 2),
            integer(1),
            exact_source("declared worked band, this test module"),
        )
        .expect("the band declares"),
        Resonator::declared(
            "axis",
            Rat::zero(),
            integer(2),
            exact_source("declared worked band, this test module"),
        )
        .expect("the band declares"),
    ];
    let coupling = ModalCoupling::declared(
        vec![mode(1), mode(2)],
        vec![
            vec![Rat::one(), Rat::zero()],
            vec![Rat::zero(), Rat::one()],
        ],
    )
    .expect("the coupling declares");
    ResonatorBank::declared(
        "worked-two-band",
        ratio(1, 4),
        bands,
        coupling,
        vec![current(1, 0), current(1, 0)],
        vec![Rat::one(), Rat::one()],
    )
    .expect("the bank declares")
}

/// One band consuming mode `1` and **not** mode `3`. Mode `3` is the uncoupled mode that makes a
/// unison look different.
fn one_band_two_modes() -> ResonatorBank {
    let bands = vec![
        Resonator::declared(
            "single",
            ratio(1, 3),
            integer(1),
            exact_source("declared single band, this test module"),
        )
        .expect("the band declares"),
    ];
    let coupling =
        ModalCoupling::declared(vec![mode(1), mode(3)], vec![vec![Rat::one(), Rat::zero()]])
            .expect("the coupling declares");
    ResonatorBank::declared(
        "worked-one-band",
        ratio(1, 2),
        bands,
        coupling,
        vec![current(1, 0)],
        vec![Rat::one()],
    )
    .expect("the bank declares")
}

/// A bank declared over **wide** exact rationals: `γ` and `Ω` are ratios of three-hundred-bit
/// integers. Every ceiling on the *count* of anything admits it — one band, one mode, a positive
/// step — and its exact state gains thousands of bits per step, which is what the projected-work
/// bound is for.
fn wide_rational_bank() -> ResonatorBank {
    let wide = |offset: i64| {
        let base: BigInt = BigInt::from(1u8) << 300u32;
        Rat::new(base.clone(), base + BigInt::from(offset))
    };
    let bands = vec![
        Resonator::declared(
            "wide",
            wide(1),
            wide(3),
            exact_source("declared wide-rational band, this test module"),
        )
        .expect("the band declares"),
    ];
    let coupling = ModalCoupling::declared(vec![mode(1)], vec![vec![Rat::one()]])
        .expect("the coupling declares");
    ResonatorBank::declared(
        "wide-rational",
        ratio(1, 4),
        bands,
        coupling,
        vec![current(1, 0)],
        vec![Rat::one()],
    )
    .expect("the bank declares")
}

fn doctrine() -> ExactReceiverPrimaryDoctrine {
    ExactReceiverPrimaryDoctrine::new(Rat::one(), Rat::zero()).expect("the doctrine declares")
}

// ---------------------------------------------------------------------------------------------
// the exact discrete law
// ---------------------------------------------------------------------------------------------

/// The Rust equivalent of the Lean `cayley`/`gain` definitions, checked by hand on a band whose
/// arithmetic closes in small rationals. With `h = 1/4`, `γ = 1/2`, `Ω = 1`:
/// `hλ = (−1/8, 1/4)`, so `2 + hλ = (15/8, 1/4)` and `2 − hλ = (17/8, −1/4)`.
#[test]
fn the_declared_law_is_the_exact_cayley_map_of_the_pole() {
    let bank = worked_bank();
    let numerator = current(0, 0)
        .add(&ExactComplexWaveCurrent::new(ratio(15, 8), ratio(1, 4)));
    let denominator = ExactComplexWaveCurrent::new(ratio(17, 8), ratio(-1, 4));
    let expected = numerator.multiply(&denominator.reciprocal().expect("the denominator inverts"));
    assert_eq!(bank.transition(0).expect("the transition returns"), expected);
    let gain = ExactComplexWaveCurrent::new(ratio(1, 4), Rat::zero())
        .multiply(&denominator.reciprocal().expect("the denominator inverts"));
    assert_eq!(bank.gain(0).expect("the gain returns"), gain);
}

/// Lean: `normSq_cayley_lt_one` and `normSq_cayley_eq_one`. The discrete reading and R1's
/// continuous half-plane reading are held to **exact** agreement band by band; neither is a
/// tolerance and neither is derived from the other.
#[test]
fn the_left_half_plane_maps_inside_the_unit_disc() {
    let bank = worked_bank();
    let stability = bank.stability().expect("the stability reading returns");
    assert_eq!(stability.len(), 2);
    for band in &stability {
        assert_eq!(
            band.inside_unit_disc, band.continuous_left_half_plane,
            "band {} disagrees between the discrete and continuous readings",
            band.name
        );
        assert_eq!(band.on_unit_circle, band.continuous_on_axis);
    }
    assert!(stability[0].inside_unit_disc);
    assert!(stability[0].transition_norm_square < Rat::one());
    assert!(stability[1].on_unit_circle);
    assert_eq!(stability[1].transition_norm_square, Rat::one());
}

/// The Cayley denominator's real part is `2 + hγ ≥ 2`, so the law is total for every declared band
/// a validating constructor admits. Lean: `cayley_den_ne_zero`.
#[test]
fn the_cayley_law_is_total_for_every_admitted_band() {
    for (decay, rate, step) in [
        (0, 0, (1, 1)),
        (0, 1_000_000, (1, 1_000_000)),
        (1_000_000, 0, (1_000_000, 1)),
        (3, -7, (11, 13)),
    ] {
        let band = Resonator::declared(
            "total",
            integer(decay),
            integer(rate),
            exact_source("totality sweep"),
        )
        .expect("the band declares");
        let bank = ResonatorBank::declared(
            "totality",
            ratio(step.0, step.1),
            vec![band],
            ModalCoupling::declared(vec![mode(1)], vec![vec![Rat::one()]])
                .expect("the coupling declares"),
            vec![current(1, 0)],
            vec![Rat::one()],
        )
        .expect("the bank declares");
        assert!(bank.transition(0).is_ok());
        assert!(bank.gain(0).is_ok());
    }
}

// ---------------------------------------------------------------------------------------------
// causality and superposition
// ---------------------------------------------------------------------------------------------

/// Lean: `Bank.run_causal`. Two input histories agreeing on the first `n` populations give the
/// same state at step `n`, however they differ afterwards — and they do differ afterwards, which
/// is checked so the test cannot pass vacuously.
#[test]
fn the_state_after_n_steps_ignores_every_later_input() {
    let bank = worked_bank();
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    let shared = population(&[(1, 1, 0), (2, 0, 1)]);
    let divergent = population(&[(1, 5, 3), (2, -2, 7)]);
    let left = vec![shared.clone(), shared.clone(), shared.clone()];
    let right = vec![shared.clone(), shared.clone(), divergent.clone()];
    let left_run = bank.run(&rest, &left[..2]).expect("the run returns");
    let right_run = bank.run(&rest, &right[..2]).expect("the run returns");
    assert_eq!(left_run.state, right_run.state, "the prefix decides the state");
    let left_full = bank.run(&rest, &left).expect("the run returns");
    let right_full = bank.run(&rest, &right).expect("the run returns");
    assert_ne!(
        left_full.state, right_full.state,
        "the later input must actually matter, or this test is vacuous"
    );
}

/// Lean: `Bank.run_add`. Superposition holds **exactly** through the whole bank from rest, at
/// every step, in the state and in the pressure. This is the reading the colour receiver's
/// `ExactReceiverPhasePopulation::receive` makes possible by summing same-mode currents before any
/// quadratic response.
#[test]
fn superposition_holds_through_the_bank() {
    let bank = worked_bank();
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    let left = population(&[(1, 2, -1), (2, 0, 3)]);
    let right = population(&[(1, -5, 4), (2, 7, 1)]);
    let mut joint = left.clone();
    for (id, value) in &right.coherent_modes {
        joint.receive(*id, value);
    }
    let left_run = bank
        .run_held(&rest, &left, 6)
        .expect("the run returns");
    let right_run = bank
        .run_held(&rest, &right, 6)
        .expect("the run returns");
    let joint_run = bank
        .run_held(&rest, &joint, 6)
        .expect("the run returns");
    assert_eq!(
        joint_run.state,
        left_run
            .state
            .superposed(&right_run.state)
            .expect("the states superpose")
    );
    for step in 0..joint_run.pressures.len() {
        assert_eq!(
            joint_run.pressures[step],
            &left_run.pressures[step] + &right_run.pressures[step],
            "the pressure projection is linear at step {step}"
        );
    }
}

/// Lean: `Bank.pressure_add`. The one-dimensional projection is itself linear, which is exactly
/// why it is **not** where the ordering matters.
#[test]
fn the_pressure_projection_is_linear_and_comes_last() {
    let bank = worked_bank();
    let left = BankState::declared(vec![current(3, -1), current(0, 2)]).expect("a state declares");
    let right = BankState::declared(vec![current(-5, 4), current(1, 1)]).expect("a state declares");
    let joint = left.superposed(&right).expect("the states superpose");
    assert_eq!(
        bank.pressure(&joint).expect("the pressure returns"),
        &bank.pressure(&left).expect("the pressure returns")
            + &bank.pressure(&right).expect("the pressure returns")
    );
}

// ---------------------------------------------------------------------------------------------
// why the ordering is law
// ---------------------------------------------------------------------------------------------

/// Lean: `colour_does_not_distribute`. The colour law's quadratic phase response taken **before**
/// superposition returns a different object: this is the cross-term identity
/// `|Σ z_j|² = Σ |z_j|² + 2 Re Σ_{j<k} conj(z_j) z_k`, and what a quantize-first reading discards
/// is the relative phase. The existing law computes the three responses after superposition and
/// only then saturates, and the acoustic receiver respects the same ordering.
#[test]
fn the_colour_law_does_not_distribute_over_superposition() {
    let doctrine = doctrine();
    let left = population(&[(1, 1, 0)]);
    let right = population(&[(1, 1, 0)]);
    let mut joint = left.clone();
    for (id, value) in &right.coherent_modes {
        joint.receive(*id, value);
    }
    let separate_left = doctrine.transduce(&left);
    let separate_right = doctrine.transduce(&right);
    let together = doctrine.transduce(&joint);
    let summed: Vec<Rat> = separate_left
        .primaries
        .iter()
        .zip(separate_right.primaries.iter())
        .map(|(a, b)| a + b)
        .collect();
    assert_ne!(
        together.primaries.to_vec(),
        summed,
        "superpose-then-respond and respond-then-superpose must differ, or the ordering is empty"
    );
    // Cancellation is the sharper face of the same fact: two opposite currents on one mode cancel
    // in the population and give exactly zero response, while their separate responses do not.
    let opposite = population(&[(1, -1, 0)]);
    let mut cancelling = left.clone();
    for (id, value) in &opposite.coherent_modes {
        cancelling.receive(*id, value);
    }
    let cancelled = doctrine.transduce(&cancelling);
    assert_eq!(cancelled.primaries.to_vec(), vec![Rat::zero(); 3]);
    assert_ne!(
        doctrine.transduce(&left).primaries.to_vec(),
        vec![Rat::zero(); 3]
    );
}

/// Lean: `quantize_then_superpose_ne_superpose_then_quantize`. Two pressures of half a quantization
/// step each export as silence; their superposition exports as one step. The export face is
/// therefore produced **last** and never read back.
#[test]
fn quantize_then_superpose_differs_from_superpose_then_quantize() {
    let full_scale = integer(PCM16_PEAK);
    let half = ratio(1, 4);
    let separate = export_pcm16("ordering", 8_000, full_scale.clone(), &[half.clone(), half.clone()])
        .expect("the export returns");
    let together = export_pcm16("ordering", 8_000, full_scale, &[&half + &half])
        .expect("the export returns");
    let summed = i32::from(separate.samples[0]) + i32::from(separate.samples[1]);
    assert_eq!(summed, 0);
    assert_eq!(i32::from(together.samples[0]), 1);
    assert_ne!(summed, i32::from(together.samples[0]));
}

// ---------------------------------------------------------------------------------------------
// energy, the rate form, and the exact pole
// ---------------------------------------------------------------------------------------------

/// Lean: `energy_advance_le`. At zero input the declared energy never rises, and the conservative
/// band conserves it exactly rather than nearly.
#[test]
fn the_declared_energy_is_nonincreasing_at_zero_input() {
    let bank = worked_bank();
    let silence = ExactReceiverPhasePopulation::default();
    let mut state =
        BankState::declared(vec![current(2, 1), current(3, -4)]).expect("a state declares");
    let mut previous = bank.energy(&state).expect("the energy returns");
    for _ in 0..8 {
        state = bank.advance(&state, &silence).expect("the step returns");
        let energy = bank.energy(&state).expect("the energy returns");
        assert!(energy <= previous);
        previous = energy;
    }
    // The conservative band alone conserves the reading exactly.
    let axis_only =
        BankState::declared(vec![current(0, 0), current(3, -4)]).expect("a state declares");
    let advanced = bank
        .advance(&axis_only, &silence)
        .expect("the step returns");
    assert_eq!(
        bank.energy(&advanced).expect("the energy returns"),
        bank.energy(&axis_only).expect("the energy returns")
    );
}

/// Lean: `energy_advance_lt`. A band with positive decay strictly dissipates, exactly.
#[test]
fn positive_decay_strictly_dissipates() {
    let bank = worked_bank();
    let silence = ExactReceiverPhasePopulation::default();
    let excited =
        BankState::declared(vec![current(2, 1), current(0, 0)]).expect("a state declares");
    let advanced = bank.advance(&excited, &silence).expect("the step returns");
    assert!(
        bank.energy(&advanced).expect("the energy returns")
            < bank.energy(&excited).expect("the energy returns")
    );
}

/// Lean: `rateForm_realBlock`. The continuous rate form at the declared energy metric is exactly
/// `diag(−2 γ_b e_b)` over both quadratures, and its inertia is negative on the dissipating band
/// and null on the conservative one. The rate form is taken through
/// `causal_chord::rate_form`, and the signature through `inertia::inertia`; neither is rebuilt.
#[test]
fn the_band_rate_form_is_minus_twice_the_decay() {
    let bank = worked_bank();
    let form = bank.rate_form().expect("the rate form returns");
    assert_eq!(form.extent(), 4);
    for band in 0..2 {
        let expected = integer(-2) * bank.bands()[band].decay() * &bank.energy_weights()[band];
        assert_eq!(*form.at(2 * band, 2 * band), expected);
        assert_eq!(*form.at(2 * band + 1, 2 * band + 1), expected);
        assert_eq!(*form.at(2 * band, 2 * band + 1), Rat::zero());
        assert_eq!(*form.at(2 * band + 1, 2 * band), Rat::zero());
    }
    let signature = inertia(&form);
    assert_eq!(signature.negative, 2, "the dissipating band contributes two negative directions");
    assert_eq!(signature.zero, 2, "the conservative band contributes two null directions");
    assert_eq!(signature.positive, 0, "no band grows");
}

/// Lean: `charpoly_realBlock`. Each band's pole is named by the exact rational factor
/// `X² + 2γX + (γ² + Ω²)`, so the chord's pole atlas accounts for exactly the declared bands.
#[test]
fn each_band_names_its_pole_by_an_exact_factor() {
    let bank = worked_bank();
    let chord = bank.chord(PoleReading::Named).expect("the chord returns");
    let characteristic = chord.characteristic();
    let product = bank.bands()[0]
        .characteristic_factor()
        .times(&bank.bands()[1].characteristic_factor());
    assert_eq!(characteristic.made_monic(), product.made_monic());
    assert_eq!(chord.extent, 4);
}

/// The R1 contract, executed: **every audible component carries its source mode, its excitation,
/// its transport path, its approximation error and its residual**, and the band whose exact pole
/// factor it is.
#[test]
fn every_audible_component_carries_the_r1_contract() {
    let bank = worked_bank();
    let components = bank
        .audible_components(PoleReading::Named)
        .expect("the components return");
    assert!(!components.is_empty());
    let mut named_bands = BTreeSet::new();
    for audible in &components {
        assert!(audible.mode.is_some(), "every excitation column names a declared mode");
        assert_eq!(audible.component.receiver_name, "pressure");
        assert_eq!(audible.component.transport_path, 0);
        assert!(audible.component.residual.is_zero(), "the residual is exactly zero");
        assert!(
            matches!(
                audible.component.approximation_error,
                crate::causal_chord::ApproximationError::Exact
                    | crate::causal_chord::ApproximationError::FactorOnly
            ),
            "an exact factor or a named factor, never an unstated approximation"
        );
        assert!(
            audible
                .component
                .source_name
                .starts_with(&format!("mode {}", audible.mode.expect("named").0)),
            "the source name carries the declared mode"
        );
        if let Some(band) = &audible.band {
            named_bands.insert(band.clone());
        }
    }
    assert_eq!(
        named_bands,
        BTreeSet::from(["low".to_owned(), "axis".to_owned()]),
        "both declared bands are reached by some audible component"
    );
}

/// **Two bands with mirror-signed `Ω` carry the identical characteristic factor and must still be
/// told apart.** The factor is `X² + 2γX + (γ² + Ω²)` and sees `Ω` only through `Ω²`, so `up` and
/// `down` below are polynomially indistinguishable. The block-diagonal structure distinguishes them
/// exactly: mode `1` drives only `up`'s block and mode `2` only `down`'s, and the excitation column
/// names the mode. The rule this replaces — the first band whose factor equals the component's pole
/// factor — hands **both** components the name `up`, and the last assertion here exhibits that.
#[test]
fn mirror_bands_are_attributed_by_block_and_not_by_polynomial_equality() {
    let bands = vec![
        Resonator::declared("up", ratio(1, 2), integer(1), exact_source("mirror pair"))
            .expect("the band declares"),
        Resonator::declared("down", ratio(1, 2), integer(-1), exact_source("mirror pair"))
            .expect("the band declares"),
    ];
    assert_ne!(bands[0].rate(), bands[1].rate(), "the two bands are distinct");
    assert_eq!(
        bands[0].characteristic_factor().made_monic(),
        bands[1].characteristic_factor().made_monic(),
        "and their exact pole factors are equal, so polynomial equality cannot separate them"
    );
    let coupling = ModalCoupling::declared(
        vec![mode(1), mode(2)],
        vec![
            vec![Rat::one(), Rat::zero()],
            vec![Rat::zero(), Rat::one()],
        ],
    )
    .expect("the coupling declares");
    let bank = ResonatorBank::declared(
        "mirror-pair",
        ratio(1, 4),
        bands,
        coupling,
        vec![current(1, 0), current(1, 0)],
        vec![Rat::one(), Rat::one()],
    )
    .expect("the bank declares");

    let components = bank
        .audible_components(PoleReading::Named)
        .expect("the components return");
    assert!(!components.is_empty());
    let mut reached = BTreeSet::new();
    for audible in &components {
        let declared = audible.mode.expect("every excitation column names a declared mode");
        let (expected_name, expected_index) = if declared == mode(1) {
            ("up", 0)
        } else {
            assert_eq!(declared, mode(2));
            ("down", 1)
        };
        assert_eq!(
            audible.originating_bands,
            vec![expected_index],
            "exactly one block drives this column at a nonzero kappa and carries this factor"
        );
        assert_eq!(audible.band_index, Some(expected_index));
        assert_eq!(
            audible.band.as_deref(),
            Some(expected_name),
            "the component out of block {expected_index} is attributed to that block's band"
        );
        reached.insert(expected_name.to_owned());
    }
    assert_eq!(
        reached,
        BTreeSet::from(["up".to_owned(), "down".to_owned()]),
        "both mirror bands are reached"
    );

    // The superseded rule, executed here so the difference is exhibited and not merely described:
    // matching the pole factor against the band list returns `up` for a component that came out of
    // `down`'s block. Under that rule this test's `assert_eq!` on the name above cannot pass.
    let from_down = components
        .iter()
        .find(|audible| audible.band.as_deref() == Some("down"))
        .expect("some component comes out of the second block");
    let aliased = bank
        .bands()
        .iter()
        .find(|band| {
            band.characteristic_factor().made_monic()
                == from_down.component.pole_factor.made_monic()
        })
        .expect("some band carries that factor");
    assert_eq!(
        aliased.name(),
        "up",
        "polynomial equality aliases the mirror pair onto the first band"
    );
}

// ---------------------------------------------------------------------------------------------
// one lineage: two receivers of one source
// ---------------------------------------------------------------------------------------------

/// Lean: `metamer_sounds_different`. Exchanging which of two co-present modes carries which
/// quadrature is **invisible** to the colour law — it accumulates its quadratic response across
/// modes — and plainly audible to a bank that couples the two modes to different resonators.
/// Equal colour does not imply equal timbre.
#[test]
fn metamers_sound_different() {
    let bank = worked_bank();
    let doctrine = doctrine();
    let left = population(&[(1, 1, 0), (2, 0, 1)]);
    let right = population(&[(1, 0, 1), (2, 1, 0)]);
    let left_reading = joint_reading(&bank, &doctrine, &left, 3).expect("the reading returns");
    let right_reading = joint_reading(&bank, &doctrine, &right, 3).expect("the reading returns");
    assert_eq!(
        left_reading.colour, right_reading.colour,
        "the two populations are colour metamers"
    );
    assert_ne!(
        left_reading.acoustic.state, right_reading.acoustic.state,
        "and the bank tells them apart"
    );
}

/// Lean: `unison_looks_different`. Current on a mode no resonator couples to is exactly invisible
/// to the bank and plainly visible to colour. Equal timbre does not imply equal colour, and the
/// bank **reports** the mode it does not consume rather than dropping it.
#[test]
fn unisons_look_different() {
    let bank = one_band_two_modes();
    let doctrine = doctrine();
    let bare = population(&[(1, 1, 0)]);
    let decorated = population(&[(1, 1, 0), (3, 1, 0)]);
    let bare_reading = joint_reading(&bank, &doctrine, &bare, 4).expect("the reading returns");
    let decorated_reading =
        joint_reading(&bank, &doctrine, &decorated, 4).expect("the reading returns");
    assert_eq!(
        bare_reading.acoustic.state, decorated_reading.acoustic.state,
        "the two populations are acoustic unisons"
    );
    assert_ne!(
        bare_reading.colour, decorated_reading.colour,
        "and colour tells them apart"
    );
    assert_eq!(
        decorated_reading.acoustic.unconsumed_modes,
        vec![mode(3)],
        "the mode the bank cannot hear is reported, never dropped"
    );
    assert!(bare_reading.acoustic.unconsumed_modes.is_empty());
}

/// Lean: `population_change_moves_both`. The two readings are maps out of one type, so a change of
/// the population generally moves both.
#[test]
fn a_change_of_population_moves_both_receivers() {
    let bank = worked_bank();
    let doctrine = doctrine();
    let before = joint_reading(&bank, &doctrine, &population(&[(1, 1, 0)]), 3)
        .expect("the reading returns");
    let after = joint_reading(&bank, &doctrine, &population(&[(1, 2, 0)]), 3)
        .expect("the reading returns");
    assert_ne!(before.colour, after.colour);
    assert_ne!(before.acoustic.state, after.acoustic.state);
    assert_eq!(
        before.population.coherent_modes.keys().collect::<Vec<_>>(),
        after.population.coherent_modes.keys().collect::<Vec<_>>(),
        "both readings are taken from one carried population and its own mode identities"
    );
}

// ---------------------------------------------------------------------------------------------
// hostile declarations
// ---------------------------------------------------------------------------------------------

#[test]
fn a_growing_band_is_refused_by_name() {
    let refusal = Resonator::declared(
        "growing",
        integer(-1),
        integer(1),
        exact_source("hostile"),
    )
    .expect_err("a negative decay is refused");
    assert!(matches!(refusal, AcousticRefusal::NegativeDecay { .. }));
}

#[test]
fn an_unsourced_or_unnamed_declaration_is_refused() {
    assert!(matches!(
        Resonator::declared("", Rat::zero(), Rat::zero(), exact_source("s"))
            .expect_err("an unnamed band is refused"),
        AcousticRefusal::UnnamedResonator
    ));
    assert!(matches!(
        Resonator::declared("b", Rat::zero(), Rat::zero(), exact_source(""))
            .expect_err("an unsourced rate is refused"),
        AcousticRefusal::UnsourcedRate { .. }
    ));
}

/// A rate declared as an isolating-interval readout is **checked** against that interval's
/// midpoint. An irrational eigenvalue has no rational value, so a readout that is not the readout
/// it claims to be is refused rather than carried.
#[test]
fn a_readout_that_is_not_its_intervals_midpoint_is_refused() {
    let interval = ExactInterval::new(ratio(1, 2), ratio(3, 2)).expect("the interval declares");
    let honest = Resonator::declared(
        "readout",
        Rat::one(),
        Rat::one(),
        RateProvenance::IsolatingIntervalMidpoint {
            source: "R3 exact Hodge spectrum".to_owned(),
            interval: interval.clone(),
        },
    )
    .expect("the honest readout declares");
    assert!(honest.provenance().is_readout());
    assert_eq!(honest.provenance().interval(), Some(&interval));
    let refusal = Resonator::declared(
        "readout",
        Rat::one(),
        integer(7),
        RateProvenance::IsolatingIntervalMidpoint {
            source: "R3 exact Hodge spectrum".to_owned(),
            interval,
        },
    )
    .expect_err("a mismatched readout is refused");
    assert!(matches!(refusal, AcousticRefusal::MidpointDisagrees { .. }));
}

#[test]
fn a_non_positive_step_is_refused_by_name() {
    let bands = vec![
        Resonator::declared("b", Rat::zero(), Rat::one(), exact_source("s"))
            .expect("the band declares"),
    ];
    let coupling = ModalCoupling::declared(vec![mode(1)], vec![vec![Rat::one()]])
        .expect("the coupling declares");
    for step in [Rat::zero(), integer(-1)] {
        let refusal = ResonatorBank::declared(
            "hostile",
            step,
            bands.clone(),
            coupling.clone(),
            vec![current(1, 0)],
            vec![Rat::one()],
        )
        .expect_err("a non-positive step is refused");
        assert!(matches!(refusal, AcousticRefusal::NonPositiveStep { .. }));
    }
}

#[test]
fn mismatched_declared_shapes_are_refused_by_name() {
    let bands = vec![
        Resonator::declared("b", Rat::zero(), Rat::one(), exact_source("s"))
            .expect("the band declares"),
    ];
    let coupling = ModalCoupling::declared(vec![mode(1)], vec![vec![Rat::one()]])
        .expect("the coupling declares");
    assert!(matches!(
        ResonatorBank::declared(
            "hostile",
            Rat::one(),
            bands.clone(),
            coupling.clone(),
            vec![current(1, 0), current(1, 0)],
            vec![Rat::one()],
        )
        .expect_err("a mismatched pressure count is refused"),
        AcousticRefusal::PressureWeightCount { .. }
    ));
    assert!(matches!(
        ResonatorBank::declared(
            "hostile",
            Rat::one(),
            bands.clone(),
            coupling.clone(),
            vec![current(1, 0)],
            vec![Rat::one(), Rat::one()],
        )
        .expect_err("a mismatched energy count is refused"),
        AcousticRefusal::EnergyWeightCount { .. }
    ));
    assert!(matches!(
        ResonatorBank::declared(
            "hostile",
            Rat::one(),
            bands,
            coupling,
            vec![current(1, 0)],
            vec![Rat::zero()],
        )
        .expect_err("a non-positive energy weight is refused"),
        AcousticRefusal::NonPositiveEnergyWeight { .. }
    ));
}

#[test]
fn hostile_couplings_are_refused_by_name() {
    assert!(matches!(
        ModalCoupling::declared(vec![mode(1), mode(1)], vec![vec![Rat::one(), Rat::one()]])
            .expect_err("a repeated mode is refused"),
        AcousticRefusal::DuplicateMode
    ));
    assert!(matches!(
        ModalCoupling::declared(vec![mode(1), mode(2)], vec![vec![Rat::one()]])
            .expect_err("a short row is refused"),
        AcousticRefusal::CouplingRowShape { .. }
    ));
    assert!(matches!(
        ModalCoupling::declared(Vec::new(), vec![vec![Rat::one()]])
            .expect_err("an empty coupling is refused"),
        AcousticRefusal::EmptyCoupling
    ));
    let wide: Vec<DimensionalWaveModeId> =
        (0..=MODE_CEILING as u64).map(DimensionalWaveModeId).collect();
    let row = vec![Rat::zero(); wide.len()];
    assert!(matches!(
        ModalCoupling::declared(wide, vec![row]).expect_err("an over-wide coupling is refused"),
        AcousticRefusal::ModePopulationAboveCeiling { .. }
    ));
}

/// Every declared count is checked against its ceiling **before** anything is allocated from it.
#[test]
fn declared_counts_are_bounded_before_they_are_used() {
    assert!(matches!(
        BankState::rest(BAND_CEILING + 1).expect_err("an over-wide rest state is refused"),
        AcousticRefusal::BandPopulationAboveCeiling { .. }
    ));
    let bank = worked_bank();
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    assert!(matches!(
        bank.run_held(&rest, &ExactReceiverPhasePopulation::default(), STEP_CEILING + 1)
            .expect_err("an over-long run is refused"),
        AcousticRefusal::RunAboveCeiling { .. }
    ));
    assert!(matches!(
        export_pcm16("x", 0, Rat::one(), &[]).expect_err("a zero sample rate is refused"),
        AcousticRefusal::ZeroSampleRate
    ));
    assert!(matches!(
        export_pcm16("x", 8_000, Rat::zero(), &[])
            .expect_err("a non-positive full scale is refused"),
        AcousticRefusal::NonPositiveFullScale { .. }
    ));
}

/// **A run far under [`STEP_CEILING`] is still refused, by the work it projects.** The step ceiling
/// bounds the retained trace and nothing else: the exact state gains a whole Cayley coefficient's
/// bit length at every step, so the arithmetic is quadratic in the length and a declaration inside
/// the step ceiling can be hours of work. [`STEP_WORK_CEILING`] is what refuses it, before the loop
/// runs and before anything is allocated from the declared count.
#[test]
fn a_run_under_the_step_ceiling_is_refused_by_the_projected_work() {
    let bank = worked_bank();
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    let step_bits = bank.step_bit_length().expect("the projection returns");
    assert!(step_bits > 0, "a declared step carries some arithmetic");

    // Well inside STEP_CEILING, and far past the measured five-second run.
    let long = 16_384u64;
    assert!(long < STEP_CEILING, "the step ceiling admits this declaration");
    assert!(
        bank.projected_run_work(&rest, long)
            .expect("the projection returns")
            > STEP_WORK_CEILING
    );
    let refusal = bank
        .run_held(&rest, &population(&[(1, 1, 0)]), long)
        .expect_err("a long exact run is refused by its projected work");
    assert!(
        matches!(refusal, AcousticRefusal::RunWorkAboveCeiling { steps, .. } if steps == long),
        "{refusal}"
    );

    // A normal run is admitted and returns exactly what it returned before the bound existed.
    assert!(
        bank.projected_run_work(&rest, 8).expect("the projection returns") <= STEP_WORK_CEILING
    );
    let admitted = bank
        .run_held(&rest, &population(&[(1, 1, 0)]), 8)
        .expect("a short run is still admitted");
    assert_eq!(admitted.steps, 8);
    assert_eq!(admitted.pressures.len(), 9);
    let history = vec![population(&[(1, 1, 0)]); 4];
    assert!(bank.run(&rest, &history).is_ok());

    // **The bound is on the work and not on the step count.** A bank declared over wide rationals
    // is refused at a length the narrow bank is admitted at, through the same ceiling.
    let wide = wide_rational_bank();
    let wide_rest = BankState::rest(wide.band_count()).expect("the rest state exists");
    let wide_bits = wide.step_bit_length().expect("the projection returns");
    assert!(
        wide_bits > 100 * step_bits,
        "the wide bank's declared rationals are wide: {wide_bits} bits against {step_bits}"
    );
    assert!(
        bank.projected_run_work(&rest, 512).expect("the projection returns") <= STEP_WORK_CEILING,
        "the narrow bank is admitted at five hundred and twelve steps"
    );
    // The ceiling's stated measured basis, held to the constant rather than left in prose: on this
    // bank the run that took about five seconds is admitted and the one that took about
    // thirty-three seconds is refused.
    assert_eq!(step_bits, 17, "the worked bank's widest Cayley coefficient");
    assert!(
        bank.projected_run_work(&rest, 1_024).expect("the projection returns") <= STEP_WORK_CEILING,
        "the measured five-second run stays admitted"
    );
    assert!(
        bank.projected_run_work(&rest, 2_048).expect("the projection returns") > STEP_WORK_CEILING,
        "the measured thirty-three-second run is refused"
    );
    assert!(matches!(
        wide.run_held(&wide_rest, &population(&[(1, 1, 0)]), 512)
            .expect_err("the wide bank is refused at the same length"),
        AcousticRefusal::RunWorkAboveCeiling { .. }
    ));
    // The declared-history entry point is admitted through the same bound.
    let wide_history = vec![population(&[(1, 1, 0)]); 512];
    assert!(matches!(
        wide.run(&wide_rest, &wide_history)
            .expect_err("a declared history is bounded by the same projection"),
        AcousticRefusal::RunWorkAboveCeiling { .. }
    ));
}

/// The exact chord of a wide bank is refused by name rather than left running.
#[test]
fn a_wide_bank_refuses_the_exact_chord_rather_than_running() {
    let width = CHORD_EXTENT_CEILING / 2 + 1;
    let bands: Vec<Resonator> = (0..width)
        .map(|at| {
            Resonator::declared(
                format!("band{at}"),
                Rat::one(),
                integer(at as i64 + 1),
                exact_source("width sweep"),
            )
            .expect("the band declares")
        })
        .collect();
    let coupling = ModalCoupling::declared(
        vec![mode(1)],
        (0..width).map(|_| vec![Rat::one()]).collect(),
    )
    .expect("the coupling declares");
    let bank = ResonatorBank::declared(
        "wide",
        Rat::one(),
        bands,
        coupling,
        vec![current(1, 0); width],
        vec![Rat::one(); width],
    )
    .expect("the bank declares");
    assert!(matches!(
        bank.chord(PoleReading::Named)
            .expect_err("a wide chord is refused"),
        AcousticRefusal::ChordExtentAboveCeiling { .. }
    ));
    // The bank itself still runs: the ceiling is on the exact chord, not on the receiver.
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    assert!(bank.run_held(&rest, &population(&[(1, 1, 0)]), 2).is_ok());
}

/// A state of the wrong width is refused by name at every entry point that consumes one.
#[test]
fn a_mismatched_state_is_refused_at_every_entry_point() {
    let bank = worked_bank();
    let narrow = BankState::declared(vec![current(1, 0)]).expect("a state declares");
    assert!(matches!(
        bank.pressure(&narrow).expect_err("a narrow state is refused"),
        AcousticRefusal::StateShape { .. }
    ));
    assert!(matches!(
        bank.energy(&narrow).expect_err("a narrow state is refused"),
        AcousticRefusal::StateShape { .. }
    ));
    assert!(matches!(
        bank.advance(&narrow, &ExactReceiverPhasePopulation::default())
            .expect_err("a narrow state is refused"),
        AcousticRefusal::StateShape { .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// the exterior export face
// ---------------------------------------------------------------------------------------------

/// The export is integers and an exact rational residual enclosure. There is no float in it, and
/// nothing reads it back.
#[test]
fn the_export_face_is_integer_and_carries_its_exact_residual() {
    let full_scale = Rat::one();
    let pressures = vec![
        Rat::zero(),
        ratio(1, 2),
        ratio(-1, 2),
        Rat::one(),
        integer(-1),
        integer(3),
    ];
    let face = export_pcm16("export", 8_000, full_scale.clone(), &pressures)
        .expect("the export returns");
    assert_eq!(face.samples().len(), pressures.len());
    assert_eq!(face.samples()[0], 0);
    assert_eq!(face.samples()[3], PCM16_PEAK as i16);
    assert_eq!(face.clipped(), 1, "the pressure of three saturates and says so");
    // A saturating pressure's residual is outside the quantization step by construction, and the
    // enclosure says so rather than hiding it: three saturates at one, so the residual reaches two.
    assert_eq!(face.residual_enclosure().upper, integer(2));
    // Without the saturating sample every residual lies inside half a quantization step, exactly.
    let step = &full_scale / integer(PCM16_PEAK);
    let half_step = &step / integer(2);
    let unclipped = export_pcm16("export", 8_000, full_scale, &pressures[..5])
        .expect("the export returns");
    assert_eq!(unclipped.clipped(), 0);
    assert!(unclipped.residual_enclosure().upper <= half_step);
    assert!(unclipped.residual_enclosure().lower >= -half_step);
    assert!(unclipped.residual_enclosure().lower <= unclipped.residual_enclosure().upper);
}

/// **An export face above [`SAMPLE_CEILING`] is unconstructible, not merely unchecked.** The type's
/// fields are private, it derives `Serialize` and not `Deserialize`, and it has no `Default`, no
/// second constructor and no mutator, so [`export_pcm16`] — which refuses the declared population
/// before it allocates — is the only way a face comes into existence. That is why [`wav_bytes`]
/// carries no second ceiling: it cannot be handed a face that has not already passed this one.
#[test]
fn a_face_above_the_sample_ceiling_cannot_be_produced() {
    let over = vec![Rat::zero(); SAMPLE_CEILING + 1];
    let refusal = export_pcm16("over", 8_000, Rat::one(), &over)
        .expect_err("a declared sample population above the ceiling is refused");
    assert!(
        matches!(
            refusal,
            AcousticRefusal::SamplePopulationAboveCeiling { declared, ceiling }
                if declared == SAMPLE_CEILING + 1 && ceiling == SAMPLE_CEILING
        ),
        "{refusal}"
    );
    // Every face that does exist respects the ceiling, and the encoder reads it through the
    // accessor rather than a public field.
    let face = export_pcm16("under", 8_000, Rat::one(), &[Rat::zero(), ratio(1, 2)])
        .expect("the export returns");
    assert!(face.samples().len() <= SAMPLE_CEILING);
    assert_eq!(face.schema(), PRESSURE_EXPORT_SCHEMA);
    assert_eq!(face.lineage(), "under");
    assert_eq!(wav_bytes(&face).expect("the document returns").len(), 44 + 4);
}

/// A declared sample rate that overflows the RIFF byte rate is refused **by its own name**. It is
/// not a zero sample rate, and reporting it as one named the wrong defect.
#[test]
fn a_sample_rate_that_overflows_the_byte_rate_refuses_by_its_own_name() {
    let face = export_pcm16("fast", u32::MAX, Rat::one(), &[Rat::zero()])
        .expect("a large declared sample rate is still a face");
    assert_eq!(face.sample_rate(), u32::MAX);
    let refusal = wav_bytes(&face).expect_err("the RIFF byte rate overflows");
    assert!(
        matches!(
            refusal,
            AcousticRefusal::SampleRateOverflowsByteRate { declared } if declared == u32::MAX
        ),
        "{refusal}"
    );
    assert_ne!(
        refusal,
        AcousticRefusal::ZeroSampleRate,
        "the rate is not zero and the refusal must not say so"
    );
    let sane = export_pcm16("fast", 48_000, Rat::one(), &[Rat::zero()])
        .expect("the export returns");
    assert!(wav_bytes(&sane).is_ok(), "a rate that does not overflow still encodes");
}

#[test]
fn the_wav_face_is_a_declared_riff_document() {
    let face = export_pcm16("export", 8_000, Rat::one(), &[Rat::zero(), ratio(1, 2)])
        .expect("the export returns");
    let bytes = wav_bytes(&face).expect("the document returns");
    assert_eq!(&bytes[0..4], b"RIFF");
    assert_eq!(&bytes[8..12], b"WAVE");
    assert_eq!(&bytes[12..16], b"fmt ");
    assert_eq!(&bytes[36..40], b"data");
    assert_eq!(u32::from_le_bytes(bytes[40..44].try_into().unwrap()), 4);
    assert_eq!(bytes.len(), 44 + 4);
    assert_eq!(u32::from_le_bytes(bytes[4..8].try_into().unwrap()), 40);
}

// ---------------------------------------------------------------------------------------------
// driving the bank from an exact Hodge spectrum
// ---------------------------------------------------------------------------------------------

struct Founded {
    complex: GradedCausalComplex,
    #[allow(dead_code)]
    vertices: Vec<CausalCellId>,
}

/// A complex founded from a declared 1-skeleton, the same hand `hodge_receiver`'s own tests use.
fn found(vertices: usize, edges: &[(usize, usize)]) -> Founded {
    let events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let mut vertex_cells = Vec::new();
    for at in 0..vertices {
        vertex_cells.push(
            complex
                .found_cell(format!("v{at}"), events.clone(), 0, CausalChain::default())
                .expect("a vertex founds"),
        );
    }
    for (lower, upper) in edges {
        assert!(lower < upper, "an edge is written in ascending order");
        let mut boundary = CausalChain::default();
        boundary.add_term(vertex_cells[*upper], ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(vertex_cells[*lower], ComparativeMultiplicity::negative(1_u8));
        complex
            .found_cell(format!("e{lower}_{upper}"), events.clone(), 1, boundary)
            .expect("an edge founds");
    }
    complex.validate().expect("the founded complex stands");
    Founded {
        complex,
        vertices: vertex_cells,
    }
}

/// **The bridge from R3's exact spectrum to R2's declared bands.**
///
/// Each nonzero eigenvalue becomes one band. Where the eigenvalue is rational the rate is that
/// exact rational; where it is irrational — which is the usual case — the eigenvalue **has no
/// rational value**, so the declared rate is the midpoint of its Sturm-certified isolating
/// interval and [`RateProvenance::IsolatingIntervalMidpoint`] carries the interval beside it and
/// names it a readout. The decay and the couplings are declared here and are not read off the
/// spectrum; the bands are `κ_bm = δ_bm`, so each band consumes its own Hodge mode.
fn bank_from_spectrum(
    lineage: &str,
    spectrum: &ExactHodgeSpectrum,
    decay: Rat,
    step: Rat,
    limit: usize,
    narrowed_gap: Option<ExactInterval>,
) -> ResonatorBank {
    let source = format!(
        "R3 exact Hodge spectrum of {lineage}, grade {}, isolation depth {}",
        spectrum.grade, spectrum.isolation_depth
    );
    let mut bands = Vec::new();
    let mut modes = Vec::new();
    let mut narrowed_gap = narrowed_gap;
    for (at, interval) in spectrum.intervals().into_iter().enumerate() {
        if bands.len() == limit {
            break;
        }
        if interval.is_point() && interval.lower.is_zero() {
            continue; // the harmonic population is not a rate
        }
        // The smallest positive eigenvalue is the spectral gap, and R3 owns a narrowing for it.
        // Every other eigenvalue arrives at the width its *isolation* needed, which is a
        // separation certificate and not a narrow readout — R3 exposes no per-eigenvalue
        // refinement, so the coarser midpoint is what an honest readout is here.
        let interval = match narrowed_gap.take() {
            Some(narrow) => narrow,
            None => interval,
        };
        let midpoint = (&interval.lower + &interval.upper) / integer(2);
        let provenance = if interval.is_point() {
            RateProvenance::Exact {
                source: source.clone(),
            }
        } else {
            RateProvenance::IsolatingIntervalMidpoint {
                source: source.clone(),
                interval,
            }
        };
        bands.push(
            Resonator::declared(format!("mode{at}"), decay.clone(), midpoint, provenance)
                .expect("the band declares"),
        );
        modes.push(mode(at as u64));
    }
    assert!(!bands.is_empty(), "the spectrum carries a positive eigenvalue");
    let width = bands.len();
    let rows: Vec<Vec<Rat>> = (0..width)
        .map(|band| {
            (0..width)
                .map(|column| if band == column { Rat::one() } else { Rat::zero() })
                .collect()
        })
        .collect();
    let coupling = ModalCoupling::declared(modes, rows).expect("the coupling declares");
    ResonatorBank::declared(
        lineage,
        step,
        bands,
        coupling,
        vec![current(1, 0); width],
        vec![Rat::one(); width],
    )
    .expect("the bank declares")
}

/// A declared unit excitation on every band's own Hodge mode. It is a **declared** excitation and
/// not a measured amplitude: R3 writes down no eigenvector where the eigenvalue is irrational, and
/// this module does not invent one.
fn unit_population(bank: &ResonatorBank) -> ExactReceiverPhasePopulation {
    let mut carried = ExactReceiverPhasePopulation::default();
    for declared in bank.coupling().modes() {
        carried.receive(*declared, &current(1, 0));
    }
    carried
}

/// **The always-runnable twin of the M5 measurement.** The path `0—1—2—3` has grade-zero spectrum
/// `0, 2−√2, 2, 2+√2`; two of those are irrational and arrive as isolating intervals, so the two
/// corresponding bands carry declared *readouts* and say so, while the rational eigenvalue `2`
/// carries an exact rate. The star on four has spectrum `0, 1, 1, 4` and is completely rational.
/// The two banks return different exact states from the same declared excitation: the spectrum,
/// read through this receiver, separates the two complexes.
#[test]
fn the_exact_hodge_spectrum_drives_the_bank_and_separates_two_complexes() {
    let metric = MetricDeclaration::unit("every cell weight one, declared");
    let readings: Vec<(&str, ExactHodgeSpectrum)> = [
        ("path-of-four", found(4, &[(0, 1), (1, 2), (2, 3)])),
        ("star-on-four", found(4, &[(0, 1), (0, 2), (0, 3)])),
    ]
    .into_iter()
    .map(|(lineage, founded)| {
        let operator =
            HodgeOperator::found(lineage, &founded.complex, &metric, &BoundaryCondition::Free)
                .expect("the operator founds");
        let spectrum = exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH)
            .expect("the spectrum returns");
        (lineage, spectrum)
    })
    .collect();

    let mut states = Vec::new();
    for (lineage, spectrum) in &readings {
        let bank = bank_from_spectrum(lineage, spectrum, ratio(1, 10), ratio(1, 8), 3, None);
        let excitation = unit_population(&bank);
        let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
        let run = bank.run_held(&rest, &excitation, 8).expect("the run returns");
        assert_eq!(run.steps, 8);
        assert_eq!(run.pressures.len(), 9);
        assert!(run.unconsumed_modes.is_empty());
        states.push((lineage.to_string(), run.state.clone(), run.pressures[8].clone()));
    }
    assert_ne!(
        states[0].2, states[1].2,
        "the two spectra separate under the acoustic receiver"
    );
    assert_ne!(states[0].1, states[1].1);

    // The path's irrational eigenvalues arrive as readouts and say so; the star's are all exact.
    let path_bank =
        bank_from_spectrum("path-of-four", &readings[0].1, ratio(1, 10), ratio(1, 8), 3, None);
    assert!(
        path_bank
            .bands()
            .iter()
            .any(|band| band.provenance().is_readout()),
        "an irrational Hodge eigenvalue must arrive as a declared readout"
    );
    let star_bank =
        bank_from_spectrum("star-on-four", &readings[1].1, ratio(1, 10), ratio(1, 8), 3, None);
    assert!(
        star_bank
            .bands()
            .iter()
            .all(|band| !band.provenance().is_readout()),
        "a completely rational spectrum needs no readout"
    );
}

// ---------------------------------------------------------------------------------------------
// the measured M5 reading
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
const M5_STRUCTURES: [(&str, &str); 3] = [
    ("designed-free", "designed-free-rbx1.cif"),
    ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
    ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
];
const RBX1_RESIDUES: usize = 108;
const WINDOW: usize = 24;
const CONTACT_SQUARED: i64 = 64;

fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

fn require_structure_root() -> PathBuf {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured acoustic reading \
         cannot be taken, and this test refuses to report success without taking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif. Every law this module owns is checked without any fixture by \
         the synthetic tests above, and the spectrum-driven reading is checked without a fixture \
         by the_exact_hodge_spectrum_drives_the_bank_and_separates_two_complexes.",
        root.display()
    );
    root
}

fn rbx1_window(path: &Path) -> Result<Vec<Vec<Rat>>, String> {
    use crate::physical_intake::mmcif::StructurePresentation;
    let presentation = StructurePresentation::read(path).map_err(|error| error.to_string())?;
    let chain = presentation
        .chain_with_residue_count(RBX1_RESIDUES)
        .map_err(|error| error.to_string())?;
    let mut window = Vec::new();
    for residue in chain.residues.iter().take(WINDOW) {
        let at = residue
            .labelled_atom("CA")
            .map_err(|error| error.to_string())?
            .ok_or_else(|| format!("residue {} carries no alpha carbon", residue.source_ordinal))?;
        let atom = &residue.atoms[at];
        window.push(vec![
            atom.x.exact_centre().map_err(|error| error.to_string())?,
            atom.y.exact_centre().map_err(|error| error.to_string())?,
            atom.z.exact_centre().map_err(|error| error.to_string())?,
        ]);
    }
    if window.len() != WINDOW {
        return Err(format!(
            "the chain carries {} alpha carbons, fewer than the declared window of {WINDOW}",
            window.len()
        ));
    }
    Ok(window)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

fn contact_complex(window: &[Vec<Rat>]) -> Founded {
    let aperture = integer(CONTACT_SQUARED);
    let mut edges = Vec::new();
    for left in 0..WINDOW {
        for right in (left + 1)..WINDOW {
            if right == left + 1 || squared_distance(&window[left], &window[right]) <= aperture {
                edges.push((left, right));
            }
        }
    }
    found(WINDOW, &edges)
}

/// **The receiver applied to a real object.** The bank is driven by the Hodge/chord mode population
/// of one M5 RBX1 presentation: R3's exact grade-zero spectrum over the declared 24-residue RBX1
/// window at the 8 Å aperture supplies the modes, each band's `Ω_b` is the declared readout of its
/// eigenvalue's Sturm-certified isolating interval, the decay and step are declared rationals, and
/// the excitation is one declared unit current per mode. The exact bank state after eight steps is
/// returned for all three presentations, and the three are required to be **pairwise distinct**
/// exactly.
#[test]
#[ignore = "exact spectral isolation on a 24-cell Laplacian, three times; measured cost is printed"]
fn the_acoustic_receiver_separates_the_three_m5_presentations() {
    let root = require_structure_root();
    let metric = MetricDeclaration::unit("every cell weight one, declared");
    let mut readings = Vec::new();
    for (lineage, file) in M5_STRUCTURES {
        let window = rbx1_window(&root.join(file))
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        let founded = contact_complex(&window);
        let operator =
            HodgeOperator::found(lineage, &founded.complex, &metric, &BoundaryCondition::Free)
                .expect("the operator founds");
        let started = std::time::Instant::now();
        let spectrum = exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH)
            .expect("the spectrum returns");
        let elapsed = started.elapsed();
        let narrowed = refine_spectral_gap(&spectrum, &ratio(1, 100_000), DEFAULT_ISOLATION_DEPTH)
            .expect("the refinement returns");
        let bank = bank_from_spectrum(
            lineage,
            &spectrum,
            ratio(1, 10),
            ratio(1, 8),
            4,
            Some(narrowed.clone()),
        );
        let excitation = unit_population(&bank);
        let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
        let run = bank.run_held(&rest, &excitation, 8).expect("the run returns");
        let readouts = bank
            .bands()
            .iter()
            .filter(|band| band.provenance().is_readout())
            .count();
        println!(
            "{lineage}: spectrum in {elapsed:?}, {} distinct eigenvalues, {} bands, {readouts} of \
             them declared readouts; after 8 steps the exact pressure is {} and the exact energy \
             is {}",
            spectrum.distinct(),
            bank.band_count(),
            run.pressures[8],
            run.energies[8]
        );
        for (at, band) in bank.bands().iter().enumerate() {
            let width = band
                .provenance()
                .interval()
                .map(|interval| &interval.upper - &interval.lower);
            println!(
                "  band {at} {}: gamma {} omega {} ({}), readout interval width {}",
                band.name(),
                band.decay(),
                band.rate(),
                if band.provenance().is_readout() {
                    "declared readout of an isolating interval"
                } else {
                    "exact rational eigenvalue"
                },
                width
                    .as_ref()
                    .map(std::string::ToString::to_string)
                    .unwrap_or_else(|| "exact".to_owned())
            );
        }
        println!("  exact state: {:?}", run.state.amplitudes());
        // The declared energy is bounded and the bank is stable: every band dissipates.
        for band in bank.stability().expect("the stability reading returns") {
            assert!(band.inside_unit_disc, "band {} must dissipate", band.name);
        }
        let rates: Vec<Rat> = bank.bands().iter().map(|band| band.rate().clone()).collect();
        readings.push((lineage, run, rates));
    }
    for left in 0..readings.len() {
        for right in (left + 1)..readings.len() {
            assert_ne!(
                readings[left].1.pressures.last(),
                readings[right].1.pressures.last(),
                "{} and {} must separate under the acoustic receiver",
                readings[left].0,
                readings[right].0
            );
            assert_ne!(readings[left].1.state, readings[right].1.state);
            // The separation is band by band and not only in the aggregate: every one of the four
            // declared rates differs between every pair of presentations.
            for band in 0..readings[left].2.len().min(readings[right].2.len()) {
                assert_ne!(
                    readings[left].2[band], readings[right].2[band],
                    "{} and {} share band {band}'s declared rate",
                    readings[left].0, readings[right].0
                );
            }
        }
    }
}

/// The export face, taken from the measured M5 run and written under `.local/artifacts/`. It is an
/// exterior face produced last, from exact rational pressures, and nothing reads it back.
#[test]
#[ignore = "writes an exterior artifact; run with the measured M5 reading"]
fn the_m5_pressure_exports_as_an_exterior_wav_face() {
    let root = require_structure_root();
    let metric = MetricDeclaration::unit("every cell weight one, declared");
    let (lineage, file) = M5_STRUCTURES[0];
    let window = rbx1_window(&root.join(file)).unwrap_or_else(|error| panic!("{lineage}: {error}"));
    let founded = contact_complex(&window);
    let operator =
        HodgeOperator::found(lineage, &founded.complex, &metric, &BoundaryCondition::Free)
            .expect("the operator founds");
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let bank = bank_from_spectrum(lineage, &spectrum, ratio(1, 1_000), ratio(1, 64), 4, None);
    let excitation = unit_population(&bank);
    let rest = BankState::rest(bank.band_count()).expect("the rest state exists");
    // **The face is short by construction, and that is a measured property of exactness.** An exact
    // rational resonator state gains the bit length of one Cayley denominator at every step, and the
    // pressure projection carries the product of all four bands' denominators, so the cost of an
    // exterior audio face grows quadratically in its length. Sixty-four samples return in seconds;
    // two hundred and fifty-six take minutes. The exact state is the object and the face is a
    // readout, so the readout is the thing that gets shortened.
    let run = bank.run_held(&rest, &excitation, 64).expect("the run returns");
    let peak = run
        .pressures
        .iter()
        .map(num_traits::Signed::abs)
        .max()
        .expect("the run carries pressures");
    let face = export_pcm16(lineage, 8_000, peak, &run.pressures).expect("the export returns");
    let bytes = wav_bytes(&face).expect("the document returns");
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(".local/artifacts");
    std::fs::create_dir_all(&directory).expect("the artifact directory exists");
    let path = directory.join(format!("acoustic-receiver-{lineage}.wav"));
    std::fs::write(&path, &bytes).expect("the exterior face writes");
    // The residual is exact and its numerator carries the run's accumulated denominator, so it is
    // reported as the bound it satisfies rather than printed in full: every unclipped sample lies
    // inside half a quantization step of the declared full scale.
    let half_step = face.full_scale() / integer(PCM16_PEAK) / integer(2);
    assert_eq!(face.clipped(), 0, "the declared full scale is the run's own peak");
    assert!(face.residual_enclosure().upper <= half_step);
    assert!(face.residual_enclosure().lower >= -half_step);
    println!(
        "wrote {} ({} samples at {} Hz, {} clipped, every residual inside half a quantization step)",
        path.display(),
        face.samples().len(),
        face.sample_rate(),
        face.clipped()
    );
}
