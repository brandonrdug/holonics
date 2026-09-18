//! **The acoustic receiver: a resonator bank on the colour receiver's own mode population.**
//!
//! [definition] This is receiver **R2** of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`. A bank of causal resonators
//!
//! ```text
//! r_b' = (−γ_b + i Ω_b) r_b + Σ_m κ_bm A_m(t)
//! ```
//!
//! consumes **the same co-present mode population the existing colour receiver consumes**, so that
//! colour and timbre factor through one current and one lineage rather than through two authored
//! mappings.
//!
//! The paired Lean owner is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/AcousticReceiver.lean`
//! (`Soma.Holonics.Foundation.AcousticReceiver`). Every theorem there appears here as a test or an
//! invariant.
//!
//! # Recovery, not founding: what the colour receiver actually is
//!
//! [established-bounded; source-inspected] The plan's first requirement on R2 is that it consume
//! the *existing* colour receiver's population rather than author a parallel one. That receiver is
//! [`crate::dimensional_wave`], and it has three parts:
//!
//! - [`ExactReceiverPhasePopulation`] is **the type that carries the co-present mode population**:
//!   a `BTreeMap<DimensionalWaveModeId, ExactComplexWaveCurrent>` of exact Gaussian-rational
//!   amplitudes plus a neutral `support_multiplicity`. Its `receive` sums same-mode currents *in
//!   mode*, so relative phase reinforces or cancels there and nowhere else; distinct modes stay
//!   separate until a receiver doctrine acts. This module consumes **that type** and founds no
//!   second population.
//! - [`ExactReceiverPrimaryDoctrine::transduce`] is **the colour law**. It forms the three exact
//!   nonnegative quadratic phase responses `(|Re A|², |Im A|², |Re A + Im A|²)` accumulated over
//!   the co-present modes *after* same-mode superposition, adds the neutral support response, and
//!   **only then** applies the saturating aperture `P_j / (aperture + ΣP)`.
//! - The integer readout is downstream and last of all: `examples/arithmetic_dimensional_receiver.rs`
//!   quantizes the resulting primaries to `Rgb8` *after* the doctrine has run.
//!
//! [definition] The acoustic receiver respects the same ordering. Same-mode superposition happens
//! in the population; the bank is exactly linear in that population ([`ResonatorBank::run`], and
//! the test `superposition_holds_through_the_bank`); the one-dimensional pressure projection
//! ([`ResonatorBank::pressure`]) happens **last**; and the integer sample quantization
//! ([`export_pcm16`]) is an exterior export face produced after everything and never read back.
//! `the_colour_law_does_not_distribute_over_superposition` and
//! `quantize_then_superpose_differs_from_superpose_then_quantize` exhibit concretely why that
//! ordering is law and not a convention: a nonlinear reading taken before superposition returns a
//! different object. This is the cross-term identity
//! `|Σ z_j|² = Σ |z_j|² + 2 Re Σ_{j<k} conj(z_j) z_k` of
//! `research/records/2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md`
//! — what quantize-first discards is the relative phase.
//!
//! # The exact discrete law, and why it is not an approximated exponential
//!
//! [definition] The continuous resonator's response `exp(λ t)` is **not rational**, so it is not
//! the law. The declared law is the exact **Cayley (bilinear) map** of `λ = −γ_b + i Ω_b` at a
//! declared rational step `h`:
//!
//! ```text
//! z_b = (2 + h λ_b) / (2 − h λ_b),      g_b = h / (2 − h λ_b),
//! r_b(n+1) = z_b r_b(n) + g_b Σ_m κ_bm A_m(n).
//! ```
//!
//! `γ_b`, `Ω_b`, `κ_bm` and `h` are declared rationals with sources, so `z_b` and `g_b` are
//! **Gaussian rationals** — elements of `Q(i)` carried by [`ExactComplexWaveCurrent`], the same
//! carrier the colour receiver's currents use. The state is exact at every step; no decimal, no
//! float and no audio sample ever enters it.
//!
//! [proved-derived; formal-checked] The map is **total**: `Re(2 − hλ) = 2 + hγ ≥ 2 > 0` for
//! `h > 0` and `γ ≥ 0`, so the denominator never vanishes and the step needs no guard. It
//! **preserves stability exactly**: `‖2 + hλ‖² − ‖2 − hλ‖² = 8 h Re λ`, so the open left half
//! plane maps into the open unit disc and the imaginary axis onto the unit circle, decided by the
//! sign of `γ` alone with no tolerance anywhere. The Lean theorems are `cayley_den_ne_zero`,
//! `normSq_cayley_lt_one` and `normSq_cayley_eq_one`; [`ResonatorBank::stability`] is the
//! executable equivalent, and it holds the discrete reading and R1's continuous half-plane count to
//! exact agreement band by band.
//!
//! # Built on R1, not beside it
//!
//! [definition] Each resonator is a one-pole causal chord and the bank is a **block-diagonal
//! [`Linearization`]** of [`crate::causal_chord`] driven by the mode amplitudes through `κ`.
//! [`ResonatorBank::linearization`] realifies band `b` over `Q` as
//!
//! ```text
//! A_b = [[−γ_b, −Ω_b], [Ω_b, −γ_b]],
//! ```
//!
//! exactly as [`crate::causal_chord::resolvent_probe`] realifies a Gaussian-rational probe point;
//! excitation column `2m` is mode `m`'s real quadrature and `2m+1` its imaginary one; and the
//! single readout row is the one-dimensional pressure projection. Everything the plan requires of a
//! returned component — its source mode, excitation, transport path, exact pole factor,
//! multiplicity, residue, participating support, approximation error and residual — is then
//! [`crate::causal_chord::ChordComponent`] itself, obtained by *calling* R1.
//! [`AudibleComponent`] adds only the two facts R1 cannot know: which declared mode and quadrature
//! the excitation column names, and which band's pole the factor is.
//! `charpoly_realBlock` proves the band's characteristic factor is exactly `X² + 2γX + (γ² + Ω²)`,
//! which is why a component's pole is an exact rational factor even when the `Ω` that produced it
//! was read off an isolating interval.
//!
//! # Energy, and the rate form it is tied to
//!
//! [proved-derived; implemented-exact] The declared quadratic energy is
//! `E = Σ_b e_b ‖r_b‖²` at declared positive rational weights. At zero input
//! `r_b ↦ z_b r_b`, so `E ↦ Σ_b e_b ‖z_b‖² ‖r_b‖²`: nonincreasing for `γ_b ≥ 0` and **strictly**
//! decreasing wherever `γ_b > 0` and the band is excited. [`ResonatorBank::rate_form`] returns the
//! continuous `Σ_G = AᵀG + GA` of `research/records/2026-09-15_INTEGRATING_AND_DIFFERENTIATING_ROLES_SHARE_ONE_CURRENT.md`
//! through [`crate::causal_chord::rate_form`] — it is exactly `diag(−2 γ_b e_b)`, because the
//! rotation part of each block cancels against its transpose — and
//! [`crate::inertia::inertia`] reads its signature. The discrete decay and the continuous rate form
//! are one statement at two clocks, and the module holds them to exact agreement rather than
//! asserting the tie in prose. The Lean counterparts are `energy_advance_le`, `energy_advance_lt`
//! and `rateForm_realBlock`.
//!
//! # One lineage: two receivers of one source
//!
//! [proved-derived; implemented-exact] [`joint_reading`] takes one [`ExactReceiverPhasePopulation`]
//! and returns both readings. Neither refines the other:
//!
//! - **Metamers that sound different.** Exchanging which of two co-present modes carries which
//!   quadrature leaves the colour response *identical*, because the colour law accumulates its
//!   quadratic response across modes and cannot see which mode supplied it; the bank consumes the
//!   two modes at different `κ`, so its excitation turns by a quarter. Equal colour does not imply
//!   equal timbre (`metamers_sound_different`, Lean `metamer_sounds_different`).
//! - **Unisons that look different.** Current placed on a mode no resonator couples to is exactly
//!   invisible to the bank and plainly visible to colour. Equal timbre does not imply equal colour
//!   (`unisons_look_different`, Lean `unison_looks_different`).
//! - A change of the population generally moves both (`a_change_of_population_moves_both_receivers`,
//!   Lean `population_change_moves_both`).
//!
//! [definition] `Ω_b` is a **declared readout** whenever it comes from a spectrum. R3's exact
//! Hodge spectrum returns irrational eigenvalues as an exact polynomial plus a Sturm-certified
//! isolating interval; such an eigenvalue *has no rational value*, so this module never pretends
//! one. [`RateProvenance::IsolatingIntervalMidpoint`] carries the interval beside the rate and the
//! constructor **checks** that the declared rate really is that interval's midpoint, refusing by
//! name otherwise. The eigenvalue remains the object; the midpoint is a readout named as one.
//!
//! # The standing caution
//!
//! [definition] **Sound and colour are guidance receivers and never truth oracles.** A construction
//! may reach an acoustically stable equilibrium under an incomplete receiver while remaining false:
//! [`ResonatorBank::stability`] reports that a bank settles, not that what it settled onto is true,
//! and [`AcousticReading`] is a reading and not a verdict. Nothing in this module is an acceptance
//! condition, and no gate is built from any of it.
//!
//! # Correspondence with the Lean owner
//!
//! [definition] Every declaration of
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/AcousticReceiver.lean`
//! (namespace `Soma.Holonics.Foundation.AcousticReceiver`) and what carries it here. The first
//! column is the Lean name **exactly as it is declared there**, unqualified: the bank's members are
//! declared inside `namespace Bank`, so they appear here bare — `advance`, `run`, `drive` — as they
//! appear in the source and not under a namespace prefix. This table is the citation contract: it
//! carries every declaration of that file and no name that is not one.
//!
//! | Lean declaration | What it states | Rust counterpart |
//! |---|---|---|
//! | `pole` | the band pole `λ = −γ + iΩ` | [`Resonator::pole`] |
//! | `pole_re` | its real part is `−γ` | [`Resonator::decay`] |
//! | `pole_im` | its imaginary part is `Ω` | [`Resonator::rate`] |
//! | `cayley` | the exact one-step transition `z = (2 + hλ)/(2 − hλ)` | [`ResonatorBank::transition`] |
//! | `gain` | the matching input gain `g = h/(2 − hλ)` | [`ResonatorBank::gain`] |
//! | `cayley_den_ne_zero` | the law is total on the closed left half plane | `the_cayley_law_is_total_for_every_admitted_band` |
//! | `normSq_cayley_lt_one` | open left half plane maps inside the open unit disc | `the_left_half_plane_maps_inside_the_unit_disc` |
//! | `normSq_cayley_eq_one` | the imaginary axis maps onto the unit circle exactly | `the_left_half_plane_maps_inside_the_unit_disc` |
//! | `realBlock` | the realified `2 × 2` block of one band | [`ResonatorBank::linearization`] |
//! | `trace_realBlock` | its trace is `−2γ` | `each_band_names_its_pole_by_an_exact_factor` |
//! | `det_realBlock` | its determinant is `γ² + Ω²` | `each_band_names_its_pole_by_an_exact_factor` |
//! | `charpoly_realBlock` | its characteristic polynomial is `X² + 2γX + (γ² + Ω²)` | [`Resonator::characteristic_factor`] |
//! | `rateForm_realBlock` | `Σ_G` of the block at the unit metric is `(−2γ)·I` | [`ResonatorBank::rate_form`] |
//! | `Bank` | the declared bank of causal resonators | [`ResonatorBank`] |
//! | `bandPole` | band `b`'s pole | [`Resonator::pole`] |
//! | `transition` | band `b`'s `z_b` | [`ResonatorBank::transition`] |
//! | `bandGain` | band `b`'s `g_b` | [`ResonatorBank::gain`] |
//! | `drive` | the excitation `Σ_m κ_bm A_m` | [`ResonatorBank::drive`] |
//! | `drive_add` | the excitation is linear in the population | `superposition_holds_through_the_bank` |
//! | `advance` | one exact step | [`ResonatorBank::advance`] |
//! | `run` | the fold over a declared input history | [`ResonatorBank::run`] |
//! | `run_zero` | the run at zero steps is the declared initial state | [`ResonatorBank::run`] |
//! | `run_succ` | the run unfolds by one `advance` | [`ResonatorBank::run`] |
//! | `run_causal` | the state after `n` steps ignores every later input | `the_state_after_n_steps_ignores_every_later_input` |
//! | `run_add` | superposition holds exactly through the bank from rest | `superposition_holds_through_the_bank` |
//! | `pressure` | the one-dimensional pressure projection | [`ResonatorBank::pressure`] |
//! | `pressure_add` | that projection is itself linear | `the_pressure_projection_is_linear_and_comes_last` |
//! | `timbre` | the acoustic reading of one population | [`joint_reading`] |
//! | `energy` | the declared quadratic energy `Σ_b e_b ‖r_b‖²` | [`ResonatorBank::energy`] |
//! | `energy_advance_le` | it is nonincreasing at zero input | `the_declared_energy_is_nonincreasing_at_zero_input` |
//! | `energy_advance_lt` | a band with positive decay strictly dissipates | `positive_decay_strictly_dissipates` |
//! | `colour` | the colour receiver's three quadratic responses | [`ExactReceiverPrimaryDoctrine::transduce`] |
//! | `colour_does_not_distribute` | the colour law does not distribute over superposition | `the_colour_law_does_not_distribute_over_superposition` |
//! | `quantize` | the declared integer readout | [`export_pcm16`] |
//! | `quantize_half_eq_zero` | two half-step pressures quantize to silence | `quantize_then_superpose_differs_from_superpose_then_quantize` |
//! | `quantize_one_eq_one` | their superposition quantizes to one step | `quantize_then_superpose_differs_from_superpose_then_quantize` |
//! | `quantize_then_superpose_ne_superpose_then_quantize` | so the two orders differ | `quantize_then_superpose_differs_from_superpose_then_quantize` |
//! | `workedBank` | the worked one-band, two-mode bank with mode `1` uncoupled | `one_band_two_modes` |
//! | `metamerBank` | the worked bank with **both** modes coupled at unequal `κ` | `worked_bank` |
//! | `bandGain_workedBank_ne_zero` | that bank's gain is nonzero | `the_cayley_law_is_total_for_every_admitted_band` |
//! | `bandGain_metamerBank_ne_zero` | the metamer bank's gain is nonzero | `the_cayley_law_is_total_for_every_admitted_band` |
//! | `metamer_sounds_different` | equal colour does not imply equal timbre | `metamers_sound_different` |
//! | `unison_looks_different` | equal timbre does not imply equal colour | `unisons_look_different` |
//! | `population_change_moves_both` | a change of population generally moves both readings | `a_change_of_population_moves_both_receivers` |

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::causal_chord::{
    self, CausalChord, ChordComponent, ChordRefusal, Linearization, PoleReading,
};
use crate::dimensional_wave::{
    DimensionalWaveModeId, ExactComplexWaveCurrent, ExactPremultipliedReceiverResponse,
    ExactReceiverPhasePopulation, ExactReceiverPrimaryDoctrine,
};
use crate::exact_linear::ExactRatMatrix;
use crate::exact_value::ExactInterval;
use crate::inertia::SymmetricForm;
use crate::rational_polynomial::RationalPolynomial;

pub const ACOUSTIC_RECEIVER_SCHEMA: &str = "holonics.acoustic-receiver.v1";
pub const ACOUSTIC_READING_SCHEMA: &str = "holonics.acoustic-reading.v1";
pub const ACOUSTIC_RUN_SCHEMA: &str = "holonics.acoustic-bank-run.v1";
pub const JOINT_READING_SCHEMA: &str = "holonics.acoustic-joint-receiver-reading.v1";
pub const PRESSURE_EXPORT_SCHEMA: &str = "holonics.acoustic-pressure-export.v1";

/// The largest band population a declared bank may carry. Every loop and allocation below is
/// `bands × modes` or `bands × steps`, so this and [`MODE_CEILING`] are what bound them.
pub const BAND_CEILING: usize = 64;
/// The largest declared mode population a coupling may name.
pub const MODE_CEILING: usize = 256;
/// The largest declared run length. The run retains one exact pressure and one exact energy per
/// step, so the retained trace — not the arithmetic — is what this bounds. It is **not** a bound on
/// the work: [`STEP_WORK_CEILING`] is.
pub const STEP_CEILING: u64 = 1 << 16;
/// The largest projected exact-arithmetic work a declared run may ask for, in **bit-steps**: the
/// declared step count times the projected bit length of the exact state the last step would carry.
///
/// [`STEP_CEILING`] bounds how many steps are *retained* and does not bound what they cost. The
/// state is an exact Gaussian rational and one step multiplies it by the Cayley coefficients of the
/// declared bank, so its numerators and denominators gain a whole coefficient's bit length per step
/// and the arithmetic at step `n` is quadratic in `n`. A declaration far under [`STEP_CEILING`] can
/// therefore still run for hours, which is the defect this ceiling closes.
///
/// [established-bounded; measured] The basis, measured on this module's worked two-band bank
/// (`γ = 1/2, Ω = 1` and `γ = 0, Ω = 2` at step `h = 1/4`, whose widest Cayley coefficient is
/// seventeen bits): a run of one thousand and twenty-four steps takes about five seconds and a run
/// of two thousand and forty-eight takes about thirty-three seconds — four times the steps for six
/// and a half times the time. `2^25` bit-steps is set to admit the first and refuse the second by
/// name. The same ceiling refuses a much shorter run of a bank whose declared rationals are wide,
/// which is the point: the bound is on the work, not on the step count.
pub const STEP_WORK_CEILING: u64 = 1 << 25;
/// The largest state extent `2 × bands` at which the exact chord is taken. The Faddeev–LeVerrier
/// recurrence and the pole isolation behind [`crate::causal_chord::causal_chord_read`] grow
/// steeply, so a caller asking for the chord of a large bank is refused by name rather than left
/// running.
pub const CHORD_EXTENT_CEILING: usize = 24;
/// The largest exported sample population.
pub const SAMPLE_CEILING: usize = 1 << 20;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The bit length of an exact rational: its numerator's bits and its denominator's bits together.
/// This is the size of the thing the machine actually carries, which is what a run's cost is
/// quadratic in.
fn rational_bit_length(value: &Rat) -> u64 {
    value.numer().bits().saturating_add(value.denom().bits())
}

/// The bit length of a Gaussian rational: the wider of its two exact rational parts.
fn current_bit_length(value: &ExactComplexWaveCurrent) -> u64 {
    rational_bit_length(&value.real).max(rational_bit_length(&value.imaginary))
}

// -------------------------------------------------------------------------------------------------
// declared rates and their provenance

/// **Where a declared rational rate came from.**
///
/// The plan's instruction is that `γ_b`, `Ω_b` and `κ_bm` are declared rationals *with sources*.
/// When the source is a spectrum the rate is additionally a **readout**: an irrational eigenvalue
/// has no rational value, so what is declared is the midpoint of its Sturm-certified isolating
/// interval, and the interval travels beside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RateProvenance {
    /// The rate is exactly this rational, from the named source.
    Exact { source: String },
    /// The rate is the **declared readout** of an irrational spectral quantity: the midpoint of the
    /// named isolating interval. The eigenvalue is the object; this is a readout of it.
    IsolatingIntervalMidpoint {
        source: String,
        interval: ExactInterval,
    },
}

impl RateProvenance {
    pub fn source(&self) -> &str {
        match self {
            Self::Exact { source } | Self::IsolatingIntervalMidpoint { source, .. } => source,
        }
    }

    /// The isolating interval, when the rate is a readout of one.
    pub fn interval(&self) -> Option<&ExactInterval> {
        match self {
            Self::Exact { .. } => None,
            Self::IsolatingIntervalMidpoint { interval, .. } => Some(interval),
        }
    }

    /// Whether the rate is a readout rather than an exact value.
    pub fn is_readout(&self) -> bool {
        matches!(self, Self::IsolatingIntervalMidpoint { .. })
    }
}

/// **One declared causal resonator.**
///
/// Fields are private and every constructed value has passed [`Resonator::declared`]: there is no
/// `Default`, no `Deserialize` and no public field, so no path reconstructs one unchecked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Resonator {
    name: String,
    decay: Rat,
    rate: Rat,
    provenance: RateProvenance,
}

impl Resonator {
    /// A declared resonator. `γ ≥ 0` — a growing band is not a receiver and is refused by name —
    /// the source is required, and a rate declared as an interval readout is **checked** against
    /// that interval's midpoint rather than trusted.
    pub fn declared(
        name: impl Into<String>,
        decay: Rat,
        rate: Rat,
        provenance: RateProvenance,
    ) -> Result<Self, AcousticRefusal> {
        let name = name.into();
        if name.is_empty() {
            return Err(AcousticRefusal::UnnamedResonator);
        }
        if decay.is_negative() {
            return Err(AcousticRefusal::NegativeDecay { band: name });
        }
        if provenance.source().is_empty() {
            return Err(AcousticRefusal::UnsourcedRate { band: name });
        }
        if let Some(interval) = provenance.interval() {
            let midpoint = (&interval.lower + &interval.upper) / integer(2);
            if midpoint != rate {
                return Err(AcousticRefusal::MidpointDisagrees {
                    band: name,
                    declared: rate.to_string(),
                    midpoint: midpoint.to_string(),
                });
            }
        }
        Ok(Self {
            name,
            decay,
            rate,
            provenance,
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// `γ_b`.
    pub fn decay(&self) -> &Rat {
        &self.decay
    }

    /// `Ω_b`.
    pub fn rate(&self) -> &Rat {
        &self.rate
    }

    pub fn provenance(&self) -> &RateProvenance {
        &self.provenance
    }

    /// `λ_b = −γ_b + i Ω_b`, in the same Gaussian-rational carrier the colour receiver's currents
    /// use.
    pub fn pole(&self) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(-self.decay.clone(), self.rate.clone())
    }

    /// The band's exact characteristic factor `X² + 2γX + (γ² + Ω²)`, whose roots are `−γ ± iΩ`.
    /// The Lean owner's `charpoly_realBlock` is the proof that this is the realified block's
    /// characteristic polynomial.
    pub fn characteristic_factor(&self) -> RationalPolynomial {
        RationalPolynomial::new(vec![
            &self.decay * &self.decay + &self.rate * &self.rate,
            integer(2) * &self.decay,
            Rat::one(),
        ])
    }
}

// -------------------------------------------------------------------------------------------------
// the coupling

/// **`κ_bm`: how much of each declared mode each band consumes.**
///
/// The modes are named by [`DimensionalWaveModeId`] — the colour receiver's own mode identity — so
/// the two receivers address one population and not two.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ModalCoupling {
    modes: Vec<DimensionalWaveModeId>,
    rows: Vec<Vec<Rat>>,
}

impl ModalCoupling {
    /// A declared coupling. The declared mode population and band population are each checked
    /// against their ceilings **before** anything is allocated from them, every row is checked
    /// against the declared mode count, and a repeated mode is refused by name.
    pub fn declared(
        modes: Vec<DimensionalWaveModeId>,
        rows: Vec<Vec<Rat>>,
    ) -> Result<Self, AcousticRefusal> {
        if modes.is_empty() {
            return Err(AcousticRefusal::EmptyCoupling);
        }
        if modes.len() > MODE_CEILING {
            return Err(AcousticRefusal::ModePopulationAboveCeiling {
                declared: modes.len(),
                ceiling: MODE_CEILING,
            });
        }
        let distinct: BTreeSet<DimensionalWaveModeId> = modes.iter().copied().collect();
        if distinct.len() != modes.len() {
            return Err(AcousticRefusal::DuplicateMode);
        }
        if rows.is_empty() {
            return Err(AcousticRefusal::EmptyCoupling);
        }
        if rows.len() > BAND_CEILING {
            return Err(AcousticRefusal::BandPopulationAboveCeiling {
                declared: rows.len(),
                ceiling: BAND_CEILING,
            });
        }
        for (band, row) in rows.iter().enumerate() {
            if row.len() != modes.len() {
                return Err(AcousticRefusal::CouplingRowShape {
                    band,
                    declared: row.len(),
                    modes: modes.len(),
                });
            }
        }
        Ok(Self { modes, rows })
    }

    pub fn modes(&self) -> &[DimensionalWaveModeId] {
        &self.modes
    }

    pub fn bands(&self) -> usize {
        self.rows.len()
    }

    /// `κ_bm` by band and by *index into the declared mode list*.
    pub fn at(&self, band: usize, mode_index: usize) -> Option<&Rat> {
        self.rows.get(band)?.get(mode_index)
    }

    /// Whether any band consumes this declared mode at all.
    fn consumes(&self, mode_index: usize) -> bool {
        self.rows
            .iter()
            .any(|row| row.get(mode_index).is_some_and(|value| !value.is_zero()))
    }
}

// -------------------------------------------------------------------------------------------------
// the bank

/// **The bank of causal resonators.**
///
/// Fields are private and every value has passed [`ResonatorBank::declared`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResonatorBank {
    schema: String,
    lineage: String,
    step: Rat,
    bands: Vec<Resonator>,
    coupling: ModalCoupling,
    pressure: Vec<ExactComplexWaveCurrent>,
    energy_weights: Vec<Rat>,
}

impl ResonatorBank {
    /// A declared bank. The step must be strictly positive — that is what makes the Cayley map
    /// total and stability-preserving — every declared vector must have exactly one entry per
    /// band, every energy weight must be strictly positive, and band names must be distinct.
    pub fn declared(
        lineage: impl Into<String>,
        step: Rat,
        bands: Vec<Resonator>,
        coupling: ModalCoupling,
        pressure: Vec<ExactComplexWaveCurrent>,
        energy_weights: Vec<Rat>,
    ) -> Result<Self, AcousticRefusal> {
        let lineage = lineage.into();
        if lineage.is_empty() {
            return Err(AcousticRefusal::UnnamedBank);
        }
        if !step.is_positive() {
            return Err(AcousticRefusal::NonPositiveStep {
                declared: step.to_string(),
            });
        }
        if bands.is_empty() {
            return Err(AcousticRefusal::EmptyBank);
        }
        if bands.len() > BAND_CEILING {
            return Err(AcousticRefusal::BandPopulationAboveCeiling {
                declared: bands.len(),
                ceiling: BAND_CEILING,
            });
        }
        if coupling.bands() != bands.len() {
            return Err(AcousticRefusal::CouplingBandCount {
                declared: coupling.bands(),
                bands: bands.len(),
            });
        }
        if pressure.len() != bands.len() {
            return Err(AcousticRefusal::PressureWeightCount {
                declared: pressure.len(),
                bands: bands.len(),
            });
        }
        if energy_weights.len() != bands.len() {
            return Err(AcousticRefusal::EnergyWeightCount {
                declared: energy_weights.len(),
                bands: bands.len(),
            });
        }
        for (at, weight) in energy_weights.iter().enumerate() {
            if !weight.is_positive() {
                return Err(AcousticRefusal::NonPositiveEnergyWeight {
                    band: bands[at].name.clone(),
                });
            }
        }
        let distinct: BTreeSet<&str> = bands.iter().map(|band| band.name.as_str()).collect();
        if distinct.len() != bands.len() {
            return Err(AcousticRefusal::DuplicateBandName);
        }
        Ok(Self {
            schema: ACOUSTIC_RECEIVER_SCHEMA.to_owned(),
            lineage,
            step,
            bands,
            coupling,
            pressure,
            energy_weights,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared rational step `h`.
    pub fn step(&self) -> &Rat {
        &self.step
    }

    pub fn bands(&self) -> &[Resonator] {
        &self.bands
    }

    pub fn band_count(&self) -> usize {
        self.bands.len()
    }

    pub fn coupling(&self) -> &ModalCoupling {
        &self.coupling
    }

    pub fn mode_count(&self) -> usize {
        self.coupling.modes.len()
    }

    /// The one-dimensional pressure projection's weights, one per band.
    pub fn pressure_weights(&self) -> &[ExactComplexWaveCurrent] {
        &self.pressure
    }

    pub fn energy_weights(&self) -> &[Rat] {
        &self.energy_weights
    }

    /// `2 + hλ_b` and `2 − hλ_b`. The second has real part `2 + hγ_b ≥ 2`, which is why the law is
    /// total.
    fn cayley_terms(
        &self,
        band: usize,
    ) -> Result<(ExactComplexWaveCurrent, ExactComplexWaveCurrent), AcousticRefusal> {
        let resonator = self
            .bands
            .get(band)
            .ok_or(AcousticRefusal::BandOutsideBank {
                band,
                bands: self.bands.len(),
            })?;
        let scaled = resonator.pole().scaled(&self.step);
        let two = ExactComplexWaveCurrent::new(integer(2), Rat::zero());
        Ok((two.add(&scaled), two.subtract(&scaled)))
    }

    /// **The exact one-step transition coefficient `z_b = (2 + hλ_b)/(2 − hλ_b)`**, a Gaussian
    /// rational. Lean: `cayley`.
    pub fn transition(&self, band: usize) -> Result<ExactComplexWaveCurrent, AcousticRefusal> {
        let (numerator, denominator) = self.cayley_terms(band)?;
        let inverse = denominator
            .reciprocal()
            .ok_or(AcousticRefusal::DegenerateStep)?;
        Ok(numerator.multiply(&inverse))
    }

    /// **The exact one-step input gain `g_b = h/(2 − hλ_b)`.** Lean: `gain`.
    pub fn gain(&self, band: usize) -> Result<ExactComplexWaveCurrent, AcousticRefusal> {
        let (_, denominator) = self.cayley_terms(band)?;
        let inverse = denominator
            .reciprocal()
            .ok_or(AcousticRefusal::DegenerateStep)?;
        Ok(ExactComplexWaveCurrent::new(self.step.clone(), Rat::zero()).multiply(&inverse))
    }

    /// Every band's `(z_b, g_b)`, computed once so a long run does not rebuild them per step.
    fn coefficients(
        &self,
    ) -> Result<Vec<(ExactComplexWaveCurrent, ExactComplexWaveCurrent)>, AcousticRefusal> {
        (0..self.bands.len())
            .map(|band| Ok((self.transition(band)?, self.gain(band)?)))
            .collect()
    }

    /// **The excitation `u_b = Σ_m κ_bm A_m` read off the colour receiver's own population.**
    ///
    /// A declared mode absent from the population contributes exactly zero. A mode present in the
    /// population that no band consumes is **reported** by [`ResonatorBank::unconsumed_modes`],
    /// never silently dropped.
    pub fn drive(
        &self,
        population: &ExactReceiverPhasePopulation,
    ) -> Vec<ExactComplexWaveCurrent> {
        let mut excitation = vec![ExactComplexWaveCurrent::zero(); self.bands.len()];
        for (index, mode) in self.coupling.modes.iter().enumerate() {
            let Some(current) = population.coherent_modes.get(mode) else {
                continue;
            };
            for (band, accumulated) in excitation.iter_mut().enumerate() {
                let Some(coefficient) = self.coupling.at(band, index) else {
                    continue;
                };
                if coefficient.is_zero() {
                    continue;
                }
                *accumulated = accumulated.add(&current.scaled(coefficient));
            }
        }
        excitation
    }

    /// The modes this population carries that **no** band of this bank consumes. The acoustic
    /// reading is blind to exactly these, and the colour reading is not; that difference is what
    /// `unisons_look_different` exhibits.
    pub fn unconsumed_modes(
        &self,
        population: &ExactReceiverPhasePopulation,
    ) -> Vec<DimensionalWaveModeId> {
        let declared: BTreeMap<DimensionalWaveModeId, usize> = self
            .coupling
            .modes
            .iter()
            .enumerate()
            .map(|(index, mode)| (*mode, index))
            .collect();
        population
            .coherent_modes
            .keys()
            .filter(|mode| match declared.get(mode) {
                None => true,
                Some(index) => !self.coupling.consumes(*index),
            })
            .copied()
            .collect()
    }

    /// One exact step. Lean: `advance`.
    pub fn advance(
        &self,
        state: &BankState,
        population: &ExactReceiverPhasePopulation,
    ) -> Result<BankState, AcousticRefusal> {
        let coefficients = self.coefficients()?;
        self.advance_with(&coefficients, state, population)
    }

    fn advance_with(
        &self,
        coefficients: &[(ExactComplexWaveCurrent, ExactComplexWaveCurrent)],
        state: &BankState,
        population: &ExactReceiverPhasePopulation,
    ) -> Result<BankState, AcousticRefusal> {
        if state.amplitudes.len() != self.bands.len() {
            return Err(AcousticRefusal::StateShape {
                declared: state.amplitudes.len(),
                bands: self.bands.len(),
            });
        }
        let excitation = self.drive(population);
        let amplitudes = coefficients
            .iter()
            .zip(state.amplitudes.iter())
            .zip(excitation.iter())
            .map(|(((transition, gain), amplitude), drive)| {
                transition.multiply(amplitude).add(&gain.multiply(drive))
            })
            .collect();
        Ok(BankState { amplitudes })
    }

    /// **The projected per-step growth of the exact state's bit length**, in bits.
    ///
    /// [definition] One step multiplies the state by the Cayley transition `z_b` and adds the gain
    /// `g_b` times the excitation, so the state's numerators and denominators gain a whole
    /// coefficient's bit length at every step. This returns the widest such coefficient over the
    /// bank — numerator bits and denominator bits together, over both quadratures of `z_b` and of
    /// `g_b`. It is a **projection from the declared step's own arithmetic**, computed before any
    /// loop runs and without reference to any input history; it is not a theorem about a particular
    /// run, and it is what [`ResonatorBank::projected_run_work`] multiplies out.
    pub fn step_bit_length(&self) -> Result<u64, AcousticRefusal> {
        let mut widest = 0u64;
        for band in 0..self.bands.len() {
            let transition = current_bit_length(&self.transition(band)?);
            let gain = current_bit_length(&self.gain(band)?);
            widest = widest.max(transition).max(gain);
        }
        Ok(widest)
    }

    /// **The projected exact work of a declared run, in bit-steps**: the declared step count times
    /// the bit length the state is projected to carry at the last step. Checked arithmetic
    /// throughout; an overflow is a refusal and never a wrap.
    pub fn projected_run_work(
        &self,
        state: &BankState,
        steps: u64,
    ) -> Result<u64, AcousticRefusal> {
        let step_bits = self.step_bit_length()?;
        let carried = state
            .amplitudes
            .iter()
            .map(current_bit_length)
            .max()
            .unwrap_or(0);
        let projected = steps
            .checked_mul(step_bits)
            .and_then(|growth| growth.checked_add(carried))
            .ok_or(AcousticRefusal::RunWorkOverflows)?;
        steps
            .checked_mul(projected)
            .ok_or(AcousticRefusal::RunWorkOverflows)
    }

    /// **What every run is admitted through, before a single step is taken.**
    ///
    /// [`STEP_CEILING`] bounds the retained trace; [`STEP_WORK_CEILING`] bounds the arithmetic. Both
    /// are checked here, in that order, and both refuse by name. Nothing is allocated and no step is
    /// taken until this has returned.
    fn admit_run(&self, state: &BankState, steps: u64) -> Result<(), AcousticRefusal> {
        if steps > STEP_CEILING {
            return Err(AcousticRefusal::RunAboveCeiling {
                declared: steps,
                ceiling: STEP_CEILING,
            });
        }
        let work = self.projected_run_work(state, steps)?;
        if work > STEP_WORK_CEILING {
            return Err(AcousticRefusal::RunWorkAboveCeiling {
                steps,
                step_bits: self.step_bit_length()?,
                work,
                ceiling: STEP_WORK_CEILING,
            });
        }
        Ok(())
    }

    /// **The run over a declared input history**, retaining the exact pressure and exact energy at
    /// every step. The one-dimensional pressure projection is taken **last** at each step, after
    /// the whole bank has advanced.
    ///
    /// The declared history's length is admitted through [`STEP_CEILING`] **and** through
    /// [`STEP_WORK_CEILING`] before anything is allocated or stepped.
    pub fn run(
        &self,
        state: &BankState,
        history: &[ExactReceiverPhasePopulation],
    ) -> Result<BankRun, AcousticRefusal> {
        let steps = u64::try_from(history.len()).map_err(|_| AcousticRefusal::RunAboveCeiling {
            declared: u64::MAX,
            ceiling: STEP_CEILING,
        })?;
        self.admit_run(state, steps)?;
        let coefficients = self.coefficients()?;
        let mut current = state.clone();
        let mut pressures = vec![self.pressure(&current)?];
        let mut energies = vec![self.energy(&current)?];
        let mut unconsumed: BTreeSet<DimensionalWaveModeId> = BTreeSet::new();
        for population in history {
            unconsumed.extend(self.unconsumed_modes(population));
            current = self.advance_with(&coefficients, &current, population)?;
            pressures.push(self.pressure(&current)?);
            energies.push(self.energy(&current)?);
        }
        Ok(BankRun {
            schema: ACOUSTIC_RUN_SCHEMA.to_owned(),
            lineage: self.lineage.clone(),
            steps,
            state: current,
            pressures,
            energies,
            unconsumed_modes: unconsumed.into_iter().collect(),
        })
    }

    /// The run of a **held** population for a declared number of steps. The declared count is
    /// checked against [`STEP_CEILING`] and the projected work against [`STEP_WORK_CEILING`] before
    /// any iteration or allocation uses it.
    pub fn run_held(
        &self,
        state: &BankState,
        population: &ExactReceiverPhasePopulation,
        steps: u64,
    ) -> Result<BankRun, AcousticRefusal> {
        self.admit_run(state, steps)?;
        let coefficients = self.coefficients()?;
        let mut current = state.clone();
        let mut pressures = vec![self.pressure(&current)?];
        let mut energies = vec![self.energy(&current)?];
        for _ in 0..steps {
            current = self.advance_with(&coefficients, &current, population)?;
            pressures.push(self.pressure(&current)?);
            energies.push(self.energy(&current)?);
        }
        Ok(BankRun {
            schema: ACOUSTIC_RUN_SCHEMA.to_owned(),
            lineage: self.lineage.clone(),
            steps,
            state: current,
            pressures,
            energies,
            unconsumed_modes: self.unconsumed_modes(population),
        })
    }

    /// **The one-dimensional pressure projection, taken last.**
    /// `p = Σ_b Re(conj(w_b) r_b) = Σ_b (Re w_b · Re r_b + Im w_b · Im r_b)`, exactly rational.
    pub fn pressure(&self, state: &BankState) -> Result<Rat, AcousticRefusal> {
        if state.amplitudes.len() != self.bands.len() {
            return Err(AcousticRefusal::StateShape {
                declared: state.amplitudes.len(),
                bands: self.bands.len(),
            });
        }
        Ok(self
            .pressure
            .iter()
            .zip(state.amplitudes.iter())
            .fold(Rat::zero(), |sum, (weight, amplitude)| {
                sum + &weight.real * &amplitude.real + &weight.imaginary * &amplitude.imaginary
            }))
    }

    /// The declared quadratic energy `E = Σ_b e_b ‖r_b‖²`, exactly rational.
    pub fn energy(&self, state: &BankState) -> Result<Rat, AcousticRefusal> {
        if state.amplitudes.len() != self.bands.len() {
            return Err(AcousticRefusal::StateShape {
                declared: state.amplitudes.len(),
                bands: self.bands.len(),
            });
        }
        Ok(self
            .energy_weights
            .iter()
            .zip(state.amplitudes.iter())
            .fold(Rat::zero(), |sum, (weight, amplitude)| {
                sum + weight * amplitude.norm_square()
            }))
    }

    /// **The bank as R1's block-diagonal [`Linearization`].**
    ///
    /// Band `b` occupies state coordinates `2b` (real quadrature) and `2b+1` (imaginary), mode `m`
    /// occupies excitation columns `2m` and `2m+1`, and the single readout row is the pressure
    /// projection.
    pub fn linearization(&self) -> Result<Linearization, AcousticRefusal> {
        let bands = self.bands.len();
        let modes = self.coupling.modes.len();
        let extent = bands
            .checked_mul(2)
            .ok_or(AcousticRefusal::ExtentOverflows { bands })?;
        let columns = modes
            .checked_mul(2)
            .ok_or(AcousticRefusal::ExtentOverflows { bands: modes })?;
        let mut state = vec![vec![Rat::zero(); extent]; extent];
        for (band, resonator) in self.bands.iter().enumerate() {
            state[2 * band][2 * band] = -resonator.decay.clone();
            state[2 * band][2 * band + 1] = -resonator.rate.clone();
            state[2 * band + 1][2 * band] = resonator.rate.clone();
            state[2 * band + 1][2 * band + 1] = -resonator.decay.clone();
        }
        let mut excitation = vec![vec![Rat::zero(); columns]; extent];
        for band in 0..bands {
            for mode in 0..modes {
                let Some(coefficient) = self.coupling.at(band, mode) else {
                    continue;
                };
                excitation[2 * band][2 * mode] = coefficient.clone();
                excitation[2 * band + 1][2 * mode + 1] = coefficient.clone();
            }
        }
        let mut readout = vec![vec![Rat::zero(); extent]];
        for (band, weight) in self.pressure.iter().enumerate() {
            readout[0][2 * band] = weight.real.clone();
            readout[0][2 * band + 1] = weight.imaginary.clone();
        }
        let mut sources = Vec::new();
        for mode in &self.coupling.modes {
            sources.push(format!("mode {} real", mode.0));
            sources.push(format!("mode {} imaginary", mode.0));
        }
        Ok(Linearization::declared(
            self.lineage.clone(),
            ExactRatMatrix::shaped(extent, extent, state).map_err(ChordRefusal::from)?,
            ExactRatMatrix::shaped(extent, columns, excitation).map_err(ChordRefusal::from)?,
            ExactRatMatrix::shaped(1, extent, readout).map_err(ChordRefusal::from)?,
            sources,
            vec!["pressure".to_owned()],
        )?)
    }

    /// The exact causal chord of the bank, through R1. The state extent `2 × bands` is checked
    /// against [`CHORD_EXTENT_CEILING`] first.
    pub fn chord(&self, reading: PoleReading) -> Result<CausalChord, AcousticRefusal> {
        let extent = self
            .bands
            .len()
            .checked_mul(2)
            .ok_or(AcousticRefusal::ExtentOverflows {
                bands: self.bands.len(),
            })?;
        if extent > CHORD_EXTENT_CEILING {
            return Err(AcousticRefusal::ChordExtentAboveCeiling {
                extent,
                ceiling: CHORD_EXTENT_CEILING,
            });
        }
        Ok(causal_chord::causal_chord_read(
            &self.linearization()?,
            reading,
        )?)
    }

    /// **Every audible component, carrying the whole R1 contract plus its declared mode.**
    ///
    /// [definition] The band is attributed **structurally**, from the block-diagonal shape of the
    /// bank's state operator, and never by polynomial equality. Band `b` occupies state coordinates
    /// `2b` and `2b+1`; excitation columns `2m` and `2m+1` carry mode `m` into exactly the bands
    /// whose `κ_bm` is nonzero and into no others, so a component's excitation column names its
    /// mode and the declared coupling names which blocks that mode can have come from. Matching the
    /// component's pole factor against the band list instead is an **aliasing** rule: the factor is
    /// `X² + 2γX + (γ² + Ω²)` and depends on `Ω` only through `Ω²`, so two distinctly named bands
    /// with mirror-signed rates carry the identical factor and the first of them would be handed
    /// both components' names.
    ///
    /// What is returned is [`AudibleComponent::originating_bands`]: the blocks this column actually
    /// drives whose exact characteristic factor is this component's pole factor.
    /// [`AudibleComponent::band`] and [`AudibleComponent::band_index`] are `Some` exactly when that
    /// set is a single block. When one column drives two bands that share a factor the pole is
    /// genuinely pooled between them — the reduced denominator carries it once — and the fields say
    /// `None` rather than picking one.
    pub fn audible_components(
        &self,
        reading: PoleReading,
    ) -> Result<Vec<AudibleComponent>, AcousticRefusal> {
        let chord = self.chord(reading)?;
        let factors: Vec<RationalPolynomial> = self
            .bands
            .iter()
            .map(|band| band.characteristic_factor().made_monic())
            .collect();
        Ok(chord
            .components
            .iter()
            .map(|component| {
                let mode_index = component.excitation / 2;
                let quadrature = if component.excitation % 2 == 0 {
                    Quadrature::Real
                } else {
                    Quadrature::Imaginary
                };
                let pole_factor = component.pole_factor.made_monic();
                let originating_bands: Vec<usize> = (0..self.bands.len())
                    .filter(|band| {
                        self.coupling
                            .at(*band, mode_index)
                            .is_some_and(|coefficient| !coefficient.is_zero())
                            && factors[*band] == pole_factor
                    })
                    .collect();
                let band_index = match originating_bands.as_slice() {
                    [only] => Some(*only),
                    _ => None,
                };
                AudibleComponent {
                    mode: self.coupling.modes.get(mode_index).copied(),
                    quadrature,
                    band: band_index.map(|at| self.bands[at].name.clone()),
                    band_index,
                    originating_bands,
                    component: component.clone(),
                }
            })
            .collect())
    }

    /// **The continuous rate form `Σ_G = AᵀG + GA` at the declared energy metric**, through
    /// [`crate::causal_chord::rate_form`]. It is exactly `diag(−2 γ_b e_b)` repeated over the two
    /// quadratures, because each block's rotation part cancels against its transpose.
    pub fn rate_form(&self) -> Result<SymmetricForm, AcousticRefusal> {
        let linearization = self.linearization()?;
        let extent = linearization.extent();
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for (band, weight) in self.energy_weights.iter().enumerate() {
            rows[2 * band][2 * band] = weight.clone();
            rows[2 * band + 1][2 * band + 1] = weight.clone();
        }
        let metric = SymmetricForm::from_rows(rows).map_err(ChordRefusal::from)?;
        Ok(causal_chord::rate_form(&linearization.state, &metric)?)
    }

    /// **The stability reading, discrete and continuous, held to exact agreement.**
    ///
    /// `‖z_b‖² < 1` exactly when `γ_b > 0` exactly when `λ_b` lies in the open left half plane.
    /// The Lean theorems are `normSq_cayley_lt_one` and `normSq_cayley_eq_one`.
    pub fn stability(&self) -> Result<Vec<BandStability>, AcousticRefusal> {
        (0..self.bands.len())
            .map(|band| {
                let transition = self.transition(band)?;
                let norm_square = transition.norm_square();
                let resonator = &self.bands[band];
                Ok(BandStability {
                    name: resonator.name.clone(),
                    decay: resonator.decay.clone(),
                    rate: resonator.rate.clone(),
                    transition_norm_square: norm_square.clone(),
                    inside_unit_disc: norm_square < Rat::one(),
                    on_unit_circle: norm_square == Rat::one(),
                    continuous_left_half_plane: resonator.decay.is_positive(),
                    continuous_on_axis: resonator.decay.is_zero(),
                })
            })
            .collect()
    }
}

/// Which quadrature of a declared mode an excitation column names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Quadrature {
    Real,
    Imaginary,
}

/// One audible component: the whole R1 contract, plus the declared mode the excitation names and
/// the block of the block-diagonal state operator the component came out of.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AudibleComponent {
    /// The declared mode this component's excitation column names, when the column is inside the
    /// declared mode population.
    pub mode: Option<DimensionalWaveModeId>,
    pub quadrature: Quadrature,
    /// The name of the single block this component originated in, when
    /// [`AudibleComponent::originating_bands`] names exactly one. It is **not** the first band
    /// whose characteristic factor happens to equal the pole factor: distinct bands with
    /// mirror-signed rates share that factor exactly.
    pub band: Option<String>,
    /// The index of that single originating block.
    pub band_index: Option<usize>,
    /// Every block of the block-diagonal state operator this component can have come out of: the
    /// bands this component's excitation column drives at a nonzero `κ` whose exact characteristic
    /// factor is this component's pole factor. Normally one. More than one exactly when one column
    /// drives two bands sharing both `γ` and `Ω²`, where the reduced denominator carries the factor
    /// once and the pole is genuinely pooled; the count is returned rather than resolved.
    pub originating_bands: Vec<usize>,
    /// R1's component verbatim: source lineage and name, excitation, receiver name, transport
    /// path, exact pole factor, multiplicity, residue, support, approximation error and residual.
    pub component: ChordComponent,
}

/// One band's stability, read twice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BandStability {
    pub name: String,
    pub decay: Rat,
    pub rate: Rat,
    /// `‖z_b‖²`, exactly.
    pub transition_norm_square: Rat,
    pub inside_unit_disc: bool,
    pub on_unit_circle: bool,
    pub continuous_left_half_plane: bool,
    pub continuous_on_axis: bool,
}

// -------------------------------------------------------------------------------------------------
// the state and the run

/// **The exact bank state.** One Gaussian rational per band — the same carrier the colour
/// receiver's currents use.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BankState {
    amplitudes: Vec<ExactComplexWaveCurrent>,
}

impl BankState {
    /// The rest state of a declared band population. The count is checked against
    /// [`BAND_CEILING`] before the vector is built.
    pub fn rest(bands: usize) -> Result<Self, AcousticRefusal> {
        if bands == 0 {
            return Err(AcousticRefusal::EmptyBank);
        }
        if bands > BAND_CEILING {
            return Err(AcousticRefusal::BandPopulationAboveCeiling {
                declared: bands,
                ceiling: BAND_CEILING,
            });
        }
        Ok(Self {
            amplitudes: vec![ExactComplexWaveCurrent::zero(); bands],
        })
    }

    /// A declared state.
    pub fn declared(amplitudes: Vec<ExactComplexWaveCurrent>) -> Result<Self, AcousticRefusal> {
        if amplitudes.is_empty() {
            return Err(AcousticRefusal::EmptyBank);
        }
        if amplitudes.len() > BAND_CEILING {
            return Err(AcousticRefusal::BandPopulationAboveCeiling {
                declared: amplitudes.len(),
                ceiling: BAND_CEILING,
            });
        }
        Ok(Self { amplitudes })
    }

    pub fn amplitudes(&self) -> &[ExactComplexWaveCurrent] {
        &self.amplitudes
    }

    pub fn band_count(&self) -> usize {
        self.amplitudes.len()
    }

    /// The bandwise superposition of two states, which is what `run_add` superposes.
    pub fn superposed(&self, other: &Self) -> Result<Self, AcousticRefusal> {
        if self.amplitudes.len() != other.amplitudes.len() {
            return Err(AcousticRefusal::StateShape {
                declared: other.amplitudes.len(),
                bands: self.amplitudes.len(),
            });
        }
        Ok(Self {
            amplitudes: self
                .amplitudes
                .iter()
                .zip(other.amplitudes.iter())
                .map(|(left, right)| left.add(right))
                .collect(),
        })
    }
}

/// A completed run: the exact final state, and the exact pressure and energy at every step.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BankRun {
    pub schema: String,
    pub lineage: String,
    pub steps: u64,
    pub state: BankState,
    /// One exact pressure per step boundary, `steps + 1` of them, the projection taken last at
    /// each.
    pub pressures: Vec<Rat>,
    /// One exact declared energy per step boundary.
    pub energies: Vec<Rat>,
    /// Modes the driving population carried that no band consumes.
    pub unconsumed_modes: Vec<DimensionalWaveModeId>,
}

/// One acoustic reading of one population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AcousticReading {
    pub schema: String,
    pub lineage: String,
    pub steps: u64,
    pub state: BankState,
    pub pressure: Rat,
    pub energy: Rat,
    pub unconsumed_modes: Vec<DimensionalWaveModeId>,
}

// -------------------------------------------------------------------------------------------------
// one lineage: two receivers of one source

/// **Two receivers of one source.**
///
/// The colour reading is `dimensional_wave`'s own doctrine, called rather than reimplemented; the
/// acoustic reading is this module's. They consume the *same* [`ExactReceiverPhasePopulation`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct JointReceiverReading {
    pub schema: String,
    pub lineage: String,
    /// The one co-present mode population both receivers consume.
    pub population: ExactReceiverPhasePopulation,
    /// The colour receiver's reading, from [`ExactReceiverPrimaryDoctrine::transduce`].
    pub colour: ExactPremultipliedReceiverResponse,
    /// The acoustic receiver's reading of the same population.
    pub acoustic: AcousticReading,
}

/// Read one population through both receivers.
pub fn joint_reading(
    bank: &ResonatorBank,
    doctrine: &ExactReceiverPrimaryDoctrine,
    population: &ExactReceiverPhasePopulation,
    steps: u64,
) -> Result<JointReceiverReading, AcousticRefusal> {
    let run = bank.run_held(&BankState::rest(bank.band_count())?, population, steps)?;
    let pressure = bank.pressure(&run.state)?;
    let energy = bank.energy(&run.state)?;
    Ok(JointReceiverReading {
        schema: JOINT_READING_SCHEMA.to_owned(),
        lineage: bank.lineage.clone(),
        population: population.clone(),
        colour: doctrine.transduce(population),
        acoustic: AcousticReading {
            schema: ACOUSTIC_READING_SCHEMA.to_owned(),
            lineage: bank.lineage.clone(),
            steps,
            state: run.state,
            pressure,
            energy,
            unconsumed_modes: run.unconsumed_modes,
        },
    })
}

// -------------------------------------------------------------------------------------------------
// the exterior export face

/// **An exterior export face.** Produced last, from exact rational pressures, and never read back
/// into any law. The samples are integers and the projection's error is returned as an exact
/// rational enclosure; there is no float anywhere in this module, not even here.
///
/// [definition] **Every field is private and [`export_pcm16`] is the only constructor.** That is
/// the whole guarantee, and it is a compile-level one rather than a checked one: the type derives
/// `Serialize` and **not** `Deserialize`, has no `Default`, no `new`, no `from_*`, no public field
/// and no `&mut self` method anywhere in the crate, and `Clone` copies a value that already passed
/// the constructor. No path outside this module can therefore assemble a face at all, and no path
/// inside it assembles one except the tail of [`export_pcm16`], which refuses a declared sample
/// population above [`SAMPLE_CEILING`] before it allocates. Every `PressureExportFace` in existence
/// carries at most [`SAMPLE_CEILING`] samples, so [`wav_bytes`] cannot be handed one that does not —
/// which is what the public fields previously allowed, since a caller could build a face around the
/// ceiling check and hand it straight to the encoder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PressureExportFace {
    schema: String,
    lineage: String,
    sample_rate: u32,
    /// The declared pressure at which the export saturates.
    full_scale: Rat,
    samples: Vec<i16>,
    /// The exact enclosure of `pressure − sample·full_scale/32767` over every sample. It is a
    /// rational interval on the pressure scale and it is part of the return, not a footnote.
    residual_enclosure: ExactInterval,
    /// How many samples reached the declared saturation. A clipped sample's residual is outside the
    /// quantization step and the count says so rather than hiding it.
    clipped: usize,
}

impl PressureExportFace {
    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn sample_rate(&self) -> u32 {
        self.sample_rate
    }

    /// The declared pressure at which the export saturates.
    pub fn full_scale(&self) -> &Rat {
        &self.full_scale
    }

    /// The projected integer samples. At most [`SAMPLE_CEILING`] of them, by construction.
    pub fn samples(&self) -> &[i16] {
        &self.samples
    }

    /// The exact rational enclosure of the projection's residual over every sample.
    pub fn residual_enclosure(&self) -> &ExactInterval {
        &self.residual_enclosure
    }

    /// How many samples reached the declared saturation.
    pub fn clipped(&self) -> usize {
        self.clipped
    }
}

const PCM16_PEAK: i64 = 32_767;

/// Project exact rational pressures onto a declared 16-bit integer lattice.
///
/// The declared sample population is checked against [`SAMPLE_CEILING`] before anything is
/// allocated from it. The rounding is exact: `n = ⌊p·32767/full_scale + 1/2⌋`, clamped to the
/// representable range, and the residual is returned exactly.
pub fn export_pcm16(
    lineage: impl Into<String>,
    sample_rate: u32,
    full_scale: Rat,
    pressures: &[Rat],
) -> Result<PressureExportFace, AcousticRefusal> {
    let lineage = lineage.into();
    if lineage.is_empty() {
        return Err(AcousticRefusal::UnnamedBank);
    }
    if sample_rate == 0 {
        return Err(AcousticRefusal::ZeroSampleRate);
    }
    if !full_scale.is_positive() {
        return Err(AcousticRefusal::NonPositiveFullScale {
            declared: full_scale.to_string(),
        });
    }
    if pressures.len() > SAMPLE_CEILING {
        return Err(AcousticRefusal::SamplePopulationAboveCeiling {
            declared: pressures.len(),
            ceiling: SAMPLE_CEILING,
        });
    }
    let peak = integer(PCM16_PEAK);
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    let mut samples = Vec::new();
    let mut clipped = 0usize;
    let mut lowest = Rat::zero();
    let mut highest = Rat::zero();
    for pressure in pressures {
        let scaled = pressure * &peak / &full_scale + &half;
        let mut ordinal = scaled.floor().to_integer();
        if ordinal > BigInt::from(PCM16_PEAK) {
            ordinal = BigInt::from(PCM16_PEAK);
            clipped += 1;
        }
        if ordinal < BigInt::from(-PCM16_PEAK - 1) {
            ordinal = BigInt::from(-PCM16_PEAK - 1);
            clipped += 1;
        }
        let recovered = Rat::from_integer(ordinal.clone()) * &full_scale / &peak;
        let residual = pressure - &recovered;
        if residual < lowest {
            lowest = residual.clone();
        }
        if residual > highest {
            highest = residual;
        }
        samples.push(i16::try_from(ordinal).map_err(|_| AcousticRefusal::SampleOutsideRange)?);
    }
    let residual_enclosure =
        ExactInterval::new(lowest, highest).map_err(AcousticRefusal::Interval)?;
    Ok(PressureExportFace {
        schema: PRESSURE_EXPORT_SCHEMA.to_owned(),
        lineage,
        sample_rate,
        full_scale,
        samples,
        residual_enclosure,
        clipped,
    })
}

/// The RIFF/WAVE bytes of an export face: mono, 16-bit, little-endian PCM. Integers only.
///
/// [definition] The sample population needs no ceiling check here and gets none: a
/// [`PressureExportFace`] has private fields and one constructor, so every face this can be handed
/// already passed [`export_pcm16`]'s [`SAMPLE_CEILING`] refusal. What is still checked is the
/// arithmetic of the RIFF header itself — the byte count, the chunk size and the byte rate — each
/// with its own refusal by name.
pub fn wav_bytes(face: &PressureExportFace) -> Result<Vec<u8>, AcousticRefusal> {
    let sample_bytes = face
        .samples
        .len()
        .checked_mul(2)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or(AcousticRefusal::SamplePopulationAboveCeiling {
            declared: face.samples.len(),
            ceiling: SAMPLE_CEILING,
        })?;
    let riff_size = sample_bytes
        .checked_add(36)
        .ok_or(AcousticRefusal::SamplePopulationAboveCeiling {
            declared: face.samples.len(),
            ceiling: SAMPLE_CEILING,
        })?;
    let byte_rate =
        face.sample_rate
            .checked_mul(2)
            .ok_or(AcousticRefusal::SampleRateOverflowsByteRate {
                declared: face.sample_rate,
            })?;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"RIFF");
    bytes.extend_from_slice(&riff_size.to_le_bytes());
    bytes.extend_from_slice(b"WAVE");
    bytes.extend_from_slice(b"fmt ");
    bytes.extend_from_slice(&16u32.to_le_bytes());
    bytes.extend_from_slice(&1u16.to_le_bytes());
    bytes.extend_from_slice(&1u16.to_le_bytes());
    bytes.extend_from_slice(&face.sample_rate.to_le_bytes());
    bytes.extend_from_slice(&byte_rate.to_le_bytes());
    bytes.extend_from_slice(&2u16.to_le_bytes());
    bytes.extend_from_slice(&16u16.to_le_bytes());
    bytes.extend_from_slice(b"data");
    bytes.extend_from_slice(&sample_bytes.to_le_bytes());
    for sample in &face.samples {
        bytes.extend_from_slice(&sample.to_le_bytes());
    }
    Ok(bytes)
}

// -------------------------------------------------------------------------------------------------
// refusals

#[derive(Debug, Error)]
pub enum AcousticRefusal {
    #[error("a resonator must be named")]
    UnnamedResonator,
    #[error("a bank must carry a lineage")]
    UnnamedBank,
    #[error("band {band} declares a negative decay; a growing band is not a receiver")]
    NegativeDecay { band: String },
    #[error("band {band} declares a rate with no source")]
    UnsourcedRate { band: String },
    #[error(
        "band {band} declares the rate {declared} as an isolating-interval readout, but that \
         interval's midpoint is {midpoint}; an irrational eigenvalue has no rational value and the \
         readout must be the one it claims to be"
    )]
    MidpointDisagrees {
        band: String,
        declared: String,
        midpoint: String,
    },
    #[error("a declared step of {declared} is not positive, so the Cayley map is not a receiver")]
    NonPositiveStep { declared: String },
    #[error("the Cayley denominator vanished, which a positive step and a nonnegative decay forbid")]
    DegenerateStep,
    #[error("a bank with no band is not a receiver")]
    EmptyBank,
    #[error("a coupling with no band or no mode is not a coupling")]
    EmptyCoupling,
    #[error("a coupling may not name the same mode twice")]
    DuplicateMode,
    #[error("a bank may not name the same band twice")]
    DuplicateBandName,
    #[error("{declared} declared bands exceed the ceiling of {ceiling}")]
    BandPopulationAboveCeiling { declared: usize, ceiling: usize },
    #[error("{declared} declared modes exceed the ceiling of {ceiling}")]
    ModePopulationAboveCeiling { declared: usize, ceiling: usize },
    #[error("coupling row {band} declares {declared} coefficients for {modes} modes")]
    CouplingRowShape {
        band: usize,
        declared: usize,
        modes: usize,
    },
    #[error("the coupling declares {declared} bands against a bank of {bands}")]
    CouplingBandCount { declared: usize, bands: usize },
    #[error("{declared} pressure weights were declared for {bands} bands")]
    PressureWeightCount { declared: usize, bands: usize },
    #[error("{declared} energy weights were declared for {bands} bands")]
    EnergyWeightCount { declared: usize, bands: usize },
    #[error("band {band} declares a non-positive energy weight, so the reading is not an energy")]
    NonPositiveEnergyWeight { band: String },
    #[error("a state of {declared} amplitudes does not pair with a bank of {bands} bands")]
    StateShape { declared: usize, bands: usize },
    #[error("band {band} lies outside a bank of {bands} bands")]
    BandOutsideBank { band: usize, bands: usize },
    #[error("a bank of {bands} bands overflows the machine integer counting its state extent")]
    ExtentOverflows { bands: usize },
    #[error(
        "a state extent of {extent} exceeds the exact-chord ceiling of {ceiling}; the chord is \
         refused rather than left running"
    )]
    ChordExtentAboveCeiling { extent: usize, ceiling: usize },
    #[error("a declared run of {declared} steps exceeds the ceiling of {ceiling}")]
    RunAboveCeiling { declared: u64, ceiling: u64 },
    #[error(
        "a declared run of {steps} steps projects {work} bit-steps of exact arithmetic, above the \
         ceiling of {ceiling}; the exact state gains up to {step_bits} bits per step, so the cost \
         is quadratic in the length and this run is refused by name rather than left running"
    )]
    RunWorkAboveCeiling {
        steps: u64,
        step_bits: u64,
        work: u64,
        ceiling: u64,
    },
    #[error(
        "the projected exact work of a declared run overflows the machine integer counting it, \
         which is already past every ceiling this module carries"
    )]
    RunWorkOverflows,
    #[error("{declared} declared samples exceed the ceiling of {ceiling}")]
    SamplePopulationAboveCeiling { declared: usize, ceiling: usize },
    #[error("an export face with a zero sample rate is not a face")]
    ZeroSampleRate,
    #[error(
        "a declared sample rate of {declared} overflows the RIFF byte rate of sixteen-bit mono, \
         which is two bytes a sample; the face is a face and the document is what refuses"
    )]
    SampleRateOverflowsByteRate { declared: u32 },
    #[error("a declared full scale of {declared} is not positive")]
    NonPositiveFullScale { declared: String },
    #[error("a projected sample left the sixteen-bit range after clamping")]
    SampleOutsideRange,
    #[error(transparent)]
    Chord(#[from] ChordRefusal),
    #[error("the residual enclosure refused: {0}")]
    Interval(crate::exact_value::ExactValueError),
}

impl PartialEq for AcousticRefusal {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

#[cfg(test)]
#[path = "acoustic_receiver/tests.rs"]
mod tests;
