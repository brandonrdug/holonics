//! **Standing, memory and extinction: what a lineage retains, what it generates now, and when a
//! difference has stopped reaching a receiver.**
//!
//! \[definition\] This module is the executable owner of item **T2** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Lean
//! counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/Standing.lean`
//! (namespace `Soma.Holonics.Foundation.Standing`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `causalSignature` | [`FutureObservation`] and [`sufficiency`]'s observation family |
//! | `StandingLaw` | [`StandingLaw`] |
//! | `StandingLaw.sufficient` | [`sufficiency`] returning [`SufficiencyVerdict::Sufficient`] |
//! | `StandingLaw.separating_future_refutes_the_standing` | [`SufficiencyVerdict::NotSufficient`], which carries the separating receiver, word and two faces |
//! | `standingLaw_exists_iff_future_factors` | `a_quotient_is_a_standing_exactly_when_the_future_factors_through_it` |
//! | `two_histories_leave_one_standing` | `two_histories_leave_one_standing` |
//! | `one_present_face_two_standings_separated_later` | `one_present_face_two_standings_separated_later` |
//! | `TimedFace`, `TimedFace.occursAt` | [`TimedFace`] and [`TimedFace::occurs_at`] |
//! | `MemoryLaw`, `MemoryLaw.remember` | [`MemoryLaw`] and [`MemoryLaw::remember`] |
//! | `the_remembered_face_is_a_new_occurrence` | `the_remembered_face_is_a_new_occurrence` |
//! | `one_standing_two_contexts_two_faces` | `one_standing_two_contexts_two_faces` |
//! | `one_original_two_standings_two_reconstructions` | `one_original_two_standings_two_reconstructions` |
//! | `FaithfulAt`, `faithfulAt_iff_receiver_factors_through_standing` | [`fidelity`] and [`Fidelity`] |
//! | `the_unretained_receiver_is_reconstructed_confidently_and_wrongly` | `the_unretained_receiver_is_reconstructed_confidently_and_wrongly` |
//! | `aperture`, `aperture_comp_of_le` | [`ApertureChain::face`] and `a_coarser_aperture_reads_a_finer_face_and_returns_its_own` |
//! | `the_available_face_changes_while_the_source_does_not` | `the_available_face_changes_while_the_source_does_not` |
//! | `compatibleFibre`, `compatibleFibre_antitone` | [`ApertureChain::compatible`] and `the_compatible_fibre_is_antitone_in_the_step` |
//! | `the_fibre_is_never_a_singleton_and_a_later_step_separates` | [`ApertureChain::first_separating_step`] and `what_one_step_cannot_separate_a_later_step_can` |
//! | `Extinct` | [`extinction`] and [`ExtinctionVerdict`] |
//! | `extinct_iff_release_width_inside_tolerance` | [`extinction`] computes every width through `crate::law::receiver::width_over_readings` on the two-point family and decides with `crate::law::receiver::ReceiverWidth::releasable_at` |
//! | `extinct_mono_tolerance`, `extinct_mono_receivers` | `extinction_is_monotone_in_the_tolerance`, `extinction_is_monotone_in_the_receiver_family` |
//! | `fossilStep`, `fossilState` | [`GeneratorFamily`] built from the damped state matrix, in `the_fossil_instance_has_exact_numbers` |
//! | `the_wave_is_extinct_at_horizon_three` | `the_wave_chart_is_extinct_at_horizon_three` |
//! | `the_medium_separates_what_the_wave_chart_declared_extinct` | `the_medium_separates_what_the_wave_chart_declared_extinct` |
//! | `the_fossil_is_durable` | `the_fossil_is_durable` |
//! | `the_energy_that_left_the_wave_is_accounted_for` | `the_energy_that_left_the_wave_is_accounted_for` |
//! | `rotate`, `rotate_preserves_energy_along_every_word` | `the_rotation_conserves_the_declared_energy_exactly` |
//! | `no_horizon_releases_the_energy_receiver` | `no_horizon_releases_the_energy_receiver` |
//!
//! # The object
//!
//! \[definition\] **Standing** is a prior relation still available to present transport: the
//! retained residue of the passages a lineage has undergone. A remembered face is **generated
//! now, not retrieved** — `m_t = D_t(S_t, c_t)` with `S_t` the standing, `c_t` the present
//! context and `D_t` the current reconstruction. The original occurrence is not regenerated; a
//! new occurrence in a related family is constituted using the morphology the original helped
//! form. [`TimedFace`] carries the present time, so a reconstruction is not the original's face.
//!
//! \[definition\] **Effective extinction** of a perturbation `x` against a reference is
//! receiver-relative:
//!
//! ```text
//! Extinct_{R,G,ε}(x | 0) :⟺ ∀ ρ ∈ R, ∀ w ∈ G*, d(ρ(T_w x), ρ(T_w 0)) ≤ ε
//! ```
//!
//! and that is exactly the core receiver law's width inside tolerance on the two-point family
//! `{T_w x, T_w 0}`. [`extinction`] computes it that way: it builds
//! [`crate::law::receiver::width_over_readings`] over those two members in the sup norm and decides with
//! [`crate::law::receiver::ReceiverWidth::releasable_at`]. No second diameter is founded here.
//!
//! # Why `Extinct` is a verdict and not a search that ran out
//!
//! \[implemented-exact\] `Extinct` quantifies over **every** finite word, of which there are
//! infinitely many. An enumeration to a declared horizon can only ever *refute* it — and
//! [`ExtinctionVerdict::Separated`] is exactly that refutation, carrying the word and receiver
//! that separate. To **affirm** extinction, [`extinction`] requires a
//! [`ContractionCertificate`]: a declared coordinate chart and an exact rational factor `λ ≤ 1`,
//! **checked** against every generator, such that
//!
//! * the chart is invariant — for `i` in the chart and `j` outside it, `A[i][j] = 0`, so the
//!   chart's future depends on the chart alone; and
//! * every chart row sums to at most `λ` in absolute value, so
//!   `‖(A d)_C‖_∞ ≤ λ ‖d_C‖_∞`.
//!
//! Every reading must then be supported on that chart, with exact gain
//! `γ = max_i Σ_{j∈C} |R[i][j]|`. Transport is exactly linear, so `T_w x − T_w z = T_w(x − z)`
//! and
//!
//! ```text
//! |ρ(T_w x) − ρ(T_w z)|_∞ ≤ γ · λ^{|w|} · ‖(x − z)_C‖_∞ ≤ γ · ‖(x − z)_C‖_∞
//! ```
//!
//! for every word. When that last quantity is inside the tolerance, extinction holds for the
//! whole infinite family and [`ExtinctionVerdict::Extinct`] is returned with the bound it used.
//! When neither route decides, the return is [`ExtinctionVerdict::NotDecidedWithinBound`] naming
//! the horizon searched and the widest reading found — never a silent "extinct because nothing
//! turned up".
//!
//! # Where this sits on the relation ladder
//!
//! \[definition\] Item **T1** of the same plan, the relation-ladder owner and
//! `Foundation/RelationLadder.lean`, places identity, continuation, isomorphism, receiver
//! equality, equal potential and tolerance on one typed scale. This owner is stated against the
//! same underlying owners, and the Lean file restates its results there:
//! `Foundation/Standing.lean::causalSignature_eq_potential` identifies the causal signature with
//! the ladder's potential, `Foundation/Standing.lean::retain_eq_establishes_equalPotential` puts
//! equal standing at rung 5, `Foundation/Standing.lean::extinct_iff_withinTolerance_after_every_history`
//! identifies extinction with rung 6 after every admitted history, and
//! `Foundation/Standing.lean::extinct_at_zero_iff_equalPotential` shows the two rungs coincide at
//! `ε = 0`. Nothing here founds a second scale.
//!
//! # No floats
//!
//! \[implemented-exact\] Every state, matrix entry, gain, separation, bound and tolerance is an
//! exact `Rat`. No `f32`/`f64` appears anywhere in this module or its tests.
//!
//! # Declared-size discipline
//!
//! \[implemented-exact\] Every caller-declared extent is checked against a ceiling with checked
//! arithmetic **before** any allocation or loop it would size: [`EXTENT_CEILING`],
//! [`GENERATOR_CEILING`], [`WORD_LENGTH_CEILING`], [`WORD_COUNT_CEILING`],
//! [`POPULATION_CEILING`], [`OBSERVATION_CEILING`], [`CHECK_WORK_CEILING`] and
//! [`SEARCH_WORK_CEILING`]. The word family a horizon names grows as `Σ_{k≤h} g^k`;
//! [`GeneratorFamily::words_within`] forms that sum with `checked_add`/`checked_mul` and refuses
//! by name before reserving anything. Two of the ceilings bound *products* rather than single
//! declarations, because a product is what a hostile pair of declarations actually buys.
//!
//! # What carries an invariant and what does not
//!
//! \[implemented-exact\] [`GeneratorFamily`], [`SourcePopulation`], [`StandingLaw`],
//! [`ReceiverReading`], [`FutureObservation`], [`TimedFace`], [`MemoryLaw`], [`ApertureChain`] and
//! [`ContractionCertificate`] carry invariants, so each has private fields, exactly one validating
//! constructor, no `Default` and no `Deserialize`. [`SufficiencyVerdict`], [`Fidelity`] and
//! [`ExtinctionVerdict`] are **returns** with public fields and no invariant: nothing in this
//! module consumes one, so a hand-built verdict grants no capability. A
//! [`ContractionCertificate`] is not trusted on construction either — [`extinction`] calls
//! [`ContractionCertificate::verify`] against the actual generators before it decides anything.

use crate::geometry::Rat;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use serde::Serialize;
use thiserror::Error;

use crate::restriction::{FactorDescent, LinearRestriction, factor_descent_over};

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::law::receiver::{
    DiameterNorm, ExactFace, PassiveCoholon, Reading, WidthRefusal, width_over_readings,
};

/// The ceiling on a declared carrier extent.
///
/// \[definition\] Every transport is one `extent × extent` exact rational matrix and every reading
/// is `rows × extent`; the extent is a caller declaration and sizes both.
pub const EXTENT_CEILING: usize = 256;

/// The ceiling on the number of admitted generators.
///
/// \[definition\] The word family a horizon names is `Σ_{k≤h} g^k`, exponential in the horizon with
/// base `g`. This bounds the base before [`WORD_COUNT_CEILING`] bounds the sum.
pub const GENERATOR_CEILING: usize = 32;

/// The ceiling on a declared horizon, which is the maximum admitted word length.
pub const WORD_LENGTH_CEILING: usize = 32;

/// The ceiling on the **number of words** an enumeration may materialize.
///
/// \[definition\] A horizon inside [`WORD_LENGTH_CEILING`] with a generator count inside
/// [`GENERATOR_CEILING`] still names `32^32` words. This ceiling bounds what is actually formed,
/// and the sum is computed with checked arithmetic before the first allocation.
pub const WORD_COUNT_CEILING: usize = 1 << 14;

/// The ceiling on the number of members an enumerated source population may declare.
pub const POPULATION_CEILING: usize = 1024;

/// The ceiling on the number of declared future observations one sufficiency check may carry.
pub const OBSERVATION_CEILING: usize = 1024;

/// The ceiling on the **product** `words · receivers` an extinction search will actually read.
///
/// \[definition\] [`WORD_COUNT_CEILING`] bounds the word family and [`OBSERVATION_CEILING`] bounds
/// the receiver family, but their product is what the search actually performs, and each element
/// of it is one exact width over a two-point family. The product is formed with checked
/// arithmetic before the first word is transported.
pub const SEARCH_WORK_CEILING: usize = 1 << 18;

/// The ceiling on the **product** `pairs · observations` a sufficiency check will actually read.
///
/// \[definition\] The two ceilings above bound each declaration separately; this bounds the work,
/// which is what a hostile pair of declarations actually buys. The product is formed with checked
/// arithmetic, so a declaration whose product overflows `usize` is refused rather than wrapping.
pub const CHECK_WORK_CEILING: usize = 1 << 20;

fn zero() -> Rat {
    Rat::zero()
}

fn one() -> Rat {
    Rat::from_integer(BigInt::from(1))
}

// -------------------------------------------------------------------------------------------
// T2 (a) — the admitted passages and their ordered words
// -------------------------------------------------------------------------------------------

/// **The admitted generator family**: finitely many exact linear passages on one carrier.
///
/// \[implemented-exact\] Every field is private and the only constructor is [`Self::declared`],
/// which checks the extent, the generator count, the squareness of every map and the agreement of
/// the declared names with the declared maps. There is no `Default` and no `Deserialize`, so a
/// wire cannot mint a family whose names and maps disagree.
///
/// \[definition; agent-inferred\] **The linear-map chart of a generator family.** Each member is
/// the finite exact linear passage a generator induces on this carrier, not the generator itself:
/// a core [`crate::generator::Generator`] (transport, initial configuration, clock, phase
/// lift) enters here only through its induced map, e.g. one Cayley tick of a `Transport::Linear`
/// is the member `(I − hA/2)⁻¹(I + hA/2)`. The initial configuration, clock and winding are not
/// retained by this chart; standing sufficiency is read over the passages alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratorFamily {
    lineage: String,
    extent: usize,
    names: Vec<String>,
    maps: Vec<ExactRatMatrix>,
}

impl GeneratorFamily {
    /// A declared family. The extent is read from the first map and every other map is checked
    /// against it; the name vector is an exterior declaration and is checked against the map
    /// count rather than trusted.
    pub fn declared(
        lineage: impl Into<String>,
        names: Vec<String>,
        maps: Vec<ExactRatMatrix>,
    ) -> Result<Self, StandingRefusal> {
        if maps.is_empty() {
            return Err(StandingRefusal::EmptyGeneratorFamily);
        }
        if maps.len() > GENERATOR_CEILING {
            return Err(StandingRefusal::GeneratorCeiling {
                declared: maps.len(),
                ceiling: GENERATOR_CEILING,
            });
        }
        if names.len() != maps.len() {
            return Err(StandingRefusal::GeneratorNameCount {
                names: names.len(),
                maps: maps.len(),
            });
        }
        let extent = maps[0].rows();
        if extent == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if extent > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: extent,
                ceiling: EXTENT_CEILING,
            });
        }
        for map in &maps {
            if !map.is_square() || map.rows() != extent {
                return Err(StandingRefusal::GeneratorShape {
                    extent,
                    rows: map.rows(),
                    columns: map.columns(),
                });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            extent,
            names,
            maps,
        })
    }

    /// What this family transports.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The carrier extent.
    pub fn extent(&self) -> usize {
        self.extent
    }

    /// How many generators are admitted.
    pub fn count(&self) -> usize {
        self.maps.len()
    }

    /// The generators' declared names, in declaration order.
    pub fn names(&self) -> &[String] {
        &self.names
    }

    /// One admitted passage applied to one exact state.
    pub fn step(&self, generator: usize, state: &[Rat]) -> Result<Vec<Rat>, StandingRefusal> {
        let map = self
            .maps
            .get(generator)
            .ok_or(StandingRefusal::GeneratorAbsent {
                index: generator,
                carried: self.maps.len(),
            })?;
        if state.len() != self.extent {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.extent,
                found: state.len(),
            });
        }
        Ok(map.apply(state)?)
    }

    /// **The ordered transport word.**
    ///
    /// The convention is the Lean owner's `Foundation/TransportWord.lean::transportWord`: the
    /// word is read right to left, so the last letter acts first. A word longer than
    /// [`WORD_LENGTH_CEILING`] is refused by name before the first application.
    pub fn transport_word(
        &self,
        word: &[usize],
        state: &[Rat],
    ) -> Result<Vec<Rat>, StandingRefusal> {
        if word.len() > WORD_LENGTH_CEILING {
            return Err(StandingRefusal::WordLengthCeiling {
                declared: word.len(),
                ceiling: WORD_LENGTH_CEILING,
            });
        }
        if state.len() != self.extent {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.extent,
                found: state.len(),
            });
        }
        let mut current = state.to_vec();
        for letter in word.iter().rev() {
            current = self.step(*letter, &current)?;
        }
        Ok(current)
    }

    /// **Every admitted word of length at most `horizon`.**
    ///
    /// # Declared-size guard
    ///
    /// \[implemented-exact\] The family has `Σ_{k≤h} g^k` members, exponential in the declared
    /// horizon. That sum is formed with `checked_add` and `checked_mul` and compared against
    /// [`WORD_COUNT_CEILING`] **before** any `Vec` is reserved, so a hostile horizon is a typed
    /// refusal and never a memory request.
    pub fn words_within(&self, horizon: usize) -> Result<Vec<Vec<usize>>, StandingRefusal> {
        if horizon > WORD_LENGTH_CEILING {
            return Err(StandingRefusal::WordLengthCeiling {
                declared: horizon,
                ceiling: WORD_LENGTH_CEILING,
            });
        }
        let generators = self.maps.len();
        let mut total: usize = 0;
        let mut level: usize = 1;
        for _ in 0..=horizon {
            total = total
                .checked_add(level)
                .ok_or(StandingRefusal::WordCountCeiling {
                    horizon,
                    generators,
                    ceiling: WORD_COUNT_CEILING,
                })?;
            if total > WORD_COUNT_CEILING {
                return Err(StandingRefusal::WordCountCeiling {
                    horizon,
                    generators,
                    ceiling: WORD_COUNT_CEILING,
                });
            }
            level = level
                .checked_mul(generators)
                .ok_or(StandingRefusal::WordCountCeiling {
                    horizon,
                    generators,
                    ceiling: WORD_COUNT_CEILING,
                })?;
        }
        let mut words: Vec<Vec<usize>> = Vec::with_capacity(total);
        words.push(Vec::new());
        let mut frontier: Vec<Vec<usize>> = vec![Vec::new()];
        for _ in 0..horizon {
            let mut next: Vec<Vec<usize>> = Vec::new();
            for word in &frontier {
                for generator in 0..generators {
                    let mut extended = word.clone();
                    extended.push(generator);
                    next.push(extended);
                }
            }
            words.extend(next.iter().cloned());
            frontier = next;
        }
        Ok(words)
    }
}

// -------------------------------------------------------------------------------------------
// T2 (b) — the source population and its standing
// -------------------------------------------------------------------------------------------

/// **An enumerated lineage**: the exact source states whose standing is being compared.
///
/// \[implemented-exact\] Private fields, one validating constructor, no `Default` and no
/// `Deserialize`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourcePopulation {
    lineage: String,
    extent: usize,
    members: Vec<Vec<Rat>>,
}

impl SourcePopulation {
    /// A declared population, with its size checked against [`POPULATION_CEILING`] and its
    /// members checked against one another for a common extent.
    pub fn declared(
        lineage: impl Into<String>,
        members: Vec<Vec<Rat>>,
    ) -> Result<Self, StandingRefusal> {
        if members.is_empty() {
            return Err(StandingRefusal::EmptyPopulation);
        }
        if members.len() > POPULATION_CEILING {
            return Err(StandingRefusal::PopulationCeiling {
                declared: members.len(),
                ceiling: POPULATION_CEILING,
            });
        }
        let extent = members[0].len();
        if extent == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if extent > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: extent,
                ceiling: EXTENT_CEILING,
            });
        }
        for member in &members {
            if member.len() != extent {
                return Err(StandingRefusal::ExtentMismatch {
                    declared: extent,
                    found: member.len(),
                });
            }
        }
        // The pair count is the work this population asks for; form it with checked arithmetic.
        let count = members.len();
        count
            .checked_mul(count.saturating_sub(1))
            .ok_or(StandingRefusal::PairCountOverflows { members: count })?;
        Ok(Self {
            lineage: lineage.into(),
            extent,
            members,
        })
    }

    /// What this population is the population of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The common extent.
    pub fn extent(&self) -> usize {
        self.extent
    }

    /// The members, in declaration order.
    pub fn members(&self) -> &[Vec<Rat>] {
        &self.members
    }
}

/// **A standing law**: the exact linear retention `S` a lineage's passages leave behind.
///
/// \[definition\] `retain` is a quotient, not a decoder. Nothing requires it to be injective and
/// nothing requires the passage history to be recoverable from it — AGENTS.md: *"Causal origin
/// does not prescribe an event archive."* What it owes is [`sufficiency`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StandingLaw {
    lineage: String,
    retain: ExactRatMatrix,
}

impl StandingLaw {
    /// A declared retention map, with both extents checked against [`EXTENT_CEILING`].
    pub fn declared(
        lineage: impl Into<String>,
        retain: ExactRatMatrix,
    ) -> Result<Self, StandingRefusal> {
        if retain.rows() == 0 || retain.columns() == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if retain.columns() > EXTENT_CEILING || retain.rows() > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: retain.columns().max(retain.rows()),
                ceiling: EXTENT_CEILING,
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            retain,
        })
    }

    /// What this standing is the standing of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The source extent this standing reads.
    pub fn source_extent(&self) -> usize {
        self.retain.columns()
    }

    /// The extent of the retained residue.
    pub fn retained_extent(&self) -> usize {
        self.retain.rows()
    }

    /// The standing of one exact source state.
    pub fn retained(&self, source: &[Rat]) -> Result<Vec<Rat>, StandingRefusal> {
        if source.len() != self.retain.columns() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.retain.columns(),
                found: source.len(),
            });
        }
        Ok(self.retain.apply(source)?)
    }
}

/// **An exact linear reading**, with the receiver's declared name.
///
/// \[implemented-exact\] Private fields and one validating constructor. It implements
/// [`crate::law::receiver::Reading`], so every width taken here is the release owner's width
/// and not a second diameter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverReading {
    receiver: String,
    matrix: ExactRatMatrix,
}

impl ReceiverReading {
    /// A declared reading.
    pub fn declared(
        receiver: impl Into<String>,
        matrix: ExactRatMatrix,
    ) -> Result<Self, StandingRefusal> {
        if matrix.rows() == 0 || matrix.columns() == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if matrix.columns() > EXTENT_CEILING || matrix.rows() > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: matrix.columns().max(matrix.rows()),
                ceiling: EXTENT_CEILING,
            });
        }
        Ok(Self {
            receiver: receiver.into(),
            matrix,
        })
    }

    /// The receiver's declared name.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// The exact reading matrix.
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }

    /// The source extent this receiver reads.
    pub fn source_extent(&self) -> usize {
        self.matrix.columns()
    }

    /// The exact face of one state.
    pub fn face(&self, state: &[Rat]) -> Result<Vec<Rat>, StandingRefusal> {
        if state.len() != self.matrix.columns() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.matrix.columns(),
                found: state.len(),
            });
        }
        Ok(self.matrix.apply(state)?)
    }

    /// The composite `ρ ∘ T` of this reading with a declared passage, formed exactly.
    pub fn after(&self, passage: &ExactRatMatrix) -> Result<Self, StandingRefusal> {
        if self.matrix.columns() != passage.rows() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.matrix.columns(),
                found: passage.rows(),
            });
        }
        Self::declared(self.receiver.clone(), self.matrix.multiply(passage)?)
    }
}

impl ReceiverReading {
    /// **This reading as the core passive coholon** (plan phase 7, `Holon/Law.lean::passive_reading`):
    /// the same name and reader; the coholon reads the state as the effort under the unit storage
    /// chart, so [`Self::face`] and the coholon's value are equal entry for entry, at zero power.
    /// This type is the validated core linear receiver reading with declared extents.
    pub fn passive_coholon(&self) -> PassiveCoholon {
        PassiveCoholon::new(self.receiver.clone(), self.matrix.clone())
    }
}

impl Reading for ReceiverReading {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(self.matrix.apply(state)?))
    }
}

// -------------------------------------------------------------------------------------------
// T2 (c) — sufficiency: the factoring check
// -------------------------------------------------------------------------------------------

/// **One admitted future observation**: a receiver read after a declared ordered history.
///
/// \[definition\] The family of these is the Lean owner's `causalSignature`, enumerated at the
/// finitely many `(ρ, w)` a caller declares.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FutureObservation {
    word: Vec<usize>,
    reading: ReceiverReading,
}

impl FutureObservation {
    /// A declared observation, with its word length checked against [`WORD_LENGTH_CEILING`].
    pub fn declared(word: Vec<usize>, reading: ReceiverReading) -> Result<Self, StandingRefusal> {
        if word.len() > WORD_LENGTH_CEILING {
            return Err(StandingRefusal::WordLengthCeiling {
                declared: word.len(),
                ceiling: WORD_LENGTH_CEILING,
            });
        }
        Ok(Self { word, reading })
    }

    /// The ordered history this observation is taken after.
    pub fn word(&self) -> &[usize] {
        &self.word
    }

    /// The receiver that reads it.
    pub fn reading(&self) -> &ReceiverReading {
        &self.reading
    }
}

/// What the factoring check returned.
///
/// \[definition\] `NotSufficient` is a **refutation with its witness**: the two lineage members
/// whose standing agrees, the receiver and history that separate them, and the two faces. It is
/// the Rust form of `StandingLaw.separating_future_refutes_the_standing`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "sufficiency", rename_all = "kebab-case")]
pub enum SufficiencyVerdict {
    /// Every admitted future observation factors through the standing.
    Sufficient {
        /// How many equal-standing pairs were found.
        pairs: usize,
        /// How many observations each was read under.
        observations: usize,
    },
    /// A declared observation separates two members the standing identified.
    NotSufficient {
        /// Index of the first member.
        left: usize,
        /// Index of the second member.
        right: usize,
        /// The receiver that separated them.
        receiver: String,
        /// The ordered history it read after.
        word: Vec<usize>,
        /// The first member's face.
        left_face: Vec<Rat>,
        /// The second member's face.
        right_face: Vec<Rat>,
    },
}

/// **Is this quotient a lawful standing?**
///
/// \[implemented-exact\] Lean: `standingLaw_exists_iff_future_factors`. A retention map carries a
/// lawful standing exactly when every admitted future observation factors through it, so the
/// check is: for every pair of lineage members with equal standing, every declared observation
/// must agree. The first disagreement is returned as content.
///
/// # Declared-size guard
///
/// The work is `pairs · observations`, formed with `checked_mul` and compared against
/// [`CHECK_WORK_CEILING`] before the first reading.
pub fn sufficiency(
    standing: &StandingLaw,
    population: &SourcePopulation,
    generators: &GeneratorFamily,
    observations: &[FutureObservation],
) -> Result<SufficiencyVerdict, StandingRefusal> {
    check_sufficiency_declaration(standing, population, generators, observations)?;
    let members = population.members();
    let count = members.len();

    let retained = members
        .iter()
        .map(|member| standing.retained(member))
        .collect::<Result<Vec<_>, _>>()?;

    let mut equal_pairs = 0usize;
    for left in 0..count {
        for right in (left + 1)..count {
            if retained[left] != retained[right] {
                continue;
            }
            equal_pairs += 1;
            for observation in observations {
                let advanced_left =
                    generators.transport_word(observation.word(), &members[left])?;
                let advanced_right =
                    generators.transport_word(observation.word(), &members[right])?;
                let left_face = observation.reading().face(&advanced_left)?;
                let right_face = observation.reading().face(&advanced_right)?;
                if left_face != right_face {
                    return Ok(SufficiencyVerdict::NotSufficient {
                        left,
                        right,
                        receiver: observation.reading().receiver().to_owned(),
                        word: observation.word().to_vec(),
                        left_face,
                        right_face,
                    });
                }
            }
        }
    }
    Ok(SufficiencyVerdict::Sufficient {
        pairs: equal_pairs,
        observations: observations.len(),
    })
}

/// The declared-size and extent checks [`sufficiency`] asks before its first reading, shared with
/// [`sufficiency_descent`] so the two readings of one factoring refuse identically.
fn check_sufficiency_declaration(
    standing: &StandingLaw,
    population: &SourcePopulation,
    generators: &GeneratorFamily,
    observations: &[FutureObservation],
) -> Result<(), StandingRefusal> {
    if standing.source_extent() != population.extent() {
        return Err(StandingRefusal::ExtentMismatch {
            declared: standing.source_extent(),
            found: population.extent(),
        });
    }
    if generators.extent() != population.extent() {
        return Err(StandingRefusal::ExtentMismatch {
            declared: generators.extent(),
            found: population.extent(),
        });
    }
    if observations.len() > OBSERVATION_CEILING {
        return Err(StandingRefusal::ObservationCeiling {
            declared: observations.len(),
            ceiling: OBSERVATION_CEILING,
        });
    }
    let members = population.members();
    let count = members.len();
    let pair_count = count
        .checked_mul(count.saturating_sub(1))
        .ok_or(StandingRefusal::PairCountOverflows { members: count })?
        / 2;
    let work = pair_count.checked_mul(observations.len().max(1)).ok_or(
        StandingRefusal::CheckWorkCeiling {
            pairs: pair_count,
            observations: observations.len(),
            ceiling: CHECK_WORK_CEILING,
        },
    )?;
    if work > CHECK_WORK_CEILING {
        return Err(StandingRefusal::CheckWorkCeiling {
            pairs: pair_count,
            observations: observations.len(),
            ceiling: CHECK_WORK_CEILING,
        });
    }
    for observation in observations {
        for letter in observation.word() {
            if *letter >= generators.count() {
                return Err(StandingRefusal::GeneratorAbsent {
                    index: *letter,
                    carried: generators.count(),
                });
            }
        }
        if observation.reading().source_extent() != population.extent() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: observation.reading().source_extent(),
                found: population.extent(),
            });
        }
    }
    Ok(())
}

impl StandingLaw {
    /// **The standing as a core restriction**: `S` transports the retained residue and retains the
    /// kernel component `x − σ S x` (`crate::restriction::LinearRestriction`), which, with
    /// the standing, reopens the source exactly. Nothing requires `S` to be injective.
    pub fn restriction(&self) -> Result<LinearRestriction, StandingRefusal> {
        Ok(LinearRestriction::new(self.retain.clone())?)
    }
}

/// The sufficiency check read as the core restriction's factor descent: the reading of one member
/// is its face under every declared observation, in declaration order.
pub type SufficiencyDescent = FactorDescent<Vec<Rat>, Vec<Rat>, Vec<Vec<Rat>>>;

/// **Sufficiency as descent** (`Foundation/Standing.lean::standingLaw_exists_iff_future_factors`):
/// the admitted future factors through the standing — a witness carrying the induced reading on
/// the retained residues — or the pairs of members with equal standing that some observation
/// separates, with the kernel residuals that still separate them. [`sufficiency`]'s
/// `NotSufficient { left, right, .. }` is this descent's first break and its `Sufficient { pairs }`
/// is the witness's merged-pair count.
pub fn sufficiency_descent(
    standing: &StandingLaw,
    population: &SourcePopulation,
    generators: &GeneratorFamily,
    observations: &[FutureObservation],
) -> Result<SufficiencyDescent, StandingRefusal> {
    check_sufficiency_declaration(standing, population, generators, observations)?;
    let members = population.members();
    let mut readings = Vec::with_capacity(members.len());
    for member in members {
        let mut faces = Vec::with_capacity(observations.len());
        for observation in observations {
            let advanced = generators.transport_word(observation.word(), member)?;
            faces.push(observation.reading().face(&advanced)?);
        }
        readings.push(faces);
    }
    let restriction = standing.restriction()?;
    // The population ceiling is below the descent ceiling, so this refusal is unreachable through
    // a declared population; it is reported in the population's vocabulary.
    factor_descent_over(&restriction, members, &readings).map_err(|_| {
        StandingRefusal::PopulationCeiling {
            declared: members.len(),
            ceiling: POPULATION_CEILING,
        }
    })
}

// -------------------------------------------------------------------------------------------
// T2 (d) — memory as a generator
// -------------------------------------------------------------------------------------------

/// **A face carried at a declared time.**
///
/// \[definition\] Lean: `TimedFace`. There the time is part of the *type*, so a face generated now
/// and the face an original occurrence carried cannot be compared by `=` at all. Rust has no such
/// dependent type, so the time is carried as data and [`TimedFace::occurs_at`] is the reading that
/// separates them. A reconstruction is a **new occurrence**: it occurs now.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TimedFace {
    time: usize,
    value: Vec<Rat>,
}

impl TimedFace {
    /// A face declared at a time.
    pub fn declared(time: usize, value: Vec<Rat>) -> Result<Self, StandingRefusal> {
        if value.is_empty() {
            return Err(StandingRefusal::EmptyExtent);
        }
        if value.len() > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: value.len(),
                ceiling: EXTENT_CEILING,
            });
        }
        Ok(Self { time, value })
    }

    /// The time this face occurs at.
    pub fn occurs_at(&self) -> usize {
        self.time
    }

    /// Its exact value.
    pub fn value(&self) -> &[Rat] {
        &self.value
    }
}

/// **The reconstruction `D_t`.**
///
/// \[definition\] `m_t = D_t(S_t, c_t)`: it takes the standing and the present context and
/// *constitutes* a face at the present time. It receives no original. Both parts are exact linear
/// maps, so the whole generation is exact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MemoryLaw {
    present: usize,
    from_standing: ExactRatMatrix,
    from_context: ExactRatMatrix,
}

impl MemoryLaw {
    /// A declared reconstruction. The two maps must return faces of one extent.
    pub fn declared(
        present: usize,
        from_standing: ExactRatMatrix,
        from_context: ExactRatMatrix,
    ) -> Result<Self, StandingRefusal> {
        if from_standing.rows() != from_context.rows() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: from_standing.rows(),
                found: from_context.rows(),
            });
        }
        if from_standing.rows() == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if from_standing.rows() > EXTENT_CEILING
            || from_standing.columns() > EXTENT_CEILING
            || from_context.columns() > EXTENT_CEILING
        {
            return Err(StandingRefusal::ExtentCeiling {
                declared: from_standing
                    .rows()
                    .max(from_standing.columns())
                    .max(from_context.columns()),
                ceiling: EXTENT_CEILING,
            });
        }
        Ok(Self {
            present,
            from_standing,
            from_context,
        })
    }

    /// The present time this law generates at.
    pub fn present(&self) -> usize {
        self.present
    }

    /// The standing extent it reads.
    pub fn standing_extent(&self) -> usize {
        self.from_standing.columns()
    }

    /// The context extent it reads.
    pub fn context_extent(&self) -> usize {
        self.from_context.columns()
    }

    /// **`m_t = D_t(S_t, c_t)`**, stamped with the present time.
    ///
    /// The original is not an argument. What returns is a new occurrence in a related family,
    /// constituted from the standing the original helped form and the context of now.
    pub fn remember(
        &self,
        standing: &[Rat],
        context: &[Rat],
    ) -> Result<TimedFace, StandingRefusal> {
        if standing.len() != self.from_standing.columns() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.from_standing.columns(),
                found: standing.len(),
            });
        }
        if context.len() != self.from_context.columns() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.from_context.columns(),
                found: context.len(),
            });
        }
        let retained = self.from_standing.apply(standing)?;
        let present = self.from_context.apply(context)?;
        let value = retained
            .iter()
            .zip(&present)
            .map(|(left, right)| left + right)
            .collect();
        TimedFace::declared(self.present, value)
    }
}

/// What the fidelity check returned.
///
/// \[definition\] Lean: `faithfulAt_iff_receiver_factors_through_standing`. A reconstruction can
/// agree with the original at receiver `ρ` **exactly when** `ρ` factors through what standing
/// retained; `NotRetained` carries the two lineage members that refute the factoring, which is
/// `Foundation/Receiver.lean::ReceiverInsufficiency` returned as data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "fidelity", rename_all = "kebab-case")]
pub enum Fidelity {
    /// The receiver factors through the standing: a faithful reconstruction exists.
    Faithful {
        /// The receiver's declared name.
        receiver: String,
        /// How many equal-standing pairs were checked.
        checked: usize,
    },
    /// The receiver does not factor: no reconstruction from standing alone can return it.
    NotRetained {
        /// The receiver's declared name.
        receiver: String,
        /// Index of the first member.
        left: usize,
        /// Index of the second member.
        right: usize,
        /// The first member's face.
        left_face: Vec<Rat>,
        /// The second member's face.
        right_face: Vec<Rat>,
    },
}

/// **The fidelity law, executable.**
///
/// \[implemented-exact\] The reading supplied is `ρ ∘ T` — the receiver composed with the passage
/// from the original's time to now, which [`ReceiverReading::after`] forms exactly. The check is
/// the factoring criterion and nothing else: two members with one standing must have one face.
pub fn fidelity(
    standing: &StandingLaw,
    reading: &ReceiverReading,
    population: &SourcePopulation,
) -> Result<Fidelity, StandingRefusal> {
    if standing.source_extent() != population.extent() {
        return Err(StandingRefusal::ExtentMismatch {
            declared: standing.source_extent(),
            found: population.extent(),
        });
    }
    if reading.source_extent() != population.extent() {
        return Err(StandingRefusal::ExtentMismatch {
            declared: reading.source_extent(),
            found: population.extent(),
        });
    }
    let members = population.members();
    let count = members.len();
    count
        .checked_mul(count.saturating_sub(1))
        .ok_or(StandingRefusal::PairCountOverflows { members: count })?;
    let retained = members
        .iter()
        .map(|member| standing.retained(member))
        .collect::<Result<Vec<_>, _>>()?;
    let faces = members
        .iter()
        .map(|member| reading.face(member))
        .collect::<Result<Vec<_>, _>>()?;
    let mut checked = 0usize;
    for left in 0..count {
        for right in (left + 1)..count {
            if retained[left] != retained[right] {
                continue;
            }
            checked += 1;
            if faces[left] != faces[right] {
                return Ok(Fidelity::NotRetained {
                    receiver: reading.receiver().to_owned(),
                    left,
                    right,
                    left_face: faces[left].clone(),
                    right_face: faces[right].clone(),
                });
            }
        }
    }
    Ok(Fidelity::Faithful {
        receiver: reading.receiver().to_owned(),
        checked,
    })
}

// -------------------------------------------------------------------------------------------
// T2 (e) — the receiver that keeps changing after its source stops
// -------------------------------------------------------------------------------------------

/// **A refinement chain of apertures.**
///
/// \[definition\] Lean: `aperture`. The face at step `t` reads the first `t` coordinates of a
/// source and returns zero beyond them, so `t ↦ face(t, ·)` is a chain that acquires distinctions
/// while the source does nothing at all. Its link law is
/// `face(coarse, face(fine, x)) = face(coarse, x)` for `coarse ≤ fine`, which is the zero
/// changing-receiver defect of `Transport/ChangingReceiver.lean::defect`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ApertureChain {
    lineage: String,
    extent: usize,
}

impl ApertureChain {
    /// A declared chain over a carrier of the given extent.
    pub fn declared(lineage: impl Into<String>, extent: usize) -> Result<Self, StandingRefusal> {
        if extent == 0 {
            return Err(StandingRefusal::EmptyExtent);
        }
        if extent > EXTENT_CEILING {
            return Err(StandingRefusal::ExtentCeiling {
                declared: extent,
                ceiling: EXTENT_CEILING,
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            extent,
        })
    }

    /// What this chain reads.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The carrier extent.
    pub fn extent(&self) -> usize {
        self.extent
    }

    /// The face at one step of the chain: the first `step` coordinates, zero beyond.
    pub fn face(&self, step: usize, source: &[Rat]) -> Result<Vec<Rat>, StandingRefusal> {
        if source.len() != self.extent {
            return Err(StandingRefusal::ExtentMismatch {
                declared: self.extent,
                found: source.len(),
            });
        }
        Ok(source
            .iter()
            .enumerate()
            .map(
                |(index, value)| {
                    if index < step { value.clone() } else { zero() }
                },
            )
            .collect())
    }

    /// Whether a candidate is in the fibre of sources compatible with what step `t` can read of
    /// the reference.
    pub fn compatible(
        &self,
        step: usize,
        candidate: &[Rat],
        reference: &[Rat],
    ) -> Result<bool, StandingRefusal> {
        Ok(self.face(step, candidate)? == self.face(step, reference)?)
    }

    /// **The first step of the chain that separates two sources**, or `None` when no step up to
    /// the carrier's extent does. What one step cannot separate a later step can; this returns
    /// which one.
    pub fn first_separating_step(
        &self,
        left: &[Rat],
        right: &[Rat],
    ) -> Result<Option<usize>, StandingRefusal> {
        for step in 0..=self.extent {
            if !self.compatible(step, left, right)? {
                return Ok(Some(step));
            }
        }
        Ok(None)
    }
}

// -------------------------------------------------------------------------------------------
// T2 (f) — effective extinction
// -------------------------------------------------------------------------------------------

/// **A contraction certificate on a declared coordinate chart.**
///
/// \[definition\] The chart is a set of coordinates and `factor` is an exact rational `λ ≤ 1`.
/// [`Self::verify`] **checks** against every generator that the chart is invariant and that every
/// chart row sums to at most `λ`. Nothing is assumed: a tower whose steps do not actually contract
/// is refused by name with the row that refutes it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ContractionCertificate {
    chart: Vec<usize>,
    factor: Rat,
}

impl ContractionCertificate {
    /// A declared certificate. The chart is sorted and checked for duplicates and for membership
    /// in the extent; the factor is checked to be in `[0, 1]`.
    pub fn declared(
        chart: Vec<usize>,
        factor: Rat,
        extent: usize,
    ) -> Result<Self, StandingRefusal> {
        if chart.is_empty() {
            return Err(StandingRefusal::EmptyChart);
        }
        if chart.len() > extent {
            return Err(StandingRefusal::ChartOutsideExtent {
                coordinate: chart.len(),
                extent,
            });
        }
        let mut sorted = chart;
        sorted.sort_unstable();
        for pair in sorted.windows(2) {
            if pair[0] == pair[1] {
                return Err(StandingRefusal::ChartRepeatsCoordinate {
                    coordinate: pair[0],
                });
            }
        }
        if let Some(last) = sorted.last()
            && *last >= extent
        {
            return Err(StandingRefusal::ChartOutsideExtent {
                coordinate: *last,
                extent,
            });
        }
        if factor.is_negative() || factor > one() {
            return Err(StandingRefusal::FactorOutsideUnitInterval {
                declared: factor.to_string(),
            });
        }
        Ok(Self {
            chart: sorted,
            factor,
        })
    }

    /// The chart, sorted.
    pub fn chart(&self) -> &[usize] {
        &self.chart
    }

    /// The exact contraction factor.
    pub fn factor(&self) -> &Rat {
        &self.factor
    }

    /// Whether a coordinate is inside the chart.
    fn holds(&self, coordinate: usize) -> bool {
        self.chart.binary_search(&coordinate).is_ok()
    }

    /// **Check the certificate against every admitted generator.**
    ///
    /// Two obligations, both exact: the chart is invariant (`A[i][j] = 0` for `i` inside and `j`
    /// outside), and every chart row sums in absolute value to at most `λ`.
    pub fn verify(&self, generators: &GeneratorFamily) -> Result<(), StandingRefusal> {
        let extent = generators.extent();
        if let Some(last) = self.chart.last()
            && *last >= extent
        {
            return Err(StandingRefusal::ChartOutsideExtent {
                coordinate: *last,
                extent,
            });
        }
        for (index, map) in generators.maps.iter().enumerate() {
            for row in self.chart.iter().copied() {
                let mut sum = zero();
                for column in 0..extent {
                    let entry = map.get(row, column)?;
                    if self.holds(column) {
                        sum += entry.abs();
                    } else if !entry.is_zero() {
                        return Err(StandingRefusal::ChartNotInvariant {
                            generator: generators.names[index].clone(),
                            row,
                            column,
                        });
                    }
                }
                if sum > self.factor {
                    return Err(StandingRefusal::ChartDoesNotContract {
                        generator: generators.names[index].clone(),
                        row,
                        sum: sum.to_string(),
                        factor: self.factor.to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    /// **The exact gain of a reading supported on the chart**: `max_i Σ_{j∈C} |R[i][j]|`.
    ///
    /// A reading with a nonzero entry outside the chart is refused by name: the certificate says
    /// nothing about coordinates it does not cover, and pretending otherwise is how a false
    /// extinction verdict would be manufactured.
    pub fn reading_gain(&self, reading: &ReceiverReading) -> Result<Rat, StandingRefusal> {
        let columns = reading.matrix.columns();
        if let Some(last) = self.chart.last()
            && *last >= columns
        {
            return Err(StandingRefusal::ChartOutsideExtent {
                coordinate: *last,
                extent: columns,
            });
        }
        let mut gain = zero();
        for row in 0..reading.matrix.rows() {
            let mut sum = zero();
            for column in 0..columns {
                let entry = reading.matrix.get(row, column)?;
                if self.holds(column) {
                    sum += entry.abs();
                } else if !entry.is_zero() {
                    return Err(StandingRefusal::ReadingOutsideChart {
                        receiver: reading.receiver.clone(),
                        row,
                        column,
                    });
                }
            }
            if sum > gain {
                gain = sum;
            }
        }
        Ok(gain)
    }

    /// The exact sup-norm separation of two states restricted to the chart.
    pub fn chart_separation(&self, left: &[Rat], right: &[Rat]) -> Result<Rat, StandingRefusal> {
        if left.len() != right.len() {
            return Err(StandingRefusal::ExtentMismatch {
                declared: left.len(),
                found: right.len(),
            });
        }
        let mut widest = zero();
        for coordinate in self.chart.iter().copied() {
            let (Some(a), Some(b)) = (left.get(coordinate), right.get(coordinate)) else {
                return Err(StandingRefusal::ChartOutsideExtent {
                    coordinate,
                    extent: left.len(),
                });
            };
            let separation = (a - b).abs();
            if separation > widest {
                widest = separation;
            }
        }
        Ok(widest)
    }
}

/// What the extinction check returned.
///
/// \[definition\] Three values, never two. `Extinct` is certificate-backed and holds for the whole
/// infinite word family; `Separated` is a refutation carrying its witness; and
/// `NotDecidedWithinBound` says plainly that the search reached its declared horizon without
/// either.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "extinction", rename_all = "kebab-case")]
pub enum ExtinctionVerdict {
    /// Every admitted future word keeps every declared receiver inside the tolerance, proved by
    /// the certificate rather than by a finite search.
    Extinct {
        /// The declared tolerance.
        tolerance: Rat,
        /// The exact bound `max_ρ γ_ρ · ‖(x − z)_C‖_∞` the certificate produced.
        bound: Rat,
        /// The chart the certificate covers.
        chart: Vec<usize>,
        /// The exact contraction factor it verified.
        factor: Rat,
    },
    /// A declared receiver and an admitted word separate the perturbation beyond tolerance.
    Separated {
        /// The receiver that separates.
        receiver: String,
        /// The ordered history it read after.
        word: Vec<usize>,
        /// The exact width it read on the two-point family.
        width: Rat,
        /// The declared tolerance it exceeded.
        tolerance: Rat,
    },
    /// Neither route decided: no separator inside the declared horizon, and no certificate that
    /// covers the declared receivers.
    NotDecidedWithinBound {
        /// The horizon searched.
        horizon: usize,
        /// How many words were read.
        words: usize,
        /// The widest reading found.
        widest: Rat,
        /// The receiver that attained it.
        receiver: String,
        /// Why the certificate route did not decide.
        reason: String,
    },
}

/// **Effective extinction of a perturbation against a reference.**
///
/// \[implemented-exact\] Lean: `Extinct` and `extinct_iff_release_width_inside_tolerance`. Every
/// width is taken by [`crate::law::receiver::width_over_readings`] over the two-point family
/// `{T_w x, T_w z}` through the core [`crate::law::receiver::width_over_readings`] law in the sup norm, and the decision is
/// [`crate::law::receiver::ReceiverWidth::releasable_at`]. This module computes no diameter of
/// its own.
///
/// The certificate route is tried first because it is cheap and decides the whole infinite family;
/// the enumeration is tried second and can only refute. See the module header for the exact
/// inequality the certificate discharges.
pub fn extinction(
    generators: &GeneratorFamily,
    receivers: &[ReceiverReading],
    perturbation: &[Rat],
    reference: &[Rat],
    horizon: usize,
    tolerance: &Rat,
    certificate: Option<&ContractionCertificate>,
) -> Result<ExtinctionVerdict, StandingRefusal> {
    if receivers.is_empty() {
        return Err(StandingRefusal::EmptyReceiverFamily);
    }
    if receivers.len() > OBSERVATION_CEILING {
        return Err(StandingRefusal::ObservationCeiling {
            declared: receivers.len(),
            ceiling: OBSERVATION_CEILING,
        });
    }
    if tolerance.is_negative() {
        return Err(StandingRefusal::NegativeTolerance {
            declared: tolerance.to_string(),
        });
    }
    let extent = generators.extent();
    if perturbation.len() != extent {
        return Err(StandingRefusal::ExtentMismatch {
            declared: extent,
            found: perturbation.len(),
        });
    }
    if reference.len() != extent {
        return Err(StandingRefusal::ExtentMismatch {
            declared: extent,
            found: reference.len(),
        });
    }
    for reading in receivers {
        if reading.source_extent() != extent {
            return Err(StandingRefusal::ExtentMismatch {
                declared: extent,
                found: reading.source_extent(),
            });
        }
    }

    // The certificate route. It is checked, never trusted, and it decides the whole word family.
    let mut certificate_reason =
        "no contraction certificate was supplied for this receiver family".to_owned();
    if let Some(certificate) = certificate {
        certificate.verify(generators)?;
        let separation = certificate.chart_separation(perturbation, reference)?;
        let mut bound = zero();
        let mut covered = true;
        for reading in receivers {
            match certificate.reading_gain(reading) {
                Ok(gain) => {
                    let reach = &gain * &separation;
                    if reach > bound {
                        bound = reach;
                    }
                }
                Err(StandingRefusal::ReadingOutsideChart { receiver, .. }) => {
                    certificate_reason = format!(
                        "the receiver {receiver} reads a coordinate the certified chart does not \
                         cover"
                    );
                    covered = false;
                    break;
                }
                Err(other) => return Err(other),
            }
        }
        if covered {
            if &bound <= tolerance {
                return Ok(ExtinctionVerdict::Extinct {
                    tolerance: tolerance.clone(),
                    bound,
                    chart: certificate.chart().to_vec(),
                    factor: certificate.factor().clone(),
                });
            }
            certificate_reason = format!(
                "the certified bound {bound} is outside the declared tolerance {tolerance}"
            );
        }
    }

    // The enumeration route. It can only refute, and it returns the first witness it finds.
    let words = generators.words_within(horizon)?;
    let search_work =
        words
            .len()
            .checked_mul(receivers.len())
            .ok_or(StandingRefusal::SearchWorkCeiling {
                words: words.len(),
                receivers: receivers.len(),
                ceiling: SEARCH_WORK_CEILING,
            })?;
    if search_work > SEARCH_WORK_CEILING {
        return Err(StandingRefusal::SearchWorkCeiling {
            words: words.len(),
            receivers: receivers.len(),
            ceiling: SEARCH_WORK_CEILING,
        });
    }
    let mut widest = zero();
    let mut widest_receiver = receivers[0].receiver().to_owned();
    for word in &words {
        let advanced_perturbation = generators.transport_word(word, perturbation)?;
        let advanced_reference = generators.transport_word(word, reference)?;
        for reading in receivers {
            let faces = [
                reading.read(&advanced_perturbation)?,
                reading.read(&advanced_reference)?,
            ];
            let width = width_over_readings(
                reading.receiver(),
                &format!("{}|{{x,0}}", generators.lineage()),
                &faces,
                DiameterNorm::Supremum,
            )?;
            if !width.releasable_at(tolerance) {
                return Ok(ExtinctionVerdict::Separated {
                    receiver: reading.receiver().to_owned(),
                    word: word.clone(),
                    width: width.diameter().clone(),
                    tolerance: tolerance.clone(),
                });
            }
            if width.diameter() > &widest {
                widest = width.diameter().clone();
                widest_receiver = reading.receiver().to_owned();
            }
        }
    }
    Ok(ExtinctionVerdict::NotDecidedWithinBound {
        horizon,
        words: words.len(),
        widest,
        receiver: widest_receiver,
        reason: certificate_reason,
    })
}

// -------------------------------------------------------------------------------------------
// T2 (g) — refusals
// -------------------------------------------------------------------------------------------

/// Why a standing, a reconstruction or an extinction check was refused. Every failure is returned
/// as content; nothing here panics on a declaration.
#[derive(Debug, Error)]
pub enum StandingRefusal {
    /// A generator family with no generator transports nothing.
    #[error("a generator family with no generator transports nothing")]
    EmptyGeneratorFamily,
    /// The declared generator count is past its ceiling.
    #[error("a declared generator count of {declared} is past the ceiling of {ceiling}")]
    GeneratorCeiling {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The declared generator names and maps disagree in number.
    #[error("{names} declared generator names do not match {maps} declared maps")]
    GeneratorNameCount {
        /// How many names.
        names: usize,
        /// How many maps.
        maps: usize,
    },
    /// A declared generator is not a square map of the family's extent.
    #[error("a generator of extent {extent} cannot be a {rows} by {columns} map")]
    GeneratorShape {
        /// The family's extent.
        extent: usize,
        /// The map's rows.
        rows: usize,
        /// The map's columns.
        columns: usize,
    },
    /// A word names a generator the family does not carry.
    #[error("generator {index} is absent from a family of {carried}")]
    GeneratorAbsent {
        /// The index named.
        index: usize,
        /// How many the family carries.
        carried: usize,
    },
    /// An extent of zero carries nothing.
    #[error("an extent of zero carries nothing")]
    EmptyExtent,
    /// A declared extent is past its ceiling.
    #[error("a declared extent of {declared} is past the ceiling of {ceiling}")]
    ExtentCeiling {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// Two declared extents disagree.
    #[error("an extent of {declared} was declared and {found} was presented")]
    ExtentMismatch {
        /// The declared extent.
        declared: usize,
        /// What was presented.
        found: usize,
    },
    /// A declared word is longer than the ceiling.
    #[error("a declared word length of {declared} is past the ceiling of {ceiling}")]
    WordLengthCeiling {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The word family a horizon names is past the ceiling.
    #[error(
        "a horizon of {horizon} over {generators} generators names more words than the ceiling \
         of {ceiling}"
    )]
    WordCountCeiling {
        /// The declared horizon.
        horizon: usize,
        /// The generator count.
        generators: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A population with no member is not a lineage.
    #[error("a population with no member is not a lineage")]
    EmptyPopulation,
    /// The declared population is past its ceiling.
    #[error("a declared population of {declared} is past the ceiling of {ceiling}")]
    PopulationCeiling {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The pair count of a declared population overflows.
    #[error("the pair count of {members} declared members overflows")]
    PairCountOverflows {
        /// How many members.
        members: usize,
    },
    /// The declared observation family is past its ceiling.
    #[error("a declared observation family of {declared} is past the ceiling of {ceiling}")]
    ObservationCeiling {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The work a sufficiency check would perform is past its ceiling.
    #[error(
        "{pairs} equal-standing pairs read under {observations} observations is past the work \
         ceiling of {ceiling}"
    )]
    CheckWorkCeiling {
        /// The pair count.
        pairs: usize,
        /// The observation count.
        observations: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The work an extinction search would perform is past its ceiling.
    #[error(
        "{words} admitted words read by {receivers} receivers is past the search work ceiling of \
         {ceiling}"
    )]
    SearchWorkCeiling {
        /// The word count.
        words: usize,
        /// The receiver count.
        receivers: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// An empty receiver family declares nothing extinct.
    #[error("an empty receiver family declares nothing extinct")]
    EmptyReceiverFamily,
    /// A negative tolerance is not a tolerance.
    #[error("a declared tolerance of {declared} is negative")]
    NegativeTolerance {
        /// What was declared.
        declared: String,
    },
    /// An empty chart certifies nothing.
    #[error("an empty chart certifies nothing")]
    EmptyChart,
    /// A declared chart names a coordinate outside the extent.
    #[error("a chart naming coordinate {coordinate} is outside an extent of {extent}")]
    ChartOutsideExtent {
        /// The coordinate named.
        coordinate: usize,
        /// The extent.
        extent: usize,
    },
    /// A declared chart names one coordinate twice.
    #[error("a chart names coordinate {coordinate} twice")]
    ChartRepeatsCoordinate {
        /// The repeated coordinate.
        coordinate: usize,
    },
    /// A declared contraction factor is outside `[0, 1]`.
    #[error("a declared contraction factor of {declared} is outside the unit interval")]
    FactorOutsideUnitInterval {
        /// What was declared.
        declared: String,
    },
    /// The chart is not invariant under a declared generator.
    #[error(
        "the generator {generator} carries a nonzero entry at row {row}, column {column}, so the \
         certified chart is not invariant under it"
    )]
    ChartNotInvariant {
        /// The generator's declared name.
        generator: String,
        /// The chart row.
        row: usize,
        /// The column outside the chart.
        column: usize,
    },
    /// The chart does not contract under a declared generator.
    #[error(
        "the generator {generator} has chart row {row} summing to {sum}, which is past the \
         declared factor {factor}"
    )]
    ChartDoesNotContract {
        /// The generator's declared name.
        generator: String,
        /// The chart row.
        row: usize,
        /// The exact row sum.
        sum: String,
        /// The declared factor.
        factor: String,
    },
    /// A declared reading reads outside the certified chart.
    #[error(
        "the receiver {receiver} reads coordinate {column} at row {row}, which the certified \
         chart does not cover"
    )]
    ReadingOutsideChart {
        /// The receiver's declared name.
        receiver: String,
        /// The reading row.
        row: usize,
        /// The column outside the chart.
        column: usize,
    },
    /// The receiver-width law refused.
    #[error(transparent)]
    Width(#[from] WidthRefusal),
    /// The exact linear algebra refused.
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// The core restriction refused the standing's retention map.
    #[error(transparent)]
    Restriction(#[from] crate::holon::HolonError),
}

impl PartialEq for StandingRefusal {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

#[cfg(test)]
#[path = "standing_tests.rs"]
mod tests;
