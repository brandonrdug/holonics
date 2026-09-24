//! **T1 — the relation ladder: one typed scale between two occurrences.**
//!
//! [definition] This module is the executable owner of item **T1** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Lean
//! counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/RelationLadder.lean`
//! (namespace `Soma.Holonics.Foundation.RelationLadder`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `Rung`, `Rung.entailed`, `Rung.entails` | [`Rung`], [`Rung::entailed`], [`Rung::entails`] |
//! | `entails_refl`, `entails_trans`, `entails_antisymm`, `entails_is_not_total` | the order tests |
//! | `no_rung_below_identity_entails_identity` | [`Rung::entails`] and its test |
//! | `rungMeet`, `rungMeet_comm`, `rungMeet_lower`, `rungMeet_greatest` | [`rung_meet`] |
//! | `Situation` | [`Situation`], built by [`Situation::declare`] |
//! | `SituationAuto`, `SituationAuto.step_natural`, `SituationAuto.observe_natural` | [`SituationAutomorphism`], [`Situation::check_automorphism`] |
//! | `equalPotential_of_closedCarrier` | `Situation::automorphism_carrier_is_closed` and [`Situation::classify`] |
//! | `ReceiverEqualAt`, `PresentAgreement` | [`Situation::present_agreement`] |
//! | `EqualPotential`, `potential` | [`Situation::search_separator`] and [`PotentialVerdict`] |
//! | `WithinTolerance`, `withinTolerance_symm`, `withinToleranceIterate` | [`ToleranceReading`] |
//! | `separatorRefutesEqualPotential` | [`Separator`] |
//! | `equalPotentialAntitone` | [`Situation::search_separator`] over the enlarged declaration |
//! | `Expression`, `eval`, `four`, `twoSquared`, `bumpExponent`, `postcomposeAdd` | [`Expression`], [`eval`], [`four`], [`two_squared`], [`bump_exponent`], [`postcompose_add`] |
//! | `Enactment`, `gaps`, `normalizedByFirst`, `musicalFace`, `absoluteFace` | [`Enactment`], [`gaps`], [`normalized_by_first`], [`musical_face`], [`absolute_face`] |
//! | `transpose`, `scaleTempo`, `revoice`, `Admissible`, `enact` | [`transpose`], [`scale_tempo`], [`revoice`], [`Admissible`], [`enact`] |
//!
//! # The governing statement
//!
//! [project-postulate] Brandon, September 18: *Identity belongs to an occurrence. Persistence
//! belongs to lineage. Sameness belongs to a receiver. Potential belongs to a family of future
//! interactions.* `4` and `2^2` differ in [`Expression`] and agree under [`eval`]; the equality
//! belongs to the scalar receiver and does not ascend to identify the formulations. Every
//! counterexample the Lean owner constructs is mirrored here as a test.
//!
//! # Three relativity classes
//!
//! [proved-derived] Rung 1 is absolute. Rungs 3–6 are relative to the declared `(G, R)` that
//! [`Situation`] carries. Rung 2 is relative to a declared **lineage**, so it is on a different
//! axis: [`Rung::Continuation`] is incomparable with [`Rung::ReceiverEqual`] and with
//! [`Rung::EqualPotential`], and [`Classification`] therefore reports it beside the chain rather
//! than inside it.
//!
//! # What is never claimed
//!
//! [definition] **"Not separated within the declared bound" is its own return.** The separator
//! search runs over finite ordered generator histories up to a declared history-length ceiling.
//! Exhausting that ceiling without a separator returns
//! [`PotentialVerdict::NotSeparatedWithinBound`], which carries the bound it ran under and is
//! **never** reported as equal potential. The only executable route to [`Rung::EqualPotential`] is
//! an automorphism checked on a finite carrier containing both occurrences and closed under every
//! admitted generator and both symmetry maps. The closure check supplies the finite situation to
//! which `situationAutoImpliesEqualPotential` applies; a caller's completeness flag alone supplies
//! no proof. A probe without that checked closure stays a probe
//! ([`ClassificationNote::IsomorphismOnlyOnAProbe`]).
//!
//! # No floats, and every declared size is bounded before it is used
//!
//! [implemented-exact] Every carrier, face and reading is exact: `BigUint`, `BigInt`,
//! `BigRational`. [`Situation::declare`] computes the word population
//! `sum_{k=0..L} |G|^k` with checked arithmetic and refuses above [`WORD_POPULATION_CEILING`]
//! before any enumeration; [`eval`] bounds the expression's depth, node count, exponent and result
//! bit length before evaluating; [`Enactment::declare`] bounds its sequences. Every refusal is a
//! typed [`LadderRefusal`], never a panic.

use std::fmt::Debug;

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

// -------------------------------------------------------------------------------------------
// Declared ceilings
// -------------------------------------------------------------------------------------------

/// The largest admitted generator family.
pub const GENERATOR_CEILING: usize = 64;
/// The largest admitted receiver family.
pub const RECEIVER_CEILING: usize = 64;
/// The longest admitted ordered generator history.
pub const HISTORY_LENGTH_CEILING: usize = 20;
/// The largest admitted population of ordered histories, `sum_{k=0..L} |G|^k`.
pub const WORD_POPULATION_CEILING: usize = 1 << 20;
/// The largest admitted number of `(history, receiver)` probes in one search.
pub const PROBE_CEILING: usize = 1 << 22;
/// The largest admitted occurrence probe for an equivariance check.
pub const AUTOMORPHISM_PROBE_CEILING: usize = 1 << 16;
/// The deepest admitted [`Expression`].
pub const EXPRESSION_DEPTH_CEILING: usize = 64;
/// The largest admitted [`Expression`] node count.
pub const EXPRESSION_NODE_CEILING: usize = 4096;
/// The largest admitted exponent in an [`Expression`].
pub const EXPONENT_CEILING: u64 = 1 << 12;
/// The largest admitted bit length of an [`eval`] result.
pub const VALUE_BIT_CEILING: u64 = 1 << 14;
/// The longest admitted pitch or onset sequence in an [`Enactment`].
pub const SEQUENCE_CEILING: usize = 4096;

// -------------------------------------------------------------------------------------------
// Typed refusals
// -------------------------------------------------------------------------------------------

/// Every way this module declines to answer. A refusal is content; nothing here panics.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum LadderRefusal {
    /// A situation with no receiver declares nothing, so no rung below identity is statable.
    #[error("a situation must declare at least one receiver")]
    NoReceiverDeclared,
    /// The declared generator family is larger than [`GENERATOR_CEILING`].
    #[error("the declared generator family has {declared} members, above the ceiling {ceiling}")]
    GeneratorFamilyTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The declared receiver family is larger than [`RECEIVER_CEILING`].
    #[error("the declared receiver family has {declared} members, above the ceiling {ceiling}")]
    ReceiverFamilyTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The declared history-length ceiling is above [`HISTORY_LENGTH_CEILING`].
    #[error("the declared history length {declared} is above the ceiling {ceiling}")]
    HistoryLengthTooLarge {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The ordered-history population the declaration implies is above what may be enumerated.
    /// Computed with checked arithmetic **before** anything is enumerated or allocated.
    #[error(
        "the declaration implies {implied} ordered histories over {generators} generators at \
         length {length}, above the ceiling {ceiling}"
    )]
    HistoryPopulationTooLarge {
        /// The implied population, or `usize::MAX` when the computation itself overflowed.
        implied: usize,
        /// The declared generator count.
        generators: usize,
        /// The declared history length.
        length: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The `(history, receiver)` probe population is above [`PROBE_CEILING`].
    #[error("the declaration implies {implied} probes, above the ceiling {ceiling}")]
    ProbePopulationTooLarge {
        /// The implied probe population.
        implied: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// An occurrence probe larger than [`AUTOMORPHISM_PROBE_CEILING`].
    #[error("the occurrence probe has {declared} members, above the ceiling {ceiling}")]
    OccurrenceProbeTooLarge {
        /// How many were supplied.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A tolerance must be declared non-negative; a negative one names no aperture.
    #[error("the declared tolerance is negative")]
    NegativeTolerance,
    /// An [`Expression`] deeper than [`EXPRESSION_DEPTH_CEILING`].
    #[error("the expression is deeper than the ceiling {ceiling}")]
    ExpressionTooDeep {
        /// The ceiling.
        ceiling: usize,
    },
    /// An [`Expression`] with more nodes than [`EXPRESSION_NODE_CEILING`].
    #[error("the expression has more than {ceiling} nodes")]
    ExpressionTooLarge {
        /// The ceiling.
        ceiling: usize,
    },
    /// An exponent above [`EXPONENT_CEILING`].
    #[error("the exponent is above the ceiling {ceiling}")]
    ExponentTooLarge {
        /// The ceiling.
        ceiling: u64,
    },
    /// A power whose result would exceed [`VALUE_BIT_CEILING`] bits, refused before it is formed.
    #[error("the power would need about {bits} bits, above the ceiling {ceiling}")]
    ValueTooWide {
        /// The implied bit length.
        bits: u64,
        /// The ceiling.
        ceiling: u64,
    },
    /// A pitch or onset sequence longer than [`SEQUENCE_CEILING`].
    #[error("the sequence has {declared} entries, above the ceiling {ceiling}")]
    SequenceTooLong {
        /// How many were supplied.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// An enactment whose pitch and onset sequences do not pair up.
    #[error("the enactment has {pitches} pitches and {onsets} onsets")]
    UnpairedEnactment {
        /// How many pitches.
        pitches: usize,
        /// How many onsets.
        onsets: usize,
    },
    /// A tempo factor of zero is not an admissible transformation: it collapses every onset.
    #[error("a tempo factor of zero is not admissible")]
    ZeroTempoFactor,
    /// An ordered history naming a generator the situation does not declare.
    #[error("the history names generator {index}, and only {declared} are declared")]
    UndeclaredGenerator {
        /// The index the history named.
        index: usize,
        /// How many generators the situation declares.
        declared: usize,
    },
}

// -------------------------------------------------------------------------------------------
// The typed scale
// -------------------------------------------------------------------------------------------

/// [definition] **The scale moved to the core** (plan phase 7): [`Rung`] and [`rung_meet`] are the
/// relation a receiver establishes, and the core tube's defect profile reads it, so they live in
/// `holonics::law::receiver` and are re-exported here at their existing paths.
use holonics::law::receiver::{Rung, rung_meet};

// -------------------------------------------------------------------------------------------
// The declared situation
// -------------------------------------------------------------------------------------------

type Act<S> = Box<dyn Fn(&S) -> Result<S, LadderRefusal> + Send + Sync>;
type Read<S, F> = Box<dyn Fn(&S) -> Result<F, LadderRefusal> + Send + Sync>;
type ExactRead<S> = Box<dyn Fn(&S) -> Result<BigRational, LadderRefusal> + Send + Sync>;

/// One admitted generator: a name and an exact, possibly refusing, total map of the carrier.
pub struct NamedGenerator<S> {
    name: String,
    act: Act<S>,
}

impl<S> NamedGenerator<S> {
    /// Declare a generator.
    pub fn new(
        name: impl Into<String>,
        act: impl Fn(&S) -> Result<S, LadderRefusal> + Send + Sync + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            act: Box::new(act),
        }
    }

    /// Its declared name, which is what a separator reports.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Carry one occurrence to its successor.
    pub fn apply(&self, occurrence: &S) -> Result<S, LadderRefusal> {
        (self.act)(occurrence)
    }
}

impl<S> Debug for NamedGenerator<S> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NamedGenerator")
            .field("name", &self.name)
            .finish_non_exhaustive()
    }
}

/// One admitted receiver: a name and an exact, possibly refusing, reading of the carrier.
pub struct NamedReceiver<S, F> {
    name: String,
    read: Read<S, F>,
}

impl<S, F> NamedReceiver<S, F> {
    /// Declare a receiver.
    pub fn new(
        name: impl Into<String>,
        read: impl Fn(&S) -> Result<F, LadderRefusal> + Send + Sync + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            read: Box::new(read),
        }
    }

    /// Its declared name, which is what a separator reports.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Read one occurrence.
    pub fn observe(&self, occurrence: &S) -> Result<F, LadderRefusal> {
        (self.read)(occurrence)
    }
}

impl<S, F> Debug for NamedReceiver<S, F> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NamedReceiver")
            .field("name", &self.name)
            .finish_non_exhaustive()
    }
}

/// The declared situation `(G, R)` together with the history-length ceiling the separator search
/// runs under. Its fields are private and the only route in is [`Situation::declare`], which
/// checks every declared size before anything is enumerated.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::Situation`.
pub struct Situation<S, F> {
    generators: Vec<NamedGenerator<S>>,
    receivers: Vec<NamedReceiver<S, F>>,
    history_ceiling: usize,
    history_population: usize,
}

impl<S, F> Debug for Situation<S, F> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Situation")
            .field("generators", &self.generators.len())
            .field("receivers", &self.receivers.len())
            .field("history_ceiling", &self.history_ceiling)
            .field("history_population", &self.history_population)
            .finish()
    }
}

/// The population `sum_{k=0..=ceiling} generators^k`, computed with checked arithmetic and
/// abandoned as soon as it passes [`WORD_POPULATION_CEILING`].
fn history_population(generators: usize, ceiling: usize) -> Option<usize> {
    if generators == 0 {
        return Some(1);
    }
    if generators == 1 {
        return ceiling.checked_add(1);
    }
    let mut total: usize = 0;
    let mut power: usize = 1;
    for _ in 0..=ceiling {
        total = total.checked_add(power)?;
        if total > WORD_POPULATION_CEILING {
            return None;
        }
        power = power.checked_mul(generators)?;
    }
    Some(total)
}

impl<S, F> Situation<S, F> {
    /// Declare a situation. Every declared size is checked here, before any enumeration or
    /// allocation sized by it.
    pub fn declare(
        generators: Vec<NamedGenerator<S>>,
        receivers: Vec<NamedReceiver<S, F>>,
        history_ceiling: usize,
    ) -> Result<Self, LadderRefusal> {
        if receivers.is_empty() {
            return Err(LadderRefusal::NoReceiverDeclared);
        }
        if generators.len() > GENERATOR_CEILING {
            return Err(LadderRefusal::GeneratorFamilyTooLarge {
                declared: generators.len(),
                ceiling: GENERATOR_CEILING,
            });
        }
        if receivers.len() > RECEIVER_CEILING {
            return Err(LadderRefusal::ReceiverFamilyTooLarge {
                declared: receivers.len(),
                ceiling: RECEIVER_CEILING,
            });
        }
        if history_ceiling > HISTORY_LENGTH_CEILING {
            return Err(LadderRefusal::HistoryLengthTooLarge {
                declared: history_ceiling,
                ceiling: HISTORY_LENGTH_CEILING,
            });
        }
        let Some(population) = history_population(generators.len(), history_ceiling) else {
            return Err(LadderRefusal::HistoryPopulationTooLarge {
                implied: usize::MAX,
                generators: generators.len(),
                length: history_ceiling,
                ceiling: WORD_POPULATION_CEILING,
            });
        };
        if population > WORD_POPULATION_CEILING {
            return Err(LadderRefusal::HistoryPopulationTooLarge {
                implied: population,
                generators: generators.len(),
                length: history_ceiling,
                ceiling: WORD_POPULATION_CEILING,
            });
        }
        let Some(probes) = population.checked_mul(receivers.len()) else {
            return Err(LadderRefusal::ProbePopulationTooLarge {
                implied: usize::MAX,
                ceiling: PROBE_CEILING,
            });
        };
        if probes > PROBE_CEILING {
            return Err(LadderRefusal::ProbePopulationTooLarge {
                implied: probes,
                ceiling: PROBE_CEILING,
            });
        }
        Ok(Self {
            generators,
            receivers,
            history_ceiling,
            history_population: population,
        })
    }

    /// The admitted generators.
    pub fn generators(&self) -> &[NamedGenerator<S>] {
        &self.generators
    }

    /// The admitted receivers.
    pub fn receivers(&self) -> &[NamedReceiver<S, F>] {
        &self.receivers
    }

    /// The declared history-length ceiling the separator search runs under.
    pub fn history_ceiling(&self) -> usize {
        self.history_ceiling
    }

    /// The ordered-history population that ceiling implies, checked at declaration time.
    pub fn history_population(&self) -> usize {
        self.history_population
    }

    /// Transport an occurrence along an ordered history, written as the Lean list: the **head is
    /// applied last**, exactly as `Foundation/TransportWord.lean::transportWord`.
    pub fn transport_word(&self, word: &[usize], occurrence: &S) -> Result<S, LadderRefusal>
    where
        S: Clone,
    {
        let mut carried = occurrence.clone();
        for &generator in word.iter().rev() {
            let Some(named) = self.generators.get(generator) else {
                return Err(LadderRefusal::UndeclaredGenerator {
                    index: generator,
                    declared: self.generators.len(),
                });
            };
            carried = named.apply(&carried)?;
        }
        Ok(carried)
    }
}

// -------------------------------------------------------------------------------------------
// Separators, verdicts, classification
// -------------------------------------------------------------------------------------------

/// A separating `(w, rho)`: the ordered history and the receiver at which the two occurrences
/// differ, with both exact faces. One of these refutes equal potential outright.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::separatorRefutesEqualPotential`, and
/// `Foundation/CausalRelevance.lean::futureHistory_quotientNe_returns_separator` for the returned
/// separator itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separator<F> {
    /// The ordered history, as the Lean list: the head is applied last.
    pub word: Vec<usize>,
    /// The generator names of that history, head first.
    pub word_names: Vec<String>,
    /// Which declared receiver separates.
    pub receiver: usize,
    /// Its declared name.
    pub receiver_name: String,
    /// The face returned from the left occurrence.
    pub left_face: F,
    /// The face returned from the right occurrence.
    pub right_face: F,
}

/// What a bounded separator search returns. **Never** "equal potential".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PotentialVerdict<F> {
    /// A separating `(w, rho)` was found, so equal potential is refuted.
    Separated(Separator<F>),
    /// The declared bound was exhausted without a separator. This is its own return: it states
    /// what was searched, and it is not equal potential.
    NotSeparatedWithinBound {
        /// The history-length ceiling the search ran under.
        history_length: usize,
        /// How many ordered histories were actually examined.
        histories_examined: usize,
        /// How many receivers each history was read by.
        receivers: usize,
    },
}

/// What a bounded reachability search returns. **Never** "no continuation".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContinuationVerdict {
    /// The situation's own transports reach: this ordered history carries the first occurrence to
    /// the second.
    Reached {
        /// The ordered history, as the Lean list.
        word: Vec<usize>,
        /// Its generator names.
        word_names: Vec<String>,
    },
    /// The declared bound was exhausted without reaching. A lineage declared from outside the
    /// situation may still carry one occurrence to the other.
    NotReachedWithinBound {
        /// The history-length ceiling the search ran under.
        history_length: usize,
        /// How many ordered histories were examined.
        histories_examined: usize,
    },
}

/// A declared symmetry of the carrier, offered as a rung-3 witness. Whether it really is one is
/// decided by [`Situation::check_automorphism`] against the two equivariance laws.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::SituationAuto`.
pub struct SituationAutomorphism<S> {
    name: String,
    forward: Act<S>,
    inverse: Act<S>,
}

impl<S> SituationAutomorphism<S> {
    /// Declare a candidate symmetry and its inverse.
    pub fn new(
        name: impl Into<String>,
        forward: impl Fn(&S) -> Result<S, LadderRefusal> + Send + Sync + 'static,
        inverse: impl Fn(&S) -> Result<S, LadderRefusal> + Send + Sync + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            forward: Box::new(forward),
            inverse: Box::new(inverse),
        }
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Apply the symmetry.
    pub fn forward(&self, occurrence: &S) -> Result<S, LadderRefusal> {
        (self.forward)(occurrence)
    }

    /// Apply its declared inverse.
    pub fn inverse(&self, occurrence: &S) -> Result<S, LadderRefusal> {
        (self.inverse)(occurrence)
    }
}

impl<S> Debug for SituationAutomorphism<S> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SituationAutomorphism")
            .field("name", &self.name)
            .finish_non_exhaustive()
    }
}

/// What an equivariance check returns over a declared occurrence probe. The two failure arms are
/// exactly the two halves of the Lean hypothesis, and each is separately necessary:
/// `receiverEquivarianceIsNecessary` and `generatorEquivarianceIsNecessary`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquivarianceReading<S, F> {
    /// Both laws held at every probe occurrence. The classifier separately checks endpoint
    /// membership and generator/symmetry closure before promoting this to an isomorphism.
    HeldOnProbe {
        /// How many occurrences were probed.
        probe: usize,
    },
    /// The declared inverse is not the inverse at this occurrence.
    NotABijection {
        /// The probe occurrence.
        occurrence: S,
    },
    /// `phi(T_g x) != T_g(phi x)` at this occurrence and generator.
    GeneratorSquareFails {
        /// The probe occurrence.
        occurrence: S,
        /// The generator's declared name.
        generator: String,
    },
    /// `rho(phi x) != rho x` at this occurrence and receiver.
    ReceiverTriangleFails {
        /// The probe occurrence.
        occurrence: S,
        /// The receiver's declared name.
        receiver: String,
        /// The face read through the symmetry.
        through: F,
        /// The face read directly.
        direct: F,
    },
}

/// An exact rational reading with its declared tolerance. The tolerance is the receiver's
/// declaration; it is checked non-negative and is never fitted.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::WithinTolerance`.
pub struct ToleranceReading<S> {
    name: String,
    read: ExactRead<S>,
    tolerance: BigRational,
}

impl<S> ToleranceReading<S> {
    /// Declare a rational reading and its tolerance. A negative tolerance names no aperture and is
    /// refused.
    pub fn declare(
        name: impl Into<String>,
        read: impl Fn(&S) -> Result<BigRational, LadderRefusal> + Send + Sync + 'static,
        tolerance: BigRational,
    ) -> Result<Self, LadderRefusal> {
        if tolerance.is_negative() {
            return Err(LadderRefusal::NegativeTolerance);
        }
        Ok(Self {
            name: name.into(),
            read: Box::new(read),
            tolerance,
        })
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its declared tolerance.
    pub fn tolerance(&self) -> &BigRational {
        &self.tolerance
    }

    /// The exact reading of one occurrence.
    pub fn read(&self, occurrence: &S) -> Result<BigRational, LadderRefusal> {
        (self.read)(occurrence)
    }

    /// Whether the two readings lie inside the declared tolerance.
    ///
    /// Lean counterpart: `Foundation/RelationLadder.lean::WithinTolerance`.
    pub fn holds(&self, left: &S, right: &S) -> Result<bool, LadderRefusal> {
        let difference = self.read(left)? - self.read(right)?;
        Ok(difference.abs() <= self.tolerance)
    }
}

impl<S> Debug for ToleranceReading<S> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ToleranceReading")
            .field("name", &self.name)
            .field("tolerance", &self.tolerance)
            .finish_non_exhaustive()
    }
}

/// A rung-3 claim: the candidate symmetry, the occurrence probe the caller offers, and whether
/// that probe **is** the carrier. If it is not, the reading stays a probe and the rung is not
/// established.
pub struct AutomorphismClaim<'a, S> {
    /// The candidate symmetry.
    pub automorphism: &'a SituationAutomorphism<S>,
    /// The occurrences at which the two equivariance laws are checked.
    pub probe: &'a [S],
    /// Request a finite-carrier check. Retained for API compatibility: `true` does not establish
    /// completeness. The classifier checks endpoint membership and closure under every generator
    /// and both symmetry maps before establishing the isomorphism on that invariant carrier.
    pub probe_is_the_whole_carrier: bool,
}

/// Everything a classification depends on beyond the situation itself.
pub struct Declarations<'a, S> {
    /// The rung-3 claim, if the caller offers one.
    pub automorphism: Option<AutomorphismClaim<'a, S>>,
    /// The rung-6 reading and its tolerance, if the caller declares one.
    pub tolerance: Option<&'a ToleranceReading<S>>,
}

impl<S> Default for Declarations<'_, S> {
    fn default() -> Self {
        Self {
            automorphism: None,
            tolerance: None,
        }
    }
}

impl<S> Debug for Declarations<'_, S> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Declarations")
            .field("automorphism", &self.automorphism.is_some())
            .field("tolerance", &self.tolerance.is_some())
            .finish()
    }
}

/// Why the rung above the one established was not established. Several may apply.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClassificationNote {
    /// The two occurrences are one occurrence, so the ladder is at its top.
    Identical,
    /// A separating `(w, rho)` refutes the rung above.
    SeparatorFound,
    /// No separator within the declared bound. **Not** equal potential.
    NotSeparatedWithinBound,
    /// The equivariance held only on a probe the caller did not declare exhaustive, so rung 3 is
    /// not established. A probe stays a probe.
    IsomorphismOnlyOnAProbe,
    /// The alleged carrier omits an endpoint or is not closed under its generators and symmetry.
    AutomorphismCarrierNotClosed,
    /// The declared candidate symmetry failed one of the two equivariance laws.
    EquivarianceFails,
    /// No candidate symmetry was declared, so rung 3 was not examined.
    NoAutomorphismDeclared,
    /// The declared symmetry does not carry the first occurrence to the second.
    AutomorphismDoesNotCarry,
    /// A caller declared the equivariance probe exhaustive, and the bounded search nevertheless
    /// returned a separator. The separator is evidence and the declaration is not, so rung 3 is
    /// not established.
    IsomorphismContradictedBySeparator,
    /// No tolerance reading was declared, so rung 6 was not examined.
    NoToleranceDeclared,
    /// The declared tolerance was exceeded.
    ToleranceExceeded,
    /// The situation's own transports did not reach within the declared bound.
    NotReachedWithinBound,
}

/// The complete reading of one pair against the ladder.
///
/// `strongest` is the maximum along the identity chain
/// `Identity > Isomorphism > EqualPotential > ReceiverEqual > WithinTolerance > NoRelation`.
/// `continuation` is reported **beside** it, because rung 2 is relative to a lineage and is
/// incomparable with rungs 4, 5 and 6 — the ladder's first finding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Classification<S, F> {
    /// The strongest rung established on the identity chain.
    pub strongest: Rung,
    /// Every rung established, including [`Rung::Continuation`] when the transports reach.
    pub established: Vec<Rung>,
    /// The rung immediately above `strongest` on the chain, when there is one.
    pub next_rung: Option<Rung>,
    /// The witness refuting that next rung, when the search produced one.
    pub separator: Option<Separator<F>>,
    /// What the bounded separator search returned.
    pub potential: PotentialVerdict<F>,
    /// What the bounded reachability search returned.
    pub continuation: ContinuationVerdict,
    /// The equivariance reading of the declared candidate symmetry, when one was declared.
    pub equivariance: Option<EquivarianceReading<S, F>>,
    /// Why the next rung was not established.
    pub notes: Vec<ClassificationNote>,
}

/// The identity chain, strongest first. [`Rung::Continuation`] is deliberately absent: it is on
/// the other axis.
const IDENTITY_CHAIN: [Rung; 6] = [
    Rung::Identity,
    Rung::Isomorphism,
    Rung::EqualPotential,
    Rung::ReceiverEqual,
    Rung::WithinTolerance,
    Rung::NoRelation,
];

fn next_rung_above(rung: Rung) -> Option<Rung> {
    let position = IDENTITY_CHAIN.iter().position(|&entry| entry == rung)?;
    position.checked_sub(1).and_then(|above| IDENTITY_CHAIN.get(above).copied())
}

impl<S, F> Situation<S, F>
where
    S: Clone + PartialEq,
    F: Clone + PartialEq,
{
    /// **Rung 4.** Whether every declared receiver returns the same face now, and the separating
    /// receiver when one does not. The returned separator has the empty history.
    ///
    /// Lean counterpart: `Foundation/RelationLadder.lean::PresentAgreement`.
    pub fn present_agreement(
        &self,
        left: &S,
        right: &S,
    ) -> Result<Option<Separator<F>>, LadderRefusal> {
        for (index, receiver) in self.receivers.iter().enumerate() {
            let left_face = receiver.observe(left)?;
            let right_face = receiver.observe(right)?;
            if left_face != right_face {
                return Ok(Some(Separator {
                    word: Vec::new(),
                    word_names: Vec::new(),
                    receiver: index,
                    receiver_name: receiver.name.clone(),
                    left_face,
                    right_face,
                }));
            }
        }
        Ok(None)
    }

    /// **Rung 5, bounded.** Search the ordered histories up to the declared ceiling for a
    /// separating `(w, rho)`.
    ///
    /// Exhausting the bound without one returns [`PotentialVerdict::NotSeparatedWithinBound`],
    /// which is its own return and is never equal potential. The history population was checked at
    /// declaration time, so this walk is bounded before it starts.
    pub fn search_separator(
        &self,
        left: &S,
        right: &S,
    ) -> Result<PotentialVerdict<F>, LadderRefusal> {
        let mut path: Vec<usize> = Vec::with_capacity(self.history_ceiling);
        let mut examined = 0usize;
        if let Some(separator) = self.walk(left, right, 0, &mut path, &mut examined)? {
            return Ok(PotentialVerdict::Separated(separator));
        }
        Ok(PotentialVerdict::NotSeparatedWithinBound {
            history_length: self.history_ceiling,
            histories_examined: examined,
            receivers: self.receivers.len(),
        })
    }

    /// The bounded depth-first walk over ordered histories. `depth` never exceeds the ceiling
    /// checked in [`Situation::declare`], so the recursion is bounded by a validated value and
    /// nothing is allocated from an unchecked declaration.
    fn walk(
        &self,
        left: &S,
        right: &S,
        depth: usize,
        path: &mut Vec<usize>,
        examined: &mut usize,
    ) -> Result<Option<Separator<F>>, LadderRefusal> {
        *examined = examined.saturating_add(1);
        for (index, receiver) in self.receivers.iter().enumerate() {
            let left_face = receiver.observe(left)?;
            let right_face = receiver.observe(right)?;
            if left_face != right_face {
                let word: Vec<usize> = path.iter().rev().copied().collect();
                let word_names = word
                    .iter()
                    .map(|&generator| {
                        self.generators
                            .get(generator)
                            .map(|named| named.name.clone())
                            .unwrap_or_default()
                    })
                    .collect();
                return Ok(Some(Separator {
                    word,
                    word_names,
                    receiver: index,
                    receiver_name: receiver.name.clone(),
                    left_face,
                    right_face,
                }));
            }
        }
        if depth >= self.history_ceiling {
            return Ok(None);
        }
        for (index, generator) in self.generators.iter().enumerate() {
            let carried_left = generator.apply(left)?;
            let carried_right = generator.apply(right)?;
            path.push(index);
            let found = self.walk(&carried_left, &carried_right, depth + 1, path, examined)?;
            path.pop();
            if found.is_some() {
                return Ok(found);
            }
        }
        Ok(None)
    }

    /// **Rung 2, through the situation's own transports.** Whether some ordered history within the
    /// declared ceiling carries `from` to `to`.
    ///
    /// Exhausting the bound returns [`ContinuationVerdict::NotReachedWithinBound`], never "no
    /// continuation": a lineage declared from outside the situation is a different object, and
    /// `Foundation/RelationLadder.lean::equalPotentialWithoutAGeneratorContinuation` is the proved
    /// negative form for the finite case.
    pub fn reaches(&self, from: &S, to: &S) -> Result<ContinuationVerdict, LadderRefusal> {
        let mut path: Vec<usize> = Vec::with_capacity(self.history_ceiling);
        let mut examined = 0usize;
        if let Some(word) = self.reach_walk(from, to, 0, &mut path, &mut examined)? {
            let word_names = word
                .iter()
                .map(|&generator| {
                    self.generators
                        .get(generator)
                        .map(|named| named.name.clone())
                        .unwrap_or_default()
                })
                .collect();
            return Ok(ContinuationVerdict::Reached { word, word_names });
        }
        Ok(ContinuationVerdict::NotReachedWithinBound {
            history_length: self.history_ceiling,
            histories_examined: examined,
        })
    }

    fn reach_walk(
        &self,
        carried: &S,
        target: &S,
        depth: usize,
        path: &mut Vec<usize>,
        examined: &mut usize,
    ) -> Result<Option<Vec<usize>>, LadderRefusal> {
        *examined = examined.saturating_add(1);
        if carried == target {
            return Ok(Some(path.iter().rev().copied().collect()));
        }
        if depth >= self.history_ceiling {
            return Ok(None);
        }
        for (index, generator) in self.generators.iter().enumerate() {
            let next = generator.apply(carried)?;
            path.push(index);
            let found = self.reach_walk(&next, target, depth + 1, path, examined)?;
            path.pop();
            if found.is_some() {
                return Ok(found);
            }
        }
        Ok(None)
    }

    /// **Rung 3, checked.** Test both halves of the equivariance hypothesis at every occurrence of
    /// a declared probe: the generator square and the receiver triangle, plus that the declared
    /// inverse really inverts.
    ///
    /// Lean counterpart: `SituationAuto.step_natural` and `SituationAuto.observe_natural`.
    pub fn check_automorphism(
        &self,
        automorphism: &SituationAutomorphism<S>,
        probe: &[S],
    ) -> Result<EquivarianceReading<S, F>, LadderRefusal> {
        if probe.len() > AUTOMORPHISM_PROBE_CEILING {
            return Err(LadderRefusal::OccurrenceProbeTooLarge {
                declared: probe.len(),
                ceiling: AUTOMORPHISM_PROBE_CEILING,
            });
        }
        for occurrence in probe {
            let carried = automorphism.forward(occurrence)?;
            if &automorphism.inverse(&carried)? != occurrence {
                return Ok(EquivarianceReading::NotABijection {
                    occurrence: occurrence.clone(),
                });
            }
            for generator in &self.generators {
                let through = automorphism.forward(&generator.apply(occurrence)?)?;
                let direct = generator.apply(&carried)?;
                if through != direct {
                    return Ok(EquivarianceReading::GeneratorSquareFails {
                        occurrence: occurrence.clone(),
                        generator: generator.name.clone(),
                    });
                }
            }
            for receiver in &self.receivers {
                let through = receiver.observe(&carried)?;
                let direct = receiver.observe(occurrence)?;
                if through != direct {
                    return Ok(EquivarianceReading::ReceiverTriangleFails {
                        occurrence: occurrence.clone(),
                        receiver: receiver.name.clone(),
                        through,
                        direct,
                    });
                }
            }
        }
        Ok(EquivarianceReading::HeldOnProbe { probe: probe.len() })
    }

    /// Check the finite invariant carrier on which an exhaustive symmetry claim is made.
    /// Closure extends the checked generator squares to every finite word by induction.
    /// `S` may describe a larger ambient type; no claim about occurrences outside this carrier
    /// is needed to establish the two contained occurrences' future equivalence.
    fn automorphism_carrier_is_closed(
        &self,
        claim: &AutomorphismClaim<'_, S>,
        left: &S,
        right: &S,
    ) -> Result<bool, LadderRefusal> {
        let probe = claim.probe;
        // Membership uses PartialEq, so count its worst-case comparisons before this work.
        let implied = probe.len().checked_mul(probe.len())
            .and_then(|n| n.checked_mul(self.generators.len() + 2))
            .and_then(|n| probe.len().checked_mul(2).and_then(|ends| n.checked_add(ends)))
            .unwrap_or(usize::MAX);
        if implied > PROBE_CEILING {
            return Err(LadderRefusal::ProbePopulationTooLarge { implied, ceiling: PROBE_CEILING });
        }
        if !probe.contains(left) || !probe.contains(right) {
            return Ok(false);
        }
        for occurrence in probe {
            if !probe.contains(&claim.automorphism.forward(occurrence)?)
                || !probe.contains(&claim.automorphism.inverse(occurrence)?) {
                return Ok(false);
            }
            for generator in &self.generators {
                if !probe.contains(&generator.apply(occurrence)?) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// **The classifier.** The strongest rung established, every rung established, the rung
    /// immediately above, and the separator witness refuting it when the bounded search found one.
    ///
    /// The one route to [`Rung::EqualPotential`] is a candidate symmetry whose equivariance was
    /// checked over a finite invariant carrier containing both occurrences: that is the Lean
    /// theorem `situationAutoImpliesEqualPotential` on the checked restriction. A bounded search that
    /// finds no separator establishes nothing above [`Rung::ReceiverEqual`].
    pub fn classify(
        &self,
        left: &S,
        right: &S,
        declared: &Declarations<'_, S>,
    ) -> Result<Classification<S, F>, LadderRefusal> {
        let mut notes: Vec<ClassificationNote> = Vec::new();
        let mut established: Vec<Rung> = Vec::new();

        let identical = left == right;

        // Rung 5, bounded. A separator is evidence and is read before any declaration.
        let potential = self.search_separator(left, right)?;
        let separator = match &potential {
            PotentialVerdict::Separated(separator) => {
                notes.push(ClassificationNote::SeparatorFound);
                Some(separator.clone())
            }
            PotentialVerdict::NotSeparatedWithinBound { .. } => {
                notes.push(ClassificationNote::NotSeparatedWithinBound);
                None
            }
        };

        // Rung 3, as far as it is checkable.
        let mut equivariance = None;
        let mut isomorphism = false;
        match &declared.automorphism {
            None => notes.push(ClassificationNote::NoAutomorphismDeclared),
            Some(claim) => {
                let reading = self.check_automorphism(claim.automorphism, claim.probe)?;
                let carries = &claim.automorphism.forward(left)? == right;
                match (&reading, carries, claim.probe_is_the_whole_carrier) {
                    (EquivarianceReading::HeldOnProbe { .. }, true, true) => {
                        if separator.is_some() {
                            notes.push(ClassificationNote::IsomorphismContradictedBySeparator);
                        } else if !self.automorphism_carrier_is_closed(claim, left, right)? {
                            notes.push(ClassificationNote::AutomorphismCarrierNotClosed);
                        } else {
                            isomorphism = true;
                        }
                    }
                    (EquivarianceReading::HeldOnProbe { .. }, true, false) => {
                        notes.push(ClassificationNote::IsomorphismOnlyOnAProbe);
                    }
                    (EquivarianceReading::HeldOnProbe { .. }, false, _) => {
                        notes.push(ClassificationNote::AutomorphismDoesNotCarry);
                    }
                    _ => notes.push(ClassificationNote::EquivarianceFails),
                }
                equivariance = Some(reading);
            }
        }

        // Rung 4.
        let present = self.present_agreement(left, right)?;
        let receiver_equal = present.is_none();

        // Rung 6.
        let within_tolerance = match declared.tolerance {
            None => {
                notes.push(ClassificationNote::NoToleranceDeclared);
                false
            }
            Some(reading) => {
                let inside = reading.holds(left, right)?;
                if !inside {
                    notes.push(ClassificationNote::ToleranceExceeded);
                }
                inside
            }
        };

        // Rung 2, through the situation's own transports.
        let continuation = self.reaches(left, right)?;
        let reaches = matches!(continuation, ContinuationVerdict::Reached { .. });
        if !reaches {
            notes.push(ClassificationNote::NotReachedWithinBound);
        }

        let strongest = if identical {
            notes.push(ClassificationNote::Identical);
            Rung::Identity
        } else if isomorphism {
            Rung::Isomorphism
        } else if receiver_equal {
            Rung::ReceiverEqual
        } else if within_tolerance {
            Rung::WithinTolerance
        } else {
            Rung::NoRelation
        };

        for rung in strongest.entailed() {
            if *rung != Rung::Continuation {
                established.push(*rung);
            }
        }
        if reaches && !established.contains(&Rung::Continuation) {
            established.push(Rung::Continuation);
        }
        if within_tolerance && !established.contains(&Rung::WithinTolerance) {
            established.push(Rung::WithinTolerance);
        }
        established.sort_unstable();
        established.dedup();

        Ok(Classification {
            strongest,
            established,
            next_rung: next_rung_above(strongest),
            separator,
            potential,
            continuation,
            equivariance,
            notes,
        })
    }
}

// -------------------------------------------------------------------------------------------
// Worked instance (a): `Expression` against `eval`
// -------------------------------------------------------------------------------------------

/// A construction, retained as the syntax tree it is. [`eval`] is one receiver of it.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::Expression`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression {
    /// A literal.
    Lit(BigUint),
    /// A sum.
    Add(Box<Expression>, Box<Expression>),
    /// A product.
    Mul(Box<Expression>, Box<Expression>),
    /// A power.
    Pow(Box<Expression>, Box<Expression>),
}

impl Expression {
    /// A literal from a small natural.
    pub fn lit(value: u64) -> Self {
        Expression::Lit(BigUint::from(value))
    }

    /// The depth and node count, walked with an explicit stack so no unbounded recursion runs
    /// before the ceilings are checked. Refuses above [`EXPRESSION_NODE_CEILING`] or
    /// [`EXPRESSION_DEPTH_CEILING`].
    pub fn within_ceilings(&self) -> Result<(usize, usize), LadderRefusal> {
        let mut stack: Vec<(&Expression, usize)> = vec![(self, 1)];
        let mut nodes = 0usize;
        let mut deepest = 0usize;
        while let Some((node, depth)) = stack.pop() {
            nodes = nodes.saturating_add(1);
            if nodes > EXPRESSION_NODE_CEILING {
                return Err(LadderRefusal::ExpressionTooLarge {
                    ceiling: EXPRESSION_NODE_CEILING,
                });
            }
            if depth > deepest {
                deepest = depth;
            }
            if depth > EXPRESSION_DEPTH_CEILING {
                return Err(LadderRefusal::ExpressionTooDeep {
                    ceiling: EXPRESSION_DEPTH_CEILING,
                });
            }
            match node {
                Expression::Lit(_) => {}
                Expression::Add(left, right)
                | Expression::Mul(left, right)
                | Expression::Pow(left, right) => {
                    stack.push((left, depth + 1));
                    stack.push((right, depth + 1));
                }
            }
        }
        Ok((deepest, nodes))
    }
}

/// The scalar receiver: the denoted value, exactly.
///
/// The depth, node count, exponent and result bit length are all bounded before the value is
/// formed, so a caller-supplied expression cannot drive an unbounded allocation or recursion.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::eval`.
pub fn eval(expression: &Expression) -> Result<BigUint, LadderRefusal> {
    expression.within_ceilings()?;
    eval_checked(expression)
}

/// Refuse a value whose bit length is above the declared ceiling, before it is formed.
fn within_value_ceiling(bits: u64) -> Result<(), LadderRefusal> {
    if bits > VALUE_BIT_CEILING {
        return Err(LadderRefusal::ValueTooWide {
            bits,
            ceiling: VALUE_BIT_CEILING,
        });
    }
    Ok(())
}

fn eval_checked(expression: &Expression) -> Result<BigUint, LadderRefusal> {
    match expression {
        Expression::Lit(value) => {
            // A caller-supplied literal is itself a declared size.
            within_value_ceiling(value.bits())?;
            Ok(value.clone())
        }
        Expression::Add(left, right) => {
            let left = eval_checked(left)?;
            let right = eval_checked(right)?;
            within_value_ceiling(left.bits().max(right.bits()).saturating_add(1))?;
            Ok(left + right)
        }
        Expression::Mul(left, right) => {
            let left = eval_checked(left)?;
            let right = eval_checked(right)?;
            // A product doubles the width, so a depth-bounded tree of products still amplifies
            // exponentially. The width is checked before the product is formed.
            within_value_ceiling(left.bits().saturating_add(right.bits()))?;
            Ok(left * right)
        }
        Expression::Pow(base, exponent) => {
            let base = eval_checked(base)?;
            let exponent = eval_checked(exponent)?;
            let Ok(exponent) = u64::try_from(exponent) else {
                return Err(LadderRefusal::ExponentTooLarge {
                    ceiling: EXPONENT_CEILING,
                });
            };
            if exponent > EXPONENT_CEILING {
                return Err(LadderRefusal::ExponentTooLarge {
                    ceiling: EXPONENT_CEILING,
                });
            }
            within_value_ceiling(base.bits().max(1).saturating_mul(exponent.max(1)))?;
            let Ok(exponent) = u32::try_from(exponent) else {
                return Err(LadderRefusal::ExponentTooLarge {
                    ceiling: EXPONENT_CEILING,
                });
            };
            Ok(base.pow(exponent))
        }
    }
}

/// The literal `4`.
pub fn four() -> Expression {
    Expression::lit(4)
}

/// The construction `2 ^ 2`.
pub fn two_squared() -> Expression {
    Expression::Pow(Box::new(Expression::lit(2)), Box::new(Expression::lit(2)))
}

/// A generator that rewrites the **construction**: it increments the exponent of a power and
/// leaves every other expression alone.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::bumpExponent`.
pub fn bump_exponent(expression: &Expression) -> Expression {
    match expression {
        Expression::Pow(base, exponent) => match exponent.as_ref() {
            Expression::Lit(value) => Expression::Pow(
                base.clone(),
                Box::new(Expression::Lit(value + BigUint::one())),
            ),
            _ => expression.clone(),
        },
        _ => expression.clone(),
    }
}

/// A generator family that only **post-composes** `eval`: it replaces an expression by the literal
/// of its value shifted by `shift`. Every member factors through the scalar receiver, so it can
/// never reach the difference in construction.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::postcomposeAdd`.
pub fn postcompose_add(shift: u64, expression: &Expression) -> Result<Expression, LadderRefusal> {
    Ok(Expression::Lit(eval(expression)? + BigUint::from(shift)))
}

/// The situation whose one generator rewrites the construction and whose one receiver is `eval`.
pub fn construction_situation() -> Result<Situation<Expression, BigUint>, LadderRefusal> {
    Situation::declare(
        vec![NamedGenerator::new("bump-exponent", |expression: &Expression| {
            Ok(bump_exponent(expression))
        })],
        vec![NamedReceiver::new("eval", |expression: &Expression| {
            eval(expression)
        })],
        3,
    )
}

/// The situation whose generators only post-compose `eval`.
pub fn value_situation() -> Result<Situation<Expression, BigUint>, LadderRefusal> {
    Situation::declare(
        vec![
            NamedGenerator::new("postcompose-add-0", |expression: &Expression| {
                postcompose_add(0, expression)
            }),
            NamedGenerator::new("postcompose-add-1", |expression: &Expression| {
                postcompose_add(1, expression)
            }),
        ],
        vec![NamedReceiver::new("eval", |expression: &Expression| {
            eval(expression)
        })],
        4,
    )
}

/// Both generator families at once: the enlarged declaration that refines the potential class.
pub fn joint_expression_situation() -> Result<Situation<Expression, BigUint>, LadderRefusal> {
    Situation::declare(
        vec![
            NamedGenerator::new("bump-exponent", |expression: &Expression| {
                Ok(bump_exponent(expression))
            }),
            NamedGenerator::new("postcompose-add-0", |expression: &Expression| {
                postcompose_add(0, expression)
            }),
            NamedGenerator::new("postcompose-add-1", |expression: &Expression| {
                postcompose_add(1, expression)
            }),
        ],
        vec![NamedReceiver::new("eval", |expression: &Expression| {
            eval(expression)
        })],
        3,
    )
}

// -------------------------------------------------------------------------------------------
// Worked instance (b): the same song
// -------------------------------------------------------------------------------------------

/// An **enactment**: an exact rational pitch sequence, an exact rational onset sequence, and a
/// declared timbre label. No float participates. Built only through [`Enactment::declare`], which
/// bounds both sequences and requires them to pair up.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::Enactment`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Enactment {
    pitch: Vec<BigRational>,
    onset: Vec<BigRational>,
    timbre: u64,
}

impl Enactment {
    /// Declare an enactment.
    pub fn declare(
        pitch: Vec<BigRational>,
        onset: Vec<BigRational>,
        timbre: u64,
    ) -> Result<Self, LadderRefusal> {
        if pitch.len() > SEQUENCE_CEILING {
            return Err(LadderRefusal::SequenceTooLong {
                declared: pitch.len(),
                ceiling: SEQUENCE_CEILING,
            });
        }
        if onset.len() > SEQUENCE_CEILING {
            return Err(LadderRefusal::SequenceTooLong {
                declared: onset.len(),
                ceiling: SEQUENCE_CEILING,
            });
        }
        if pitch.len() != onset.len() {
            return Err(LadderRefusal::UnpairedEnactment {
                pitches: pitch.len(),
                onsets: onset.len(),
            });
        }
        Ok(Self {
            pitch,
            onset,
            timbre,
        })
    }

    /// The exact pitches.
    pub fn pitch(&self) -> &[BigRational] {
        &self.pitch
    }

    /// The exact onsets.
    pub fn onset(&self) -> &[BigRational] {
        &self.onset
    }

    /// The declared timbre label.
    pub fn timbre(&self) -> u64 {
        self.timbre
    }
}

/// Consecutive differences of an exact rational sequence.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::gaps`.
pub fn gaps(sequence: &[BigRational]) -> Vec<BigRational> {
    sequence
        .windows(2)
        .filter_map(|pair| match pair {
            [first, second] => Some(second - first),
            _ => None,
        })
        .collect()
}

/// A sequence normalized by its first entry. Division in the rationals is exact; the total
/// convention `x / 0 = 0` is declared here rather than hidden, matching the Lean owner.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::normalizedByFirst`.
pub fn normalized_by_first(sequence: &[BigRational]) -> Vec<BigRational> {
    let Some((first, rest)) = sequence.split_first() else {
        return Vec::new();
    };
    let mut normalized = Vec::with_capacity(sequence.len());
    normalized.push(BigRational::one());
    for entry in rest {
        if first.is_zero() {
            normalized.push(BigRational::zero());
        } else {
            normalized.push(entry / first);
        }
    }
    normalized
}

/// What the musical receiver returns: the interval contour and the rhythm-ratio contour.
pub type MusicalFace = (Vec<BigRational>, Vec<BigRational>);

/// What the richer receiver returns: absolute pitch, absolute onset and the timbre label.
pub type AbsoluteFace = (Vec<BigRational>, Vec<BigRational>, u64);

/// **The musical receiver**: interval contour and rhythm-ratio contour.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::musicalFace`.
pub fn musical_face(enactment: &Enactment) -> MusicalFace {
    (
        gaps(&enactment.pitch),
        normalized_by_first(&gaps(&enactment.onset)),
    )
}

/// **The richer receiver**: absolute pitch, absolute onset and the timbre label.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::absoluteFace`.
pub fn absolute_face(enactment: &Enactment) -> AbsoluteFace {
    (
        enactment.pitch.clone(),
        enactment.onset.clone(),
        enactment.timbre,
    )
}

/// Transposition by one exact rational interval.
pub fn transpose(interval: &BigRational, enactment: &Enactment) -> Enactment {
    Enactment {
        pitch: enactment.pitch.iter().map(|value| value + interval).collect(),
        onset: enactment.onset.clone(),
        timbre: enactment.timbre,
    }
}

/// Tempo scaling by an exact nonzero rational factor. A zero factor is not admissible.
pub fn scale_tempo(
    factor: &BigRational,
    enactment: &Enactment,
) -> Result<Enactment, LadderRefusal> {
    if factor.is_zero() {
        return Err(LadderRefusal::ZeroTempoFactor);
    }
    Ok(Enactment {
        pitch: enactment.pitch.clone(),
        onset: enactment.onset.iter().map(|time| factor * time).collect(),
        timbre: enactment.timbre,
    })
}

/// Re-voicing: a different declared timbre, the same pitches and onsets.
pub fn revoice(label: u64, enactment: &Enactment) -> Enactment {
    Enactment {
        pitch: enactment.pitch.clone(),
        onset: enactment.onset.clone(),
        timbre: label,
    }
}

/// **The admissible transformations of the song.**
///
/// Lean counterpart: `Foundation/RelationLadder.lean::Admissible`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Admissible {
    /// Transpose by an exact interval.
    Transpose(BigRational),
    /// Scale the tempo by an exact factor, which must be nonzero.
    ScaleTempo(BigRational),
    /// Re-voice.
    Revoice(u64),
}

/// How an admissible transformation acts.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::enact`.
pub fn enact(
    transformation: &Admissible,
    enactment: &Enactment,
) -> Result<Enactment, LadderRefusal> {
    match transformation {
        Admissible::Transpose(interval) => Ok(transpose(interval, enactment)),
        Admissible::ScaleTempo(factor) => scale_tempo(factor, enactment),
        Admissible::Revoice(label) => Ok(revoice(*label, enactment)),
    }
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn whole(value: i64) -> BigRational {
    BigRational::from(BigInt::from(value))
}

/// The admissible generator family used by both song situations.
fn admissible_generators() -> Vec<NamedGenerator<Enactment>> {
    vec![
        NamedGenerator::new("transpose+1", |enactment: &Enactment| {
            enact(&Admissible::Transpose(whole(1)), enactment)
        }),
        NamedGenerator::new("tempo*2", |enactment: &Enactment| {
            enact(&Admissible::ScaleTempo(whole(2)), enactment)
        }),
        NamedGenerator::new("tempo*1/2", |enactment: &Enactment| {
            enact(&Admissible::ScaleTempo(rational(1, 2)), enactment)
        }),
        NamedGenerator::new("revoice-7", |enactment: &Enactment| {
            enact(&Admissible::Revoice(7), enactment)
        }),
    ]
}

/// **The song**: the family of admissible enactments together with the admissible
/// transformations, read by the musical receiver. The song is not one acoustic object.
pub fn song_situation() -> Result<Situation<Enactment, MusicalFace>, LadderRefusal> {
    Situation::declare(
        admissible_generators(),
        vec![NamedReceiver::new("musical", |enactment: &Enactment| {
            Ok(musical_face(enactment))
        })],
        3,
    )
}

/// The same family read by the richer receiver, which separates the enactments.
pub fn absolute_situation() -> Result<Situation<Enactment, AbsoluteFace>, LadderRefusal> {
    Situation::declare(
        admissible_generators(),
        vec![NamedReceiver::new("absolute", |enactment: &Enactment| {
            Ok(absolute_face(enactment))
        })],
        3,
    )
}

/// One enactment: three pitches a whole tone apart, evenly spaced.
pub fn first_enactment() -> Result<Enactment, LadderRefusal> {
    Enactment::declare(
        vec![whole(0), whole(2), whole(4)],
        vec![whole(0), whole(1), whole(2)],
        0,
    )
}

/// Another: transposed by seven, twice as slow, differently voiced.
pub fn second_enactment() -> Result<Enactment, LadderRefusal> {
    let first = first_enactment()?;
    let transposed = transpose(&whole(7), &first);
    let slowed = scale_tempo(&whole(2), &transposed)?;
    Ok(revoice(1, &slowed))
}

#[cfg(test)]
mod tests;
