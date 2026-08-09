//! One emission read against a **declared second body's** standing, on material both were given.
//!
//! ## The defect this closes
//!
//! `canon/THE_HOLOBROCHOS_SPINE.md` §2, from Soma's `MATHEMATICAL_HOLONICS.md`, retains this as
//! mathematically exact:
//!
//! > *"comparison is **situated by a frame** and is therefore at least a frame/object/object
//! > relation"*
//!
//! [`crate::surprisal`] carries an exact measure and could not obey that sentence, because every
//! entry point it offers takes **one** population. `entropy(P)` is a one-body read. `cross_entropy(P,
//! Q)` has two objects but returns a single weighted form with no member exhibited and nowhere to put
//! the refusal, so an event `Q` has no standing for collapses the whole reading. Neither returns a
//! *residual population*. This module supplies the missing slot: the frame is declared, both objects
//! are named, and the return is the residual **per member**, each carrying its own exact symbolic
//! surprisal.
//!
//! ## The three arms are one oriented residual
//!
//! `CLAUDE.md` §13 rule 2 states the object: *"`r = Δ(y,y*;F)` is the complete oriented residual;
//! `L = ℓ_B(r)` is one receiver's measurement of it."* This module returns `r` and never forms `L`.
//! There is no total on any return of this file, and there is no method that answers *how good is
//! this body* — a scalar that measures is lawful, a scalar that governs is not, and a single number
//! ranking two bodies would govern.
//!
//! ```text
//!   Founded    the body emitted it; the reference's standing does not carry it.
//!              `Support::Unsupported` — the typed refusal — and the law's resolution is that the
//!              reference FOUNDs, so the member carries the depth the reference takes on when it
//!              does. Never a smoothing constant.
//!   Shared     both carry it. `separation = S_body(a) − S_reference(a)`, exactly, as a form.
//!   Withheld   the reference carries it and the body did not emit it. The residual is ORIENTED and
//!              this is its other sign; `situate(reference, body)` moves these members to `Founded`.
//! ```
//!
//! ## `OPEN` is retained, never resolved
//!
//! §3 of the spine again: *"`OPEN` does not itself choose correction, branching, or a new axis."*
//! [`SituatedReading::orderings_at`] returns the **complete within-arm relation** — every pair with
//! its four-state verdict and **both members' forms on the entry** — rather than a sorted list. That
//! is not a stylistic choice: `Open` is not transitive, so the relation admits no linear extension,
//! and any sort would have to break an `Open` by picking a side. The pair is retained instead.
//!
//! Orderings are within one arm. A `Founded` member is situated by a depth and a `Shared` member by
//! a difference of depths; ordering one against the other would compare two quantities of different
//! kinds under one verdict, which is the frame confusion this module exists to prevent.
//!
//! ## What is NOT expressed through `gluing.rs`, and why
//!
//! [`crate::gluing`] is the nearest standing two-body organ, and its Mayer–Vietoris connecting map
//! is keyed to a cover — to *which receivers*. It is the right instrument for a different question,
//! and three facts keep this reading out of it:
//!
//! 1. `read_cover` takes **one** `GradedCausalComplex` and two subcomplexes of it. Two bodies given
//!    the same material emit two populations, and the only complex containing both is the larger
//!    body's own, in which the reference's emission is a **subcomplex**. A cover whose two sections
//!    are nested has union equal to the larger section, so exactness forces `δ ≡ 0` at every grade —
//!    `gluing.rs`'s own control `a_cover_that_must_glue_returns_no_obstruction` is that case. The
//!    nested two-body comparison is invisible to Mayer–Vietoris **by a theorem**, not by an
//!    implementation gap, and `examples/the_measure_is_situated.rs` measures it rather than asserting
//!    it.
//! 2. `δ` returns a **rank over ℤ** per grade. It has no slot for a ℚ-linear form over prime axes and
//!    exhibits no member. The two returns are different species and neither refines the other.
//! 3. What the two organs share is the sentence, and it is worth naming: the Mayer–Vietoris class
//!    lives in the disagreement of two *receivers* over one source; this residual lives in the
//!    disagreement of two *bodies* over one material. Same shape, different carrier.
//!
//! ## Float-free
//!
//! Every quantity here is a [`SymbolicSurprisal`] — a ℚ-linear form in `{log₂ p}`, stored as its
//! coefficient map and never evaluated — a [`BigUint`] occurrence count, or an [`ExactOrdering`]
//! whose `Open` arm is the honest answer at a declared grain. There is no tolerance, no epsilon, no
//! weight and no threshold in this file.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::Zero;
use serde::{Deserialize, Serialize};

use crate::conditioned_derivation::Passage;
use crate::exact_value::ExactOrdering;
use crate::surprisal::{
    entropy, read_population, Grain, Support, SurprisalError, SymbolicSurprisal,
};

// -------------------------------------------------------------------------------------------------
// The material, and what a body emitted on it
// -------------------------------------------------------------------------------------------------

/// One body's emission over a declared material: the exact occurrence count per named event.
///
/// `body` and `material` are carried, not decorative. `material` is checked against the frame's on
/// every reading, so two emissions read on two materials are refused rather than compared — which is
/// the frame half of the frame/object/object relation being structural instead of documentary.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Emission {
    /// Which body emitted this. Carried into every receipt, so no reading is anonymous.
    pub body: String,
    /// The declared material it was read on.
    pub material: String,
    counts: BTreeMap<String, BigUint>,
}

impl Emission {
    pub fn by(body: &str, material: &str) -> Self {
        Self {
            body: body.to_owned(),
            material: material.to_owned(),
            counts: BTreeMap::new(),
        }
    }

    /// One more occurrence of a named event.
    pub fn observe(&mut self, event: &str) {
        self.observe_times(event, 1);
    }

    /// `times` more occurrences. Zero is a no-op rather than a stored zero: an event with no
    /// occurrences is an event the emission does not carry, and storing it would make the
    /// `Founded` and `Shared` arms disagree about the same fact.
    pub fn observe_times(&mut self, event: &str, times: u32) {
        if times == 0 || event.is_empty() {
            return;
        }
        *self
            .counts
            .entry(event.to_owned())
            .or_insert_with(BigUint::zero) += BigUint::from(times);
    }

    /// The occurrence multiset, in canonical event order. The returned artifact.
    pub fn counts(&self) -> &BTreeMap<String, BigUint> {
        &self.counts
    }

    pub fn events(&self) -> BTreeSet<&str> {
        self.counts.keys().map(String::as_str).collect()
    }

    pub fn occurrences(&self, event: &str) -> BigUint {
        self.counts.get(event).cloned().unwrap_or_else(BigUint::zero)
    }

    /// The total occurrence count. **A denominator, never a verdict** — it is what a probability is
    /// taken against and nothing reads it as a magnitude of the body.
    pub fn total(&self) -> BigUint {
        self.counts.values().sum()
    }

    pub fn is_empty(&self) -> bool {
        self.counts.is_empty()
    }

    /// The emission on the `u64` axis [`crate::surprisal`] reads, under a declared name table.
    fn on_axis(&self, table: &EventTable) -> BTreeMap<u64, BigUint> {
        self.counts
            .iter()
            .filter_map(|(event, count)| {
                table.id(event).map(|id| (id, count.clone()))
            })
            .collect()
    }
}

/// The declared name table: the union of both emissions' events, in canonical order, each on the
/// `u64` axis `surprisal` reads.
///
/// The axis is an internal coordinate and is never returned. Every member of every reading is named
/// by its event text, because a returned integer would be a receiver-visible coordinate promoted
/// into the artifact — `CLAUDE.md` §0's fourth lesson.
struct EventTable {
    names: Vec<String>,
    index: BTreeMap<String, u64>,
}

impl EventTable {
    fn over(left: &Emission, right: &Emission) -> Self {
        let mut names: BTreeSet<&str> = left.events();
        names.extend(right.events());
        let names: Vec<String> = names.into_iter().map(str::to_owned).collect();
        let index = names
            .iter()
            .enumerate()
            .map(|(at, name)| (name.clone(), at as u64))
            .collect();
        Self { names, index }
    }

    fn id(&self, event: &str) -> Option<u64> {
        self.index.get(event).copied()
    }

    fn name(&self, id: u64) -> &str {
        &self.names[id as usize]
    }
}

// -------------------------------------------------------------------------------------------------
// The frame
// -------------------------------------------------------------------------------------------------

/// The third term. What an event is, what material it was read on, and the grain every ordering in
/// this reading is taken at.
///
/// A measure computed from one body alone is a one-body read and is not a comparison. This type is
/// the slot that makes the read situated, and it is required rather than optional.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frame {
    /// What an event is under this reading, stated. Two readings of the same bytes under two event
    /// laws are visibly two frames.
    pub receiver: String,
    /// The material both emissions were read on. Both must name it.
    pub material: String,
    /// The declared grain. Printed in every receipt; a verdict is never separable from it.
    pub grain: Grain,
}

impl Frame {
    pub fn new(receiver: &str, material: &str, grain: Grain) -> Self {
        Self {
            receiver: receiver.to_owned(),
            material: material.to_owned(),
            grain,
        }
    }

    /// The same frame at another declared grain. The receiver and the material do not move.
    pub fn at_grain(&self, grain: Grain) -> Self {
        Self {
            grain,
            ..self.clone()
        }
    }
}

impl std::fmt::Display for Frame {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "frame[material={:?}, event={:?}, {}]",
            self.material, self.receiver, self.grain
        )
    }
}

// -------------------------------------------------------------------------------------------------
// The residual, per member
// -------------------------------------------------------------------------------------------------

/// Which arm of the oriented residual a member stands in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ResidualArm {
    Founded,
    Shared,
    Withheld,
}

impl ResidualArm {
    /// Every arm, in the order a receipt prints them.
    pub const ALL: [Self; 3] = [Self::Founded, Self::Shared, Self::Withheld];

    pub fn named(&self) -> &'static str {
        match self {
            Self::Founded => "founded",
            Self::Shared => "shared",
            Self::Withheld => "withheld",
        }
    }
}

/// Where one event of the declared material stands between the two bodies.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Situation {
    /// The body emitted it; the reference's standing has no relation carrying it.
    ///
    /// `Support::Unsupported` is the typed refusal, and the law's resolution is that the live event
    /// **FOUNDs a new relation and changes the support**. `after_found` is the depth the reference
    /// takes on when it does — computed by actually founding it, never by a smoothing constant, and
    /// never by a large finite stand-in for infinity.
    Founded {
        emitted: SymbolicSurprisal,
        after_found: SymbolicSurprisal,
    },
    /// Both carry it. `separation = emitted − carried`, exactly, as a form.
    ///
    /// Its vanishing is decided by the coefficient test — ℚ-linear independence of `{log₂ p}` — with
    /// **no enclosure taken**, so no grain can move a `Shared` member into or out of the residual.
    Shared {
        emitted: SymbolicSurprisal,
        carried: SymbolicSurprisal,
        separation: SymbolicSurprisal,
    },
    /// The reference carries it and the body did not emit it.
    Withheld { carried: SymbolicSurprisal },
}

/// One event of the declared material, situated between the two bodies.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedMember {
    /// The event, **named**. Never an index.
    pub event: String,
    pub emitted_occurrences: BigUint,
    pub referenced_occurrences: BigUint,
    pub situation: Situation,
}

impl SituatedMember {
    pub fn arm(&self) -> ResidualArm {
        match self.situation {
            Situation::Founded { .. } => ResidualArm::Founded,
            Situation::Shared { .. } => ResidualArm::Shared,
            Situation::Withheld { .. } => ResidualArm::Withheld,
        }
    }

    /// The form this member's arm situates it by. Named by [`Self::situating_form_named`], because
    /// the three arms situate by three different quantities and a reader must not have to guess.
    pub fn situating_form(&self) -> &SymbolicSurprisal {
        match &self.situation {
            Situation::Founded { after_found, .. } => after_found,
            Situation::Shared { separation, .. } => separation,
            Situation::Withheld { carried } => carried,
        }
    }

    pub fn situating_form_named(&self) -> &'static str {
        match &self.situation {
            Situation::Founded { .. } => "the depth the reference takes on when it FOUNDs this event",
            Situation::Shared { .. } => "S_body - S_reference",
            Situation::Withheld { .. } => "the depth the reference carries and the body did not emit",
        }
    }

    /// The four-state verdict of this member's situating form against the zero form, at a declared
    /// grain.
    ///
    /// This is how a sign is read here. `CLAUDE.md` §2b: a bare stored sign keeps the magnitude and
    /// discards the passage that produced it, so nothing on this type stores one — the direction is
    /// re-derived from the retained form on demand, and may return `Open`.
    pub fn against_zero(&self, grain: Grain) -> Result<ExactOrdering, SurprisalError> {
        self.situating_form()
            .compare_grain(&SymbolicSurprisal::zero(), grain)
    }
}

/// One ordered pair, with the verdict the declared grain reached and **both members' forms on the
/// entry**.
///
/// An `Open` entry loses nothing: the two forms are here, exactly, and a caller refining the grain
/// re-asks the same pair. That is what retaining an `Open` means operationally.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedOrdering {
    pub arm: ResidualArm,
    pub left: String,
    pub right: String,
    pub left_form: SymbolicSurprisal,
    pub right_form: SymbolicSurprisal,
    pub grain: Grain,
    pub verdict: ExactOrdering,
}

impl SituatedOrdering {
    pub fn is_open(&self) -> bool {
        self.verdict == ExactOrdering::Open
    }

    /// The entry rendered as its artifact: both events, both forms, the grain, the verdict.
    pub fn render(&self) -> String {
        format!(
            "{} vs {}  ->  {:?}  at {}\n      left  = {}\n      right = {}",
            self.left,
            self.right,
            self.verdict,
            self.grain,
            self.left_form.named(),
            self.right_form.named()
        )
    }
}

// -------------------------------------------------------------------------------------------------
// The reading
// -------------------------------------------------------------------------------------------------

/// A body's emission, situated against a declared reference body's, on one material.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedReading {
    pub frame: Frame,
    pub body: String,
    pub reference: String,
    /// Every event of the declared material, in canonical order. The population.
    pub members: Vec<SituatedMember>,
}

impl SituatedReading {
    pub fn arm(&self, arm: ResidualArm) -> Vec<&SituatedMember> {
        self.members
            .iter()
            .filter(|member| member.arm() == arm)
            .collect()
    }

    pub fn founded(&self) -> Vec<&SituatedMember> {
        self.arm(ResidualArm::Founded)
    }

    pub fn shared(&self) -> Vec<&SituatedMember> {
        self.arm(ResidualArm::Shared)
    }

    pub fn withheld(&self) -> Vec<&SituatedMember> {
        self.arm(ResidualArm::Withheld)
    }

    /// **The residual.** Every member the reference does not already account for: both off-diagonal
    /// arms whole, plus the shared members whose separation does not vanish.
    ///
    /// An empty return is a return and not a failure. It says the reference already carries
    /// everything this body emitted, at the same depths, and carries nothing the body did not.
    pub fn separating(&self) -> Vec<&SituatedMember> {
        self.members
            .iter()
            .filter(|member| match &member.situation {
                Situation::Shared { separation, .. } => !separation.is_zero(),
                Situation::Founded { .. } | Situation::Withheld { .. } => true,
            })
            .collect()
    }

    /// The situated read returned nothing.
    ///
    /// Structural first — no founded arm, no withheld arm — then exact: every shared member's
    /// separation vanishes by the coefficient test with **no enclosure taken**, so no grain can move
    /// this answer.
    ///
    /// A reading with no members at all returns `false`. A check that passes on an empty population
    /// is a check that cannot fail, which is `CLAUDE.md` §8's own defect wearing a passing result.
    pub fn returns_zero(&self) -> bool {
        !self.members.is_empty() && self.separating().is_empty()
    }

    /// Every within-arm pair with its four-state verdict, at the frame's declared grain.
    pub fn orderings(&self) -> Result<Vec<SituatedOrdering>, SurprisalError> {
        self.orderings_at(self.frame.grain)
    }

    /// The same relation at another declared grain.
    ///
    /// **The complete relation, never a sort.** `Open` is not transitive, so the relation admits no
    /// linear extension and any ranking would have to break an `Open` by picking a side.
    ///
    /// **Cost law:** quadratic in each arm's population, and each pair takes one enclosure of one
    /// difference form at the declared grain. Stated because `CLAUDE.md` §8 requires reproducing what
    /// an organ costs and not only what it returns.
    pub fn orderings_at(&self, grain: Grain) -> Result<Vec<SituatedOrdering>, SurprisalError> {
        let mut relation = Vec::new();
        for arm in ResidualArm::ALL {
            let members = self.arm(arm);
            for (at, left) in members.iter().enumerate() {
                for right in members.iter().skip(at + 1) {
                    let left_form = left.situating_form();
                    let right_form = right.situating_form();
                    relation.push(SituatedOrdering {
                        arm,
                        left: left.event.clone(),
                        right: right.event.clone(),
                        left_form: left_form.clone(),
                        right_form: right_form.clone(),
                        grain,
                        verdict: left_form.compare_grain(right_form, grain)?,
                    });
                }
            }
        }
        Ok(relation)
    }

    /// The pairs the declared grain could not order, both members carried on every entry.
    pub fn open_orderings_at(
        &self,
        grain: Grain,
    ) -> Result<Vec<SituatedOrdering>, SurprisalError> {
        Ok(self
            .orderings_at(grain)?
            .into_iter()
            .filter(SituatedOrdering::is_open)
            .collect())
    }

    /// Every event this reading holds, named. The retention check an `Open` is judged against.
    pub fn event_names(&self) -> BTreeSet<&str> {
        self.members
            .iter()
            .map(|member| member.event.as_str())
            .collect()
    }
}

// -------------------------------------------------------------------------------------------------
// The read
// -------------------------------------------------------------------------------------------------

/// Situate one body's emission against a declared reference body's, on the material the frame names.
///
/// Both emissions must name the frame's material; a reading across two materials is refused rather
/// than taken. Nothing else is required of the pair — in particular the reference may be the body
/// itself, which is the calibration case and must return zero, exactly as `gluing.rs`'s identity
/// cover must return no obstruction.
pub fn situate(
    body: &Emission,
    reference: &Emission,
    frame: &Frame,
) -> Result<SituatedReading, SituatedRefusal> {
    if body.material != frame.material || reference.material != frame.material {
        return Err(SituatedRefusal::MaterialsDiffer {
            frame: frame.material.clone(),
            body: body.material.clone(),
            reference: reference.material.clone(),
        });
    }

    let table = EventTable::over(body, reference);
    let emitted = body.on_axis(&table);
    let referenced = reference.on_axis(&table);

    let in_body = read_population(&emitted, &emitted)?;
    let in_reference_of_emitted = read_population(&emitted, &referenced)?;
    let in_reference = read_population(&referenced, &referenced)?;

    let mut members = Vec::with_capacity(table.names.len());
    for (id, event) in table.names.iter().enumerate() {
        let id = id as u64;
        let emitted_occurrences = body.occurrences(event);
        let referenced_occurrences = reference.occurrences(event);

        let situation = match (
            in_body.get(&id),
            in_reference_of_emitted.get(&id),
            in_reference.get(&id),
        ) {
            // The body emitted it and the reference's standing does not carry it. The FOUND.
            (Some(Support::Supported(own)), Some(Support::Unsupported), _) => {
                let mut founding = referenced.clone();
                Support::found(&mut founding, id);
                let Support::Supported(after_found) = Support::read(&founding, id)? else {
                    // `found` inserts the event with a positive count, so the re-read is supported.
                    return Err(SituatedRefusal::FoundingDidNotSupport {
                        event: table.name(id).to_owned(),
                    });
                };
                Situation::Founded {
                    emitted: own.clone(),
                    after_found,
                }
            }
            // Both carry it.
            (Some(Support::Supported(own)), Some(Support::Supported(carried)), _) => {
                Situation::Shared {
                    emitted: own.clone(),
                    carried: carried.clone(),
                    separation: own.minus(carried),
                }
            }
            // The reference carries it and the body did not emit it.
            (None, _, Some(Support::Supported(carried))) => Situation::Withheld {
                carried: carried.clone(),
            },
            // Neither body has standing for it. Unreachable: the table is the union of the two
            // emissions' events, so every id is carried by at least one of them with a positive
            // count. Returned by name rather than asserted away.
            _ => {
                return Err(SituatedRefusal::EventStandsInNeitherBody {
                    event: table.name(id).to_owned(),
                })
            }
        };

        members.push(SituatedMember {
            event: event.clone(),
            emitted_occurrences,
            referenced_occurrences,
            situation,
        });
    }

    Ok(SituatedReading {
        frame: frame.clone(),
        body: body.body.clone(),
        reference: reference.body.clone(),
        members,
    })
}

/// **The one-body read**, kept here so the two can be printed side by side.
///
/// `H(P) = Σ_a P(a)·S_P(a)`: the emission received through its own code, with no reference body at
/// all. It is a lawful *measurement* — `CLAUDE.md` §13 rule 2's jurisdiction test — and it is not a
/// comparison, because a comparison is situated by a frame and is therefore at least a
/// frame/object/object relation. It says nothing about this body relative to any other, and nothing
/// in this module admits, ranks, or gates on it.
///
/// It is here because the whole content of this module is that it and [`situate`] disagree: on
/// material where a body founded nothing beyond its reference, the situated read returns zero and
/// this returns a non-zero form.
pub fn one_body_read(emission: &Emission) -> Result<Support, SurprisalError> {
    let table = EventTable::over(emission, emission);
    entropy(&emission.on_axis(&table))
}

// -------------------------------------------------------------------------------------------------
// The seam: a conditioned-derivation passage population, read as an emission
// -------------------------------------------------------------------------------------------------

/// Read a [`Passage`] population into an emission over one declared statement.
///
/// **The declared receiver, and it belongs in the [`Frame`]:** one event per identifier that a route
/// *reaching this statement* recruited, counted at the exact multiplicity that route named it. Routes
/// reaching other statements are not on this face — which is what makes the face situated by the
/// query rather than by the deposit as a whole, and what lets a body's production bring an identifier
/// the reference's standing genuinely does not carry.
///
/// This is the edge, not an organ. `canon/THE_HOLOBROCHOS_SPINE.md` §5 measured that
/// `crates/holonic-engine` contains zero module cycles and that its analyses terminate in `stdout`;
/// putting this seam in the library rather than in a driver is the difference between an emission
/// that returns and one that does not.
pub fn emission_reaching(body: &str, material: &str, passages: &[Passage], statement: &str) -> Emission {
    let mut emission = Emission::by(body, material);
    for passage in passages {
        if passage.derivation.statement != statement {
            continue;
        }
        for (identifier, multiplicity) in &passage.derivation.recruited {
            emission.observe_times(identifier, *multiplicity);
        }
    }
    emission
}

// -------------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SituatedRefusal {
    /// The two emissions were read on different material. A comparison is situated by a frame and is
    /// therefore at least a frame/object/object relation; two objects read on two materials are not
    /// two objects of one relation, and returning a residual for them would be a number with no
    /// frame behind it.
    MaterialsDiffer {
        frame: String,
        body: String,
        reference: String,
    },
    /// A FOUND left the event without support. Structurally impossible — `found` inserts a positive
    /// count — and returned by name rather than asserted away.
    FoundingDidNotSupport { event: String },
    /// An event of the declared material stood in neither body. Structurally impossible, since the
    /// material is the union of the two emissions.
    EventStandsInNeitherBody { event: String },
    Surprisal(SurprisalError),
}

impl From<SurprisalError> for SituatedRefusal {
    fn from(error: SurprisalError) -> Self {
        Self::Surprisal(error)
    }
}

impl std::fmt::Display for SituatedRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MaterialsDiffer {
                frame,
                body,
                reference,
            } => write!(
                formatter,
                "the frame names the material {frame:?}, the body was read on {body:?} and the \
                 reference on {reference:?}; a comparison across two materials is not situated"
            ),
            Self::FoundingDidNotSupport { event } => write!(
                formatter,
                "founding {event:?} in the reference's standing left it unsupported"
            ),
            Self::EventStandsInNeitherBody { event } => write!(
                formatter,
                "the event {event:?} stands in neither body, so it is not of the declared material"
            ),
            Self::Surprisal(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for SituatedRefusal {}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame() -> Frame {
        Frame::new("a named token", "the declared bench", Grain::DECLARED)
    }

    fn emission(body: &str, entries: &[(&str, u32)]) -> Emission {
        let mut emission = Emission::by(body, "the declared bench");
        for (event, times) in entries {
            emission.observe_times(event, *times);
        }
        emission
    }

    /// **The calibration control.** A body read against itself returns zero — structurally, and by
    /// the exact coefficient test with no enclosure taken — while the one-body read of the *same*
    /// emission returns a form that does not vanish.
    ///
    /// This is the whole thesis in one test: the number a one-body measure returns is not a
    /// comparison, and treating it as one is the dropped third.
    #[test]
    fn a_body_read_against_itself_returns_zero_and_the_one_body_read_does_not() {
        let alone = emission("the body", &[("alpha", 3), ("beta", 3), ("gamma", 3), ("delta", 1)]);
        let reading = situate(&alone, &alone, &frame()).unwrap();

        assert_eq!(reading.members.len(), 4, "every event of the material is a member");
        assert!(reading.founded().is_empty());
        assert!(reading.withheld().is_empty());
        assert!(reading.separating().is_empty());
        assert!(reading.returns_zero(), "the situated read returns zero");
        for member in reading.shared() {
            let Situation::Shared { separation, .. } = &member.situation else {
                unreachable!("every member is shared here");
            };
            assert!(separation.is_zero(), "{} separated from itself", member.event);
            assert_eq!(
                member.against_zero(Grain::at(1, 4)).unwrap(),
                ExactOrdering::Equal,
                "decided on coefficients, so the coarsest grain still decides it"
            );
        }

        let Support::Supported(alone_form) = one_body_read(&alone).unwrap() else {
            panic!("a non-empty emission supports itself");
        };
        assert!(
            !alone_form.is_zero(),
            "the ONE-BODY read of the same emission is non-zero: {}",
            alone_form.named()
        );
        assert_eq!(alone_form.named(), "log2(2) + -9/10*log2(3) + log2(5)");
    }

    /// An event the reference has no standing for FOUNDs. It is not smoothed, not collapsed, and not
    /// given a large finite stand-in — the reference takes on the depth founding it actually costs.
    #[test]
    fn an_event_the_reference_does_not_carry_founds_rather_than_smoothing() {
        let body = emission("the body", &[("alpha", 1), ("novel", 1)]);
        let reference = emission("the reference", &[("alpha", 1)]);
        let reading = situate(&body, &reference, &frame()).unwrap();

        let founded = reading.founded();
        assert_eq!(founded.len(), 1);
        assert_eq!(founded[0].event, "novel");
        let Situation::Founded {
            emitted,
            after_found,
        } = &founded[0].situation
        else {
            unreachable!()
        };
        // The body emitted it at 1 of 2, so its own code gives it one bit.
        assert_eq!(emitted.named(), "log2(2)");
        // The reference's standing was a single event; founding this one makes it 1 of 2.
        assert_eq!(after_found.named(), "log2(2)");
        assert!(!reading.returns_zero());
        assert_eq!(reading.separating().len(), 2, "the FOUND, and alpha's moved depth");
    }

    /// **The residual is oriented.** Swapping the two bodies moves every founded member to withheld
    /// and negates every shared separation, exactly.
    #[test]
    fn the_residual_is_oriented_and_swapping_the_bodies_swaps_the_arms() {
        let body = emission("the body", &[("alpha", 2), ("novel", 1)]);
        let reference = emission("the reference", &[("alpha", 1), ("held", 3)]);

        let forward = situate(&body, &reference, &frame()).unwrap();
        let backward = situate(&reference, &body, &frame()).unwrap();

        assert_eq!(
            forward.founded().iter().map(|m| m.event.as_str()).collect::<Vec<_>>(),
            vec!["novel"]
        );
        assert_eq!(
            forward.withheld().iter().map(|m| m.event.as_str()).collect::<Vec<_>>(),
            vec!["held"]
        );
        assert_eq!(
            backward.founded().iter().map(|m| m.event.as_str()).collect::<Vec<_>>(),
            vec!["held"]
        );
        assert_eq!(
            backward.withheld().iter().map(|m| m.event.as_str()).collect::<Vec<_>>(),
            vec!["novel"]
        );

        let separation = |reading: &SituatedReading, event: &str| {
            reading
                .members
                .iter()
                .find(|member| member.event == event)
                .and_then(|member| match &member.situation {
                    Situation::Shared { separation, .. } => Some(separation.clone()),
                    _ => None,
                })
                .expect("alpha is shared in both directions")
        };
        let there = separation(&forward, "alpha");
        let back = separation(&backward, "alpha");
        assert!(!there.is_zero());
        assert!(
            there.plus(&back).is_zero(),
            "the two directions must cancel exactly: {} against {}",
            there.named(),
            back.named()
        );
    }

    /// **The four-state ordering is non-vacuous, and the grain is what moves it.**
    ///
    /// One pair of shared members, two declared grains, two verdicts — and on the `Open` return both
    /// members are still on the reading and both forms are on the entry, so nothing was discarded to
    /// reach it.
    #[test]
    fn the_ordering_is_four_state_and_the_grain_is_what_moves_it() {
        // Two separations differ by exactly `log2(5) - log2(3)`, because
        // `sep(a) - sep(b) = log2((c_ref(a)/c_body(a)) · (c_body(b)/c_ref(b)))` and the two ratios
        // here are `5/3` and `1`. That is the same separation `surprisal`'s own control shows a
        // coarse grain cannot resolve, reached through the emission counts rather than written down.
        let body = emission("the body", &[("wide", 3), ("narrow", 2), ("filler", 2)]);
        let reference = emission("the reference", &[("wide", 5), ("narrow", 2), ("filler", 1)]);
        let reading = situate(&body, &reference, &frame()).unwrap();
        assert!(!reading.returns_zero(), "every member separates on this material");

        let coarse = Grain::at(1, 4);
        let open = reading.open_orderings_at(coarse).unwrap();
        assert!(
            !open.is_empty(),
            "a four-state ordering that never returns Open has not been exercised"
        );
        for entry in &open {
            assert_eq!(entry.grain, coarse, "the receipt carries the grain that reached it");
            // Both members retained: on the entry, and on the reading.
            assert!(reading.event_names().contains(entry.left.as_str()));
            assert!(reading.event_names().contains(entry.right.as_str()));
            assert!(!entry.left_form.named().is_empty());
            assert!(!entry.right_form.named().is_empty());

            // And the refusal is not permanent. The same pair at the declared grain decides.
            let fine = entry
                .left_form
                .compare_grain(&entry.right_form, Grain::DECLARED)
                .unwrap();
            assert_ne!(
                fine,
                ExactOrdering::Open,
                "{} vs {} must decide at the declared grain",
                entry.left,
                entry.right
            );
        }

        // The relation is complete and within-arm: three shared members give three pairs.
        let relation = reading.orderings().unwrap();
        assert_eq!(relation.len(), 3);
        assert!(relation.iter().all(|entry| entry.arm == ResidualArm::Shared));
    }

    /// A reading across two materials is refused rather than taken. The frame is structural.
    #[test]
    fn a_reading_across_two_materials_is_refused() {
        let body = emission("the body", &[("alpha", 1)]);
        let mut elsewhere = Emission::by("the reference", "another bench");
        elsewhere.observe("alpha");
        assert_eq!(
            situate(&body, &elsewhere, &frame()),
            Err(SituatedRefusal::MaterialsDiffer {
                frame: "the declared bench".to_owned(),
                body: "the declared bench".to_owned(),
                reference: "another bench".to_owned(),
            })
        );
    }

    /// **The trivial echo, as a population.** An emission that reproduces its input is separated from
    /// one that founds something new by the *shape of the residual*, with nothing scored: the echo's
    /// founded arm is empty and every shared separation vanishes exactly; the founding body's does
    /// not, and it moves every shared member because the denominator moved.
    #[test]
    fn an_echo_and_a_founding_emission_differ_as_populations_with_nothing_scored() {
        let reference = emission("the reference", &[("alpha", 2), ("beta", 1)]);
        let echo = emission("the echo", &[("alpha", 2), ("beta", 1)]);
        let founding = emission("the founding body", &[("alpha", 2), ("beta", 1), ("novel", 1)]);

        let echoed = situate(&echo, &reference, &frame()).unwrap();
        assert!(echoed.returns_zero());
        assert!(echoed.founded().is_empty());
        assert_eq!(echoed.shared().len(), 2);

        let founded = situate(&founding, &reference, &frame()).unwrap();
        assert!(!founded.returns_zero());
        assert_eq!(founded.founded().len(), 1);
        // The FOUND moved the denominator, so every shared member's depth moved with it.
        assert_eq!(founded.shared().len(), 2);
        for member in founded.shared() {
            let Situation::Shared { separation, .. } = &member.situation else {
                unreachable!()
            };
            assert!(
                !separation.is_zero(),
                "{} must move when the support changes",
                member.event
            );
        }

        // And the one-body read cannot tell the echo from the reference, which is the point.
        assert_eq!(
            one_body_read(&echo).unwrap(),
            one_body_read(&reference).unwrap(),
            "receiver non-reconstruction: equal magnitudes do not identify constructions"
        );
    }

    /// A zero-occurrence observation stores nothing, so `Founded` and `Shared` cannot disagree about
    /// whether an emission carries an event.
    #[test]
    fn a_zero_occurrence_observation_founds_no_event() {
        let mut emission = Emission::by("the body", "the declared bench");
        emission.observe_times("nothing", 0);
        emission.observe_times("", 3);
        assert!(emission.is_empty());
        assert_eq!(emission.total(), BigUint::zero());
    }
}
