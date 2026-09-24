//! **B6 — passages.** `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})` as a first-class typed event, so
//! that environment change, binding, protonation and mutation are passages carrying receipts rather
//! than reparameterizations.
//!
//! [definition] This file is part of the [`crate::physical_occurrence`] owner and adds no second
//! carrier. Its vertical events are built **on** that owner's [`EnvironmentPassage`], which already
//! refuses a transport that leaves a divergent coordinate unaccounted; a [`Passage`] adds what that
//! type does not carry — the two occurrences, the exact change in the constraint complex `K`, the
//! residual needed to reopen the source, and the cost of the whole move. It owns item **B6** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`.
//!
//! # What a passage is
//!
//! [definition] A passage is an **addressed span** `source <- event -> target` carrying:
//!
//! | Component | Owner |
//! |---|---|
//! | the source occurrence | [`PassageEnd`], built from a [`SituatedFamily`] |
//! | the target occurrence | [`PassageEnd`] |
//! | the event e | [`PassageEvent`], with its own evidence requirement per kind |
//! | what changed in K | [`ConstraintDelta`], the exact per-contact class transition |
//! | what changed in Theta | [`EnvironmentDelta`], the complete coordinate divergence |
//! | the residual | [`PassageResidual`], exactly what [`Transition::reopen`] needs |
//! | the cost | [`crate::presentation_cost::CostReceipt`] |
//!
//! # Vertical and horizontal are two types with no coercion
//!
//! [definition] Environment change, binding and protonation move the **environment around one
//! object**: they are vertical. Mutation changes the object itself, so it is a **horizontal** move.
//! The axis is a type parameter, [`Vertical`] or [`Horizontal`], so:
//!
//! * `Passage<Vertical>` and `Passage<Horizontal>` are different types;
//! * there is no `From`, `Into`, `Deref` or trait object between them, and no constructor of one
//!   returns the other — [`Passage::mutation`] exists only on `impl Passage<Horizontal>` and the
//!   three vertical constructors only on `impl Passage<Vertical>`;
//! * [`Passage::then`] composes within one axis by its own signature, so a mutation can never be
//!   concatenated into a vertical chain.
//!
//! [definition] A chain that genuinely mixes the two is **not** a passage of either type in this
//! owner, and no coercion is offered to make it one. Two consecutive passages on different axes
//! are two passages, and the honest statement is that the object changed partway; see
//! [`PassageRefusal::ObjectChangedAlongTheVerticalAxis`] and
//! [`PassageRefusal::MutationAlsoMovesTheEnvironment`], which are the two directions of that
//! refusal.
//!
//! # Composition retains the joining occurrence
//!
//! [definition] AGENTS.md: "An elementary passage is an addressed span `X <- W_f -> Y`. Serial
//! composition retains the joining equality and pullback occurrence population. Equal endpoints,
//! counts or digests do not preserve lineage by themselves." [`Passage::then`] therefore requires
//! the joining [`PassageEnd`] to be **equal as a value** — occurrence identity, lineage,
//! environment and object — and **retains it**: the composite's [`Passage::steps`] carry every
//! step's own two ends, so the joining occurrence is recoverable from the composite and is not
//! quotiented away by the endpoints matching.
//!
//! [proved-derived] Composition is associative **exactly**: [`Passage::then`] concatenates the
//! step list, so `(p ∘ q) ∘ r` and `p ∘ (q ∘ r)` are equal values, not merely equal at their
//! endpoints. The composed [`ConstraintDelta`] and [`crate::presentation_cost::CostReceipt`] are
//! left folds over that one list, so they inherit the same equality rather than carrying a
//! bracketing of their own.
//!
//! # A passage is not invertible in general
//!
//! [proved-derived] [`Passage`] is a [`Transition`]: [`Transition::apply`] transports the face,
//! [`Transition::residual`] retains the whole source face — its environment, its object identity
//! and its class at every contact — and [`Transition::reopen`] returns the source exactly.
//! `apply` is constant in the source's classes, so two different sources of one passage have the
//! same transported face and the transported face alone determines nothing;
//! [`Passage::reverse_passage`] returns
//! [`holonics::restriction::tower::ReversePassageReceipt::OnlyWithTheResidual`] with the two merged
//! faces. **The reverse exists exactly when the residual is retained**, which is the passage
//! instance of `Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual`;
//! [`Transition::check_reopen`] is the receipt that it is exact and not an approximation.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean`, section
//! **B6**, namespace `Soma.Holonics.Foundation.PhysicalOccurrence`.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `PassageAxis`, `vertical_ne_horizontal` | [`Vertical`], [`Horizontal`], two distinct types |
//! | `PassageEvent`, `PassageEvent.axis` | [`PassageEvent`], [`PassageEvent::axis_label`] |
//! | `mutation_is_horizontal`, `the_other_three_are_vertical` | the constructors' `impl` blocks |
//! | `Delta`, `Delta.comp`, `Delta.comp_assoc` | [`ConstraintDelta`], [`ConstraintDelta::compose`] |
//! | `Delta.Composable`, `Delta.comp_composable` | [`PassageRefusal::DeltaEndpointsDisagree`] |
//! | `Delta.idOn`, `Delta.idOn_comp`, `Delta.comp_idOn` | [`ConstraintDelta::identity_on`] |
//! | `TypedPassage`, `TypedPassage.steps_on_axis` | [`Passage`] with its private step list |
//! | `no_vertical_passage_carries_a_mutation`, `no_horizontal_passage_carries_an_environment_change` | `Passage<Vertical>` has no mutation constructor |
//! | `TypedPassage.comp`, `TypedPassage.comp_assoc` | [`Passage::then`] |
//! | `ClassAction`, `ClassAction.apply`, `ClassAction.residual`, `ClassAction.reopen`, `ClassAction.reopen_apply` | the [`Transition`] impl |
//! | `ClassAction.Reversible`, `ClassAction.traversability_is_the_residual` | [`Passage::reverse_passage`] |
//! | `ClassAction.collapsing_merges_two_faces`, `ClassAction.collapsing_not_reversible` | the merged-faces receipt on the M5 binding passage |
//! | `passage_contract` | the whole B6 contract |

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use num_bigint::BigUint;
use serde::Serialize;
use thiserror::Error;

use super::{
    Coordinate, CoordinateName, CoordinateValue, Environment, EnvironmentDisagreement,
    EnvironmentPassage, EnvironmentRefusal, ObjectKinship, OccurrenceId, SituatedFamily,
};
use holonics::restriction::tower::{ReversePassageReceipt, Transition};
use crate::physical_constraint_complex::{ContactClass, DistanceAperture};
use crate::presentation_cost::{CostReceipt, Counted, code_bits};

// ---------------------------------------------------------------------------------------------
// The two axes
// ---------------------------------------------------------------------------------------------

/// The axis a passage moves along. There are exactly two and this trait is **sealed**: an exterior
/// crate cannot introduce a third axis, nor a coercion between the two that exist.
pub trait PassageAxis: sealed::Sealed + Clone + Copy + std::fmt::Debug + PartialEq + Eq {
    /// The axis's name, for receipts and refusals.
    const LABEL: &'static str;
}

mod sealed {
    /// Closes [`super::PassageAxis`] to the two axes this owner declares.
    pub trait Sealed {}
    impl Sealed for super::Vertical {}
    impl Sealed for super::Horizontal {}
}

/// **The vertical axis**: the environment moves and the object does not. Environment change,
/// binding and protonation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Vertical;

/// **The horizontal axis**: the object itself changes. Mutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Horizontal;

impl PassageAxis for Vertical {
    const LABEL: &'static str = "vertical: the environment moves around one object";
}

impl PassageAxis for Horizontal {
    const LABEL: &'static str = "horizontal: the object itself changes";
}

// ---------------------------------------------------------------------------------------------
// The event
// ---------------------------------------------------------------------------------------------

/// **The event `e` of `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})`.**
///
/// [definition] Each kind carries its own evidence, and its constructor checks that evidence
/// against the two environments rather than accepting the label. A binding that does not add its
/// partner to the oligomeric state is not a binding; a protonation that does not move the acidity
/// axis is not a protonation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum PassageEvent {
    /// The environment index changes and nothing else is claimed about the mechanism.
    EnvironmentChange {
        /// The typed environment passage, which already accounts for every divergent axis.
        environment: EnvironmentPassage,
    },
    /// A partner binds: the oligomeric state gains it, and the object acquires a component.
    Binding {
        /// The partner that bound.
        partner: String,
        /// How many copies of it the target carries beyond the source. Exact.
        added_copies: u32,
        /// The typed environment passage that carries the reading across.
        environment: EnvironmentPassage,
    },
    /// The protonation assumption changes with the pH enclosure it depends on.
    Protonation {
        /// The assumption the source was read under.
        from_assumption: String,
        /// The assumption the target is read under.
        to_assumption: String,
        /// The typed environment passage that carries the reading across.
        environment: EnvironmentPassage,
    },
    /// The object itself changes at one site. Horizontal.
    Mutation {
        /// The one-based ordinal of the changed monomer in the left component's sequence.
        site: u32,
        /// The monomer the source carried there.
        from_monomer: String,
        /// The monomer the target carries there.
        to_monomer: String,
    },
}

impl PassageEvent {
    /// The axis this event moves along.
    pub const fn axis_label(&self) -> &'static str {
        match self {
            Self::EnvironmentChange { .. } | Self::Binding { .. } | Self::Protonation { .. } => {
                Vertical::LABEL
            }
            Self::Mutation { .. } => Horizontal::LABEL,
        }
    }

    /// A short name for receipts.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::EnvironmentChange { .. } => "environment-change",
            Self::Binding { .. } => "binding",
            Self::Protonation { .. } => "protonation",
            Self::Mutation { .. } => "mutation",
        }
    }

    /// The typed environment passage a vertical event carries. `None` for a mutation, which is a
    /// move at one environment.
    pub const fn environment_passage(&self) -> Option<&EnvironmentPassage> {
        match self {
            Self::EnvironmentChange { environment }
            | Self::Binding { environment, .. }
            | Self::Protonation { environment, .. } => Some(environment),
            Self::Mutation { .. } => None,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The ends
// ---------------------------------------------------------------------------------------------

/// One end of a passage: which occurrence, where it sat and what it was a face of.
///
/// [definition] The joining end of a serial composition is retained as a value of this type, so
/// equal endpoints are checked as an equality of the whole record — identity, lineage, environment
/// and object — rather than inferred from a matching count or digest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PassageEnd {
    /// Which occurrence.
    pub occurrence: OccurrenceId,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The environment it was read at.
    pub environment: Environment,
    /// The object it was a face of.
    pub object: ObjectKinship,
    /// The receiver its classes were taken against.
    pub aperture: DistanceAperture,
}

impl PassageEnd {
    /// The end a situated family presents.
    pub fn of(family: &SituatedFamily) -> Self {
        Self {
            occurrence: family.occurrence,
            lineage: family.lineage.clone(),
            environment: family.environment.clone(),
            object: family.kinship(),
            aperture: family.aperture.clone(),
        }
    }
}

/// **The face a passage moves**: one occurrence's environment, object and class at every addressed
/// contact.
///
/// [definition] This is the `Source` and `Target` of the [`Transition`]. The exact squared-distance
/// intervals stay in the [`SituatedFamily`] they were read from; what a passage transports and
/// drops is the *classification*, which is what `K` is.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OccurrenceFace {
    /// Which occurrence.
    pub occurrence: OccurrenceId,
    /// Where it was read.
    pub environment: Environment,
    /// What it is a face of.
    pub object: ObjectKinship,
    /// The class at every addressed contact, in the family's own order.
    pub classes: Vec<((u32, u32), ContactClass)>,
}

impl OccurrenceFace {
    /// The face a situated family presents.
    pub fn of(family: &SituatedFamily) -> Self {
        Self {
            occurrence: family.occurrence,
            environment: family.environment.clone(),
            object: family.kinship(),
            classes: family
                .readings
                .iter()
                .map(|reading| (reading.pair, reading.class))
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The delta in K
// ---------------------------------------------------------------------------------------------

/// One addressed contact's class transition across a passage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct PairTransition {
    /// The addressed contact.
    pub pair: (u32, u32),
    /// What the source read.
    pub before: ContactClass,
    /// What the target reads.
    pub after: ContactClass,
}

impl PairTransition {
    /// Whether the class moved at all.
    pub fn changed(&self) -> bool {
        self.before != self.after
    }
}

/// **The exact typed delta in the constraint complex `K`.**
///
/// [definition] The complete per-contact transition, in the addressed order both families carry.
/// It is computed from the two complexes by [`ConstraintDelta::between`] and never declared. The
/// derived readings — [`ConstraintDelta::formed`], [`ConstraintDelta::broken`],
/// [`ConstraintDelta::opened`], [`ConstraintDelta::closed`] and the full
/// [`ConstraintDelta::census`] — are projections of it, so no reading can disagree with another.
///
/// `Deserialize` is not derived: a delta is computed from two faces, never remounted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConstraintDelta {
    /// The schema this delta serializes under.
    pub schema: String,
    transitions: Vec<PairTransition>,
}

impl ConstraintDelta {
    /// The schema stamp.
    pub const SCHEMA: &'static str = "holonic-engine.constraint-complex-delta.v1";

    /// **The exact delta between two faces**, computed from the two complexes.
    ///
    /// Refuses two families addressing different contact populations or the same population in a
    /// different order: without a common addressing there is no per-contact transition to state.
    pub fn between(
        source: &SituatedFamily,
        target: &SituatedFamily,
    ) -> Result<Self, PassageRefusal> {
        if source.readings.len() != target.readings.len() {
            return Err(PassageRefusal::PairPopulationDisagrees {
                left: source.occurrence,
                right: target.occurrence,
                left_pairs: source.readings.len(),
                right_pairs: target.readings.len(),
            });
        }
        let mut transitions = Vec::with_capacity(source.readings.len());
        for (a, b) in source.readings.iter().zip(&target.readings) {
            if a.pair != b.pair {
                return Err(PassageRefusal::PairOrderDisagrees {
                    left: source.occurrence,
                    right: target.occurrence,
                    left_pair: a.pair,
                    right_pair: b.pair,
                });
            }
            transitions.push(PairTransition {
                pair: a.pair,
                before: a.class,
                after: b.class,
            });
        }
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            transitions,
        })
    }

    /// The delta that moves nothing, at one face's addressing.
    ///
    /// Lean counterpart: `Delta.idOn`, with `Delta.idOn_comp` and `Delta.comp_idOn`.
    pub fn identity_on(face: &SituatedFamily) -> Self {
        Self {
            schema: Self::SCHEMA.to_owned(),
            transitions: face
                .readings
                .iter()
                .map(|reading| PairTransition {
                    pair: reading.pair,
                    before: reading.class,
                    after: reading.class,
                })
                .collect(),
        }
    }

    /// Every transition, in addressed order.
    pub fn transitions(&self) -> &[PairTransition] {
        &self.transitions
    }

    /// How many contacts the delta addresses.
    pub fn contacts(&self) -> usize {
        self.transitions.len()
    }

    /// Whether the delta addresses no contact at all.
    pub fn is_empty(&self) -> bool {
        self.transitions.is_empty()
    }

    /// Contacts the target reads formed that the source read excluded.
    pub fn formed(&self) -> Vec<(u32, u32)> {
        self.select(ContactClass::Outside, ContactClass::Inside)
    }

    /// Contacts the target reads excluded that the source read formed.
    pub fn broken(&self) -> Vec<(u32, u32)> {
        self.select(ContactClass::Inside, ContactClass::Outside)
    }

    /// Contacts the source decided and the target leaves open. The reading opened; nothing is
    /// resolved by a default.
    pub fn opened(&self) -> Vec<(u32, u32)> {
        self.transitions
            .iter()
            .filter(|transition| {
                transition.before != ContactClass::Open && transition.after == ContactClass::Open
            })
            .map(|transition| transition.pair)
            .collect()
    }

    /// Contacts the source left open and the target decides, with the class it closed to.
    pub fn closed(&self) -> Vec<((u32, u32), ContactClass)> {
        self.transitions
            .iter()
            .filter(|transition| {
                transition.before == ContactClass::Open && transition.after != ContactClass::Open
            })
            .map(|transition| (transition.pair, transition.after))
            .collect()
    }

    /// Contacts whose class did not move, by class.
    pub fn retained(&self, class: ContactClass) -> Vec<(u32, u32)> {
        self.select(class, class)
    }

    /// Every contact whose class moved.
    pub fn changed(&self) -> Vec<(u32, u32)> {
        self.transitions
            .iter()
            .filter(|transition| transition.changed())
            .map(|transition| transition.pair)
            .collect()
    }

    /// **The complete exact census**: the three-by-three table of class transitions, indexed by
    /// `ContactClass::wire()` before and after. Every addressed contact is counted exactly once.
    pub fn census(&self) -> [[usize; 3]; 3] {
        let mut table = [[0_usize; 3]; 3];
        for transition in &self.transitions {
            table[transition.before.wire() as usize][transition.after.wire() as usize] += 1;
        }
        table
    }

    fn select(&self, before: ContactClass, after: ContactClass) -> Vec<(u32, u32)> {
        self.transitions
            .iter()
            .filter(|transition| transition.before == before && transition.after == after)
            .map(|transition| transition.pair)
            .collect()
    }

    /// The source classes this delta records, as a face's own class list.
    pub fn before_classes(&self) -> Vec<((u32, u32), ContactClass)> {
        self.transitions
            .iter()
            .map(|transition| (transition.pair, transition.before))
            .collect()
    }

    /// The target classes this delta records.
    pub fn after_classes(&self) -> Vec<((u32, u32), ContactClass)> {
        self.transitions
            .iter()
            .map(|transition| (transition.pair, transition.after))
            .collect()
    }

    /// **Exact serial composition of deltas.**
    ///
    /// Refuses unless the second delta starts, contact by contact, where the first ends. The
    /// composite's transition at each contact is `(first.before, second.after)` — so composition is
    /// exact and associative, and a class that moves away and back collapses into a retention
    /// rather than being double counted.
    ///
    /// Lean counterpart: `Delta.comp`, `Delta.Composable` and `Delta.comp_assoc`.
    pub fn compose(&self, second: &Self) -> Result<Self, PassageRefusal> {
        if self.transitions.len() != second.transitions.len() {
            return Err(PassageRefusal::DeltaPopulationDisagrees {
                first: self.transitions.len(),
                second: second.transitions.len(),
            });
        }
        let mut transitions = Vec::with_capacity(self.transitions.len());
        for (a, b) in self.transitions.iter().zip(&second.transitions) {
            if a.pair != b.pair {
                return Err(PassageRefusal::PairOrderDisagrees {
                    left: OccurrenceId(0),
                    right: OccurrenceId(0),
                    left_pair: a.pair,
                    right_pair: b.pair,
                });
            }
            if a.after != b.before {
                return Err(PassageRefusal::DeltaEndpointsDisagree {
                    pair: a.pair,
                    first_ends_at: a.after,
                    second_starts_at: b.before,
                });
            }
            transitions.push(PairTransition {
                pair: a.pair,
                before: a.before,
                after: b.after,
            });
        }
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            transitions,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// The delta in Theta
// ---------------------------------------------------------------------------------------------

/// **The exact change in the environment coordinates `Theta`.**
///
/// [definition] The divergence is the complete one [`Environment::disagreement`] returns, so an
/// axis either side left undeclared is in it: a passage across two silences still names the
/// silence. [`EnvironmentDelta::retained`] is the complement — the axes certified to agree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnvironmentDelta {
    /// The schema this delta serializes under.
    pub schema: String,
    from: Environment,
    to: Environment,
    /// The complete divergence, in axis order.
    pub changed: EnvironmentDisagreement,
    /// The axes certified to agree on both sides.
    pub retained: Vec<CoordinateName>,
}

impl EnvironmentDelta {
    /// The exact delta between two environments.
    pub fn between(from: &Environment, to: &Environment) -> Self {
        let changed = from.disagreement(to);
        let names = changed.names();
        Self {
            schema: "holonic-engine.environment-coordinate-delta.v1".to_owned(),
            from: from.clone(),
            to: to.clone(),
            retained: CoordinateName::ALL
                .into_iter()
                .filter(|name| !names.contains(name))
                .collect(),
            changed,
        }
    }

    /// The environment it leaves.
    pub const fn from(&self) -> &Environment {
        &self.from
    }

    /// The environment it arrives at.
    pub const fn to(&self) -> &Environment {
        &self.to
    }

    /// The axes that moved.
    pub fn names(&self) -> BTreeSet<CoordinateName> {
        self.changed.names()
    }

    /// Exact serial composition: refuses unless the second delta leaves where the first arrives,
    /// and recomputes the composite divergence from the two endpoint environments rather than
    /// merging two divergence lists, which would double count an axis that moved and moved back.
    pub fn compose(&self, second: &Self) -> Result<Self, PassageRefusal> {
        if self.to != second.from {
            return Err(PassageRefusal::EnvironmentDeltaEndpointsDisagree {
                disagreement: Box::new(self.to.disagreement(&second.from)),
            });
        }
        Ok(Self::between(&self.from, &second.to))
    }
}

// ---------------------------------------------------------------------------------------------
// The residual
// ---------------------------------------------------------------------------------------------

/// **What a passage does not transport, retained whole.**
///
/// [definition] A passage carries a face to another occurrence at another environment. What it
/// drops is the source face itself: which occurrence it was, where it was read, what object it was
/// a face of, and its class at every addressed contact. [`Transition::reopen`] rebuilds exactly
/// that, so `reopen(apply(x), residual(x)) = x` is an equality and not a bound —
/// `Foundation/ContinuingTower.lean::Transition.reopen_apply` at this instance.
///
/// `Deserialize` is not derived: a residual is produced by [`Transition::residual`] and never
/// remounted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PassageResidual {
    /// The schema this residual serializes under.
    pub schema: String,
    /// Which occurrence the source was.
    pub occurrence: OccurrenceId,
    /// The environment it was read at.
    pub environment: Environment,
    /// The object it was a face of.
    pub object: ObjectKinship,
    /// Its class at every addressed contact.
    pub classes: Vec<((u32, u32), ContactClass)>,
}

impl PassageResidual {
    /// The residual a face leaves behind.
    pub fn of(face: &OccurrenceFace) -> Self {
        Self {
            schema: "holonic-engine.passage-residual.v1".to_owned(),
            occurrence: face.occurrence,
            environment: face.environment.clone(),
            object: face.object.clone(),
            classes: face.classes.clone(),
        }
    }

    /// The face it reopens.
    pub fn face(&self) -> OccurrenceFace {
        OccurrenceFace {
            occurrence: self.occurrence,
            environment: self.environment.clone(),
            object: self.object.clone(),
            classes: self.classes.clone(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// One step
// ---------------------------------------------------------------------------------------------

/// One elementary passage, with its two ends and its four receipts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PassageStep {
    /// The event.
    pub event: PassageEvent,
    /// The source occurrence.
    pub from: PassageEnd,
    /// The target occurrence.
    pub to: PassageEnd,
    /// What changed in `K`.
    pub constraint_delta: ConstraintDelta,
    /// What changed in `Theta`.
    pub environment_delta: EnvironmentDelta,
    /// What is needed to reopen the source.
    pub residual: PassageResidual,
    /// What the step cost.
    pub cost: CostReceipt,
}

/// **The declared ceiling on the addressed-contact population an exact class fibre is taken over.**
///
/// [definition] The residual axis of a step's receipt is the exact code size of the class word,
/// `code_bits(3^contacts)`, and `3^contacts` is a real integer that must be built. At this ceiling
/// it is a 1.6-megabit number, already larger than the presentation it costs; above it the receipt
/// would cost more than the passage it is a receipt for. A wider population is
/// [`PassageRefusal::ContactPopulationTooWideForAnExactCodeSize`], never a truncated exponent and
/// never a floating-point estimate of the code size.
pub const EXACT_CLASS_FIBRE_CEILING: usize = 1_000_000;

/// **Whether an addressed-contact population admits an exact class-fibre code size.**
///
/// [definition] The guard [`step_cost`] takes before it exponentiates, exposed so a caller can ask
/// before building the passage and so the refusal is testable without materializing a million
/// contacts. Every coordinate of the receipt it guards is measured off the delta or derived from
/// measured counts by a stated rule, so [`CostReceipt::is_accounted`] holds; the residual axis
/// counts the **class word** the passage retains — one of three classes at each addressed contact —
/// and does not code the source environment index or object identity, which the residual retains
/// whole beside it.
pub fn exact_class_fibre_admits(contacts: usize) -> Result<(), PassageRefusal> {
    exact_class_fibre_exponent(contacts).map(|_| ())
}

/// **The exponent an exact class fibre `3^contacts` is taken to, or a typed refusal.**
///
/// [definition] The same guard as [`exact_class_fibre_admits`], returning the exponent it
/// authorizes. Both the declared ceiling and the narrowing to the `u32` that `BigUint::pow` takes
/// are refusals here: an addressed-contact population that does not convert exactly is
/// [`PassageRefusal::ContactPopulationTooWideForAnExactCodeSize`] and is **never** narrowed to a
/// zero exponent, which would silently cost the passage as though it addressed no contact at all.
pub fn exact_class_fibre_exponent(contacts: usize) -> Result<u32, PassageRefusal> {
    let too_wide = || PassageRefusal::ContactPopulationTooWideForAnExactCodeSize {
        contacts,
        ceiling: EXACT_CLASS_FIBRE_CEILING,
    };
    if contacts > EXACT_CLASS_FIBRE_CEILING {
        return Err(too_wide());
    }
    u32::try_from(contacts).map_err(|_| too_wide())
}

/// The exact cost receipt of one step, derived from its own delta.
fn step_cost(
    event: &PassageEvent,
    delta: &ConstraintDelta,
) -> Result<CostReceipt, PassageRefusal> {
    let contacts = delta.contacts();
    // The guard returns the exponent it authorizes: the ceiling and the narrowing to `u32` are one
    // typed refusal, so no population can reach the exponentiation as a silent zero.
    let exponent = exact_class_fibre_exponent(contacts)?;
    let changed = delta.changed().len();
    let class_fibre = BigUint::from(3_u32).pow(exponent);
    let residual_bits = code_bits(&class_fibre);
    let bytes = (&residual_bits + BigUint::from(7_u32)) / BigUint::from(8_u32);
    Ok(CostReceipt {
        presentation: format!(
            "passage step {} over {contacts} addressed contacts; the residual axis codes the \
             source class word only, and the source environment index and object identity are \
             retained whole beside it",
            event.label()
        ),
        bytes: Counted::derived(
            bytes,
            "ceiling of the residual code size in bits divided by eight",
        ),
        decode_work: Counted::measured(
            BigUint::from(contacts),
            "one step per addressed contact to rebuild the target face from the source face and \
             the delta",
        ),
        update_work: Counted::measured(
            BigUint::from(changed),
            "the exact number of addressed contacts whose class the delta moves",
        ),
        certificate_work: Counted::derived(
            BigUint::from(contacts),
            "one comparison per addressed contact in Transition::check_reopen",
        ),
        residual: Counted::derived(
            residual_bits,
            "presentation_cost::code_bits of the exact class fibre 3^contacts",
        ),
    })
}

// ---------------------------------------------------------------------------------------------
// The passage
// ---------------------------------------------------------------------------------------------

/// **A passage: `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})` as a typed event carrying receipts.**
///
/// [definition] The axis `A` is [`Vertical`] or [`Horizontal`] and there is no coercion between
/// them. The step list is private, nonempty, and every step is on the axis the type names.
/// `Deserialize` is not derived: a passage is declared through one of the four constructors and
/// never remounted past their evidence checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Passage<A: PassageAxis> {
    /// The schema this passage serializes under.
    pub schema: String,
    steps: Vec<PassageStep>,
    axis: PhantomData<A>,
}

impl<A: PassageAxis> Passage<A> {
    /// The schema stamp.
    pub const SCHEMA: &'static str = "holonic-engine.physical-passage.v1";

    /// The steps, in order. A single elementary passage has one.
    pub fn steps(&self) -> &[PassageStep] {
        &self.steps
    }

    /// The source occurrence.
    pub fn from(&self) -> &PassageEnd {
        &self.steps[0].from
    }

    /// The target occurrence.
    pub fn to(&self) -> &PassageEnd {
        &self.steps[self.steps.len() - 1].to
    }

    /// **The joining occurrences a serial composition retained.** Empty for an elementary passage.
    ///
    /// [definition] AGENTS.md's addressed-span rule: equal endpoints do not preserve lineage by
    /// themselves, so the composite retains the occurrences it was joined at rather than reporting
    /// only its two ends.
    pub fn joining(&self) -> Vec<&PassageEnd> {
        self.steps[1..].iter().map(|step| &step.from).collect()
    }

    /// The axis this passage moves along.
    pub const fn axis_label(&self) -> &'static str {
        A::LABEL
    }

    /// **The composite delta in `K`**, an exact left fold over the step list.
    pub fn constraint_delta(&self) -> Result<ConstraintDelta, PassageRefusal> {
        let mut delta = self.steps[0].constraint_delta.clone();
        for step in &self.steps[1..] {
            delta = delta.compose(&step.constraint_delta)?;
        }
        Ok(delta)
    }

    /// **The composite delta in `Theta`**, an exact left fold over the step list.
    pub fn environment_delta(&self) -> Result<EnvironmentDelta, PassageRefusal> {
        let mut delta = self.steps[0].environment_delta.clone();
        for step in &self.steps[1..] {
            delta = delta.compose(&step.environment_delta)?;
        }
        Ok(delta)
    }

    /// **The composite cost**, the serial composition of the step receipts by
    /// [`CostReceipt::compose`], whose law is `ReceiverCodeCost.serial_boundary_balance`. It is a
    /// left fold over the one step list, so both bracketings of a composition produce the same
    /// receipt.
    pub fn cost(&self) -> CostReceipt {
        let mut cost = self.steps[0].cost.clone();
        for step in &self.steps[1..] {
            cost = cost.compose(&step.cost);
        }
        cost
    }

    /// The residual this passage retains, which reopens its source: the first step's own.
    ///
    /// [definition] Named apart from [`Transition::residual`], which is the residual **of a
    /// presented source** and is the law-carrying one. `ComposedTransition`'s residual is the
    /// *pair* of component residuals, which is an upper bound here because the first step already
    /// retains the whole source face. The receipt that this residual suffices is
    /// [`Transition::check_reopen`], run on the composite.
    pub fn retained_residual(&self) -> &PassageResidual {
        &self.steps[0].residual
    }

    /// The events, in order.
    pub fn events(&self) -> Vec<&PassageEvent> {
        self.steps.iter().map(|step| &step.event).collect()
    }

    /// **Serial composition, retaining the joining occurrence.**
    ///
    /// Refuses unless this passage's target end is equal *as a value* to the next passage's source
    /// end — occurrence identity, lineage, environment, object and aperture — and unless the two
    /// constraint deltas actually compose contact by contact.
    ///
    /// [proved-derived] Associative exactly: the step list is concatenated, and `Vec` concatenation
    /// is associative, so `(p ∘ q) ∘ r` and `p ∘ (q ∘ r)` are equal values.
    ///
    /// Lean counterpart: `TypedPassage.comp`, with `TypedPassage.comp_assoc`.
    pub fn then(&self, next: &Self) -> Result<Self, PassageRefusal> {
        if self.to() != next.from() {
            return Err(PassageRefusal::JoiningOccurrenceDiffers {
                left: Box::new(self.to().clone()),
                right: Box::new(next.from().clone()),
            });
        }
        // The composition of the deltas is checked here so that a composite whose deltas do not
        // meet is refused at composition rather than at the first reading of the composite.
        self.constraint_delta()?
            .compose(&next.constraint_delta()?)?;
        self.environment_delta()?
            .compose(&next.environment_delta()?)?;
        let mut steps = self.steps.clone();
        steps.extend(next.steps.iter().cloned());
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            steps,
            axis: PhantomData,
        })
    }

    /// **Whether the reverse passage exists from the transported face alone**, over a declared
    /// population of source faces.
    ///
    /// [proved-derived] It does not, in general: [`Transition::apply`] replaces the classes by the
    /// composite delta's target classes, so any two faces of this passage's source addressing are
    /// merged. The return is `continuing_tower`'s own
    /// [`ReversePassageReceipt`], and the `OnlyWithTheResidual` arm names the two merged faces.
    /// Cited law: `Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual`.
    pub fn reverse_passage(
        &self,
        faces: &[OccurrenceFace],
    ) -> ReversePassageReceipt<OccurrenceFace> {
        let transported: Vec<OccurrenceFace> = faces.iter().map(|face| self.apply(face)).collect();
        for (left, left_face) in transported.iter().enumerate() {
            for (right, right_face) in transported.iter().enumerate().skip(left + 1) {
                if left_face == right_face && faces[left] != faces[right] {
                    return ReversePassageReceipt::OnlyWithTheResidual {
                        merged_left: faces[left].clone(),
                        merged_right: faces[right].clone(),
                    };
                }
            }
        }
        ReversePassageReceipt::FromTheFaceAlone {
            faces_checked: faces.len(),
        }
    }
}

impl<A: PassageAxis> Transition for Passage<A> {
    type Source = OccurrenceFace;
    type Target = OccurrenceFace;
    type Residual = PassageResidual;

    fn apply(&self, source: &Self::Source) -> Self::Target {
        let target = self.to();
        let composite = self.constraint_delta();
        // [proved-derived] The `Err` arm below is unreachable on every value of this type, and the
        // fallback is kept only so that `apply` is total without a panic.
        //
        // The invariant: **every `Passage` value's step list composes contact by contact.** A
        // `Passage` is produced only by one of the four elementary constructors, which give it one
        // step, or by `Passage::then`. `constraint_delta` is the left fold of `ConstraintDelta::
        // compose` over that list, so on a one-step passage it never composes and cannot refuse.
        // `then` refuses unless `self.constraint_delta()?.compose(&next.constraint_delta()?)?`
        // succeeds; composition preserves the addressed pairs and carries `before` from its left
        // and `after` from its right, so that success says exactly that the last step of `self`
        // ends where the first step of `next` begins, at every addressed contact and in the same
        // order. By induction on `then` the whole concatenated list therefore composes, which is
        // the fold this line runs.
        debug_assert!(
            composite.is_ok(),
            "invariant: a Passage is founded one step at a time and composed only through \
             Passage::then, which refuses a join whose deltas do not meet"
        );
        let classes = composite.map_or_else(|_| source.classes.clone(), |delta| delta.after_classes());
        OccurrenceFace {
            occurrence: target.occurrence,
            environment: target.environment.clone(),
            object: target.object.clone(),
            classes,
        }
    }

    fn residual(&self, source: &Self::Source) -> Self::Residual {
        PassageResidual::of(source)
    }

    fn reopen(&self, _target: &Self::Target, residual: &Self::Residual) -> Self::Source {
        residual.face()
    }
}

// ---------------------------------------------------------------------------------------------
// The three vertical constructors
// ---------------------------------------------------------------------------------------------

impl Passage<Vertical> {
    /// **An environment change.** The environment index moves and the object does not.
    ///
    /// Refuses a supplied [`EnvironmentPassage`] that does not leave the source environment or does
    /// not arrive at the target's, and refuses a target that is a face of a different object.
    pub fn environment_change(
        source: &SituatedFamily,
        target: &SituatedFamily,
        environment: EnvironmentPassage,
    ) -> Result<Self, PassageRefusal> {
        check_vertical(source, target, &environment)?;
        found_step(
            PassageEvent::EnvironmentChange { environment },
            source,
            target,
        )
    }

    /// **A binding.** A partner enters the oligomeric state, so the object acquires a component.
    ///
    /// Refuses unless the oligomeric state is declared on both sides and the target really carries
    /// more copies of the named partner than the source does. The exact difference is retained as
    /// [`PassageEvent::Binding::added_copies`].
    pub fn binding(
        source: &SituatedFamily,
        target: &SituatedFamily,
        environment: EnvironmentPassage,
        partner: impl Into<String>,
    ) -> Result<Self, PassageRefusal> {
        check_vertical(source, target, &environment)?;
        let partner = partner.into();
        let before = oligomeric_copies(&source.environment, &partner)?;
        let after = oligomeric_copies(&target.environment, &partner)?;
        let Some(added_copies) = after.checked_sub(before).filter(|added| *added > 0) else {
            return Err(PassageRefusal::BindingDoesNotAddThePartner {
                partner,
                before,
                after,
            });
        };
        found_step(
            PassageEvent::Binding {
                partner,
                added_copies,
                environment,
            },
            source,
            target,
        )
    }

    /// **A protonation.** The acidity axis moves, with the assumption the reading depends on.
    ///
    /// Refuses unless the acidity axis is declared on both sides and actually differs. An axis
    /// undeclared on either side is not a protonation event: nothing states what changed.
    pub fn protonation(
        source: &SituatedFamily,
        target: &SituatedFamily,
        environment: EnvironmentPassage,
    ) -> Result<Self, PassageRefusal> {
        check_vertical(source, target, &environment)?;
        let before = declared_acidity(&source.environment)?;
        let after = declared_acidity(&target.environment)?;
        if before == after {
            return Err(PassageRefusal::ProtonationDoesNotMoveTheAcidity {
                assumption: before.1,
            });
        }
        found_step(
            PassageEvent::Protonation {
                from_assumption: before.1,
                to_assumption: after.1,
                environment,
            },
            source,
            target,
        )
    }
}

// ---------------------------------------------------------------------------------------------
// The horizontal constructor
// ---------------------------------------------------------------------------------------------

impl Passage<Horizontal> {
    /// **A mutation.** The object itself changes at one site, at one environment.
    ///
    /// Refuses a mutation that also moves the environment — that is two events and must be
    /// presented as two passages — a mutation that changes the target component, a mutation that
    /// changes more than the named site, a site whose monomers do not match the declaration, and a
    /// change of sequence length, which is an indel and not a substitution this owner types.
    pub fn mutation(
        source: &SituatedFamily,
        target: &SituatedFamily,
        site: u32,
    ) -> Result<Self, PassageRefusal> {
        if source.environment != target.environment {
            return Err(PassageRefusal::MutationAlsoMovesTheEnvironment {
                disagreement: Box::new(source.environment.disagreement(&target.environment)),
            });
        }
        let before = source.kinship();
        let after = target.kinship();
        if before.right_sequence != after.right_sequence {
            return Err(PassageRefusal::MutationChangesTheTarget);
        }
        if before.left_sequence.len() != after.left_sequence.len() {
            return Err(PassageRefusal::MutationChangesTheSequenceLength {
                before: before.left_sequence.len(),
                after: after.left_sequence.len(),
            });
        }
        let differing: Vec<u32> = before
            .left_sequence
            .iter()
            .zip(&after.left_sequence)
            .enumerate()
            .filter(|(_, (a, b))| a != b)
            .map(|(at, _)| at as u32 + 1)
            .collect();
        if differing != vec![site] {
            return Err(PassageRefusal::MutationDoesNotChangeExactlyTheSite {
                site,
                differing_at: differing,
            });
        }
        let at = site as usize - 1;
        found_step(
            PassageEvent::Mutation {
                site,
                from_monomer: before.left_sequence[at].clone(),
                to_monomer: after.left_sequence[at].clone(),
            },
            source,
            target,
        )
    }
}

// ---------------------------------------------------------------------------------------------
// The shared checks
// ---------------------------------------------------------------------------------------------

fn found_step<A: PassageAxis>(
    event: PassageEvent,
    source: &SituatedFamily,
    target: &SituatedFamily,
) -> Result<Passage<A>, PassageRefusal> {
    let constraint_delta = ConstraintDelta::between(source, target)?;
    let environment_delta = EnvironmentDelta::between(&source.environment, &target.environment);
    let cost = step_cost(&event, &constraint_delta)?;
    let step = PassageStep {
        event,
        from: PassageEnd::of(source),
        to: PassageEnd::of(target),
        residual: PassageResidual::of(&OccurrenceFace::of(source)),
        constraint_delta,
        environment_delta,
        cost,
    };
    Ok(Passage {
        schema: Passage::<A>::SCHEMA.to_owned(),
        steps: vec![step],
        axis: PhantomData,
    })
}

fn check_vertical(
    source: &SituatedFamily,
    target: &SituatedFamily,
    environment: &EnvironmentPassage,
) -> Result<(), PassageRefusal> {
    if source.kinship() != target.kinship() {
        return Err(PassageRefusal::ObjectChangedAlongTheVerticalAxis {
            left: source.occurrence,
            right: target.occurrence,
        });
    }
    if environment.from() != &source.environment {
        return Err(PassageRefusal::Environment(
            EnvironmentRefusal::PassageDoesNotLeaveThisEnvironment {
                disagreement: Box::new(environment.from().disagreement(&source.environment)),
            },
        ));
    }
    if environment.to() != &target.environment {
        return Err(PassageRefusal::Environment(
            EnvironmentRefusal::PassageDoesNotArriveAtThisEnvironment {
                disagreement: Box::new(environment.to().disagreement(&target.environment)),
            },
        ));
    }
    Ok(())
}

/// The exact declared copy count of one entity in an environment's oligomeric state.
fn oligomeric_copies(environment: &Environment, partner: &str) -> Result<u32, PassageRefusal> {
    let coordinate = environment.coordinate(CoordinateName::OligomericState)?;
    match coordinate {
        Coordinate::Declared {
            value: CoordinateValue::OligomericState(state),
            ..
        } => Ok(state.copies.get(partner).copied().unwrap_or(0)),
        Coordinate::Declared { .. } => Err(PassageRefusal::Environment(
            EnvironmentRefusal::CoordinateMisfiled {
                filed_under: CoordinateName::OligomericState,
                belongs_to: CoordinateName::OligomericState,
            },
        )),
        Coordinate::Undeclared { .. } => Err(PassageRefusal::AxisUndeclaredForThisEvent {
            name: CoordinateName::OligomericState,
            lineage: environment.lineage.clone(),
        }),
    }
}

/// The declared acidity of an environment, as its exact enclosure rendered for the receipt and its
/// protonation assumption.
fn declared_acidity(environment: &Environment) -> Result<(String, String), PassageRefusal> {
    let coordinate = environment.coordinate(CoordinateName::Acidity)?;
    match coordinate {
        Coordinate::Declared {
            value: CoordinateValue::Acidity(acidity),
            ..
        } => Ok((
            format!("{:?}", acidity.p_h),
            acidity.protonation_assumption.clone(),
        )),
        Coordinate::Declared { .. } => Err(PassageRefusal::Environment(
            EnvironmentRefusal::CoordinateMisfiled {
                filed_under: CoordinateName::Acidity,
                belongs_to: CoordinateName::Acidity,
            },
        )),
        Coordinate::Undeclared { .. } => Err(PassageRefusal::AxisUndeclaredForThisEvent {
            name: CoordinateName::Acidity,
            lineage: environment.lineage.clone(),
        }),
    }
}

/// The census of a delta as a readable table, for a receipt. Testimony, never an identity.
pub fn census_table(delta: &ConstraintDelta) -> BTreeMap<(&'static str, &'static str), usize> {
    let names = ["excluded", "formed", "open"];
    let census = delta.census();
    let mut table = BTreeMap::new();
    for (before, row) in census.iter().enumerate() {
        for (after, count) in row.iter().enumerate() {
            if *count > 0 {
                table.insert((names[before], names[after]), *count);
            }
        }
    }
    table
}

// ---------------------------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------------------------

/// Why a passage, a delta or a composition refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum PassageRefusal {
    /// A vertical passage was offered two faces of different objects.
    #[error(
        "occurrences {left:?} and {right:?} are faces of different objects; changing the object \
         is a horizontal move and is typed as Passage<Horizontal>, which this is not"
    )]
    ObjectChangedAlongTheVerticalAxis {
        /// The source occurrence.
        left: OccurrenceId,
        /// The target occurrence.
        right: OccurrenceId,
    },
    /// A mutation was offered two faces at different environments.
    #[error(
        "a mutation is a move at one environment, and these two environments diverge; a mutation \
         that also moves the environment is two events and is presented as two passages"
    )]
    MutationAlsoMovesTheEnvironment {
        /// The complete divergence.
        disagreement: Box<EnvironmentDisagreement>,
    },
    /// A mutation changed the target component.
    #[error("a mutation of the binder must leave the target component's sequence unchanged")]
    MutationChangesTheTarget,
    /// A mutation changed the sequence length.
    #[error(
        "the left sequence has {before} monomers before and {after} after; that is an indel, not \
         the substitution this owner types"
    )]
    MutationChangesTheSequenceLength {
        /// Before.
        before: usize,
        /// After.
        after: usize,
    },
    /// A mutation did not change exactly the declared site.
    #[error("the declared site is {site} but the sequences differ at {differing_at:?}")]
    MutationDoesNotChangeExactlyTheSite {
        /// The declared site.
        site: u32,
        /// Where they actually differ.
        differing_at: Vec<u32>,
    },
    /// A binding does not add its partner.
    #[error(
        "the declared partner {partner:?} is carried {before} times before and {after} times \
         after; a binding adds a partner and this does not"
    )]
    BindingDoesNotAddThePartner {
        /// The partner.
        partner: String,
        /// Copies before.
        before: u32,
        /// Copies after.
        after: u32,
    },
    /// A protonation does not move the acidity axis.
    #[error(
        "the acidity axis reads {assumption:?} on both sides; a protonation moves it and this does \
         not"
    )]
    ProtonationDoesNotMoveTheAcidity {
        /// The assumption both sides carry.
        assumption: String,
    },
    /// An event needs an axis the environment leaves undeclared.
    #[error(
        "this event is a claim about the {name} axis, which {lineage:?} explicitly leaves \
         undeclared; an undeclared axis cannot be the evidence for an event about it"
    )]
    AxisUndeclaredForThisEvent {
        /// The axis.
        name: CoordinateName,
        /// The environment's lineage.
        lineage: String,
    },
    /// Two faces address different numbers of contacts.
    #[error(
        "occurrences {left:?} and {right:?} address {left_pairs} and {right_pairs} contacts"
    )]
    PairPopulationDisagrees {
        /// The source occurrence.
        left: OccurrenceId,
        /// The target occurrence.
        right: OccurrenceId,
        /// How many the source addresses.
        left_pairs: usize,
        /// How many the target addresses.
        right_pairs: usize,
    },
    /// Two faces address the contacts in a different order.
    #[error(
        "occurrences {left:?} and {right:?} are not in the same contact order: {left_pair:?} \
         against {right_pair:?}"
    )]
    PairOrderDisagrees {
        /// The source occurrence.
        left: OccurrenceId,
        /// The target occurrence.
        right: OccurrenceId,
        /// The source's contact.
        left_pair: (u32, u32),
        /// The target's contact.
        right_pair: (u32, u32),
    },
    /// Two deltas address different numbers of contacts.
    #[error("the two deltas address {first} and {second} contacts and do not compose")]
    DeltaPopulationDisagrees {
        /// The first delta's contact count.
        first: usize,
        /// The second's.
        second: usize,
    },
    /// Two deltas do not meet at a contact.
    #[error(
        "at contact {pair:?} the first delta ends at {first_ends_at:?} and the second starts at \
         {second_starts_at:?}; they do not compose"
    )]
    DeltaEndpointsDisagree {
        /// The contact.
        pair: (u32, u32),
        /// Where the first ends.
        first_ends_at: ContactClass,
        /// Where the second starts.
        second_starts_at: ContactClass,
    },
    /// Two environment deltas do not meet.
    #[error("the first environment delta does not arrive where the second leaves")]
    EnvironmentDeltaEndpointsDisagree {
        /// The complete divergence.
        disagreement: Box<EnvironmentDisagreement>,
    },
    /// A serial composition's joining occurrence differs.
    #[error(
        "the joining occurrence differs: {left:?} against {right:?}. Equal endpoints do not \
         preserve lineage by themselves, so the joining occurrence is compared as a whole value"
    )]
    JoiningOccurrenceDiffers {
        /// The first passage's target end.
        left: Box<PassageEnd>,
        /// The second passage's source end.
        right: Box<PassageEnd>,
    },
    /// The addressed-contact population is wider than an exact class-fibre code size is taken over.
    #[error(
        "this passage addresses {contacts} contacts, above the declared ceiling {ceiling} for an \
         exact class-fibre code size; 3^contacts would be a larger number than the presentation it \
         costs. The receipt refuses rather than truncating the exponent or estimating in floating \
         point"
    )]
    ContactPopulationTooWideForAnExactCodeSize {
        /// How many contacts the passage addresses.
        contacts: usize,
        /// The declared ceiling.
        ceiling: usize,
    },
    /// The environment owner refused.
    #[error("the environment refused: {0}")]
    Environment(#[from] EnvironmentRefusal),
}

#[cfg(test)]
#[path = "passage/tests.rs"]
mod tests;
