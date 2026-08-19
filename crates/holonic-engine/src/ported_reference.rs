//! **SERIAL REFERENCE AND AUDIT MACHINERY — QUARANTINED FROM THE PRODUCTION CONE, 2026-08-18.**
//!
//! Everything in this module was lifted out of [`crate::ported_operation`] the day the adversarial
//! audit ([`research/records/2026-08-18_THE_SITE_RETURNED_BUT_THE_CARD_DID_NOT_OWN_THE_PATH_AND_PHOENIX_REMAINS_A_PARTIAL_LIFT.md`])
//! found that a module whose header said *"this is a bridge, not an engine; it owns no
//! arithmetic"* had grown a twelve-variant transformer-shaped operation enum and a host `enact`
//! loop that ran normalization, chronology, GELU, contact, gating and residual semantics on one
//! CPU core around CUDA contraction leaves. That is the shape the Phoenix master plan names as the
//! defect it exists to prevent — *CUDA leaf products around CPU-owned semantics are not a resident
//! pathway* — and the correction directive of the same day rules that
//! [`PortedOperationKind`] **must not remain the production instruction set** and that
//! [`PortedCarrier`] host closures **must not execute production semantics**.
//!
//! So this is what it now is and nothing more: **a serial reference realization**, lawful only as
//! admission/parity testimony beside a resident deed, exactly as `AGENTS.md` places CPU code —
//! *"CPU implementations remain admission audits only."* It may be driven by an audit driver; it may
//! not be reached from any production or frozen-inference dependency cone. The resident owner
//! carries a source-scan gate asserting that it is not.
//!
//! What it retains is unchanged in mechanism from the day it was written, defects included, because
//! a reference that was silently repaired would no longer be the thing the audit graded: the
//! contact's interval division is still the one the audit convicted for negative numerators, the
//! roots are still isolated at `ROOT_OCTAVES = 44` and the rotations rounded at
//! `ROTATION_OCTAVES = 40`, and every local width is still *exhibited, not propagated*. The resident
//! owner repairs each of those on the card, and the difference between the two is measurable.
//!
//! The generic half — typed ports, transport words, lift defect, front formation, species,
//! closure and candidate testimony — stays in [`crate::ported_operation`] and is what the
//! production cone composes.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::causal::EventId;
use crate::evolution::EvolutionLawId;
use crate::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use crate::exact_work::ExactWork;
use crate::interaction::OccurrencePort;
use crate::ported_operation::{Front, OperationSpecies, PortedError, PortedOperationComplex};


// ---------------------------------------------------------------------------------------------
// THE REALIZATION: a BINDING of occurrences to exact operations, ordered by the diagram itself
// ---------------------------------------------------------------------------------------------
//
// This follows `realization::ReceiverProgram` exactly, because that is the standing pattern for
// enacting an `EvolutionShape` and there is no second one. A program **binds**; it does not
// schedule. Every ordering question is answered by `CausalDiagram::layers` and every dataflow
// question by the shape's own interaction bonds, so a source-specific semantic scheduler cannot
// arise here — there is nowhere to put one.
//
// `ReceiverProgram::validate` checks that every occurrence has an operation, that the operation's
// arity matches its law's, that one law carries one species, that every input is carried by an
// interaction, and that causal placement holds. [`PortedProgram::validate`] checks the same five
// things and one more that matters here: **the operation's species must equal the species the
// operation was bound with in the complex.** A face-species operation on a transport-species law
// refuses.

/// One exact operation a ported occurrence may be bound to.
///
/// Each names the owner that carries it. **None of them is implemented here** — the realization
/// calls the standing owner, and where an apparatus is needed it calls the declared
/// [`PortedCarrier`] rather than reaching for one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PortedOperationKind {
    /// An index selects a construction from a declared population. Species: construction.
    Lookup { population: String, row: usize },
    /// A linear map, carried by the declared apparatus. Species: transport.
    Contract { population: String },
    /// `gain * x / sqrt(mean(x^2) + floor)`, the root isolated by
    /// `exact_value::AlgebraicRoot::reciprocal_square_root`. Species: transport.
    RebaseByGain {
        population: String,
        floor: Rat,
        /// **A declared candidate, not a default.** Some rested maps store the gain and some store
        /// an offset whose law reads `1 + g`. The material does not decide it; a receiver
        /// separation does, and this field is what makes a matched sibling possible.
        gain_carries_unit: bool,
    },
    /// Re-entry of a retained standing. Species: construction.
    ReEntry,
    /// Pointwise product of two standings. Species: construction.
    Hadamard,
    /// A pointwise constitutive law through
    /// `exact_value::CertifiedSeries::hyperbolic_tangent_enclosure`. Species: transport.
    GatedPassage {
        terms: usize,
        /// **The inner argument the source's `hidden_activation` declares.**
        ///
        /// `None` is `x` itself, which makes the passage `x·sigmoid(2x)` — the form this operation
        /// carried before the source was consulted, retained so a diagram that used it is still
        /// readable. `Some((scale, cubic))` is `scale·(x + cubic·x³)`, which with the surrounding
        /// `½x(1 + tanh(·))` is `gelu_pytorch_tanh`.
        ///
        /// Both constants are **exact rationals read through the IEEE-754 mouth from the `binary64`
        /// words the source's implementation computes with**, so this is
        /// `SourceTestimony::Implementation` rather than an approximation of one. The source does
        /// not compute `sqrt(2/pi)`; it computes with one particular stored word, and that word is
        /// exactly representable here.
        inner: Option<(Rat, Rat)>,
    },
    /// A declared quotient onto the stored grain, through `exact_value::ieee754::round_into`.
    /// Species: quotient.
    GrainBoundary,
    /// **A targeted ablation: a declared span of coordinates is withdrawn and retained.**
    ///
    /// This is the intervention a dissection and a condensation are made of. It differs from
    /// [`Self::Project`] in what it emits — a projection narrows the port, an ablation keeps the
    /// port's width and empties a declared span — so a matched sibling differs from its base in
    /// exactly this one relation and nothing downstream changes shape.
    ///
    /// What it withdrew is its **retained fibre**, exhibited at its own occurrence. Species:
    /// quotient.
    Ablate { from: usize, count: usize },
    /// **A projection onto a declared span of coordinates.** A head slice is a quotient by the
    /// tablet's own reading — it collapses the complementary coordinates — so it owes them, and
    /// what it dropped is exactly its retained fibre. Species: quotient.
    Project { from: usize, count: usize },
    /// A discrete group action indexed by an integer position, through
    /// `exact_value::{AlgebraicRoot::nth_root, CertifiedSeries::rotation_power}`. The
    /// transcendental runs once per band and a position is an integer power, so the chronology's
    /// exact carrier is the integer. Species: transport.
    Chronology {
        /// **The band ladder, founded once when the program is bound.**
        ///
        /// This carried the base and re-founded the ladder per occurrence until 2026-08-18, which
        /// put a Sturm isolation of a degree-`bands` polynomial inside the hot path — twenty of them
        /// per position, each a Sturm sequence over a degree-128 polynomial with rational
        /// coefficients. A ladder is **standing material of the site**, not something an occurrence
        /// recomputes. The same held for the band's **group element**: founding its series per
        /// occurrence cost two hundred and fifty milliseconds an occurrence, twenty per position,
        /// for a value that does not change. `R(p a) = R(a)^p` — the element is the site's and the
        /// integer is the position's.
        /// **Named, not carried.** The band elements are standing material of the site, so the
        /// program NAMES them and the carrier supplies them. Carrying them inline made every
        /// chronology occurrence repeat five hundred and twelve exact rationals, which is material
        /// living in program text — and a native rest would have sealed it once per occurrence.
        rotations: String,
        position: u64,
        /// **A declared candidate.** A rotation needs two coordinates and a chart of width `d`
        /// offers two pairings: the two halves, or adjacent entries. They are different group
        /// actions on one chart and the container does not say which.
        pairs_halves: bool,
    },
    /// **The reconvergence of a front: parts assembled into one standing, in bond order.**
    ///
    /// Variadic — the law's arity is the number of parts — because a front's breadth is the
    /// diagram's, not a number written here. Species: construction.
    Concatenate,
    /// **The bracket and the carried construction, over a reach the DIAGRAM declares.**
    ///
    /// Variadic: the law's own arity is `1 + 2n` — one receiver chart, then `n` presented
    /// orientations and `n` carried constructions — and the reach comes from the bonds rather than
    /// from a number here. The faces go through `exact_contact`, the family through
    /// `exact_value::CertifiedSeries::exponential_enclosure`, and the result is bounded by the
    /// population's own hull because a convex combination lies inside it. Species: construction.
    ContactAndCarry { terms: usize, scale_width: usize },
}

impl PortedOperationKind {
    /// The species this operation **is**. A program binding it to a law of another species refuses.
    pub fn species(&self) -> OperationSpecies {
        match self {
            Self::Lookup { .. }
            | Self::ReEntry
            | Self::Hadamard
            | Self::ContactAndCarry { .. }
            | Self::Concatenate => OperationSpecies::Construction,
            Self::Contract { .. }
            | Self::RebaseByGain { .. }
            | Self::GatedPassage { .. }
            | Self::Chronology { .. } => OperationSpecies::Transport,
            Self::GrainBoundary | Self::Project { .. } | Self::Ablate { .. } => {
                OperationSpecies::Quotient
            }
        }
    }

    /// The arity this operation admits, or `None` where **the law's own arity is the arity**.
    ///
    /// A contact's reach is declared by the diagram's bonds, not by a number written here, so the
    /// variadic case defers to the law rather than fixing one.
    fn admitted_arity(&self) -> Option<(usize, usize)> {
        Some(match self {
            Self::Lookup { .. } => (0, 1),
            Self::Contract { .. }
            | Self::RebaseByGain { .. }
            | Self::GatedPassage { .. }
            | Self::Chronology { .. }
            | Self::Project { .. }
            | Self::Ablate { .. }
            | Self::GrainBoundary => (1, 1),
            Self::ReEntry | Self::Hadamard => (2, 1),
            Self::ContactAndCarry { .. } | Self::Concatenate => return None,
        })
    }

    /// The arity a law must declare for this operation, given that law's own input count.
    fn arity_against(&self, law_inputs: usize, law_outputs: usize) -> bool {
        match self.admitted_arity() {
            Some((inputs, outputs)) => law_inputs == inputs && law_outputs == outputs,
            None => match self {
                // One receiver chart, then a reach of presented/carried pairs.
                Self::ContactAndCarry { .. } => {
                    law_outputs == 1 && law_inputs >= 3 && law_inputs % 2 == 1
                }
                _ => law_outputs == 1 && law_inputs >= 1,
            },
        }
    }

    fn inputs_of(&self, law_inputs: usize) -> usize {
        match self.admitted_arity() {
            Some((inputs, _)) => inputs,
            None => law_inputs,
        }
    }
}

/// The apparatus a realization is handed, so the bridge owns none.
///
/// **This is the seam §12.4 draws.** A contraction belongs on the strongest lawful resident
/// surface; reading a stored population belongs to the source mouth. Neither belongs to a diagram,
/// and a realization that reached for either would be an apparatus owner rather than a bridge.
pub trait PortedCarrier {
    /// Contract a standing through a declared stored population, exactly.
    fn contract(&mut self, population: &str, standing: &[Rat]) -> Result<Vec<Rat>, String>;
    /// A declared stored population's own exact values.
    fn stored(&mut self, population: &str) -> Result<Vec<Rat>, String>;
    /// One row of a declared stored population, exactly.
    fn stored_row(&mut self, population: &str, row: usize) -> Result<Vec<Rat>, String>;
    /// The declared quotient onto the stored grain: the carried value and its **exact** residual.
    fn grain(&mut self, standing: &[Rat]) -> Result<(Vec<Rat>, Vec<Rat>), String>;
    /// A declared population of band group elements. **Material, not program text**: a chronology
    /// names its ladder and the apparatus supplies it, so a native rest seals it once.
    fn rotations(
        &mut self,
        population: &str,
    ) -> Result<Vec<(ExactInterval, ExactInterval)>, String>;
}

/// An executable assignment from every occurrence in one ported complex to one exact operation.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortedProgram {
    pub operations: BTreeMap<EventId, PortedOperationKind>,
}

impl PortedProgram {
    pub fn bind(
        &mut self,
        occurrence: EventId,
        operation: PortedOperationKind,
    ) -> Option<PortedOperationKind> {
        self.operations.insert(occurrence, operation)
    }

    /// **Six checks, five of them `ReceiverProgram`'s own and the sixth this bridge's.**
    pub fn validate(&self, complex: &PortedOperationComplex) -> Result<(), PortedError> {
        complex.shape.validate()?;
        for event in complex.shape.occurrences.keys() {
            if !self.operations.contains_key(event) {
                return Err(PortedError::OccurrenceUnbound { occurrence: *event });
            }
        }
        for event in self.operations.keys() {
            if !complex.shape.occurrences.contains_key(event) {
                return Err(PortedError::ForeignOccurrence { occurrence: *event });
            }
        }
        let mut law_species: BTreeMap<EvolutionLawId, OperationSpecies> = BTreeMap::new();
        for (event, operation) in &self.operations {
            let occurrence = &complex.shape.occurrences[event];
            let law = &complex.shape.laws[&occurrence.law];
            if !operation.arity_against(law.inputs.len(), law.outputs.len()) {
                let (inputs, outputs) = operation.admitted_arity().unwrap_or((0, 1));
                return Err(PortedError::ArityDisagrees {
                    occurrence: *event,
                    law_inputs: law.inputs.len(),
                    law_outputs: law.outputs.len(),
                    admitted_inputs: inputs,
                    admitted_outputs: outputs,
                });
            }
            // **The sixth check.** The bound species and the operation's species must agree.
            let declared = complex
                .operations
                .get(&occurrence.law)
                .map(|bound| bound.species)
                .ok_or(PortedError::OccurrenceUnbound { occurrence: *event })?;
            if declared != operation.species() {
                return Err(PortedError::SpeciesDisagrees {
                    occurrence: *event,
                    declared,
                    operation: operation.species(),
                });
            }
            if let Some(existing) = law_species.insert(occurrence.law, operation.species()) {
                if existing != operation.species() {
                    return Err(PortedError::OneLawManySpecies { law: occurrence.law });
                }
            }
        }
        // Every input a law declares must be carried to by an interaction bond, except where the
        // operation admits none. An uncarried input is a dataflow the diagram does not state.
        let targets: BTreeSet<OccurrencePort> = complex
            .shape
            .interactions
            .values()
            .flat_map(|interaction| &interaction.bonds)
            .map(|bond| bond.target)
            .collect();
        for (event, operation) in &self.operations {
            let occurrence = &complex.shape.occurrences[event];
            let inputs = operation.inputs_of(complex.shape.laws[&occurrence.law].inputs.len());
            for input in 0..inputs {
                if !targets.contains(&OccurrencePort::input(*event, input)) {
                    return Err(PortedError::InputUncarried {
                        occurrence: *event,
                        input,
                    });
                }
            }
        }
        Ok(())
    }
}

/// What one realization returned, with its retained fibre and its exact work.
#[derive(Clone, Debug)]
pub struct PortedRealizationReceipt {
    /// The standing at every occurrence port the diagram wrote, retained rather than summarized.
    pub carried: BTreeMap<OccurrencePort, Vec<Rat>>,
    /// The co-present fronts, in the order the chronology gave them.
    pub fronts: Vec<Front>,
    /// Every grain boundary's exact residual, by occurrence. **Exhibited, never propagated.**
    pub retained: BTreeMap<EventId, Vec<Rat>>,
    pub work: ExactWork,
}

impl PortedRealizationReceipt {
    /// **The retained fibre as a POPULATION**, which is what it is.
    ///
    /// Returns how many entries were retained, how many of those were retained whole, and the
    /// widest single residual with the occurrence that made it. It does **not** sum them: a sum of
    /// exact rationals drawn from different frames has an unbounded denominator and is a magnitude
    /// across a horizon besides, which crosses nothing.
    pub fn retained_population(&self) -> (usize, usize, Option<(EventId, Rat)>) {
        let mut entries = 0usize;
        let mut nonzero = 0usize;
        let mut widest: Option<(EventId, Rat)> = None;
        for (occurrence, residuals) in &self.retained {
            for residual in residuals {
                entries += 1;
                let magnitude = if residual.is_negative() {
                    -residual.clone()
                } else {
                    residual.clone()
                };
                if magnitude.is_zero() {
                    continue;
                }
                nonzero += 1;
                if widest.as_ref().map(|(_, held)| magnitude > *held).unwrap_or(true) {
                    widest = Some((*occurrence, magnitude));
                }
            }
        }
        (entries, nonzero, widest)
    }

    pub fn ports_written(&self) -> usize {
        self.carried.len()
    }
}

/// **Realize a bound complex: the diagram decides the order and the bonds decide the dataflow.**
///
/// The only loop here is over `CausalDiagram::layers`, and within a layer the occurrences are
/// co-present — the front. Nothing in this function knows what a foreign map is.
/// **A hand on a front — a gauge, not a schedule.**
///
/// `CausalDiagram::layers()` decides which occurrences are co-present; nothing here can change that.
/// A hand only chooses how a front the diagram *already declared co-present* is traversed, so it
/// states no order the diagram did not force. Co-presence is exactly the claim that this choice is
/// invisible, and `CLAUDE.md` §8 requires a gauge to exhibit its own orbit rather than assert one —
/// `PivotRule::ALL` was built to prevent a defect and became the defect because nobody measured its
/// orbit on the declared material.
///
/// [`FrontHand::DraggedAcross`] is the control that makes the other three non-vacuous. It moves an
/// occurrence **between** fronts, which is an order the diagram refused, and the realization must
/// refuse it back.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FrontHand {
    /// The hand `layers()` founded. The diagram's own.
    AsFounded,
    /// Every front traversed against its founding hand.
    Reversed,
    /// Every front rotated by one. A second, independent element of the same gauge.
    Rotated,
    /// **THE CONTROL.** One occurrence is dragged into the front of a producer it actually depends
    /// on, so its input is unwritten when it runs.
    ///
    /// The first form of this dragged the front's *first* occurrence into its predecessor by
    /// position, and it changed nothing — `layers()` is a topological layering, so an occurrence
    /// whose inputs all come from strictly earlier fronts is still lawful one layer up. **A control
    /// that does not produce the illegal state it is testing for is not a control.** This one is
    /// built from the bond map, which is why it needs the complex.
    DraggedOntoItsProducer,
}

impl FrontHand {
    /// Apply the hand. Only [`FrontHand::DraggedAcross`] changes front *membership*; the others
    /// permute within a front and leave the chronology exactly where the diagram put it.
    pub fn applied(self, fronts: Vec<Front>) -> Vec<Front> {
        match self {
            Self::AsFounded => fronts,
            Self::Reversed => fronts
                .into_iter()
                .map(|front| Front {
                    depth: front.depth,
                    occurrences: front.occurrences.into_iter().rev().collect(),
                })
                .collect(),
            Self::Rotated => fronts
                .into_iter()
                .map(|front| {
                    let mut occurrences = front.occurrences;
                    if occurrences.len() > 1 {
                        occurrences.rotate_left(1);
                    }
                    Front {
                        depth: front.depth,
                        occurrences,
                    }
                })
                .collect(),
            // Without the complex this hand cannot find a producer, so it is the identity and
            // says so. `applied_to` is the form that can build it.
            Self::DraggedOntoItsProducer => fronts,
        }
    }

    /// [`FrontHand::applied`], with the complex available so [`FrontHand::DraggedOntoItsProducer`]
    /// can read the bond map.
    ///
    /// Returns the handed fronts beside **what it actually disturbed** — the occurrence it moved and
    /// the producer it was moved onto — so the control's own premise is exhibited rather than
    /// assumed. `None` there means the hand found no such pair and the control did not fire.
    pub fn applied_to(
        self,
        complex: &PortedOperationComplex,
        fronts: Vec<Front>,
    ) -> (Vec<Front>, Option<(EventId, EventId)>) {
        let Self::DraggedOntoItsProducer = self else {
            return (self.applied(fronts), None);
        };
        let mut producing: BTreeMap<EventId, EventId> = BTreeMap::new();
        for interaction in complex.shape.interactions.values() {
            for bond in &interaction.bonds {
                producing.insert(bond.target.event, bond.source.event);
            }
        }
        let mut depth_of: BTreeMap<EventId, usize> = BTreeMap::new();
        for front in &fronts {
            for occurrence in &front.occurrences {
                depth_of.insert(*occurrence, front.depth);
            }
        }
        // The first consumer whose producer sits in a strictly earlier front. Moving it into the
        // producer's front puts it beside the thing it needs rather than after it.
        let disturbed = fronts.iter().find_map(|front| {
            front.occurrences.iter().find_map(|consumer| {
                let producer = producing.get(consumer)?;
                let producer_depth = *depth_of.get(producer)?;
                (producer_depth < front.depth).then_some((*consumer, *producer, producer_depth))
            })
        });
        let Some((consumer, producer, producer_depth)) = disturbed else {
            return (fronts, None);
        };
        let handed = fronts
            .into_iter()
            .map(|front| {
                let mut occurrences: Vec<EventId> = front
                    .occurrences
                    .into_iter()
                    .filter(|occurrence| *occurrence != consumer)
                    .collect();
                if front.depth == producer_depth {
                    // **FIRST, not last.** Appending it after the producer leaves a legal order —
                    // measured, and the control returned no refusal until this line said `insert`.
                    // The illegal state being tested for is a consumer running BEFORE its producer.
                    occurrences.insert(0, consumer);
                }
                Front {
                    depth: front.depth,
                    occurrences,
                }
            })
            .collect();
        (handed, Some((consumer, producer)))
    }
}

/// [`realize`] under a declared front hand. See [`FrontHand`] for why this is a gauge rather than a
/// schedule.
pub fn realize_under(
    complex: &PortedOperationComplex,
    program: &PortedProgram,
    carrier: &mut dyn PortedCarrier,
    entering: &BTreeMap<OccurrencePort, Vec<Rat>>,
    hand: FrontHand,
) -> Result<PortedRealizationReceipt, PortedError> {
    realize_handed(complex, program, carrier, entering, hand)
}

pub fn realize(
    complex: &PortedOperationComplex,
    program: &PortedProgram,
    carrier: &mut dyn PortedCarrier,
    entering: &BTreeMap<OccurrencePort, Vec<Rat>>,
) -> Result<PortedRealizationReceipt, PortedError> {
    realize_handed(complex, program, carrier, entering, FrontHand::AsFounded)
}

fn realize_handed(
    complex: &PortedOperationComplex,
    program: &PortedProgram,
    carrier: &mut dyn PortedCarrier,
    entering: &BTreeMap<OccurrencePort, Vec<Rat>>,
    hand: FrontHand,
) -> Result<PortedRealizationReceipt, PortedError> {
    program.validate(complex)?;
    complex.witness.validate(&complex.shape)?;

    let mut carried: BTreeMap<OccurrencePort, Vec<Rat>> = entering.clone();
    let mut retained: BTreeMap<EventId, Vec<Rat>> = BTreeMap::new();
    let mut work = ExactWork::nothing();
    let (fronts, _) = hand.applied_to(complex, complex.fronts()?);

    // Every bond, indexed by the port it carries **to**. This is the diagram's dataflow.
    let mut arriving: BTreeMap<OccurrencePort, OccurrencePort> = BTreeMap::new();
    for interaction in complex.shape.interactions.values() {
        for bond in &interaction.bonds {
            arriving.insert(bond.target, bond.source);
        }
    }

    for front in &fronts {
        // **ONE STEP PER FRONT, not per operation.** `ExactWork::dependency_span` is documented as
        // *the longest chain of steps that must happen in order*, and a front's members do not
        // happen in order — that is what a front is. Stepping inside `enact` counted 174 for a
        // layer whose span is 23, which is exactly the contraction-count-versus-dependency-span
        // confusion the corpus names. `exact_linear` and `inertia` step once per genuine pivot and
        // were already correct.
        work.stepped();
        for occurrence in &front.occurrences {
            let operation = &program.operations[occurrence];
            let law = &complex.shape.laws[&complex.shape.occurrences[occurrence].law];
            let inputs = operation.inputs_of(law.inputs.len());
            let mut admitted: Vec<Vec<Rat>> = Vec::with_capacity(inputs);
            for input in 0..inputs {
                let port = OccurrencePort::input(*occurrence, input);
                let source = arriving
                    .get(&port)
                    .copied()
                    .ok_or(PortedError::InputUncarried {
                        occurrence: *occurrence,
                        input,
                    })?;
                admitted.push(
                    carried
                        .get(&source)
                        .cloned()
                        .ok_or(PortedError::StandingAbsent { port: source })?,
                );
            }
            let clock = std::time::Instant::now();
            let emitted = enact(operation, &admitted, carrier, &mut work, occurrence, &mut retained)?;
            if std::env::var("PORTED_TRACE").is_ok() {
                eprintln!(
                    "    {:?} {:?} in {:?} -> {} entries",
                    occurrence,
                    operation_name(operation),
                    clock.elapsed(),
                    emitted.len()
                );
            }
            carried.insert(OccurrencePort::output(*occurrence, 0), emitted);
        }
    }

    Ok(PortedRealizationReceipt {
        carried,
        fronts,
        retained,
        work,
    })
}

fn operation_name(operation: &PortedOperationKind) -> &'static str {
    match operation {
        PortedOperationKind::Lookup { .. } => "lookup",
        PortedOperationKind::Contract { .. } => "contract",
        PortedOperationKind::RebaseByGain { .. } => "rebase",
        PortedOperationKind::ReEntry => "re-entry",
        PortedOperationKind::Hadamard => "hadamard",
        PortedOperationKind::GatedPassage { .. } => "gated passage",
        PortedOperationKind::GrainBoundary => "grain",
        PortedOperationKind::Project { .. } => "project",
        PortedOperationKind::Ablate { .. } => "ablate",
        PortedOperationKind::Chronology { .. } => "chronology",
        PortedOperationKind::ContactAndCarry { .. } => "contact",
        PortedOperationKind::Concatenate => "concatenate",
    }
}

fn enact(
    operation: &PortedOperationKind,
    admitted: &[Vec<Rat>],
    carrier: &mut dyn PortedCarrier,
    work: &mut ExactWork,
    occurrence: &EventId,
    retained: &mut BTreeMap<EventId, Vec<Rat>>,
) -> Result<Vec<Rat>, PortedError> {
    let apparatus = |reason: String| PortedError::Apparatus { reason };
    Ok(match operation {
        PortedOperationKind::Lookup { population, row } => {
            carrier.stored_row(population, *row).map_err(apparatus)?
        }
        PortedOperationKind::Contract { population } => {
            carrier
                .contract(population, &admitted[0])
                .map_err(apparatus)?
        }
        PortedOperationKind::RebaseByGain {
            population,
            floor,
            gain_carries_unit,
        } => {
            let gain = carrier.stored(population).map_err(apparatus)?;
            let section = &admitted[0];
            if section.len() != gain.len() {
                return Err(PortedError::WidthDisagrees {
                    left: section.len(),
                    right: gain.len(),
                });
            }
            let width = Rat::from_integer(BigInt::from(section.len() as u64));
            let mut squares = Rat::zero();
            for value in section {
                squares += value * value;
                work.multiplied(1);
                work.added(1);
            }
            let mean = squares / width + floor;
            let root = AlgebraicRoot::reciprocal_square_root(&mean, ROOT_OCTAVES)
                .map_err(|error| PortedError::Value { reason: format!("{error:?}") })?;
            let enclosure = root.enclosure();
            let two = Rat::from_integer(BigInt::from(2));
            let mut out = Vec::with_capacity(section.len());
            let mut widths = Vec::with_capacity(section.len());
            let unit = if *gain_carries_unit {
                Rat::one()
            } else {
                Rat::zero()
            };
            for (value, gain) in section.iter().zip(&gain) {
                let scaled = value * (gain + &unit);
                let low = &enclosure.lower * &scaled;
                let high = &enclosure.upper * &scaled;
                let (below, above) = if low <= high { (low, high) } else { (high, low) };
                out.push((&below + &above) / &two);
                widths.push((&above - &below) / &two);
                work.multiplied(2);
            }
            // The root's own width is what this operation could not carry: exhibited, not propagated.
            retained.entry(*occurrence).or_default().extend(widths);
            out
        }
        PortedOperationKind::ReEntry => {
            if admitted[0].len() != admitted[1].len() {
                return Err(PortedError::WidthDisagrees {
                    left: admitted[0].len(),
                    right: admitted[1].len(),
                });
            }
            admitted[0]
                .iter()
                .zip(&admitted[1])
                .map(|(retained_path, returned_path)| {
                    work.added(1);
                    retained_path + returned_path
                })
                .collect()
        }
        PortedOperationKind::Hadamard => {
            if admitted[0].len() != admitted[1].len() {
                return Err(PortedError::WidthDisagrees {
                    left: admitted[0].len(),
                    right: admitted[1].len(),
                });
            }
            admitted[0]
                .iter()
                .zip(&admitted[1])
                .map(|(left, right)| {
                    work.multiplied(1);
                    left * right
                })
                .collect()
        }
        PortedOperationKind::GatedPassage { terms, inner } => {
            let one = Rat::one();
            let two = Rat::from_integer(BigInt::from(2));
            let mut out = Vec::with_capacity(admitted[0].len());
            let mut widths = Vec::with_capacity(admitted[0].len());
            for value in &admitted[0] {
                // The turn's argument. `x` itself, or the declared cubic the source names.
                let argument = match inner {
                    None => value.clone(),
                    Some((scale, cubic)) => {
                        work.multiplied(4);
                        work.added(1);
                        scale * (value + cubic * value * value * value)
                    }
                };
                let turned = CertifiedSeries::hyperbolic_tangent_enclosure(&argument, *terms)
                    .map_err(|error| PortedError::Value { reason: format!("{error:?}") })?;
                let low = (&turned.lower + &one) * value / &two;
                let high = (&turned.upper + &one) * value / &two;
                let (below, above) = if low <= high { (low, high) } else { (high, low) };
                out.push((&below + &above) / &two);
                widths.push((&above - &below) / &two);
                work.multiplied(3);
                work.added(2);
            }
            retained.entry(*occurrence).or_default().extend(widths);
            out
        }
        PortedOperationKind::Chronology {
            rotations,
            position,
            pairs_halves,
        } => {
            let section = &admitted[0];
            let bands = section.len() / 2;
            let elements = carrier
                .rotations(rotations)
                .map_err(|reason| PortedError::Apparatus { reason })?;
            if bands == 0 || elements.len() < bands {
                return Err(PortedError::WidthDisagrees {
                    left: section.len(),
                    right: 2 * elements.len(),
                });
            }
            let two = Rat::from_integer(BigInt::from(2));
            let mut out = section.clone();
            let mut widths = vec![Rat::zero(); section.len()];
            for band in 0..bands {
                // The band's group element is the site's; a position is its integer power.
                let (cosine, sine) = compose_rotation(&elements[band], *position)
                    .map_err(|error| PortedError::Value { reason: format!("{error:?}") })?;
                let (first, second) = if *pairs_halves {
                    (band, band + bands)
                } else {
                    (2 * band, 2 * band + 1)
                };
                let x = section[first].clone();
                let y = section[second].clone();
                let real = interval_scaled(&cosine, &x);
                let cross = interval_scaled(&sine, &y);
                let left = interval_scaled(&sine, &x);
                let right = interval_scaled(&cosine, &y);
                out[first] = ((&real.0 - &cross.1) + (&real.1 - &cross.0)) / &two;
                out[second] = ((&left.0 + &right.0) + (&left.1 + &right.1)) / &two;
                widths[first] = ((&real.1 - &cross.0) - (&real.0 - &cross.1)) / &two;
                widths[second] = ((&left.1 + &right.1) - (&left.0 + &right.0)) / &two;
                work.multiplied(4);
                work.added(2);
            }
            retained.entry(*occurrence).or_default().extend(widths);
            out
        }
        PortedOperationKind::ContactAndCarry { terms, scale_width } => {
            let reach = (admitted.len() - 1) / 2;
            let query = &admitted[0];
            let presented = &admitted[1..1 + reach];
            let constructions = &admitted[1 + reach..];
            let scale = AlgebraicRoot::reciprocal_square_root(
                &Rat::from_integer(BigInt::from(*scale_width as u64)),
                ROOT_OCTAVES,
            )
            .map_err(|error| PortedError::Value { reason: format!("{error:?}") })?;
            let two = Rat::from_integer(BigInt::from(2));
            let scale_point =
                (&scale.enclosure().lower + &scale.enclosure().upper) / &two;
            // The faces, exactly, and the population's own hand retained beside each.
            let mut faces = Vec::with_capacity(reach);
            for orientation in presented {
                let mut face = Rat::zero();
                for (a, b) in query.iter().zip(orientation.iter()) {
                    face += a * b;
                    work.multiplied(1);
                    work.added(1);
                }
                faces.push(face * &scale_point);
            }
            // The declared null enters no ratio; it is the gauge, made visible.
            let null = faces.iter().max().cloned().unwrap_or_else(Rat::zero);
            let mut weights = Vec::with_capacity(reach);
            for face in &faces {
                weights.push(
                    CertifiedSeries::exponential_enclosure(&(face - &null), *terms).map_err(
                        |error| PortedError::Value {
                            reason: format!("{error:?}"),
                        },
                    )?,
                );
            }
            let dimension = constructions.first().map(Vec::len).unwrap_or(0);
            let mut out = Vec::with_capacity(dimension);
            let mut widths = Vec::with_capacity(dimension);
            for coordinate in 0..dimension {
                let mut low = Rat::zero();
                let mut high = Rat::zero();
                let mut total_low = Rat::zero();
                let mut total_high = Rat::zero();
                let mut lowest: Option<Rat> = None;
                let mut highest: Option<Rat> = None;
                for (weight, construction) in weights.iter().zip(constructions) {
                    let value = &construction[coordinate];
                    let (a, b) = interval_scaled(weight, value);
                    low += a;
                    high += b;
                    total_low += &weight.lower;
                    total_high += &weight.upper;
                    lowest = Some(match lowest {
                        Some(held) if held <= *value => held,
                        _ => value.clone(),
                    });
                    highest = Some(match highest {
                        Some(held) if held >= *value => held,
                        _ => value.clone(),
                    });
                }
                // **A convex combination lies inside its population's hull.** Interval arithmetic
                // drops that dependency exactly as a product drops it in a square, so the law is
                // applied here and the quotient is clamped to the hull it cannot leave.
                let quotient_low = &low / &total_high;
                let quotient_high = &high / &total_low;
                let floor = lowest.unwrap_or_else(Rat::zero);
                let ceiling = highest.unwrap_or_else(Rat::zero);
                let below = quotient_low.max(floor.clone());
                let above = quotient_high.min(ceiling);
                let (below, above) = if below <= above {
                    (below, above)
                } else {
                    (floor.clone(), floor)
                };
                out.push((&below + &above) / &two);
                widths.push((&above - &below) / &two);
            }
            retained.entry(*occurrence).or_default().extend(widths);
            out
        }
        PortedOperationKind::Concatenate => {
            admitted.iter().flat_map(|part| part.iter().cloned()).collect()
        }
        PortedOperationKind::Ablate { from, count } => {
            let section = &admitted[0];
            let upper = (from + count).min(section.len());
            let mut out = section.clone();
            let mut withdrawn = Vec::with_capacity(upper.saturating_sub(*from));
            for at in *from..upper {
                withdrawn.push(section[at].clone());
                out[at] = Rat::zero();
            }
            // **What an ablation withdrew is its retained fibre.** Nothing is discarded, so the
            // predecessor is reconstructible from the return and the fibre together.
            retained.entry(*occurrence).or_default().extend(withdrawn);
            out
        }
        PortedOperationKind::Project { from, count } => {
            let section = &admitted[0];
            if from + count > section.len() {
                return Err(PortedError::WidthDisagrees {
                    left: from + count,
                    right: section.len(),
                });
            }
            // **What a projection drops is its retained fibre**, exhibited rather than discarded.
            let dropped: Vec<Rat> = section[..*from]
                .iter()
                .chain(&section[from + count..])
                .cloned()
                .collect();
            retained.entry(*occurrence).or_default().extend(dropped);
            section[*from..from + count].to_vec()
        }
        PortedOperationKind::GrainBoundary => {
            let (carried, residual) = carrier.grain(&admitted[0]).map_err(apparatus)?;
            retained.entry(*occurrence).or_default().extend(residual);
            carried
        }
    })
}

/// `R(a)^p` by repeated composition of one enclosed group element. The transcendental was
/// evaluated when the element was founded; a position spends only multiplication.
fn compose_rotation(
    step: &(ExactInterval, ExactInterval),
    power: u64,
) -> Result<(ExactInterval, ExactInterval), crate::exact_value::ExactValueError> {
    let mut carried = (
        ExactInterval::point(Rat::one()),
        ExactInterval::point(Rat::zero()),
    );
    for _ in 0..power {
        let real = carried.0.times(&step.0)?;
        let cross = carried.1.times(&step.1)?;
        let left = carried.0.times(&step.1)?;
        let right = carried.1.times(&step.0)?;
        carried = (
            ExactInterval::new(&real.lower - &cross.upper, &real.upper - &cross.lower)?
                .round_out(ROTATION_OCTAVES)?,
            ExactInterval::new(&left.lower + &right.lower, &left.upper + &right.upper)?
                .round_out(ROTATION_OCTAVES)?,
        );
    }
    Ok(carried)
}

/// The dyadic places a composed rotation is held at, so a long chronology cannot grow its
/// denominators without bound.
const ROTATION_OCTAVES: u32 = 40;

fn interval_scaled(interval: &crate::exact_value::ExactInterval, factor: &Rat) -> (Rat, Rat) {
    let a = &interval.lower * factor;
    let b = &interval.upper * factor;
    if a <= b { (a, b) } else { (b, a) }
}

/// The dyadic places a root is isolated to. **Read from the carrier, not chosen for a result**: an
/// `i64` significand holds sixty-three octaves and a rebase composes two of them, so forty-four
/// leaves the product inside the exact word this workspace's aligned material uses.
const ROOT_OCTAVES: u32 = 44;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ported_operation::SourceTestimony;

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    /// A carrier that returns declared material, so the realization is exercised and no apparatus
    /// is reached for.
    struct DeclaredCarrier {
        stored: BTreeMap<String, Vec<Rat>>,
    }

    impl PortedCarrier for DeclaredCarrier {
        fn contract(&mut self, population: &str, standing: &[Rat]) -> Result<Vec<Rat>, String> {
            let map = self
                .stored
                .get(population)
                .ok_or_else(|| format!("no population named {population}"))?;
            // A declared square map, row-major.
            let width = standing.len();
            Ok((0..map.len() / width)
                .map(|row| {
                    map[row * width..(row + 1) * width]
                        .iter()
                        .zip(standing)
                        .fold(Rat::from_integer(BigInt::from(0)), |sum, (a, b)| sum + a * b)
                })
                .collect())
        }
        fn stored(&mut self, population: &str) -> Result<Vec<Rat>, String> {
            self.stored
                .get(population)
                .cloned()
                .ok_or_else(|| format!("no population named {population}"))
        }
        fn stored_row(&mut self, population: &str, _row: usize) -> Result<Vec<Rat>, String> {
            self.stored(population)
        }
        fn rotations(
            &mut self,
            _population: &str,
        ) -> Result<Vec<(ExactInterval, ExactInterval)>, String> {
            Ok(Vec::new())
        }
        fn grain(&mut self, standing: &[Rat]) -> Result<(Vec<Rat>, Vec<Rat>), String> {
            let mut carried = Vec::with_capacity(standing.len());
            let mut residual = Vec::with_capacity(standing.len());
            for value in standing {
                let whole = Rat::from_integer(value.to_integer());
                residual.push(value - &whole);
                carried.push(whole);
            }
            Ok((carried, residual))
        }
    }

    /// **The species check refuses a program that binds the wrong kind of operation to a law.**
    ///
    /// This is the sixth check and it is the bridge's own: a law bound as a face cannot be enacted
    /// by a transport, however well the arities line up.
    #[test]
    fn a_program_binding_the_wrong_species_to_a_law_refuses() {
        let mut complex = PortedOperationComplex::new("species check");
        let port = complex.port("standing");
        let law = complex
            .bind_operation(
                "a face",
                OperationSpecies::Face,
                vec![port],
                vec![port],
                None,
                vec![SourceTestimony::Undecided {
                    question: "declared for this test".to_owned(),
                }],
            )
            .expect("bound");
        let event = complex.occur(law).expect("occurs");
        let mut program = PortedProgram::default();
        program.bind(
            event,
            PortedOperationKind::Contract {
                population: "w".to_owned(),
            },
        );
        assert!(matches!(
            program.validate(&complex),
            Err(PortedError::SpeciesDisagrees {
                declared: OperationSpecies::Face,
                operation: OperationSpecies::Transport,
                ..
            })
        ));
    }

    /// An unbound occurrence, a disagreeing arity and an uncarried input each refuse by name.
    #[test]
    fn the_program_refuses_an_unbound_occurrence_a_wrong_arity_and_an_uncarried_input() {
        let mut complex = PortedOperationComplex::new("validation");
        let port = complex.port("standing");
        let construction = complex
            .bind_operation(
                "a construction",
                OperationSpecies::Construction,
                vec![],
                vec![port],
                Some("w".to_owned()),
                vec![SourceTestimony::DeclaredShape {
                    population: "w".to_owned(),
                    shape: vec![2],
                }],
            )
            .expect("bound");
        let entering = complex.occur(construction).expect("occurs");

        // Nothing bound at all.
        let empty = PortedProgram::default();
        assert!(matches!(
            empty.validate(&complex),
            Err(PortedError::OccurrenceUnbound { .. })
        ));

        // A two-input operation on a zero-input law.
        let mut wrong = PortedProgram::default();
        wrong.bind(entering, PortedOperationKind::ReEntry);
        assert!(matches!(
            wrong.validate(&complex),
            Err(PortedError::SpeciesDisagrees { .. } | PortedError::ArityDisagrees { .. })
        ));

        // A transport whose input no interaction carries to.
        let transport = complex
            .bind_operation(
                "a transport",
                OperationSpecies::Transport,
                vec![port],
                vec![port],
                Some("w".to_owned()),
                vec![SourceTestimony::DeclaredShape {
                    population: "w".to_owned(),
                    shape: vec![2, 2],
                }],
            )
            .expect("bound");
        let carried = complex.occur(transport).expect("occurs");
        let mut uncarried = PortedProgram::default();
        uncarried.bind(
            entering,
            PortedOperationKind::Lookup {
                population: "w".to_owned(),
                row: 0,
            },
        );
        uncarried.bind(
            carried,
            PortedOperationKind::Contract {
                population: "w".to_owned(),
            },
        );
        assert!(matches!(
            uncarried.validate(&complex),
            Err(PortedError::InputUncarried { input: 0, .. })
        ));
    }

    /// **The diagram decides the order and the bonds decide the dataflow.**
    ///
    /// Two co-present transports read the same predecessor's output and land in one front. No
    /// ordering appears anywhere in this test or in `realize`; both come from the chronology.
    #[test]
    fn the_chronology_orders_the_realization_and_the_bonds_carry_it() {
        let mut complex = PortedOperationComplex::new("realization");
        let port = complex.port("standing");
        let entering_law = complex
            .bind_operation(
                "entering construction",
                OperationSpecies::Construction,
                vec![],
                vec![port],
                Some("entering".to_owned()),
                vec![SourceTestimony::DeclaredShape {
                    population: "entering".to_owned(),
                    shape: vec![2],
                }],
            )
            .expect("bound");
        let entering = complex.occur(entering_law).expect("occurs");

        let mut branches = Vec::new();
        for name in ["left branch", "right branch"] {
            let law = complex
                .bind_operation(
                    name,
                    OperationSpecies::Transport,
                    vec![port],
                    vec![port],
                    Some("map".to_owned()),
                    vec![SourceTestimony::DeclaredShape {
                        population: "map".to_owned(),
                        shape: vec![2, 2],
                    }],
                )
                .expect("bound");
            let event = complex.occur(law).expect("occurs");
            complex
                .carries_precedence(
                    format!("{name} follows the entering construction"),
                    port,
                    OccurrencePort::output(entering, 0),
                    OccurrencePort::input(event, 0),
                )
                .expect("joined");
            branches.push(event);
        }
        // The reconvergence: both branches meet.
        let join_law = complex
            .bind_operation(
                "reconvergence",
                OperationSpecies::Construction,
                vec![port, port],
                vec![port],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "two paths meet".to_owned(),
                }],
            )
            .expect("bound");
        let join = complex.occur(join_law).expect("occurs");
        for (input, branch) in branches.iter().enumerate() {
            complex
                .carries_precedence(
                    format!("the reconvergence admits branch {input}"),
                    port,
                    OccurrencePort::output(*branch, 0),
                    OccurrencePort::input(join, input),
                )
                .expect("joined");
        }

        let mut program = PortedProgram::default();
        program.bind(
            entering,
            PortedOperationKind::Lookup {
                population: "entering".to_owned(),
                row: 0,
            },
        );
        for branch in &branches {
            program.bind(
                *branch,
                PortedOperationKind::Contract {
                    population: "map".to_owned(),
                },
            );
        }
        program.bind(join, PortedOperationKind::ReEntry);
        program.validate(&complex).expect("valid");

        let mut carrier = DeclaredCarrier {
            stored: BTreeMap::from([
                (
                    "entering".to_owned(),
                    vec![rat(3), rat(-1)],
                ),
                (
                    // A doubling map, so a branch's output is checkable by hand.
                    "map".to_owned(),
                    vec![rat(2), rat(0), rat(0), rat(2)],
                ),
            ]),
        };
        let receipt =
            realize(&complex, &program, &mut carrier, &BTreeMap::new()).expect("realized");

        // The chronology returned three fronts, and the middle one carries BOTH branches.
        assert_eq!(receipt.fronts.len(), 3);
        assert_eq!(receipt.fronts[0].breadth(), 1);
        assert_eq!(receipt.fronts[1].breadth(), 2, "the branches are co-present");
        assert_eq!(receipt.fronts[2].breadth(), 1);

        // Each branch doubled the entering construction, and the reconvergence summed them.
        for branch in &branches {
            assert_eq!(
                receipt.carried[&OccurrencePort::output(*branch, 0)],
                vec![rat(6), rat(-2)]
            );
        }
        assert_eq!(
            receipt.carried[&OccurrencePort::output(join, 0)],
            vec![rat(12), rat(-4)],
            "the reconvergence admitted both paths, not one"
        );
        // **Three, not four.** This diagram has four operations over three fronts, and the
        // assertion three lines above says the middle two are CO-PRESENT. Asserting a span of four
        // contradicted it: it counted two co-present operations as two serial steps. The assertion
        // was carrying the defect, which is the shape `CLAUDE.md` records for the eleven tests that
        // asserted `ComparativeMultiplicity`'s.
        assert_eq!(receipt.fronts.len(), 3);
        assert!(receipt.work.coordinates().iter().any(|(name, count)| *name
            == "dependency-span"
            && *count == num_bigint::BigUint::from(3u32)));
    }

    /// **A grain boundary's residual is retained per occurrence and exhibited**, never propagated.
    #[test]
    fn a_grain_boundary_retains_its_residual_at_its_own_occurrence() {
        let mut complex = PortedOperationComplex::new("grain");
        let port = complex.port("standing");
        let entering_law = complex
            .bind_operation(
                "entering",
                OperationSpecies::Construction,
                vec![],
                vec![port],
                Some("entering".to_owned()),
                vec![SourceTestimony::DeclaredShape {
                    population: "entering".to_owned(),
                    shape: vec![2],
                }],
            )
            .expect("bound");
        let entering = complex.occur(entering_law).expect("occurs");
        let grain_law = complex
            .bind_operation(
                "the declared grain",
                OperationSpecies::Quotient,
                vec![port],
                vec![port],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "a declared quotient onto the stored grain".to_owned(),
                }],
            )
            .expect("bound");
        let grain = complex.occur(grain_law).expect("occurs");
        complex
            .carries_precedence(
                "the grain admits the entering construction",
                port,
                OccurrencePort::output(entering, 0),
                OccurrencePort::input(grain, 0),
            )
            .expect("joined");

        let mut program = PortedProgram::default();
        program.bind(
            entering,
            PortedOperationKind::Lookup {
                population: "entering".to_owned(),
                row: 0,
            },
        );
        program.bind(grain, PortedOperationKind::GrainBoundary);
        program.validate(&complex).expect("valid");

        let mut carrier = DeclaredCarrier {
            stored: BTreeMap::from([(
                "entering".to_owned(),
                vec![Rat::new(BigInt::from(7), BigInt::from(2)), rat(-4)],
            )]),
        };
        let receipt =
            realize(&complex, &program, &mut carrier, &BTreeMap::new()).expect("realized");
        assert_eq!(
            receipt.carried[&OccurrencePort::output(grain, 0)],
            vec![rat(3), rat(-4)]
        );
        // value = carried + residual, exactly, and the residual is at the occurrence that made it.
        let residual = &receipt.retained[&grain];
        assert_eq!(residual[0], Rat::new(BigInt::from(1), BigInt::from(2)));
        assert!(residual[1].is_zero());
        let (entries, nonzero, widest) = receipt.retained_population();
        assert_eq!(entries, 2);
        assert_eq!(nonzero, 1);
        assert_eq!(
            widest.map(|(_, value)| value),
            Some(Rat::new(BigInt::from(1), BigInt::from(2)))
        );
    }

}
