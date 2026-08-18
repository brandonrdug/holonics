//! **A foreign operator diagram, ported into the standing operation complex.**
//!
//! Plan: [`blueprint/THE_PHOENIX_REBIRTH_LIFTS_INHERITED_HEXIS_AND_RETURNS_A_NATIVE_EXECUTABLE_ECOLOGY.md`],
//! first instance [`blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`].
//! Derivation and disposition:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §§4, 6, 12.
//!
//! # What this is, and the one thing it is not
//!
//! This is a **bridge**, not an engine. It owns no arithmetic: every exact operation belongs to
//! [`crate::exact_linear`], every typed boundary and composable path to [`crate::category`], every
//! chronology and front to [`crate::causal`], every law and interaction to [`crate::evolution`],
//! every abstract-to-exact binding to [`crate::realization`], and every behavioural quotient to
//! [`crate::receiver_exact_compression`]. What was missing was narrower than any of them:
//!
//! > Bind a foreign operator diagram, with typed ports and occurrence lineage, into the standing
//! > computational holon; retain its transport words, certify its fronts, and return
//! > inverse/adjoint/quotient testimony at the correct operation species.
//!
//! The audit that occasioned it records what happens otherwise: a transformer-shaped arithmetic
//! cabinet was built beside these owners and its whole architecture had to be withdrawn.
//!
//! # A product matrix is a compiled chart, not the object
//!
//! For a composable word `w = gamma_n ... gamma_1`, the written product `rho(w) = M_n ... M_1` is
//! **one chart realization of ordered composition**. The word, its ports, its intermediate
//! occurrences and its open exterior are the construction. [`PortedWord`] therefore retains the
//! word and compiles a total product only for a receiver that asks for that face — the rule
//! `tube::ReceiverTube` already follows with its `presentation_word`.
//!
//! **Two words with one compiled chart remain distinct** until a declared receiver proves the
//! quotient lawful. [`PortedWord::applied_receiver`] is what makes that checkable: an applied-state
//! receiver separates `AB` from `BA` for noncommuting `A` and `B`, and a chart comparison does not.
//!
//! # Fronts are not serial chains
//!
//! Q/K/V are co-present branches of one predecessor; gate and up are co-present branches of
//! another. [`Front`] reads them off [`crate::causal::CausalDiagram::layers`] rather than counting
//! contractions, because **contraction count is not dependency span** and the apparatus consequence
//! follows the second.
//!
//! # Nothing here selects a representative
//!
//! A singular or rectangular ported transport returns kernel, image, cokernel and an affine
//! preimage fibre. A rebase returns **both** identity compositions or refuses. An adjoint requires
//! declared domain and codomain metrics. All three are [`crate::exact_linear`]'s returns; this
//! module only carries the ports, the lineage and the species alongside them.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::causal::EventId;
use crate::category::BoundaryId;
use crate::evolution::{EvolutionError, EvolutionLawId, EvolutionShape};
use crate::exact_linear::{ExactLinearError, ExactRatMatrix, LinearFactorization, RebaseReceipt};
use crate::exact_work::ExactWork;
use crate::interaction::{InteractionBond, InteractionPattern, InteractionTemporality, OccurrencePort};
use crate::realization::{RealizationError, RealizationWitness};

/// The four operation species of `canon/TABLET_THE_OPERATIONS.md`. **Every ported operation is
/// exactly one of them**, and the tablet's own readings are quoted in each variant because the
/// species decides what return is owed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OperationSpecies {
    /// A ket: something is brought into standing. A stored table's lookup, a residual re-entry.
    Construction,
    /// A chart-presented map carrying one standing to another. **Only a transport may be a
    /// rebase**, and only with both identity compositions.
    Transport,
    /// A bracket: a receiver reads a construction and returns a scalar or an ordering. A contact,
    /// a norm, a probability. **A face is not machinery** and may not be manipulated as one.
    Face,
    /// A collapse by a declared family. Owes its collapsed population and its reopening rule.
    Quotient,
}

impl OperationSpecies {
    pub fn name(self) -> &'static str {
        match self {
            Self::Construction => "construction",
            Self::Transport => "transport",
            Self::Face => "face",
            Self::Quotient => "quotient",
        }
    }

    /// Whether this species may be asked for an inverse at all.
    ///
    /// `TABLET_THE_OPERATIONS`: an inverse exists only for a rebase, and a rebase is a transport.
    /// Asking a face or a quotient for one is a typed error rather than a numerical failure.
    pub fn admits_inverse(self) -> bool {
        matches!(self, Self::Transport)
    }
}

/// What decided a binding, retained so a later reader checks rather than inherits.
///
/// **`Undecided` is a first-class return.** Where the source's own testimony does not settle a
/// binding, the candidate population is retained by [`CandidateDiagrams`] and no plausible reading
/// is promoted. `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_...md` §12 requires
/// exactly that: *"If unavailable, return the complete candidate-diagram fibre."*
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceTestimony {
    /// A field of the source's own declared configuration.
    Configuration { field: String, value: String },
    /// A declared population's shape, which constrains the ports it can carry.
    DeclaredShape { population: String, shape: Vec<usize> },
    /// A statement from the source's authoritative description of itself.
    AuthoritativeDescription { statement: String },
    /// The source's executable implementation, where it is available.
    Implementation { locator: String, symbol: String },
    /// **Nothing in the admitted testimony decides this.**
    Undecided { question: String },
}

impl SourceTestimony {
    pub fn decides(&self) -> bool {
        !matches!(self, Self::Undecided { .. })
    }
}

/// A population of candidate diagrams the admitted testimony could not separate.
///
/// This is the **retained fibre** for an undecided binding. It carries every candidate, the
/// question they answer differently, and the testimony that would reopen it — so a later station
/// can settle it by *acquiring evidence* rather than by choosing.
///
/// **Human inspection of plausible output cannot collapse this.** A collapse is lawful only through
/// a declared receiver family and a separating successor history, which is
/// [`crate::receiver_exact_compression`]'s deed and not this module's. When the bridge is lifted
/// into `soma/life`, this population is what `reconstruction_fiber` receives.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateDiagrams {
    pub question: String,
    /// Every candidate, named. Never one with the others summarized away.
    pub candidates: Vec<String>,
    /// What would decide it, stated so it can be sought rather than guessed.
    pub would_be_decided_by: Vec<String>,
}

impl CandidateDiagrams {
    pub fn is_open(&self) -> bool {
        self.candidates.len() > 1
    }
}

/// One foreign operator occurrence, bound into the standing shape.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortedOperation {
    pub law: EvolutionLawId,
    pub species: OperationSpecies,
    /// The source population realizing it, where one does. A face or a construction may have none.
    pub carrier: Option<String>,
    /// Every piece of testimony bearing on this binding, kept whole.
    pub testimony: Vec<SourceTestimony>,
}

impl PortedOperation {
    pub fn is_decided(&self) -> bool {
        self.testimony.iter().any(SourceTestimony::decides)
    }
}

/// **A chart-presented transport with typed ports and chart lineage.**
///
/// The ports are [`BoundaryId`]s of the shape's own [`crate::category::CategoryPresentation`], so
/// port identity is **nominal, not structural**: two boundaries of equal extent are different
/// objects and composition across them refuses. That refusal is the first falsifier of §13.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortedTransport {
    pub name: String,
    pub source_port: BoundaryId,
    pub target_port: BoundaryId,
    /// Which chart the matrix is written in, retained because a matrix without its chart is a
    /// coordinate array and not a transport.
    pub chart: String,
    pub matrix: ExactRatMatrix,
}

impl PortedTransport {
    pub fn new(
        name: impl Into<String>,
        source_port: BoundaryId,
        target_port: BoundaryId,
        chart: impl Into<String>,
        matrix: ExactRatMatrix,
    ) -> Self {
        Self {
            name: name.into(),
            source_port,
            target_port,
            chart: chart.into(),
            matrix,
        }
    }

    /// Carry one standing across. Refuses on extent, and the port check happens in the word.
    pub fn apply(&self, standing: &[Rat]) -> Result<Vec<Rat>, PortedError> {
        Ok(self.matrix.apply(standing)?)
    }

    /// The complete factorization: kernel, image, open exterior, rank, and what it cost.
    pub fn factorization(&self) -> Result<LinearFactorization, PortedError> {
        Ok(self.matrix.factorization()?)
    }

    /// **Is this a rebase?** Both identity compositions or a refusal carrying the factorization.
    pub fn rebase_receipt(&self) -> Result<RebaseReceipt, PortedError> {
        Ok(self.matrix.rebase_receipt()?)
    }

    /// The metric adjoint, with both receiver metrics declared. Never a bare transpose.
    pub fn metric_adjoint(
        &self,
        domain_metric: &ExactRatMatrix,
        codomain_metric: &ExactRatMatrix,
    ) -> Result<Self, PortedError> {
        Ok(Self {
            name: format!("{}^dagger", self.name),
            // An adjoint carries the covector the other way: the ports swap.
            source_port: self.target_port,
            target_port: self.source_port,
            chart: format!("{} (metric adjoint)", self.chart),
            matrix: self.matrix.metric_adjoint(domain_metric, codomain_metric)?,
        })
    }
}

/// **An ordered composable word of ported transports.**
///
/// The word is the construction. A total product is a compiled chart and is formed only when a
/// receiver asks for that face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortedWord {
    pub name: String,
    /// In causal order: `steps[0]` runs first.
    pub steps: Vec<PortedTransport>,
}

impl PortedWord {
    /// Found a word, checking every join. **Ports must agree by identity, not by extent.**
    pub fn founded(name: impl Into<String>, steps: Vec<PortedTransport>) -> Result<Self, PortedError> {
        for pair in steps.windows(2) {
            if pair[0].target_port != pair[1].source_port {
                return Err(PortedError::PortsDoNotCompose {
                    left: pair[0].name.clone(),
                    right: pair[1].name.clone(),
                    emitted: pair[0].target_port,
                    admitted: pair[1].source_port,
                });
            }
            if pair[0].matrix.rows() != pair[1].matrix.columns() {
                return Err(PortedError::ChartExtentsDisagree {
                    left: pair[0].name.clone(),
                    right: pair[1].name.clone(),
                });
            }
        }
        Ok(Self {
            name: name.into(),
            steps,
        })
    }

    pub fn source_port(&self) -> Option<BoundaryId> {
        self.steps.first().map(|step| step.source_port)
    }

    pub fn target_port(&self) -> Option<BoundaryId> {
        self.steps.last().map(|step| step.target_port)
    }

    pub fn hops(&self) -> usize {
        self.steps.len()
    }

    /// **Enact the word in causal order**, retaining every intermediate standing.
    ///
    /// This is the construction. Nothing is flattened and no total product is formed.
    pub fn enact(&self, standing: &[Rat]) -> Result<Vec<Vec<Rat>>, PortedError> {
        let mut carried = standing.to_vec();
        let mut lineage = Vec::with_capacity(self.steps.len() + 1);
        lineage.push(carried.clone());
        for step in &self.steps {
            carried = step.apply(&carried)?;
            lineage.push(carried.clone());
        }
        Ok(lineage)
    }

    /// **The compiled receiver chart: the total product.**
    ///
    /// Formed only here, only when a receiver asks for this face, and returned with what it cost so
    /// the cost of asking is visible. Two distinct words may compile to one chart; that does not
    /// make them one word.
    pub fn compiled_chart(&self) -> Result<(ExactRatMatrix, ExactWork), PortedError> {
        let Some(first) = self.steps.first() else {
            return Err(PortedError::EmptyWord);
        };
        let mut product = first.matrix.clone();
        let mut work = ExactWork::nothing();
        for step in &self.steps[1..] {
            let (next, spent) = step.matrix.multiply_with_work(&product)?;
            product = next;
            work = work.then(&spent);
        }
        Ok((product, work))
    }

    /// **An applied-state receiver**: what this word returns on a declared standing.
    ///
    /// This is what separates two words that compile to one chart only by accident, and it is what
    /// separates `AB` from `BA` for noncommuting factors. A chart comparison cannot.
    pub fn applied_receiver(&self, standing: &[Rat]) -> Result<Vec<Rat>, PortedError> {
        let lineage = self.enact(standing)?;
        lineage.into_iter().next_back().ok_or(PortedError::EmptyWord)
    }

    /// The exact predicted work of enacting this word, before anything is dispatched.
    ///
    /// `ExactWork` is the admission instrument; a work receiver decides. Nothing here times a clock.
    pub fn predicted_work(&self, entry_bits: u64) -> ExactWork {
        let mut work = ExactWork::nothing();
        for step in &self.steps {
            work = work.then(&ExactWork::predicted_product(
                step.matrix.rows(),
                step.matrix.columns(),
                1,
                entry_bits,
            ));
        }
        work
    }
}

/// **The lift defect of one source/native square, and its chain rule.**
///
/// `chi_gamma = Phi_Y T_gamma - S_gamma Phi_X`. For `gamma` then `eta`, direct expansion gives the
/// exact discrete Leibniz rule
///
/// ```text
///   chi_(eta gamma) = chi_eta T_gamma + S_eta chi_gamma
/// ```
///
/// which attributes a whole-path defect **without flattening the tower**. A zero local square is a
/// filled higher cell; a nonzero square is retained obstruction. A norm of `chi` is a face and
/// cannot replace it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiftDefect {
    pub square: ExactRatMatrix,
}

impl LiftDefect {
    /// One square: `Phi_Y T - S Phi_X`.
    pub fn of_square(
        source_transport: &ExactRatMatrix,
        native_transport: &ExactRatMatrix,
        entering_chart: &ExactRatMatrix,
        leaving_chart: &ExactRatMatrix,
    ) -> Result<Self, PortedError> {
        let left = leaving_chart.multiply(source_transport)?;
        let right = native_transport.multiply(entering_chart)?;
        Ok(Self {
            square: left.subtract(&right)?,
        })
    }

    pub fn is_filled(&self) -> bool {
        self.square.entries().iter().all(Zero::is_zero)
    }

    /// The whole-word defect, taken **directly** on the compiled charts.
    pub fn whole_word_direct(
        source: &[ExactRatMatrix],
        native: &[ExactRatMatrix],
        entering_chart: &ExactRatMatrix,
        leaving_chart: &ExactRatMatrix,
    ) -> Result<Self, PortedError> {
        let source_product = compose_in_causal_order(source)?;
        let native_product = compose_in_causal_order(native)?;
        Self::of_square(
            &source_product,
            &native_product,
            entering_chart,
            leaving_chart,
        )
    }

    /// The whole-word defect, taken **by the recurrence**, one square at a time.
    ///
    /// `charts[k]` is the chart at the `k`-th port, so `charts.len() == source.len() + 1`. The
    /// required control is that this equals [`Self::whole_word_direct`] exactly.
    pub fn whole_word_by_recurrence(
        source: &[ExactRatMatrix],
        native: &[ExactRatMatrix],
        charts: &[ExactRatMatrix],
    ) -> Result<Self, PortedError> {
        if source.len() != native.len() || charts.len() != source.len() + 1 {
            return Err(PortedError::WordLengthsDisagree);
        }
        let Some(first_source) = source.first() else {
            return Err(PortedError::EmptyWord);
        };
        let mut accumulated =
            Self::of_square(first_source, &native[0], &charts[0], &charts[1])?.square;
        let mut source_prefix = first_source.clone();
        for step in 1..source.len() {
            let local = Self::of_square(
                &source[step],
                &native[step],
                &charts[step],
                &charts[step + 1],
            )?
            .square;
            // chi_(eta gamma) = chi_eta T_gamma + S_eta chi_gamma
            let carried_forward = local.multiply(&source_prefix)?;
            let carried_back = native[step].multiply(&accumulated)?;
            accumulated = carried_forward.add(&carried_back)?;
            source_prefix = source[step].multiply(&source_prefix)?;
        }
        Ok(Self {
            square: accumulated,
        })
    }
}

fn compose_in_causal_order(word: &[ExactRatMatrix]) -> Result<ExactRatMatrix, PortedError> {
    let Some(first) = word.first() else {
        return Err(PortedError::EmptyWord);
    };
    let mut product = first.clone();
    for step in &word[1..] {
        product = step.multiply(&product)?;
    }
    Ok(product)
}

/// **A co-present front: occurrences that share a predecessor and no dependency.**
///
/// Read off the diagram's own layering, never from a count of contractions. Q/K/V form one front;
/// gate and up form another. The apparatus consequence follows this and not the arithmetic volume.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Front {
    pub depth: usize,
    pub occurrences: Vec<EventId>,
}

impl Front {
    pub fn breadth(&self) -> usize {
        self.occurrences.len()
    }

    pub fn is_serial(&self) -> bool {
        self.occurrences.len() == 1
    }
}

/// **The bridge: a foreign operator diagram bound into the standing computational holon.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortedOperationComplex {
    pub schema: String,
    pub name: String,
    /// Boundaries are ports, laws are operations, occurrences are events, interactions are joins.
    pub shape: EvolutionShape,
    /// Which source population realizes each law.
    pub witness: RealizationWitness,
    /// Every ported operation, typed by species.
    pub operations: BTreeMap<EvolutionLawId, PortedOperation>,
    /// Everything the admitted testimony could not decide, retained whole.
    pub undecided: Vec<CandidateDiagrams>,
}

impl PortedOperationComplex {
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            schema: "holonic-engine.ported-operation-complex.v1".to_owned(),
            witness: RealizationWitness::new(name.clone()),
            name,
            shape: EvolutionShape::default(),
            operations: BTreeMap::new(),
            undecided: Vec::new(),
        }
    }

    /// Declare a typed port. **Two ports of equal extent are still two ports.**
    pub fn port(&mut self, name: impl Into<String>) -> BoundaryId {
        let name = name.into();
        let boundary = self.shape.add_boundary(name.clone());
        self.witness.bind_boundary(boundary, name);
        boundary
    }

    /// Bind one foreign operation: its ports, its species, its carrier and its testimony.
    #[allow(clippy::too_many_arguments)]
    pub fn bind_operation(
        &mut self,
        name: impl Into<String>,
        species: OperationSpecies,
        inputs: Vec<BoundaryId>,
        outputs: Vec<BoundaryId>,
        carrier: Option<String>,
        testimony: Vec<SourceTestimony>,
    ) -> Result<EvolutionLawId, PortedError> {
        let name = name.into();
        let law = self.shape.add_law(name.clone(), inputs, outputs)?;
        self.witness
            .bind_law(law, carrier.clone().unwrap_or_else(|| name.clone()));
        self.operations.insert(
            law,
            PortedOperation {
                law,
                species,
                carrier,
                testimony,
            },
        );
        Ok(law)
    }

    /// One occurrence of a bound operation, in the chronology.
    pub fn occur(&mut self, law: EvolutionLawId) -> Result<EventId, PortedError> {
        Ok(self.shape.add_occurrence(law)?)
    }

    /// A join that carries precedence: the emitted boundary becomes a genuinely later input.
    pub fn carries_precedence(
        &mut self,
        name: impl Into<String>,
        boundary: BoundaryId,
        source: OccurrencePort,
        target: OccurrencePort,
    ) -> Result<(), PortedError> {
        self.join(
            name,
            boundary,
            InteractionTemporality::CarriesPrecedence,
            vec![InteractionBond { source, target }],
        )
    }

    /// **A co-present join: a front.** Both ports participate in one same-predecessor event.
    pub fn co_present(
        &mut self,
        name: impl Into<String>,
        boundary: BoundaryId,
        bonds: Vec<InteractionBond>,
    ) -> Result<(), PortedError> {
        self.join(name, boundary, InteractionTemporality::CoPresent, bonds)
    }

    fn join(
        &mut self,
        name: impl Into<String>,
        boundary: BoundaryId,
        temporality: InteractionTemporality,
        bonds: Vec<InteractionBond>,
    ) -> Result<(), PortedError> {
        let pattern = InteractionPattern::new(name, boundary, temporality, bonds);
        self.shape.add_interaction(pattern)?;
        Ok(())
    }

    /// Retain a question the admitted testimony could not settle.
    pub fn retain_undecided(&mut self, fibre: CandidateDiagrams) {
        self.undecided.push(fibre);
    }

    /// **The co-present fronts of this diagram**, read off its own layering.
    pub fn fronts(&self) -> Result<Vec<Front>, PortedError> {
        Ok(self
            .shape
            .chronology
            .layers()
            .map_err(EvolutionError::from)?
            .into_iter()
            .enumerate()
            .map(|(depth, occurrences)| Front { depth, occurrences })
            .collect())
    }

    /// The longest chain of genuine precedence: the **dependency span**.
    ///
    /// This is the number the apparatus consequence follows, and it is not the operation count.
    pub fn dependency_span(&self) -> Result<usize, PortedError> {
        Ok(self.fronts()?.len())
    }

    /// The species census, so a reader can see at a glance what this diagram is made of.
    pub fn species_census(&self) -> BTreeMap<OperationSpecies, usize> {
        let mut census = BTreeMap::new();
        for operation in self.operations.values() {
            *census.entry(operation.species).or_insert(0) += 1;
        }
        census
    }

    /// Operations whose binding the admitted testimony did not decide, by name.
    pub fn undecided_operations(&self) -> Vec<&str> {
        self.operations
            .values()
            .filter(|operation| !operation.is_decided())
            .filter_map(|operation| {
                self.shape
                    .laws
                    .get(&operation.law)
                    .map(|law| law.name.as_str())
            })
            .collect()
    }

    /// **Is the diagram closed?** Every boundary and law bound, every chronology consistent, and no
    /// question left open. An open return names what is missing rather than reporting a count.
    pub fn closure(&self) -> Result<DiagramClosure, PortedError> {
        self.witness.validate(&self.shape)?;
        let open: Vec<String> = self
            .undecided
            .iter()
            .filter(|fibre| fibre.is_open())
            .map(|fibre| fibre.question.clone())
            .collect();
        let unbound: Vec<String> = self
            .undecided_operations()
            .into_iter()
            .map(str::to_owned)
            .collect();
        Ok(DiagramClosure {
            ports: self.shape.boundaries.objects.len(),
            operations: self.operations.len(),
            occurrences: self.shape.occurrences.len(),
            fronts: self.fronts()?.len(),
            open_questions: open,
            operations_without_deciding_testimony: unbound,
        })
    }
}

/// What the bridge returns when asked whether the diagram is closed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagramClosure {
    pub ports: usize,
    pub operations: usize,
    pub occurrences: usize,
    pub fronts: usize,
    /// Named, never counted away.
    pub open_questions: Vec<String>,
    pub operations_without_deciding_testimony: Vec<String>,
}

impl DiagramClosure {
    /// **A closed diagram has no open question.** Nothing else makes it closed.
    pub fn is_closed(&self) -> bool {
        self.open_questions.is_empty() && self.operations_without_deciding_testimony.is_empty()
    }
}

/// Two words, and whether any declared applied-state receiver separates them.
///
/// **A compiled-chart comparison is not this test.** It is the weaker one, and the whole point of
/// retaining words is that it can agree while the words differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordSeparation {
    pub charts_agree: bool,
    /// The declared standings that separated them, by index. Empty means no declared receiver did.
    pub separating_standings: Vec<usize>,
}

impl WordSeparation {
    /// Compare two words over a declared family of applied standings.
    pub fn measure(
        left: &PortedWord,
        right: &PortedWord,
        standings: &[Vec<Rat>],
    ) -> Result<Self, PortedError> {
        let charts_agree = left.compiled_chart()?.0 == right.compiled_chart()?.0;
        let mut separating = Vec::new();
        for (at, standing) in standings.iter().enumerate() {
            if left.applied_receiver(standing)? != right.applied_receiver(standing)? {
                separating.push(at);
            }
        }
        Ok(Self {
            charts_agree,
            separating_standings: separating,
        })
    }

    /// The two words are one for this declared family. **Not for any richer one**, which is what a
    /// retained word makes reopenable.
    pub fn collapsed_for_this_family(&self) -> bool {
        self.separating_standings.is_empty()
    }
}

#[derive(Debug, Error)]
pub enum PortedError {
    #[error(
        "{left} emits port {emitted:?} and {right} admits port {admitted:?}: they do not compose"
    )]
    PortsDoNotCompose {
        left: String,
        right: String,
        emitted: BoundaryId,
        admitted: BoundaryId,
    },
    #[error("{left} and {right} carry charts of disagreeing extent")]
    ChartExtentsDisagree { left: String, right: String },
    #[error("an empty word has no composition")]
    EmptyWord,
    #[error("the source and native words, or their charts, are of disagreeing length")]
    WordLengthsDisagree,
    #[error("an exact linear operation refused: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the evolution shape refused: {0}")]
    Evolution(#[from] EvolutionError),
    #[error("the realization witness refused: {0}")]
    Realization(#[from] RealizationError),
}

/// A declared population of ported operations, addressed for a receiver quotient.
///
/// The join to [`crate::receiver_exact_compression`] happens through this: a word's identity is its
/// ordered step names, and a receiver's observation is its applied return. What quotients words is
/// that owner, not this one.
pub fn word_identity(word: &PortedWord) -> Vec<String> {
    word.steps.iter().map(|step| step.name.clone()).collect()
}

/// The ports a word actually crosses, in order. Retained lineage, never inferred from extents.
pub fn word_ports(word: &PortedWord) -> Vec<BoundaryId> {
    let mut ports = BTreeSet::new();
    let mut ordered = Vec::new();
    for step in &word.steps {
        for port in [step.source_port, step.target_port] {
            if ports.insert(port) {
                ordered.push(port);
            }
        }
    }
    ordered
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| row.iter().map(|value| rat(*value)).collect())
                .collect(),
        )
        .expect("well-formed")
    }

    /// **Two same-shaped but differently typed ports refuse composition.** Port identity is
    /// nominal; a matching extent is not a matching port.
    #[test]
    fn same_shaped_but_differently_typed_ports_refuse_to_compose() {
        let mut complex = PortedOperationComplex::new("port typing");
        let carried = complex.port("carried construction");
        let presented = complex.port("presented orientation");
        let receiver = complex.port("receiver chart");
        assert_ne!(carried, presented, "two ports are two ports");

        let identity = matrix(&[&[1, 0], &[0, 1]]);
        let first = PortedTransport::new("v", carried, presented, "source chart", identity.clone());
        let mismatched =
            PortedTransport::new("o", receiver, carried, "source chart", identity.clone());
        let refusal = PortedWord::founded("mismatched", vec![first.clone(), mismatched]);
        assert!(
            matches!(refusal, Err(PortedError::PortsDoNotCompose { .. })),
            "differently typed ports must refuse"
        );

        // And the same extents compose when the ports actually agree.
        let matching = PortedTransport::new("k", presented, receiver, "source chart", identity);
        let word = PortedWord::founded("matching", vec![first, matching]).expect("composes");
        assert_eq!(word.source_port(), Some(carried));
        assert_eq!(word.target_port(), Some(receiver));
        assert_eq!(word.hops(), 2);
    }

    /// **An applied-state receiver separates `AB` from `BA`; a chart comparison of two words that
    /// happen to agree does not.**
    #[test]
    fn noncommuting_factors_separate_under_an_applied_receiver() {
        let mut complex = PortedOperationComplex::new("order");
        let port = complex.port("standing");
        let a = matrix(&[&[1, 1], &[0, 1]]);
        let b = matrix(&[&[1, 0], &[1, 1]]);
        let step = |name: &str, m: ExactRatMatrix| {
            PortedTransport::new(name, port, port, "declared chart", m)
        };
        let forward =
            PortedWord::founded("a then b", vec![step("A", a.clone()), step("B", b.clone())])
                .expect("composes");
        let backward =
            PortedWord::founded("b then a", vec![step("B", b), step("A", a)]).expect("composes");

        let standings = vec![vec![rat(1), rat(0)], vec![rat(0), rat(1)]];
        let separation =
            WordSeparation::measure(&forward, &backward, &standings).expect("measured");
        assert!(!separation.charts_agree, "AB and BA differ here");
        assert!(
            !separation.collapsed_for_this_family(),
            "an applied receiver must separate them"
        );
        assert!(!separation.separating_standings.is_empty());
    }

    /// **Two distinct words with one compiled chart remain distinct.**
    ///
    /// The chart agrees and the word population does not; only a declared receiver quotient may
    /// collapse them, and a richer receiver can reopen the class.
    #[test]
    fn two_words_with_one_compiled_chart_remain_two_words() {
        let mut complex = PortedOperationComplex::new("word identity");
        let port = complex.port("standing");
        let step = |name: &str, m: ExactRatMatrix| {
            PortedTransport::new(name, port, port, "declared chart", m)
        };
        // (2I)(3I) = (6I) = (3I)(2I): one chart, two words, and a third word again.
        let two = matrix(&[&[2, 0], &[0, 2]]);
        let three = matrix(&[&[3, 0], &[0, 3]]);
        let six = matrix(&[&[6, 0], &[0, 6]]);
        let long = PortedWord::founded(
            "two then three",
            vec![step("two", two.clone()), step("three", three)],
        )
        .expect("composes");
        let short = PortedWord::founded("six", vec![step("six", six)]).expect("composes");

        let standings = vec![vec![rat(1), rat(-1)], vec![rat(5), rat(2)]];
        let separation = WordSeparation::measure(&long, &short, &standings).expect("measured");
        assert!(separation.charts_agree);
        assert!(
            separation.collapsed_for_this_family(),
            "this receiver family does not separate them"
        );
        // But the words themselves are two, and their retained identity says so.
        assert_ne!(word_identity(&long), word_identity(&short));
        assert_eq!(long.hops(), 2);
        assert_eq!(short.hops(), 1);
        // And enacting retains every intermediate standing, which the chart discarded.
        let lineage = long.enact(&standings[0]).expect("enacted");
        assert_eq!(lineage.len(), 3, "entering, one intermediate, leaving");
        assert_eq!(lineage[1], vec![rat(2), rat(-2)]);
    }

    /// **The whole-word lift defect equals its own recurrence, exactly.**
    ///
    /// `chi_(eta gamma) = chi_eta T_gamma + S_eta chi_gamma`, iterated. This is the control §5 of
    /// the derivation requires, and a norm of `chi` cannot stand in for it.
    #[test]
    fn the_whole_word_defect_equals_the_iterated_recurrence() {
        let source = vec![
            matrix(&[&[1, 2], &[0, 1]]),
            matrix(&[&[2, 0], &[1, 3]]),
            matrix(&[&[0, 1], &[1, 1]]),
        ];
        // A native word that is deliberately NOT a perfect lift, so the defect is nonzero.
        let native = vec![
            matrix(&[&[1, 2], &[0, 1]]),
            matrix(&[&[2, 0], &[1, 4]]),
            matrix(&[&[0, 1], &[1, 1]]),
        ];
        let charts = vec![
            matrix(&[&[1, 0], &[0, 1]]),
            matrix(&[&[1, 0], &[0, 1]]),
            matrix(&[&[1, 0], &[0, 1]]),
            matrix(&[&[1, 0], &[0, 1]]),
        ];
        let direct = LiftDefect::whole_word_direct(
            &source,
            &native,
            &charts[0],
            &charts[charts.len() - 1],
        )
        .expect("direct");
        let iterated =
            LiftDefect::whole_word_by_recurrence(&source, &native, &charts).expect("recurrence");
        assert_eq!(
            direct.square, iterated.square,
            "the chain rule must be exact, not approximate"
        );
        assert!(!direct.is_filled(), "this square is a genuine obstruction");

        // A perfect lift fills every cell, and both readings agree on that too.
        let perfect = LiftDefect::whole_word_by_recurrence(&source, &source, &charts)
            .expect("recurrence");
        assert!(perfect.is_filled(), "an exact lift has no obstruction");
    }

    /// **Fronts are read off the diagram, and the dependency span is not the operation count.**
    ///
    /// Q, K and V share one predecessor and no dependency; a serial chain of three would report a
    /// span of three. The diagram reports one front of breadth three.
    #[test]
    fn co_present_branches_form_one_front_rather_than_three_hops() {
        let mut complex = PortedOperationComplex::new("front");
        let standing = complex.port("standing");
        let receiver = complex.port("receiver chart");
        let presented = complex.port("presented chart");
        let carried = complex.port("carried chart");

        let rebase = complex
            .bind_operation(
                "rebase by gain",
                OperationSpecies::Transport,
                vec![standing],
                vec![standing],
                Some("input_layernorm.weight".to_owned()),
                vec![SourceTestimony::Configuration {
                    field: "rms_norm_eps".to_owned(),
                    value: "1e-06".to_owned(),
                }],
            )
            .expect("bound");
        let entering = complex.occur(rebase).expect("occurs");

        let mut branch_events = Vec::new();
        for (name, port, carrier) in [
            ("receiver projection", receiver, "q_proj.weight"),
            ("presented projection", presented, "k_proj.weight"),
            ("carried projection", carried, "v_proj.weight"),
        ] {
            let law = complex
                .bind_operation(
                    name,
                    OperationSpecies::Transport,
                    vec![standing],
                    vec![port],
                    Some(carrier.to_owned()),
                    vec![SourceTestimony::DeclaredShape {
                        population: carrier.to_owned(),
                        shape: vec![2048, 2560],
                    }],
                )
                .expect("bound");
            let event = complex.occur(law).expect("occurs");
            complex
                .carries_precedence(
                    format!("{name} follows the rebase"),
                    standing,
                    OccurrencePort::output(entering, 0),
                    OccurrencePort::input(event, 0),
                )
                .expect("joined");
            branch_events.push(event);
        }

        let fronts = complex.fronts().expect("layered");
        assert_eq!(fronts.len(), 2, "one rebase, then one front of branches");
        assert!(fronts[0].is_serial());
        assert_eq!(fronts[1].breadth(), 3, "Q, K and V are co-present");
        assert_eq!(
            complex.dependency_span().expect("span"),
            2,
            "the span is two, not four"
        );
        let census = complex.species_census();
        assert_eq!(census.get(&OperationSpecies::Transport), Some(&4));
    }

    /// **An undecided binding is retained as a candidate population, never resolved by plausibility.**
    #[test]
    fn an_undecided_binding_stays_open_and_names_what_would_decide_it() {
        let mut complex = PortedOperationComplex::new("undecided");
        let standing = complex.port("standing");
        complex
            .bind_operation(
                "stored per-site scalar",
                OperationSpecies::Transport,
                vec![standing],
                vec![standing],
                Some("layer_scalar".to_owned()),
                vec![SourceTestimony::Undecided {
                    question: "where does the stored per-site scalar multiply?".to_owned(),
                }],
            )
            .expect("bound");
        complex.retain_undecided(CandidateDiagrams {
            question: "where does the stored per-site scalar multiply?".to_owned(),
            candidates: vec![
                "the re-entering standing".to_owned(),
                "the contact faces".to_owned(),
                "nothing; it is inert".to_owned(),
            ],
            would_be_decided_by: vec![
                "the source's executable implementation".to_owned(),
                "an intervention separating the candidates under a declared receiver".to_owned(),
            ],
        });

        let closure = complex.closure().expect("validated");
        assert!(!closure.is_closed(), "an open question is not closure");
        assert_eq!(closure.open_questions.len(), 1);
        assert_eq!(
            closure.operations_without_deciding_testimony,
            vec!["stored per-site scalar".to_owned()]
        );
        assert!(complex.undecided[0].is_open());
    }

    /// A ported transport hands the three returns straight to their owner: a rebase gives both
    /// identities, a collapsing map gives its factorization, and an adjoint needs its metrics.
    #[test]
    fn a_ported_transport_returns_at_the_correct_species() {
        let mut complex = PortedOperationComplex::new("species");
        let from = complex.port("from");
        let to = complex.port("to");
        let rebase = PortedTransport::new(
            "rebase",
            from,
            to,
            "declared chart",
            matrix(&[&[2, 1], &[1, 1]]),
        );
        assert!(matches!(
            rebase.rebase_receipt().expect("receipt"),
            RebaseReceipt::Rebase { .. }
        ));
        let collapsing = PortedTransport::new(
            "collapsing",
            from,
            to,
            "declared chart",
            matrix(&[&[1, 1], &[1, 1]]),
        );
        assert!(matches!(
            collapsing.rebase_receipt().expect("receipt"),
            RebaseReceipt::Refused { .. }
        ));
        assert_eq!(
            collapsing.factorization().expect("factored").collapsed_dimension(),
            1
        );
        // The adjoint swaps the ports, because a covector travels the other way.
        let metric = matrix(&[&[3, 0], &[0, 5]]);
        let adjoint = rebase
            .metric_adjoint(&metric, &metric)
            .expect("adjoint");
        assert_eq!(adjoint.source_port, to);
        assert_eq!(adjoint.target_port, from);
        // And the species decides what may be asked at all.
        assert!(OperationSpecies::Transport.admits_inverse());
        assert!(!OperationSpecies::Face.admits_inverse());
        assert!(!OperationSpecies::Quotient.admits_inverse());
        assert!(!OperationSpecies::Construction.admits_inverse());
    }

    /// The word predicts its exact work before anything is dispatched.
    #[test]
    fn a_word_predicts_its_work_before_dispatch() {
        let mut complex = PortedOperationComplex::new("work");
        let port = complex.port("standing");
        let word = PortedWord::founded(
            "two steps",
            vec![
                PortedTransport::new("a", port, port, "chart", matrix(&[&[1, 2], &[3, 4]])),
                PortedTransport::new("b", port, port, "chart", matrix(&[&[0, 1], &[1, 0]])),
            ],
        )
        .expect("composes");
        let predicted = word.predicted_work(16);
        let coordinates = predicted.coordinates();
        assert!(
            coordinates
                .iter()
                .any(|(name, count)| *name == "multiplications" && !count.is_zero()),
            "{coordinates:?}"
        );
        // The compiled chart also returns what asking for it cost.
        let (_, spent) = word.compiled_chart().expect("compiled");
        assert!(spent
            .coordinates()
            .iter()
            .any(|(name, count)| *name == "multiplications" && !count.is_zero()));
    }
}
