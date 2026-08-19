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

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::causal::EventId;
use crate::category::BoundaryId;
use crate::evolution::{EvolutionError, EvolutionLawId, EvolutionShape};
use crate::exact_linear::{ExactLinearError, ExactRatMatrix, LinearFactorization, RebaseReceipt};
use crate::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use crate::exact_work::{Admission, ExactWork, WorkBudget};
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

    /// **Pose a transport from a source population's own stored codewords, exactly.**
    ///
    /// The codewords enter through [`crate::exact_value::ieee754`], the workspace's declared float
    /// mouth, so the posed entries **are** the stored values rather than approximations of them.
    /// The chart lineage names where they came from, because a matrix without its chart is a
    /// coordinate array and not a transport.
    pub fn posed_from_bfloat16(
        name: impl Into<String>,
        source_port: BoundaryId,
        target_port: BoundaryId,
        chart: impl Into<String>,
        words: &[u16],
        rows: usize,
        columns: usize,
    ) -> Result<Self, PortedError> {
        if words.len() != rows.saturating_mul(columns) {
            return Err(PortedError::PosedExtentDisagrees {
                declared: rows.saturating_mul(columns),
                supplied: words.len(),
            });
        }
        let mut entries = Vec::with_capacity(rows);
        for row in 0..rows {
            let mut carried = Vec::with_capacity(columns);
            for column in 0..columns {
                let word = words[row * columns + column];
                let datum = crate::exact_value::ieee754::decode_bfloat16_bits(word)
                    .map_err(|_| PortedError::CodewordRefused { word })?;
                carried.push(datum.value());
            }
            entries.push(carried);
        }
        Ok(Self::new(
            name,
            source_port,
            target_port,
            chart,
            ExactRatMatrix::new(entries)?,
        ))
    }

    /// **What posing this transport densely would cost, before anything is posed.**
    ///
    /// Residency is the coordinate that decides here: an exact rational entry is not a machine
    /// word, and a caller that discovers this after allocating has already paid.
    pub fn predicted_posing_work(rows: usize, columns: usize, entry_bits: u64) -> ExactWork {
        let mut work = ExactWork::nothing();
        work.resident(u64::try_from(rows.saturating_mul(columns)).unwrap_or(u64::MAX));
        work.stepped();
        let _ = entry_bits;
        work
    }

    /// What factorizing this transport would cost, before it is attempted.
    pub fn predicted_factorization_work(&self, entry_bits: u64) -> ExactWork {
        ExactWork::predicted_elimination(self.matrix.rows().max(self.matrix.columns()), entry_bits)
    }

    /// **The factorization, only if a declared work receiver admits it.**
    ///
    /// A refusal is a return: it carries the priced work, the ceiling, and the coordinate that
    /// dominated the price, so a caller learns *what* made the deed expensive rather than that it
    /// was. `CLAUDE.md`: resource pressure changes partition, factorization, placement, residency,
    /// or aperture — it never authorizes raising a magic number.
    pub fn factorization_under(
        &self,
        budget: &WorkBudget,
        entry_bits: u64,
    ) -> Result<Result<LinearFactorization, Admission>, PortedError> {
        let admission = budget.admits(&self.predicted_factorization_work(entry_bits));
        if !admission.is_admitted() {
            return Ok(Err(admission));
        }
        Ok(Ok(self.factorization()?))
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
    GatedPassage { terms: usize },
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
            work.stepped();
            carrier.stored_row(population, *row).map_err(apparatus)?
        }
        PortedOperationKind::Contract { population } => {
            work.stepped();
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
            work.stepped();
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
            work.stepped();
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
            work.stepped();
            admitted[0]
                .iter()
                .zip(&admitted[1])
                .map(|(left, right)| {
                    work.multiplied(1);
                    left * right
                })
                .collect()
        }
        PortedOperationKind::GatedPassage { terms } => {
            let one = Rat::one();
            let two = Rat::from_integer(BigInt::from(2));
            let mut out = Vec::with_capacity(admitted[0].len());
            let mut widths = Vec::with_capacity(admitted[0].len());
            for value in &admitted[0] {
                let turned = CertifiedSeries::hyperbolic_tangent_enclosure(value, *terms)
                    .map_err(|error| PortedError::Value { reason: format!("{error:?}") })?;
                let low = (&turned.lower + &one) * value / &two;
                let high = (&turned.upper + &one) * value / &two;
                let (below, above) = if low <= high { (low, high) } else { (high, low) };
                out.push((&below + &above) / &two);
                widths.push((&above - &below) / &two);
                work.multiplied(3);
                work.added(2);
            }
            work.stepped();
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
            work.stepped();
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
            work.stepped();
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
            work.stepped();
            admitted.iter().flat_map(|part| part.iter().cloned()).collect()
        }
        PortedOperationKind::Ablate { from, count } => {
            let section = &admitted[0];
            let upper = (from + count).min(section.len());
            work.stepped();
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
            work.stepped();
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
            work.stepped();
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
    #[error("a transport declared {declared} entries and {supplied} codewords were supplied")]
    PosedExtentDisagrees { declared: usize, supplied: usize },
    #[error("the codeword {word:#06x} is not a finite stored value")]
    CodewordRefused { word: u16 },
    #[error("the source and native words, or their charts, are of disagreeing length")]
    WordLengthsDisagree,
    #[error("an exact linear operation refused: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the evolution shape refused: {0}")]
    Evolution(#[from] EvolutionError),
    #[error("the realization witness refused: {0}")]
    Realization(#[from] RealizationError),
    #[error("occurrence {occurrence:?} is bound to no operation")]
    OccurrenceUnbound { occurrence: EventId },
    #[error("occurrence {occurrence:?} is not in this complex")]
    ForeignOccurrence { occurrence: EventId },
    #[error(
        "occurrence {occurrence:?} declares {law_inputs} in and {law_outputs} out; the operation \
         admits {admitted_inputs} and {admitted_outputs}"
    )]
    ArityDisagrees {
        occurrence: EventId,
        law_inputs: usize,
        law_outputs: usize,
        admitted_inputs: usize,
        admitted_outputs: usize,
    },
    #[error(
        "occurrence {occurrence:?} was bound as a {declared:?} and the operation is a {operation:?}"
    )]
    SpeciesDisagrees {
        occurrence: EventId,
        declared: OperationSpecies,
        operation: OperationSpecies,
    },
    #[error("law {law:?} carries more than one operation species")]
    OneLawManySpecies { law: EvolutionLawId },
    #[error("input {input} of occurrence {occurrence:?} is carried by no interaction")]
    InputUncarried { occurrence: EventId, input: usize },
    #[error("no standing has been written at {port:?}")]
    StandingAbsent { port: OccurrencePort },
    #[error("the declared apparatus refused: {reason}")]
    Apparatus { reason: String },
    #[error("an exact value refused: {reason}")]
    Value { reason: String },
    #[error("two standings meeting at one occurrence disagree: {left} against {right}")]
    WidthDisagrees { left: usize, right: usize },
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
        assert!(receipt.work.coordinates().iter().any(|(name, count)| *name
            == "dependency-span"
            && *count == num_bigint::BigUint::from(4u32)));
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
