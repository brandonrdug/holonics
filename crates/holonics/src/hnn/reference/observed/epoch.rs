//! The aperture-one observed passage at one fixed physical medium.
//!
//! A source section is an exterior cut, never a deposit boundary. Requested prefix snapshots
//! fork the fixed medium and actual prefix motion/tree; only the actual receiving tick closes
//! ordinary absorption. The explicit terminal partial is R12 lines 209–210's last 56 cells;
//! it reports no section tick and seals the result against ordinary continuation.

use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::constitution::epoch::{
    EpochCandidateScope, EpochReceivingRecord, partition_exponent,
};
pub use crate::hnn::constitution::epoch::{
    EpochStageAttempt, EpochStageCondition, EpochStageReading, EpochStageRefusal, EpochStageValue,
};
use crate::hnn::reference::comparison::ComparisonReading;
use crate::hnn::reference::epoch::EpochForward;
use rayon::prelude::*;

/// Exterior prequential readings, in heard-cell order. The first-law resident keeps only its
/// final arrived occurrence; this complete code series is separate exterior evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedEpochCellReceipt {
    pub prediction: Faces,
    pub combined: Faces,
    pub code: ExactInterval,
    pub tree: Option<ExactInterval>,
    /// The actual pre-reception scored face, beside its code of the heard target.
    pub scored_face: crate::hnn::receiving::cells::ScoredFaceReading,
    /// The magnitude mass released by the single receiving-face partition, per class.
    pub released: Vec<Rat>,
    /// Actual kept-word chart decisions, returned as exterior evidence and never retained.
    pub word_charts: Vec<crate::hnn::chart::ChartReading>,
}

/// Actual elapsed batch intervals. Parallel return workers are timed by their joined outer
/// interval; their individual elapsed times are never summed into a claimed critical path.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ObservedEpochWallTimes {
    pub forward_batch: Duration,
    /// Includes the tree's prequential face schedule, score and exact return/compose staging.
    pub compare_return_compose_batch: Duration,
    pub grouped_deposit: Duration,
    /// Disjoint outer calls inside grouped_deposit. None means unattempted; a measured zero
    /// remains Some(Duration::ZERO). Whole staging includes the first shared normal preparation.
    /// These overlap deposit_subphases, whose unscoped intervals can span rung/probe boundaries.
    pub whole_stage: Option<Duration>,
    pub whole_probe: Option<Duration>,
    pub joint_stage: Option<Duration>,
    pub joint_probe: Option<Duration>,
    /// The existing receiving-only fallback stage; it executes no upstream finite probe.
    pub receiving_only_stage: Option<Duration>,
    /// Completed disjoint subcalls of each actual probe. These lie inside whole_probe or
    /// joint_probe, never replace them, and retain no candidate operands in resident state.
    pub probe_subphases: Vec<(EpochStageAttempt, &'static str, Duration)>,
    pub final_arrived_reread: Duration,
    pub precision_close: Duration,
    /// Only explicitly requested prefix forks, including their own joint close when reached.
    pub prefix_forks: Duration,
    /// Joined wall windows, not a sum of individual return-worker durations.
    pub compare_preparation: Duration,
    pub return_join: Duration,
    pub ordered_publication: Duration,
    /// Face partition, pullback, compose, receiving-record staging. Worker elapsed sums
    /// are workload evidence only and must never be added as a critical-path duration.
    pub return_worker_sums: [Duration; 4],
    /// Disjoint intervals observed outside the numerical deposition owner.
    pub deposit_subphases: Vec<(String, Duration)>,
}

/// A declared set of material families eligible to absorb this epoch's return.
/// Every native covector is still computed. Holding physical factors omits their
/// deposition requests and statistics; the D-only scope admits channel D alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObservedEpochDepositionScope {
    All,
    NormalMaps,
    NormalMapsAndChannelDissipation,
}

/// The comparison law that admitted this atomic publication. Neutral means
/// executed objective equality, and never counts as learned motion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObservedEpochOutcome {
    Whole,
    Joint,
    ReceivingOnly,
    Neutral,
}

/// Exterior physical evidence from this batch's actual producing words. This is not
/// retained by Resident or its cross-entropy ledger. The first word has no fabricated
/// predecessor balance; `chained` contains exactly the within-batch joins.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedEpochEnergy {
    pub words: Vec<crate::hnn::word::WordBalance>,
    pub chained: Vec<crate::hnn::word::ChainedBalance>,
    /// Both forms of the deposit are read at this last word's producing lift.
    pub producing_lift: Vec<BigInt>,
    /// The source's closing lift is a separate reference crossing, not deposit work.
    pub closing_lift: Vec<BigInt>,
    pub physical_form_changed: bool,
    /// Derived from PowerForm::held, including exact zero when E/Wc/R alone move.
    pub deposition_work: Rat,
}

impl ObservedEpochEnergy {
    pub fn closes(&self) -> bool {
        !self.words.is_empty()
            && self.chained.len() == self.words.len() - 1
            && self.words.iter().all(crate::hnn::word::WordBalance::closes)
            && self
                .chained
                .iter()
                .all(|join| join.closes() && join.lift_emits())
            && self.words[..self.words.len() - 1]
                .iter()
                .all(|word| word.commit.is_none())
            && self
                .words
                .last()
                .and_then(|word| word.commit.as_ref())
                .is_some_and(|commit| commit.deposition == self.deposition_work)
    }
}

/// Whether the whole candidate existed and its finite comparison actually completed.
/// ProbeFailed does not claim a completed wave or objective reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObservedEpochProbeState {
    SealNotFormed,
    SealedNoProbeRequired,
    ProbeFailed,
    FiniteComparisonExecuted,
}

#[derive(Debug)]
pub struct ObservedEpochReceipt {
    pub consumed: usize,
    pub cells: u64,
    pub comparison_commit: u64,
    pub partition_exponent: u32,
    pub closed_section: bool,
    pub terminal_partial: bool,
    pub carry_out: bool,
    pub reads: Vec<ObservedEpochCellReceipt>,
    pub deposit: DepositReading,
    pub energy: ObservedEpochEnergy,
    pub outcome: ObservedEpochOutcome,
    pub deposition_scope: ObservedEpochDepositionScope,
    /// One whole-candidate probe, when upstream material actually moved.
    pub comparison: Option<ComparisonReading>,
    /// A refused whole branch is discarded before receiving-only restaging.
    pub whole_refusal: Option<String>,
    /// First whole-stage evidence; receiving-only restaging never overwrites it.
    pub whole_stage_refusal: Option<EpochStageRefusal>,
    pub probe_state: ObservedEpochProbeState,
    pub publication_attempt: EpochStageAttempt,
    pub joint_attempted: bool,
    pub joint_directions: Vec<crate::hnn::constitution::EpochJointDirectionReading>,
    pub joint_comparison: Option<ComparisonReading>,
    pub joint_refusal: Option<String>,
    pub joint_stage_refusal: Option<EpochStageRefusal>,
    pub joint_probe_state: ObservedEpochProbeState,
    pub precision: ObservedPrecisionReceipt,
    pub close: Option<ClosedLocated>,
    /// Only requested cuts. A cut equal to consumed still precedes the closing deposit.
    pub prefixes: Vec<(usize, Resident, ObservedCrib)>,
    pub wall: ObservedEpochWallTimes,
}

struct ComparedRead {
    ratio: PendingRatio,
    opening: WordOpening,
    prediction: Faces,
    combined: Faces,
    released: Vec<Rat>,
    deposit: Deposit,
    receiving_parts: Vec<EpochReceivingRecord>,
    word_charts: Vec<crate::hnn::chart::ChartReading>,
    worker_times: [Duration; 4],
}

fn refusal(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

/// Only native candidate-domain refusals permit a different scoped policy.
/// Executor status, shape, identity and arithmetic failures propagate atomically;
/// they must never be retried as if they were a mathematical nondecrease.
fn receiving_restage_permitted(error: &HnnError) -> bool {
    matches!(error, HnnError::Unadmitted { reason } if matches!(*reason,
        "actual epoch certification requires the represented nonlinear factor rays"
        | "paired receiving shared-material steps require the joined source/context propagation gain certificate"
        | "a moving actual epoch ray must descend its contemporary comparison"
        | "retained epoch news cannot invent an uncertified fresh family"
        | "the native epoch joint certificate refused its candidate"
        | "the fixed actual epoch rays were not all admitted"
        | "the actual epoch ray violates its own curvature bound"
        | "the actual epoch rays violate the joint triangle bound"
        | "the actual epoch rays leave an executed pump tube"
        | "source refinement needs its pair-factor remainders inside the finer half-cell"
        | "a scheduled channel rebase waits for its original fresh positive D rate"
    ))
}

/// Only the joint proposal's own post-projection normal predicate is a new domain
/// refusal. The canonical whole non-descending invariant remains fatal.
fn joint_restage_permitted(failure: &crate::hnn::constitution::epoch::EpochStageFailure) -> bool {
    receiving_restage_permitted(&failure.error)
        || (matches!(&failure.error, HnnError::EpochStepNonDescending { .. })
            && failure.evidence.condition == EpochStageCondition::JointNormalFall)
}

fn grain_failure_restage_permitted(
    attempt: EpochStageAttempt,
    failure: &crate::hnn::constitution::epoch::EpochStageFailure,
) -> bool {
    // A normal map's own Whole alignment is independent of the optional channel endpoint.
    // Its existing descent to Joint must not acquire a redundant Whole replay.
    !(attempt == EpochStageAttempt::Whole
        && failure.evidence.condition == EpochStageCondition::ActualRayAlignment
        && failure.evidence.family == Some(crate::hnn::constitution::Family::Map))
        && match attempt {
            EpochStageAttempt::Whole => receiving_restage_permitted(&failure.error),
            EpochStageAttempt::Joint => joint_restage_permitted(failure),
            EpochStageAttempt::ReceivingOnly => false,
        }
}

/// The certificate reads the actual normalized face. The retained RHS has a separately
/// partitioned foil, so its even-row sum alone cannot reconstruct those masses.
fn with_receiving_masses(
    deposit: Deposit,
    receiver: usize,
    masses: &[Rat],
    scope: ObservedEpochDepositionScope,
) -> Result<Deposit, HnnError> {
    let mut linear = deposit.linear().to_vec();
    for step in &mut linear {
        if step.locus == LinearLocus::Receiving(receiver) {
            for sample in &mut step.samples {
                sample.masses = Some(masses.to_vec());
            }
        }
    }
    let reach = deposit.reach().cloned().ok_or(HnnError::MissingReach)?;
    Deposit::new(
        deposit.commit(),
        linear,
        match scope {
            ObservedEpochDepositionScope::All => deposit.factors().to_vec(),
            ObservedEpochDepositionScope::NormalMaps => Vec::new(),
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation => deposit
                .factors()
                .iter()
                .filter(|factor| matches!(&factor.gradient, crate::hnn::constitution::FactorGradient::Dissipation { .. }))
                .cloned()
                .collect(),
        },
        deposit.loci(),
    )
    .with_reach(reach)
    .with_landmarks(deposit.landmarks().to_vec())
    .with_landmark_observations(
        deposit
            .landmark_partition()
            .zip(deposit.landmark_observations().map(|paths| paths.to_vec())),
    )
    .map(|deposit_with_masses| deposit_with_masses.with_receiving(deposit.receiving().to_vec()))
}

/// The epoch's original comparisons, held only until atomic publication.
/// The finite law is the same correlated population likelihood ratio used by
/// FrozenComparison, with the actual prequential tree schedule on each side.
struct EpochComparison {
    combined: Faces,
    trees: Vec<LandmarkFace>,
    targets: Vec<usize>,
    target_phases: Vec<crate::hnn::ratio::TargetPhases>,
}

impl EpochComparison {
    fn evaluate(
        &self,
        population: &PortPopulation,
        receiver: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
    ) -> Result<ComparisonReading, HnnError> {
        if combined.faces.len() != self.targets.len()
            || combined.logits.len() != self.targets.len()
            || trees.len() != self.targets.len()
        {
            return Err(refusal(
                "an epoch probe keeps every original scored station",
            ));
        }
        let phase_excess = |faces: &Faces| -> Result<Rat, HnnError> {
            faces
                .faces
                .iter()
                .zip(&faces.logits)
                .zip(&self.targets)
                .zip(&self.target_phases)
                .map(|(((face, logits), target), phase)| {
                    HolonRatio::compare(
                        Faces {
                            faces: vec![face.clone()],
                            logits: vec![logits.clone()],
                        },
                        &[*target],
                        phase,
                    )
                    .map(|ratio| ratio.excess())
                })
                .sum()
        };
        let before_phase = phase_excess(&self.combined)?;
        let after_phase = phase_excess(combined)?;
        let phase_delta = &after_phase - &before_phase;
        let unchanged = combined == &self.combined && trees == self.trees;
        let mut result = None;
        // This is the existing demand ladder, never an authored epsilon or
        // a new candidate. Every refinement reads these same expressions.
        for (round, bits) in crate::hnn::receiving::cells::demand_ladder()
            .into_iter()
            .enumerate()
        {
            let scored = crate::hnn::receiving::compare_scores_at(
                population, receiver, &self.combined, &self.trees,
                combined, trees, &self.targets, bits,
            )?;
            // Preserve the native components as exterior evidence at this same demand.
            // The existing total and every admission predicate below remain unchanged.
            let class_code_change = scored.change.clone();
            let objective_change = ExactInterval::new(
                scored.change.lower + &phase_delta,
                scored.change.upper + &phase_delta,
            )?;
            let absolute = |scored: &crate::hnn::receiving::Scored, phase: &Rat| {
                ExactInterval::new(
                    scored.model.iter().map(|code| &code.lower).sum::<Rat>() + phase,
                    scored.model.iter().map(|code| &code.upper).sum::<Rat>() + phase,
                )
            };
            let reading = ComparisonReading {
                before: absolute(&scored.before, &before_phase)?,
                after: absolute(&scored.after, &after_phase)?,
                unchanged,
                strictly_improved: objective_change.upper < Rat::zero(),
                objective_change,
                epoch_class_code_change: Some(class_code_change),
                epoch_phase_excess_change: Some(phase_delta.clone()),
                reading_bits: bits,
                refinement_rounds: u32::try_from(round).map_err(|_| HnnError::CountOverflow)?,
                retained_interval_members: population.retained_interval_members(),
            };
            let done = unchanged || !reading.needs_precision();
            result = Some(reading);
            if done {
                break;
            }
        }
        result.ok_or_else(|| refusal("the epoch comparison keeps its declared reading demand"))
    }
}

impl Reference {
    /// Receive through the next actual receiving section. A short exterior section must be
    /// joined to later heard data before this call; it cannot force a physical crossing.
    pub fn observe_epoch_continuing(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_at_cuts(
            resident,
            crib,
            pairing,
            classes,
            placement,
            &[],
            false,
        )
    }

    /// Execute one actual clock-bounded batch and requested section forks transactionally.
    /// `terminal` authorizes only the selected finite life's final partial interval, never a
    /// source-section flush. Such a result is sealed and cannot be resumed as an ordinary epoch.
    pub fn observe_epoch_continuing_at_cuts(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_for(
            resident,
            crib,
            pairing,
            classes,
            placement,
            cuts,
            terminal,
            ReturnConsumer::Epoch,
        )
    }

    /// Execute the same native observed law with an explicitly selected word/flow
    /// realization. A refusal at any phase leaves both resident and crib unchanged.
    /// Source scan, face partition and certification remain owned by this shared
    /// host owner; this entry point alone claims no fully resident life.
    #[allow(clippy::too_many_arguments)]
    pub fn observe_epoch_continuing_at_cuts_with_execution(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
        execution: &dyn ObservedEpochExecution,
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_for_execution(
            resident,
            crib,
            pairing,
            classes,
            placement,
            cuts,
            terminal,
            ReturnConsumer::Epoch,
            execution,
            true,
            ObservedEpochDepositionScope::All,
            &mut |_, _| {},
        )
    }

    /// Select deposited families before any return is absorbed. All uses the
    /// ordinary policy and retains the physical-factor refusal. NormalMaps holds
    /// physical factors; the D-only scope admits channel dissipation with the same
    /// grouped rays, actual-ray certificate and same-opening finite comparison.
    #[allow(clippy::too_many_arguments)]
    pub fn observe_epoch_continuing_at_cuts_with_scope(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
        execution: &dyn ObservedEpochExecution,
        scope: ObservedEpochDepositionScope,
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_at_cuts_with_scope_diagnosed(
            resident,
            crib,
            pairing,
            classes,
            placement,
            cuts,
            terminal,
            execution,
            scope,
            &mut |_, _| {},
        )
    }

    /// Observe at most the first whole and first receiving-only stage refusal of this
    /// atomic epoch, including a fatal refusal. The callback is exterior evidence only;
    /// it cannot mutate native operands, and original errors/transaction rollback remain intact.
    #[allow(clippy::too_many_arguments)]
    pub fn observe_epoch_continuing_at_cuts_with_scope_diagnosed(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
        execution: &dyn ObservedEpochExecution,
        scope: ObservedEpochDepositionScope,
        stage_refused: &mut dyn FnMut(EpochStageAttempt, &EpochStageRefusal),
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_for_execution(
            resident,
            crib,
            pairing,
            classes,
            placement,
            cuts,
            terminal,
            ReturnConsumer::Epoch,
            execution,
            true,
            scope,
            stage_refused,
        )
    }

    // The ordinary composition is retained as the exact control for the contribution-only
    // consumer. Both routes publish through the same grouped deposition law.
    #[allow(clippy::too_many_arguments)]
    fn observe_epoch_continuing_for(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
        consumer: ReturnConsumer,
    ) -> Result<ObservedEpochReceipt, HnnError> {
        self.observe_epoch_continuing_for_execution(
            resident,
            crib,
            pairing,
            classes,
            placement,
            cuts,
            terminal,
            consumer,
            &HostObservedEpochExecution,
            false,
            ObservedEpochDepositionScope::All,
            &mut |_, _| {},
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn observe_epoch_continuing_for_execution(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        classes: &[usize],
        placement: Option<&OccurrencePlacement>,
        cuts: &[usize],
        terminal: bool,
        consumer: ReturnConsumer,
        execution: &dyn ObservedEpochExecution,
        selected_forward: bool,
        deposition_scope: ObservedEpochDepositionScope,
        stage_refused: &mut dyn FnMut(EpochStageAttempt, &EpochStageRefusal),
    ) -> Result<ObservedEpochReceipt, HnnError> {
        let forward_start = Instant::now();
        if classes.is_empty() {
            return Err(refusal("an observed epoch needs at least one heard cell"));
        }
        if resident.observed_epoch_terminal {
            return Err(refusal(
                "a terminal partial epoch cannot continue as an ordinary observed life",
            ));
        }
        if self.refining && deposition_scope != ObservedEpochDepositionScope::NormalMapsAndChannelDissipation {
            return Err(refusal(
                "observed contact-grain scheduling requires the explicit channel D scope",
            ));
        }
        if !resident.pending.is_empty() || !resident.staged.is_empty() {
            return Err(refusal(
                "an observed epoch requires consumed comparison handles",
            ));
        }
        if cuts.iter().any(|&cut| cut == 0 || cut > classes.len()) {
            return Err(refusal(
                "an observed prefix cut belongs to the submitted heard passage",
            ));
        }
        let first_placement = placement.map(|placed| placed.part(0..1)).transpose()?;
        let (boundary, _) = admit_observed_cell(
            resident,
            crib,
            pairing,
            classes[0],
            first_placement.as_ref(),
        )?;
        let phases = match resident.admitted.as_slice() {
            [phases] if phases.aperture() == 1 => phases.clone(),
            _ => {
                return Err(refusal(
                    "observed epochs require one unambiguous aperture-one receiver",
                ));
            }
        };
        let receiver = phases.ring();
        let field = resident.field.clone();
        let encoded = match placement {
            Some(placed) => boundary.encode_placed(classes, placed)?,
            None => boundary.encode(classes)?,
        };
        field.admit(&encoded)?;
        encoded.check_observed_material(&resident.constitution)?;
        let mut clock = resident.current.clone();
        let mut consumed = 0;
        let mut closed_section = false;
        let mut carry_out = false;
        for at in 0..encoded.len() {
            let step = clock.step(&field, &encoded, at)?;
            consumed = at + 1;
            closed_section = step
                .ticks
                .get(receiver)
                .copied()
                .ok_or(HnnError::RingOutside {
                    ring: receiver,
                    rings: step.ticks.len(),
                })?
                != 0;
            carry_out = step.carry_out;
            if closed_section || carry_out {
                break;
            }
        }
        let terminal_partial = !closed_section && !carry_out;
        if terminal_partial && !terminal {
            return Err(refusal(
                "an exterior section ended before the actual receiving tick; join its next heard cells",
            ));
        }
        let actual = encoded.part(0..consumed)?;
        field.capacity_for(&actual)?;
        let heard = u64::try_from(consumed).map_err(|_| HnnError::CountOverflow)?;
        let received = resident
            .moments
            .values()
            .next()
            .map_or(0, SourceMoment::cells);
        if received.checked_add(heard).ok_or(HnnError::CountOverflow)? > field.population() {
            return Err(refusal(
                "the observed epoch exceeds the declared source horizon",
            ));
        }
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        let epoch_index = match next.observed_epoch_ingress {
            Some((ring, count)) if ring == receiver => count,
            Some(_) => {
                return Err(refusal(
                    "the observed epoch ingress belongs to this receiving ring",
                ));
            }
            None if received == 0 => {
                next.observed_epoch_ingress = Some((receiver, 0));
                0
            }
            None => {
                return Err(refusal(
                    "a continued observed epoch needs its saved actual receiving ingress",
                ));
            }
        };
        let moment = match next.moments.keys().next().copied() {
            Some(moment) => moment,
            None => self.ingest(&mut next, None, &boundary.encode(&[])?)?.0,
        };
        let requested: Vec<_> = cuts
            .iter()
            .copied()
            .filter(|&cut| cut <= consumed)
            .collect();
        // This predecessor is private to this atomic transaction. A prospective
        // probe starts here, before any batch cell, source clock or chart moves.
        let comparison_opening = next.clone();
        let forward = if selected_forward {
            self.read_epoch_at_cuts_with_execution(
                &next, &moment, &phases, &actual, &requested, execution,
            )?
        } else {
            self.read_epoch_at_cuts(&next, &moment, &phases, &actual, &requested)?
        };
        let forward_batch = forward_start.elapsed();
        let compare_start = Instant::now();
        let mut prefix_forks = Duration::ZERO;
        if forward.consumed != consumed
            || forward.carry_out != carry_out
            || forward.current != clock
        {
            return Err(refusal(
                "the epoch source scan and actual receiving clock must consume the same prefix",
            ));
        }
        // The tolerance's denominator and its binary exponent are distinct readings.
        let receiver_grain = crate::hnn::field::lattice_exponent(u128::from(phases.grain()), 1);
        let exponent = partition_exponent(receiver_grain, heard, epoch_index)?;
        let comparison_commit = forward.commit;
        let EpochForward {
            reads: forwards,
            mut prefixes,
            current,
            source,
            address,
            carried,
            charts,
            wall: forward_wall,
            tally: forward_tally,
            ..
        } = forward;
        // Preserve actual releases before the parallel returns consume their words.
        // The closing source lift is already one cell past the last producing word.
        let final_read = forwards.last().ok_or_else(|| {
            refusal("an observed epoch energy receipt needs its actual producing word")
        })?;
        let producing_current = final_read.ratio.current(&field)?;
        let before_form = crate::hnn::word::PowerForm::read(
            &field,
            &comparison_opening.constitution,
            &producing_current,
        )?;
        let mut energy_words: Vec<_> = forwards.iter().map(|read| read.energy.clone()).collect();
        let energy_chained = forwards
            .iter()
            .filter_map(|read| read.chained.clone())
            .collect();
        let producing_lift = producing_current.lift().to_vec();
        let closing_lift = current.lift().to_vec();
        if carried.as_ref().is_none_or(|carry| {
            energy_words
                .last()
                .is_none_or(|word| carry.change != word.change)
        }) {
            return Err(refusal(
                "the epoch energy commit reads its actual carried last crossing",
            ));
        }
        next.wall = forward_wall;
        next.tally = forward_tally;
        let observed: Option<Vec<_>> = if phases.observation_partition().is_some() {
            Some(
                forwards
                    .iter()
                    .map(|read| {
                        let mut addresses =
                            read.ratio.observed_addresses(&[])?.ok_or_else(|| {
                                refusal("an observed tree needs its own realized observation")
                            })?;
                        if addresses.len() != 1 {
                            return Err(refusal(
                                "one observed tree address belongs to each heard cell",
                            ));
                        }
                        Ok(addresses.remove(0))
                    })
                    .collect::<Result<_, HnnError>>()?,
            )
        } else {
            None
        };
        let addresses: Vec<_> = forwards
            .iter()
            .map(|read| {
                let mut addresses = read.ratio.addresses(&[])?;
                if addresses.len() != 1 {
                    return Err(refusal(
                        "one causal tree address belongs to each heard cell",
                    ));
                }
                Ok(addresses.remove(0))
            })
            .collect::<Result<_, HnnError>>()?;
        let opening_tree = next
            .constitution
            .landmarks(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
            .clone();
        let mut tree = opening_tree.clone();
        let trees = match &observed {
            Some(addresses) => {
                tree.receive_observed_arrivals(addresses, &classes[..consumed], phases.grain())?
            }
            None => tree.receive_arrivals(&addresses, &classes[..consumed], phases.grain())?,
        };
        let combined: Vec<_> = forwards
            .iter()
            .zip(&trees)
            .map(|(read, tree)| phases.combine(&read.faces, std::slice::from_ref(tree)))
            .collect::<Result<_, _>>()?;
        let all_combined = Faces {
            faces: combined
                .iter()
                .flat_map(|faces| faces.faces.iter().cloned())
                .collect(),
            logits: combined
                .iter()
                .flat_map(|faces| faces.logits.iter().cloned())
                .collect(),
        };
        let frozen_comparison = EpochComparison {
            combined: all_combined.clone(),
            trees: trees.clone(),
            targets: classes[..consumed].to_vec(),
            target_phases: forwards
                .iter()
                .enumerate()
                .map(|(at, read)| {
                    target_phases(
                        &field,
                        read.ratio.anchor(),
                        receiver,
                        &actual.part(at..at + 1)?,
                    )
                })
                .collect::<Result<_, HnnError>>()?,
        };
        let population = next
            .constitution
            .population(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
        let scored = crate::hnn::receiving::score(
            population,
            receiver,
            &all_combined,
            &trees,
            &classes[..consumed],
        )?;
        let mut deposits = Vec::with_capacity(consumed);
        let mut receiving_parts = Vec::with_capacity(consumed);
        let mut source_operands = Vec::with_capacity(consumed);
        let mut readings = Vec::with_capacity(consumed);
        let mut snapshots = Vec::with_capacity(requested.len());
        let physical = &next.constitution;
        let map = physical
            .receiving_map(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
        // Each return stops at its own opening. Its face partition and native transpose therefore
        // read only the fixed medium and its own kept word; ordered publication follows the join.
        let compare_preparation = compare_start.elapsed();
        let joined_start = Instant::now();
        let compared: Vec<ComparedRead> = forwards
            .into_par_iter()
            .zip(combined.into_par_iter())
            .enumerate()
            .map(|(at, (read, combined))| {
                let face_start = Instant::now();
                let target = actual.part(at..at + 1)?;
                let anchors = target_phases(&field, read.ratio.anchor(), receiver, &target)?;
                let holon = HolonRatio::compare(combined.clone(), &[classes[at]], &anchors)?;
                let (covector, released) = holon.epoch_covector(exponent)?;
                let masses = holon.faces().faces[0].odometer_masses()?;
                // These three series are defined at the receiving comparison itself. There is
                // one retained RHS upstream; no return is split or partitioned a second time.
                let descent = covector.descent(0);
                let mut positive = vec![Rat::zero(); descent.len()];
                let mut foil = vec![Rat::zero(); descent.len()];
                let mut phase = vec![Rat::zero(); descent.len()];
                positive[2 * classes[at]] = Rat::one();
                for row in 0..descent.len() {
                    if row % 2 == 0 { foil[row] = &positive[row] - &descent[row]; }
                    else { phase[row] = descent[row].clone(); }
                }
                let word_charts = read.word.charts();
                let tube_passages = read.word.tube_passages()?;
                let face_partition_wall = face_start.elapsed();
                let pull_back_start = Instant::now();
                let back = read.word.return_at(&field, execution, &covector, map, &phases)?;
                let pull_back_wall = pull_back_start.elapsed();
                let compose_start = Instant::now();
                let deposit = match consumer {
                    ReturnConsumer::Epoch => compose_epoch_contribution(
                        &field, physical, &read.ratio, &read.opening, &back,
                        &[classes[at]], &scored.steps[at..at + 1],
                    )?,
                    ReturnConsumer::Word => compose(
                        &field, physical, &read.ratio, &read.opening, &back,
                        &[classes[at]], &scored.steps[at..at + 1],
                    )?.1,
                };
                let compose_wall = compose_start.elapsed();
                let records_start = Instant::now();
                // The adapter reconstructs the deposit, so attach the actual
                // producing passage only after its receiving masses are kept.
                let deposit = with_receiving_masses(deposit, receiver, &masses, deposition_scope)?
                    .with_passages(tube_passages);
                if deposit.commit() != comparison_commit {
                    return Err(refusal(
                        "every observed epoch return belongs to its one producing material",
                    ));
                }
                let receiving_parts = deposit.linear().iter()
                    .filter(|step| step.locus == LinearLocus::Receiving(receiver))
                    .flat_map(|step| &step.samples)
                    .map(|sample| {
                        if sample.covector != descent {
                            return Err(refusal("the receiving series and native return share the same retained covector"));
                        }
                        Ok(EpochReceivingRecord {
                            feature: sample.feature.clone(), positive: positive.clone(),
                            foil: foil.clone(), phase: phase.clone(),
                        })
                    }).collect::<Result<_, HnnError>>()?;
                Ok(ComparedRead {
                    ratio: read.ratio,
                    opening: read.opening,
                    prediction: read.faces,
                    combined,
                    released: released.into_iter().next().ok_or_else(|| {
                        refusal("one released magnitude row belongs to the aperture-one comparison")
                    })?,
                    deposit,
                    receiving_parts,
                    worker_times: [face_partition_wall, pull_back_wall, compose_wall, records_start.elapsed()],
                    word_charts,
                })
            })
            .collect::<Result<_, HnnError>>()?;
        let return_join = joined_start.elapsed();
        let mut return_worker_sums = [Duration::ZERO; 4];
        for read in &compared {
            for (sum, elapsed) in return_worker_sums.iter_mut().zip(read.worker_times) {
                *sum += elapsed;
            }
        }
        let ordered_start = Instant::now();
        for (at, read) in compared.into_iter().enumerate() {
            source_operands.push(read.ratio.moment().clone());
            deposits.push(read.deposit);
            receiving_parts.extend(read.receiving_parts);
            next.ledger.arrive(scored.model[at].clone(), 1);
            let before = read.ratio.current(&field)?;
            let cell_placement = placement
                .map(|placed| placed.part(at..at + 1))
                .transpose()?;
            next_crib.push(
                &field,
                &before,
                classes[at],
                cell_placement.as_ref(),
                field.crib().window,
            )?;
            let arrived = Arrived {
                ratio: read.ratio,
                targets: vec![classes[at]],
                opening: read.opening,
            };
            next.arrived = Some(arrived.clone());
            if let Some(mut prefix) = prefixes.remove(&(at + 1)) {
                let prefix_start = Instant::now();
                let mut prefix_tree = opening_tree.clone();
                match &observed {
                    Some(addresses) => {
                        prefix_tree.receive_observed_arrivals(
                            &addresses[..at + 1],
                            &classes[..at + 1],
                            phases.grain(),
                        )?;
                    }
                    None => {
                        prefix_tree.receive_arrivals(
                            &addresses[..at + 1],
                            &classes[..at + 1],
                            phases.grain(),
                        )?;
                    }
                }
                prefix.constitution = next.constitution.observed_epoch_prefix(
                    receiver,
                    prefix_tree,
                    &scored.steps[..at + 1],
                )?;
                if let Some(founding) = &mut prefix.founding {
                    for &class in &classes[..at + 1] {
                        founding.receive(class)?;
                    }
                }
                prefix.ledger = next.ledger.clone();
                prefix.arrived = Some(arrived);
                prefix.observed_epoch_ingress = Some((
                    receiver,
                    epoch_index
                        .checked_add(
                            u64::try_from(
                                &prefix.current.lift()[receiver]
                                    - &resident.current.lift()[receiver],
                            )
                            .map_err(|_| HnnError::CountOverflow)?,
                        )
                        .ok_or(HnnError::CountOverflow)?,
                ));
                let mut prefix_crib = next_crib.clone();
                if prefix.aeon.awaiting {
                    // A fork at the joint carry closes its own old-medium passage before any
                    // draw. It receives none of the life's staged covectors or closing deposit.
                    let boundary = PairedObservation::admit(&field, &prefix.constitution, pairing)?;
                    let closing = prefix_crib.closing(&field, &boundary, field.crib().window)?;
                    let family = prefix.admitted.clone();
                    close_and_locate(self, &mut prefix, &family, &closing)?;
                    prefix_crib.reopen();
                }
                snapshots.push((at + 1, prefix, prefix_crib));
                prefix_forks += prefix_start.elapsed();
            }
            readings.push(ObservedEpochCellReceipt {
                prediction: read.prediction,
                combined: read.combined,
                code: scored.model[at].clone(),
                tree: Some(scored.tree[at].clone()),
                scored_face: scored.face_readings[at].clone(),
                released: read.released,
                word_charts: read.word_charts,
            });
        }
        let ordered_publication = ordered_start.elapsed().saturating_sub(prefix_forks);
        let ticks: Vec<u64> = current
            .lift()
            .iter()
            .zip(resident.current.lift())
            .map(|(after, before)| {
                u64::try_from(after - before).map_err(|_| HnnError::CountOverflow)
            })
            .collect::<Result<_, _>>()?;
        next.current = current;
        next.moments.insert(moment, source);
        next.address = address;
        next.carried = carried;
        next.carried_error = None;
        next.charts = charts;
        next.aeon.cells = next
            .aeon
            .cells
            .checked_add(heard)
            .ok_or(HnnError::CountOverflow)?;
        next.aeon.keys_admitted = false;
        next.aeon.awaiting = carry_out;
        next.observed_epoch_ingress = Some((
            receiver,
            epoch_index
                .checked_add(ticks[receiver])
                .ok_or(HnnError::CountOverflow)?,
        ));
        next.observed_epoch_terminal = terminal_partial;
        if let Some(founding) = &mut next.founding {
            for &class in &classes[..consumed] {
                founding.receive(class)?;
            }
        }
        let retention = next.retention();
        let pair_speed = |ring: usize,
                          offset: usize,
                          pair: &crate::hnn::moment::PairPort,
                          direction: [&[Vec<Rat>]; 3]| {
            pair_ray_speed_sum(&field, &source_operands, ring, offset, pair, direction)
        };
        let compare_return_compose_batch = compare_start.elapsed().saturating_sub(prefix_forks);
        let deposit_start = Instant::now();
        let mut deposit_subphases = Vec::new();
        let mut previous_phase = deposit_start;
        let mut observe_deposit = |phase: crate::hnn::constitution::epoch::EpochDepositPhase| {
            let now = Instant::now();
            deposit_subphases.push((format!("{phase:?}"), now.duration_since(previous_phase)));
            previous_phase = now;
        };
        let shared_normals = matches!(
            deposition_scope,
            ObservedEpochDepositionScope::NormalMaps
                | ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
        );
        let mut grain_target_deferred = None;
        let mut normal_stage = if shared_normals {
            let stage =
                crate::hnn::constitution::epoch::ObservedNormalEpochStage::new(
                    &comparison_opening.constitution,
                    &deposits,
                    receiver,
                    field.ring(receiver).period(),
                    heard,
                    heard,
                    epoch_index,
                    exponent,
                    &retention,
                    tree.clone(),
                    &pair_speed,
                    &receiving_parts,
                    execution,
                    deposition_scope
                        == ObservedEpochDepositionScope::NormalMapsAndChannelDissipation,
                )?;
            let plan = if self.refining {
                crate::hnn::constitution::epoch::ObservedChannelGrainPlan::at_section(
                    &field, &retention, receiver, epoch_index,
                    next.observed_epoch_ingress.expect("set above").1,
                )?
            } else { None };
            if self.refining && plan.is_none()
                && next.observed_epoch_ingress.expect("set above").1 > epoch_index {
                grain_target_deferred = Some(crate::hnn::constitution::EpochChannelGrainDeferralReading {
                    receiver, ingress_before: epoch_index,
                    ingress_after: next.observed_epoch_ingress.expect("set above").1,
                    reason: "refining grain comparison inside ln 2 enclosure; no target staged this epoch",
                });
            }
            Some(match plan { Some(plan) => stage.with_channel_grain(plan)?, None => stage })
        } else {
            None
        };
        let mut stage =
            |scope, without_grain, observe: &mut dyn FnMut(crate::hnn::constitution::epoch::EpochDepositPhase)| {
                if let Some(stage) = normal_stage.as_mut() {
                    if without_grain { stage.without_channel_grain(scope)?; }
                    stage.stage(scope, observe)
                } else {
                    comparison_opening
                        .constitution
                        .stage_observed_epoch_with_evidence(
                            &deposits,
                            receiver,
                            field.ring(receiver).period(),
                            heard,
                            heard,
                            epoch_index,
                            exponent,
                            &retention,
                            tree.clone(),
                            &pair_speed,
                            &receiving_parts,
                            observe,
                            execution,
                            scope,
                        )
                }
            };
        let mut probe_subphases = Vec::new();
        let mut probe_candidate =
            |attempt, candidate: &crate::hnn::constitution::epoch::StagedEpochCandidate| {
                let readmission_start = Instant::now();
                let mut opening = comparison_opening.clone();
                opening.constitution =
                    candidate.comparison_material(&comparison_opening.constitution)?;
                let boundary = PairedObservation::admit(&field, &opening.constitution, pairing)?;
                let cells = match placement {
                    Some(placed) => {
                        boundary.encode_placed(&classes[..consumed], &placed.part(0..consumed)?)?
                    }
                    None => boundary.encode(&classes[..consumed])?,
                };
                probe_subphases.push((attempt, "source_readmission", readmission_start.elapsed()));
                let forward_start = Instant::now();
                let forward = if selected_forward {
                    self.read_epoch_probe_at_cuts_with_execution(
                        &opening,
                        &moment,
                        &phases,
                        &cells,
                        &[],
                        execution,
                    )?
                } else {
                    self.read_epoch_probe_at_cuts(&opening, &moment, &phases, &cells, &[])?
                };
                if forward.consumed != consumed
                    || forward.current != next.current
                    || forward.carry_out != carry_out
                {
                    return Err(refusal(
                        "the candidate probe keeps the original source and receiving clocks",
                    ));
                }
                probe_subphases.push((attempt, "forward_and_clock_check", forward_start.elapsed()));
                let tree_start = Instant::now();
                // Rebuild the prequential schedule from the ORIGINAL tree,
                // never the tree already updated by the staged candidate.
                let mut candidate_tree = opening_tree.clone();
                let trees = if phases.observation_partition().is_some() {
                    let addresses = forward
                        .reads
                        .iter()
                        .map(|read| {
                            let mut addresses =
                                read.ratio.observed_addresses(&[])?.ok_or_else(|| {
                                    refusal("the epoch probe keeps its observed addresses")
                                })?;
                            if addresses.len() != 1 {
                                return Err(refusal(
                                    "one probe tree address belongs to each heard cell",
                                ));
                            }
                            Ok(addresses.remove(0))
                        })
                        .collect::<Result<Vec<_>, HnnError>>()?;
                    candidate_tree.receive_observed_arrivals(
                        &addresses,
                        &classes[..consumed],
                        phases.grain(),
                    )?
                } else {
                    let addresses = forward
                        .reads
                        .iter()
                        .map(|read| {
                            let mut addresses = read.ratio.addresses(&[])?;
                            if addresses.len() != 1 {
                                return Err(refusal(
                                    "one probe tree address belongs to each heard cell",
                                ));
                            }
                            Ok(addresses.remove(0))
                        })
                        .collect::<Result<Vec<_>, HnnError>>()?;
                    candidate_tree.receive_arrivals(
                        &addresses,
                        &classes[..consumed],
                        phases.grain(),
                    )?
                };
                probe_subphases.push((attempt, "tree_schedule", tree_start.elapsed()));
                let combine_start = Instant::now();
                let mut combined = Faces {
                    faces: Vec::new(),
                    logits: Vec::new(),
                };
                for (at, (read, tree)) in forward.reads.iter().zip(&trees).enumerate() {
                    let target = cells.part(at..at + 1)?;
                    if target_phases(&field, read.ratio.anchor(), receiver, &target)?
                        != frozen_comparison.target_phases[at]
                    {
                        return Err(refusal(
                            "the epoch probe keeps the original target phase and anchor",
                        ));
                    }
                    let face = phases.combine(&read.faces, std::slice::from_ref(tree))?;
                    combined.faces.extend(face.faces);
                    combined.logits.extend(face.logits);
                }
                probe_subphases.push((attempt, "target_phase_and_combine", combine_start.elapsed()));
                let objective_start = Instant::now();
                let reading = frozen_comparison.evaluate(
                    comparison_opening
                        .constitution
                        .population(receiver)
                        .ok_or(HnnError::MissingReceivingMap { ring: receiver })?,
                    receiver,
                    &combined,
                    &trees,
                );
                probe_subphases.push((attempt, "objective", objective_start.elapsed()));
                reading
                // forward and its counterfactual reception end die here.
            };
        let mut comparison = None;
        let mut joint_eligible = shared_normals;
        let mut publication_attempt = EpochStageAttempt::Whole;
        let mut joint_attempted = false;
        let mut joint_directions = Vec::new();
        let mut joint_comparison = None;
        let mut joint_refusal = None;
        let mut joint_stage_refusal = None;
        let mut joint_probe_state = ObservedEpochProbeState::SealNotFormed;
        let mut whole_refusal = None;
        let mut whole_stage_refusal = None;
        let mut probe_state = ObservedEpochProbeState::SealNotFormed;
        let mut whole_probe = None;
        let mut joint_stage = None;
        let mut joint_probe = None;
        let mut receiving_only_stage = None;
        let mut grain_restage = None;
        let mut whole_stage_elapsed = std::time::Duration::ZERO;
        let mut retry_without_grain = false;
        let whole = loop {
            let whole_stage_start = Instant::now();
            let whole_candidate = stage(EpochCandidateScope::Whole, retry_without_grain, &mut observe_deposit);
            whole_stage_elapsed += whole_stage_start.elapsed();
            let grain = match &whole_candidate {
                Ok(candidate) => candidate.channel_grain_rebase(),
                Err(failure) => failure.channel_grain.clone().filter(|grain|
                    grain.contacts.iter().any(|contact| contact.levels > 0)),
            };
            let retry_permitted = match &whole_candidate {
                Ok(_) => true,
                Err(failure) => grain_failure_restage_permitted(EpochStageAttempt::Whole, failure),
            };
            let admitted = match whole_candidate {
                Ok(candidate) if !candidate.requires_comparison() => {
                    probe_state = ObservedEpochProbeState::SealedNoProbeRequired;
                    let outcome = if candidate.has_physical_motion() {
                        ObservedEpochOutcome::Whole
                    } else {
                        ObservedEpochOutcome::Neutral
                    };
                    Some((candidate.admit_receiving()?, outcome))
                }
                Ok(candidate) => {
                    probe_state = ObservedEpochProbeState::ProbeFailed;
                    // A source port is learner material. Re-admit that port under
                    // the SAME exterior class codec, pairing and placement; an old
                    // PairedObservation is correctly refused after E changes.
                    let probe_start = Instant::now();
                    let probe = probe_candidate(EpochStageAttempt::Whole, &candidate);
                    whole_probe = Some(probe_start.elapsed());
                    match probe {
                        Ok(reading) => {
                            probe_state = ObservedEpochProbeState::FiniteComparisonExecuted;
                            let neutral = reading.unchanged || reading.objective_equal();
                            let admitted = if neutral {
                                Some(candidate.admit_neutral())
                            } else {
                                candidate.admit_change(&reading.objective_change)
                            };
                            if admitted.is_none() {
                                whole_refusal = Some(reading.unresolved_reason().to_string());
                            }
                            comparison = Some(reading);
                            admitted.map(|publication| {
                                (
                                    publication,
                                    if neutral {
                                        ObservedEpochOutcome::Neutral
                                    } else {
                                        ObservedEpochOutcome::Whole
                                    },
                                )
                            })
                        }
                        Err(error) => {
                            // Unknown executor/identity/arithmetic failures do not select another
                            // NormalMaps proposal. Known native mathematical domain refusals may.
                            if shared_normals && !receiving_restage_permitted(&error) {
                                return Err(error);
                            }
                            joint_eligible = shared_normals && receiving_restage_permitted(&error);
                            whole_refusal = Some(error.to_string());
                            None
                        }
                    }
                }
                Err(failure) => {
                    stage_refused(EpochStageAttempt::Whole, &failure.evidence);
                    // Shared zero-move absorption cannot fabricate a missing fresh gain. Keep the
                    // original native error if preparation failed before it produced those gains.
                    if shared_normals && !failure.normal_inputs_prepared {
                        return Err(failure.error);
                    }
                    if !receiving_restage_permitted(&failure.error) {
                        return Err(failure.error);
                    }
                    whole_refusal = Some(failure.error.to_string());
                    whole_stage_refusal = Some(failure.evidence);
                    None
                }
            };
            if admitted.is_none() && retry_permitted && grain_restage.is_none() {
                if let Some(grain) = grain {
                    grain_restage = Some(crate::hnn::constitution::EpochChannelGrainRestageReading {
                        grain, refused_attempt: EpochStageAttempt::Whole,
                        stage_refusal: whole_stage_refusal.take(),
                        probe_refusal: whole_refusal.take(),
                    });
                    retry_without_grain = true;
                    probe_state = ObservedEpochProbeState::SealNotFormed;
                    comparison = None;
                    whole_probe = None;
                    continue;
                }
            }
            break admitted;
        };
        let whole_stage = Some(whole_stage_elapsed);
        let mut joint_admitted = None;
        if whole.is_none() && joint_eligible {
            joint_attempted = true;
            let mut retry_without_grain = false;
            loop {
                let stage_start = Instant::now();
                let candidate = stage(EpochCandidateScope::Joint, retry_without_grain, &mut observe_deposit);
                *joint_stage.get_or_insert(std::time::Duration::ZERO) += stage_start.elapsed();
                let grain = match &candidate {
                    Ok(candidate) => candidate.channel_grain_rebase(),
                    Err(failure) => failure.channel_grain.clone().filter(|grain|
                        grain.contacts.iter().any(|contact| contact.levels > 0)),
                };
                let retry_permitted = match &candidate {
                    Ok(_) => true,
                    Err(failure) => grain_failure_restage_permitted(EpochStageAttempt::Joint, failure),
                };
                match candidate {
                    Ok(candidate) if !candidate.requires_comparison() => {
                        // Zero/projected-zero upstream motion uses the established held-map
                        // receiving successor below. No finite probe is fabricated for it.
                        joint_directions = candidate.joint_directions();
                        joint_probe_state = ObservedEpochProbeState::SealedNoProbeRequired;
                    }
                    Ok(candidate) => {
                        joint_directions = candidate.joint_directions();
                        joint_probe_state = ObservedEpochProbeState::ProbeFailed;
                        let probe_start = Instant::now();
                        let probe = probe_candidate(EpochStageAttempt::Joint, &candidate);
                        joint_probe = Some(probe_start.elapsed());
                        match probe {
                            Ok(reading) => {
                                joint_probe_state = ObservedEpochProbeState::FiniteComparisonExecuted;
                                let neutral = reading.unchanged || reading.objective_equal();
                                let admitted = if neutral {
                                    Some(candidate.admit_neutral())
                                } else {
                                    candidate.admit_change(&reading.objective_change)
                                };
                                if admitted.is_none() {
                                    joint_refusal = Some(reading.unresolved_reason().to_string());
                                }
                                joint_comparison = Some(reading);
                                joint_admitted = admitted.map(|publication| {
                                    (
                                        publication,
                                        if neutral {
                                            ObservedEpochOutcome::Neutral
                                        } else {
                                            ObservedEpochOutcome::Joint
                                        },
                                    )
                                });
                            }
                            Err(error) => {
                                if !receiving_restage_permitted(&error) {
                                    return Err(error);
                                }
                                joint_refusal = Some(error.to_string());
                            }
                        }
                    }
                    Err(failure) => {
                        stage_refused(EpochStageAttempt::Joint, &failure.evidence);
                        if !failure.normal_inputs_prepared || !joint_restage_permitted(&failure) {
                            return Err(failure.error);
                        }
                        joint_directions = failure
                            .evidence
                            .readings
                            .iter()
                            .filter_map(|reading| {
                                if let EpochStageValue::JointDirection(direction) = &reading.value {
                                    Some(direction.clone())
                                } else {
                                    None
                                }
                            })
                            .collect();
                        joint_refusal = Some(failure.error.to_string());
                        joint_stage_refusal = Some(failure.evidence);
                    }
                }
                if joint_admitted.is_none() && retry_permitted && grain_restage.is_none()
                    && (joint_refusal.is_some() || joint_stage_refusal.is_some()) {
                    if let Some(grain) = grain {
                        grain_restage = Some(crate::hnn::constitution::EpochChannelGrainRestageReading {
                            grain, refused_attempt: EpochStageAttempt::Joint,
                            stage_refusal: joint_stage_refusal.take(),
                            probe_refusal: joint_refusal.take(),
                        });
                        retry_without_grain = true;
                        joint_probe_state = ObservedEpochProbeState::SealNotFormed;
                        joint_comparison = None;
                        joint_probe = None;
                        joint_directions.clear();
                        continue;
                    }
                }
                break;
            }
            if joint_admitted.is_some() {
                publication_attempt = EpochStageAttempt::Joint;
            }
        }
        let ((material, mut deposit), outcome) = match whole.or(joint_admitted) {
            Some(admitted) => admitted,
            None => {
                publication_attempt = EpochStageAttempt::ReceivingOnly;
                let stage_start = Instant::now();
                let candidate = stage(EpochCandidateScope::ReceivingOnly, false, &mut observe_deposit);
                receiving_only_stage = Some(stage_start.elapsed());
                let receiving = match candidate {
                    Ok(candidate) => candidate,
                    Err(failure) => {
                        stage_refused(EpochStageAttempt::ReceivingOnly, &failure.evidence);
                        return Err(failure.error);
                    }
                };
                let outcome = if receiving.has_physical_motion() {
                    ObservedEpochOutcome::ReceivingOnly
                } else {
                    ObservedEpochOutcome::Neutral
                };
                (receiving.admit_receiving()?, outcome)
            }
        };
        if let Some(deferred) = grain_target_deferred {
            deposit.epoch.as_mut().ok_or_else(|| refusal("an observed epoch keeps its grain deferral reading"))?
                .channel_grain_deferred = Some(deferred);
        }
        deposit.epoch.as_mut().ok_or_else(|| refusal("an observed epoch keeps its grain restage reading"))?
            .channel_grain_restaged = grain_restage;
        // Work belongs to the same LAST PRODUCING cut on both sides of the
        // admitted material change. Reading next.current here would mix the
        // final source/reference crossing into the constitutive work.
        let after_form = crate::hnn::word::PowerForm::read(&field, &material, &producing_current)?;
        let physical_form_changed = before_form != after_form;
        let last = energy_words
            .last_mut()
            .ok_or_else(|| refusal("an epoch deposit has its producing physical balance"))?;
        if before_form.power(&last.change)? != last.end
            || before_form.resonator_power(&last.change)? != last.resonator_end
        {
            return Err(refusal(
                "the physical deposit keeps the last word's producing form and crossing",
            ));
        }
        last.commit_held(&before_form, &after_form)?;
        let deposition_work = last
            .commit
            .as_ref()
            .ok_or_else(|| refusal("the physical deposit retains its executed held-momentum work"))?
            .deposition
            .clone();
        if deposition_scope == ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
            && !deposition_work.is_zero()
        {
            return Err(refusal(
                "a D-only physical epoch may publish only with exactly zero held deposition work",
            ));
        }
        let energy = ObservedEpochEnergy {
            words: energy_words,
            chained: energy_chained,
            producing_lift,
            closing_lift,
            physical_form_changed,
            deposition_work,
        };
        if !energy.closes() {
            return Err(refusal(
                "the admitted epoch retains its closing physical energy series",
            ));
        }
        observe_deposit(crate::hnn::constitution::epoch::EpochDepositPhase::Publication);
        let grouped_deposit = deposit_start.elapsed();
        next.wall.deposited += grouped_deposit;
        let reread_start = Instant::now();
        let arrived = next
            .arrived
            .as_ref()
            .ok_or_else(|| refusal("an observed epoch keeps its final arrived occurrence"))?;
        let (reread, chart_readings) = arrived.code_length(&field, &material, &mut next.charts)?;
        let final_arrived_reread = reread_start.elapsed();
        next.wall.reread += final_arrived_reread;
        next.tally.read(&chart_readings);
        next.ledger.deposit(reread)?;
        next.constitution = material;
        next.forget_kept_reads();
        let precision_start = Instant::now();
        let before_commit = next.constitution.commit();
        let before_exponent = next
            .constitution
            .lattice(Locus::ReceivingMap(receiver))?
            .exponent();
        let balance_before = next.ledger.balance().clone();
        let features: Vec<_> = deposits
            .iter()
            .flat_map(|deposit| deposit.linear())
            .filter(|step| step.locus == LinearLocus::Receiving(receiver))
            .flat_map(|step| step.samples.iter().map(|sample| sample.feature.clone()))
            .collect();
        let event =
            next.constitution
                .receiving_precision_event(receiver, &features, phases.tolerance())?;
        if let Some(event) = &event {
            next.publish_receiving_precision(event)?;
        }
        let precision = ObservedPrecisionReceipt {
            checked: true,
            features,
            event,
            before_commit,
            after_commit: next.constitution.commit(),
            before_exponent,
            after_exponent: next
                .constitution
                .lattice(Locus::ReceivingMap(receiver))?
                .exponent(),
            balance_before,
            balance_after: next.ledger.balance().clone(),
        };
        let close = if carry_out {
            let boundary = PairedObservation::admit(&field, &next.constitution, pairing)?;
            let closing = next_crib.closing(&field, &boundary, field.crib().window)?;
            let family = next.admitted.clone();
            let closed = close_and_locate(self, &mut next, &family, &closing)?;
            next_crib.reopen();
            Some(closed)
        } else {
            None
        };
        let precision_close = precision_start.elapsed();
        let wall = ObservedEpochWallTimes {
            forward_batch,
            compare_return_compose_batch,
            grouped_deposit,
            whole_stage,
            whole_probe,
            joint_stage,
            joint_probe,
            receiving_only_stage,
            probe_subphases,
            final_arrived_reread,
            precision_close,
            prefix_forks,
            compare_preparation,
            return_join,
            ordered_publication,
            return_worker_sums,
            deposit_subphases,
        };
        let cells = next
            .moments
            .get(&moment)
            .ok_or_else(|| refusal("the observed moment remains open at the crossing"))?
            .cells();
        *resident = next;
        *crib = next_crib;
        Ok(ObservedEpochReceipt {
            consumed,
            cells,
            comparison_commit,
            partition_exponent: exponent,
            closed_section,
            terminal_partial,
            carry_out,
            reads: readings,
            deposit,
            energy,
            outcome,
            deposition_scope,
            comparison,
            whole_refusal,
            whole_stage_refusal,
            probe_state,
            publication_attempt,
            joint_attempted,
            joint_directions,
            joint_comparison,
            joint_refusal,
            joint_stage_refusal,
            joint_probe_state,
            precision,
            close,
            prefixes: snapshots,
            wall,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::tests::learning::chain_declaration;
    use crate::ratio::rat;

    /// Durations are exterior observations, so the control checks attempted-call presence
    /// and disjoint wall containment, never an arbitrary minimum elapsed time.
    fn assert_rung_wall_receipt(receipt: &ObservedEpochReceipt) {
        let wall = &receipt.wall;
        let probed = |state| {
            matches!(
                state,
                ObservedEpochProbeState::ProbeFailed
                    | ObservedEpochProbeState::FiniteComparisonExecuted
            )
        };
        assert!(wall.whole_stage.is_some());
        assert_eq!(wall.whole_probe.is_some(), probed(receipt.probe_state));
        assert_eq!(wall.joint_stage.is_some(), receipt.joint_attempted);
        assert_eq!(wall.joint_probe.is_some(), probed(receipt.joint_probe_state));
        assert_eq!(
            wall.receiving_only_stage.is_some(),
            receipt.publication_attempt == EpochStageAttempt::ReceivingOnly
        );
        for (attempt, enclosing, state) in [
            (EpochStageAttempt::Whole, wall.whole_probe, receipt.probe_state),
            (EpochStageAttempt::Joint, wall.joint_probe, receipt.joint_probe_state),
        ] {
            let parts: Vec<_> = wall.probe_subphases.iter()
                .filter(|(at, _, _)| *at == attempt).collect();
            let sum: Duration = parts.iter().map(|(_, _, duration)| *duration).sum();
            assert!(sum <= enclosing.unwrap_or_default());
            if enclosing.is_none() { assert!(parts.is_empty()); }
            if state == ObservedEpochProbeState::FiniteComparisonExecuted {
                assert_eq!(parts.iter().map(|(_, phase, _)| *phase).collect::<Vec<_>>(), [
                    "source_readmission", "forward_and_clock_check", "tree_schedule",
                    "target_phase_and_combine", "objective",
                ]);
            }
        }
        assert!(
            [
                wall.whole_stage,
                wall.whole_probe,
                wall.joint_stage,
                wall.joint_probe,
                wall.receiving_only_stage,
            ]
            .into_iter()
            .flatten()
            .sum::<Duration>()
                <= wall.grouped_deposit
        );
    }

    fn opening() -> (Reference, Resident, ObservedCrib, PairingDeclaration) {
        let mut declaration = chain_declaration(1 << 16);
        declaration.receivers[0].aperture = 1;
        declaration.rings[2] = declaration.rings[1].clone();
        declaration.rings[2].lock.clear();
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        let free = ExactRatMatrix::shaped(
            8,
            4,
            (0..8)
                .map(|row| {
                    (0..4)
                        .map(|column| {
                            if (row == 2 && column == 0) || (row == 3 && column == 2) {
                                rat(1, 32)
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let source = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &source).unwrap();
        let material = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, source, carrier.symmetry())
            .unwrap();
        let reference = Reference::new(16, 1 << 40);
        let resident = reference
            .mount_with(&field, &Current::at_rest(&field), material)
            .unwrap();
        (reference, resident, ObservedCrib::new(0), pairing)
    }

    #[derive(Clone)]
    struct ProbeOpening {
        commit: u64,
        anchor: Vec<BigInt>,
        source: SourceMoment,
        opening: WordOpening,
        charts: Charts,
        material: Constitution,
        end: crate::hnn::word::ReceptionCarry,
    }

    #[derive(Default)]
    struct ProbeExecution {
        forwards: std::sync::Mutex<Vec<ProbeOpening>>,
        flows: std::sync::Mutex<
            Vec<(
                LinearLocus,
                crate::hnn::constitution::EpochRecordFlowReading,
            )>,
        >,
    }

    impl ObservedEpochExecution for ProbeExecution {
        fn forward(
            &self,
            field: &Field,
            material: &Constitution,
            ratio: &PendingRatio,
            charts: &mut Charts,
            opening: &WordOpening,
        ) -> Result<ObservedEpochForwardWord, HnnError> {
            let before_charts = charts.clone();
            let forward =
                HostObservedEpochExecution.forward(field, material, ratio, charts, opening)?;
            self.forwards.lock().unwrap().push(ProbeOpening {
                commit: material.commit(),
                anchor: ratio.anchor().to_vec(),
                source: ratio.moment().clone(),
                opening: opening.clone(),
                charts: before_charts,
                material: material.clone(),
                end: forward.reception_end.clone().absorbed(Absorption::Nothing),
            });
            Ok(forward)
        }
        fn pull_back(
            &self,
            word: Word<'_>,
            covector: &crate::hnn::ratio::RatioCovector,
            map: &ExactRatMatrix,
            phases: &ReceivingPhases,
        ) -> Result<WordReturn, HnnError> {
            HostObservedEpochExecution.pull_back(word, covector, map, phases)
        }
        fn aggregate_records(
            &self,
            locus: LinearLocus,
            rows: usize,
            columns: usize,
            receiver_grain: u32,
            epoch_cells: u64,
            epoch: u64,
            heard_cells: u64,
            records: &[crate::hnn::constitution::EpochProducerRecordReading],
        ) -> Result<crate::hnn::constitution::EpochRecordFlowReading, HnnError> {
            let reading = HostObservedEpochExecution.aggregate_records(
                locus,
                rows,
                columns,
                receiver_grain,
                epoch_cells,
                epoch,
                heard_cells,
                records,
            )?;
            self.flows.lock().unwrap().push((locus, reading.clone()));
            Ok(reading)
        }
    }

    /// Check the actual executor-produced sufficient statistics, rather than infer learning
    /// from a map change or a bit count. Discarded rungs never add the batch a second time.
    fn assert_shared_normal_absorption(
        before: &Constitution,
        after: &Constitution,
        receipt: &ObservedEpochReceipt,
        execution: &ProbeExecution,
        receiver: usize,
        period: u64,
    ) {
        use crate::hnn::constitution::epoch::{EpochArray, EpochFlow, EpochLaw};
        let epoch = receipt.deposit.epoch.as_ref().unwrap();
        let normal = |material: &Constitution, kind| match kind {
            LinearLocus::SourcePort(ring) => material.source_law(ring).unwrap().clone(),
            LinearLocus::Contrast(ring) => material.contrast_law(ring).clone(),
            LinearLocus::Receiving(ring) => material.receiving_law(ring).unwrap().clone(),
        };
        let array = |series: &crate::hnn::constitution::EpochSeriesReading| {
            EpochArray::with_row_divisors(
                series.rows,
                series.columns,
                series.exponent,
                series.numerators.clone(),
                series.row_odd_divisors.clone(),
            )
            .unwrap()
        };
        let flows = execution.flows.lock().unwrap();
        for locus in &epoch.loci {
            let old_normal = normal(before, locus.locus);
            let new_normal = normal(after, locus.locus);
            let old = match old_normal.epoch_law() {
                Some(law) => law.clone(),
                None => {
                    let law =
                        EpochLaw::from_normal(&old_normal, epoch.receiver_partition_bits).unwrap();
                    if locus.locus == LinearLocus::Receiving(receiver) {
                        let rows = (1..law.map.rows).step_by(2).collect::<Vec<_>>();
                        law.with_phase_rows(&rows, period).unwrap()
                    } else {
                        law
                    }
                }
            };
            let matching: Vec<_> = flows
                .iter()
                .filter(|(kind, _)| *kind == locus.locus)
                .collect();
            assert_eq!(
                matching.len(),
                1,
                "the actual flow is prepared once across all rungs"
            );
            let flow = &matching[0].1;
            let flow = EpochFlow {
                gram: array(&flow.gram),
                covector: array(&flow.covector),
                support: flow.support.clone(),
                partitions: Vec::new(),
                cells: epoch.heard_cells,
                partition_cells: epoch.declared_cells,
                records: flow.records,
                partition_exponent: epoch.partition_exponent,
                receiver_grain: epoch.receiver_partition_bits,
                epoch: epoch.actual_receiving_ingress,
            };
            let paired = old_normal
                .symmetry()
                .map(|symmetry| flow.paired(symmetry).unwrap());
            let flow = paired.as_ref().unwrap_or(&flow);
            let new = new_normal.epoch_law().unwrap();
            let h_plus = old.gram.add(&flow.gram).unwrap();
            let p = new.map.subtract(&old.map).unwrap();
            let gamma = EpochArray::from_dyadic_scalar(&locus.gamma).unwrap();
            let expected_r = old
                .news
                .add(&flow.covector.scalar_product(&gamma).unwrap())
                .unwrap()
                .subtract(&p.multiply(&h_plus).unwrap())
                .unwrap();
            assert_eq!(new.gram, h_plus);
            assert_eq!(new.news, expected_r);
            assert_eq!(new.crossings, old.crossings + 1);
            if receipt.outcome == ObservedEpochOutcome::ReceivingOnly
                && locus.locus != LinearLocus::Receiving(receiver)
            {
                assert_eq!(
                    new_normal.map(),
                    old_normal.map(),
                    "upstream physical map is held"
                );
            }
        }
        assert_eq!(epoch.loci.len(), flows.len());
    }

    #[test]
    fn grain_restage_keeps_normal_whole_refusal_and_unknown_errors_fatal() {
        let mut failure = crate::hnn::constitution::epoch::EpochStageFailure {
            error: HnnError::Unadmitted { reason: "a moving actual epoch ray must descend its contemporary comparison" },
            evidence: EpochStageRefusal::at("actual_normal_face", EpochStageCondition::ActualRayAlignment,
                "actual alignment", Some(Locus::SourcePort(0)), Some(crate::hnn::constitution::Family::Map)),
            normal_inputs_prepared: true, channel_grain: None,
        };
        assert!(!grain_failure_restage_permitted(EpochStageAttempt::Whole, &failure));
        failure.evidence.locus = Some(Locus::Channel(1));
        failure.evidence.family = Some(crate::hnn::constitution::Family::Factor(2));
        assert!(grain_failure_restage_permitted(EpochStageAttempt::Whole, &failure));
        assert!(grain_failure_restage_permitted(EpochStageAttempt::Joint, &failure));
        assert!(!grain_failure_restage_permitted(EpochStageAttempt::ReceivingOnly, &failure));
        for error in [HnnError::CountOverflow, HnnError::MissingReach,
            HnnError::Shape { what: "unknown executor/shape", expected: 1, found: 2 }] {
            failure.error = error;
            assert!(!grain_failure_restage_permitted(EpochStageAttempt::Whole, &failure));
            assert!(!grain_failure_restage_permitted(EpochStageAttempt::Joint, &failure));
        }
    }

    #[test]
    fn only_typed_joint_projection_refusal_reaches_zero_absorption() {
        let fatal = HnnError::EpochStepNonDescending { crossing: 0 };
        assert!(!receiving_restage_permitted(&fatal));
        let evidence = EpochStageRefusal::at(
            "joint_normal_projection",
            EpochStageCondition::JointNormalFall,
            "native joint projection normal predicate",
            Some(Locus::SourcePort(0)),
            Some(crate::hnn::constitution::Family::Map),
        );
        let failure = crate::hnn::constitution::epoch::EpochStageFailure {
            error: fatal,
            evidence,
            normal_inputs_prepared: true,
            channel_grain: None,
        };
        assert!(joint_restage_permitted(&failure));
        let mut untyped = failure;
        untyped.evidence.condition = EpochStageCondition::NativeOwner;
        assert!(!joint_restage_permitted(&untyped));
        untyped.error = HnnError::CountOverflow;
        untyped.evidence.condition = EpochStageCondition::JointNormalFall;
        assert!(!joint_restage_permitted(&untyped));
    }

    #[test]
    fn atomic_epoch_comparison_keeps_strict_neutral_and_worse_distinct() {
        let (_, resident, _, _) = opening();
        let phases = &resident.admitted[0];
        let receiver = phases.ring();
        let tree = resident
            .constitution
            .landmarks(receiver)
            .unwrap()
            .face(
                &vec![
                    crate::compression::landmark::context::Letter::Boundary;
                    resident
                        .constitution
                        .landmarks(receiver)
                        .unwrap()
                        .declaration()
                        .path_depth() as usize
                ],
                phases.grain(),
            )
            .unwrap();
        let wave = |real: Rat, other_phase: Rat| {
            let mut logits = vec![Rat::zero(); 2 * resident.field.alphabet()];
            logits[0] = real;
            logits[3] = other_phase;
            Faces::of_reads(
                &[crate::hnn::receiving::ReceivingRead::of_logits(
                    logits,
                    phases.grain(),
                )],
                phases.grain(),
            )
            .unwrap()
        };
        let combine = |wave: &Faces| phases.combine(wave, std::slice::from_ref(&tree)).unwrap();
        let frozen = EpochComparison {
            combined: combine(&wave(Rat::zero(), Rat::zero())),
            trees: vec![tree.clone()],
            targets: vec![0],
            target_phases: vec![crate::hnn::ratio::TargetPhases {
                branch: BigInt::zero(),
                phases: vec![Rat::zero()],
            }],
        };
        let population = resident.constitution.population(receiver).unwrap();
        let better = frozen
            .evaluate(
                population,
                receiver,
                &combine(&wave(Rat::one(), Rat::zero())),
                std::slice::from_ref(&tree),
            )
            .unwrap();
        assert!(better.objective_change.upper.is_negative());
        assert!(better.strictly_improved);
        let neutral = frozen
            .evaluate(
                population,
                receiver,
                &combine(&wave(Rat::zero(), Rat::one())),
                std::slice::from_ref(&tree),
            )
            .unwrap();
        assert!(!neutral.unchanged);
        assert!(neutral.objective_equal());
        assert!(!neutral.strictly_improved);
        let worse = frozen
            .evaluate(
                population,
                receiver,
                &combine(&wave(-Rat::one(), Rat::zero())),
                std::slice::from_ref(&tree),
            )
            .unwrap();
        assert!(worse.objective_change.lower.is_positive());
        assert!(!worse.strictly_improved);
        assert!(!worse.objective_equal());
    }

    fn source_probe_opening() -> (
        Reference,
        Resident,
        Resident,
        ObservedCrib,
        PairingDeclaration,
    ) {
        let (reference, original, crib, pairing) = opening();
        let field = &original.field;
        let receiver = original.admitted[0].ring();
        let width = field.ring(receiver).width();
        let readout = ExactRatMatrix::shaped(
            2 * field.alphabet(),
            width,
            (0..2 * field.alphabet())
                .map(|row| {
                    (0..width)
                        .map(|column| {
                            if (row == 0 || row == 1) && column % 2 == 0 {
                                rat(1, 8)
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let material = original
            .constitution
            .clone()
            .with_ports(receiver, None, None, Some(readout))
            .unwrap();
        let actual = reference
            .mount_with(field, &original.current, material)
            .unwrap();
        (reference, original, actual, crib, pairing)
    }

    #[test]
    fn atomic_epoch_source_move_joins_exact_comparison_from_same_opening() {
        let (reference, original, mut actual, mut crib, pairing) = source_probe_opening();
        let field = &original.field;
        let receiver = original.admitted[0].ring();
        let before = actual.clone();
        let execution = ProbeExecution::default();
        let receipt = reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut actual,
                &mut crib,
                &pairing,
                &[0; 32],
                None,
                &[],
                false,
                &execution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        assert_eq!(
            receipt.deposition_scope,
            ObservedEpochDepositionScope::NormalMaps
        );
        assert_eq!(
            receipt.outcome,
            ObservedEpochOutcome::Whole,
            "{:?}",
            receipt.whole_refusal
        );
        let comparison = receipt
            .comparison
            .as_ref()
            .expect("a physical source move needs its executed finite witness");
        assert!(comparison.strictly_improved);
        assert!(comparison.objective_change.upper.is_negative());
        assert_ne!(
            before.constitution.source_port(0),
            actual.constitution.source_port(0)
        );
        let source = receipt
            .deposit
            .epoch
            .as_ref()
            .unwrap()
            .loci
            .iter()
            .find(|locus| locus.locus == LinearLocus::SourcePort(0))
            .unwrap();
        assert!(source.actual_alignment.is_positive());
        assert!(source.represented_step.numerator_l1_bound.is_positive());
        let forwards = execution.forwards.lock().unwrap();
        let producing: Vec<_> = forwards
            .iter()
            .filter(|read| read.commit == before.constitution.commit())
            .collect();
        let candidate: Vec<_> = forwards
            .iter()
            .filter(|read| read.commit != before.constitution.commit())
            .collect();
        assert_eq!(producing.len(), receipt.consumed);
        assert_eq!(
            candidate.len(),
            receipt.consumed,
            "one prospective forward per original batch cell"
        );
        let (old, probe) = (producing[0], candidate[0]);
        assert_eq!(old.anchor, probe.anchor);
        assert_eq!(old.source, probe.source);
        assert_eq!(old.opening, probe.opening);
        assert_eq!(old.charts, probe.charts);
        assert_eq!(
            old.material.landmarks(receiver),
            probe.material.landmarks(receiver)
        );
        assert_eq!(
            old.material.population(receiver),
            probe.material.population(receiver)
        );
        // Only the actual original passage's reception end survives the probe.
        assert_eq!(
            actual.carried.as_ref(),
            Some(&producing.last().unwrap().end)
        );
        assert_eq!(actual.ledger.balance().cells, receipt.consumed as u64);
        assert_eq!(actual.ledger.balance().depositions, 1);
        let saved = actual.continuing_state(0).unwrap().to_text();
        let parsed = ContinuingState::from_text(&saved, actual.constitution.budget()).unwrap();
        let cold = reference
            .mount_continued(
                field,
                &original.current,
                original.constitution.clone(),
                &parsed,
            )
            .unwrap();
        assert_eq!(
            cold.constitution.source_port(0),
            actual.constitution.source_port(0)
        );
    }

    #[test]
    fn atomic_epoch_diverse_batches_keep_exact_admission_and_original_motion() {
        // Declared before reading: balanced, switched and reversed four-class
        // passages. These exercise the law's outcomes, not a claim that each
        // distinct comparison must admit the same material direction.
        let passages = [
            [0, 1, 2, 3, 0, 2, 1, 3, 3, 1, 0, 2, 1, 3, 2, 0],
            [0, 3, 1, 2, 3, 0, 2, 1, 0, 2, 3, 1, 2, 1, 0, 3],
            [3, 2, 1, 0, 3, 1, 2, 0, 0, 2, 3, 1, 2, 0, 1, 3],
        ];
        for classes in passages {
            let (reference, original, mut actual, mut crib, pairing) = source_probe_opening();
            let before = actual.clone();
            let receiver = actual.admitted[0].ring();
            let execution = ProbeExecution::default();
            let receipt = reference
                .observe_epoch_continuing_at_cuts_with_scope(
                    &mut actual,
                    &mut crib,
                    &pairing,
                    &classes,
                    None,
                    &[],
                    false,
                    &execution,
                    ObservedEpochDepositionScope::NormalMaps,
                )
                .unwrap();
            assert_rung_wall_receipt(&receipt);
            assert!(!receipt.terminal_partial);
            assert!(receipt.closed_section || receipt.carry_out);
            assert_eq!(actual.ledger.balance().cells, receipt.consumed as u64);
            assert_eq!(actual.ledger.balance().depositions, 1);
            assert_eq!(crib.next_position(), receipt.consumed);
            if receipt.outcome == ObservedEpochOutcome::ReceivingOnly {
                assert!(receipt.whole_refusal.is_some());
                assert_eq!(
                    before.constitution.source_law(0).unwrap().map(),
                    actual.constitution.source_law(0).unwrap().map()
                );
                let before_codec =
                    PairedObservation::admit(&before.field, &before.constitution, &pairing)
                        .unwrap();
                let after_codec =
                    PairedObservation::admit(&actual.field, &actual.constitution, &pairing)
                        .unwrap();
                assert_eq!(
                    before_codec.encode(&[0, 1, 2, 3]).unwrap(),
                    after_codec.encode(&[0, 1, 2, 3]).unwrap()
                );
            }
            assert_shared_normal_absorption(
                &before.constitution,
                &actual.constitution,
                &receipt,
                &execution,
                receiver,
                actual.field.ring(receiver).period(),
            );
            if receipt.publication_attempt == EpochStageAttempt::Joint {
                let joint = receipt
                    .joint_comparison
                    .as_ref()
                    .expect("every admitted upstream joint move executes its finite comparison");
                assert!(joint.strictly_improved || joint.objective_equal() || joint.unchanged);
                assert_eq!(
                    receipt.joint_probe_state,
                    ObservedEpochProbeState::FiniteComparisonExecuted
                );
            }
            if let Some(stage) = &receipt.whole_stage_refusal {
                assert_eq!(receipt.whole_refusal.as_ref(), Some(&stage.reason));
                assert_eq!(receipt.probe_state, ObservedEpochProbeState::SealNotFormed);
                assert!(receipt.comparison.is_none());
                assert!(!stage.seal_formed && !stage.finite_probe_executed);
            }
            if let Some(reading) = &receipt.comparison {
                assert_eq!(
                    receipt.probe_state,
                    ObservedEpochProbeState::FiniteComparisonExecuted
                );
                assert!(receipt.whole_stage_refusal.is_none());
                match receipt.outcome {
                    ObservedEpochOutcome::Whole => {
                        assert!(reading.strictly_improved);
                        assert!(reading.objective_change.upper.is_negative());
                    }
                    ObservedEpochOutcome::Neutral => {
                        // Neutral may describe the admitted whole branch, or a
                        // physically unchanged R branch after a refused whole.
                        if receipt.whole_refusal.is_none() {
                            assert!(reading.unchanged || reading.objective_equal());
                            assert!(!reading.strictly_improved);
                        }
                    }
                    ObservedEpochOutcome::ReceivingOnly | ObservedEpochOutcome::Joint => {
                        assert!(!reading.strictly_improved);
                        assert!(!reading.unchanged && !reading.objective_equal());
                    }
                }
            }
            let forwards = execution.forwards.lock().unwrap();
            let producing: Vec<_> = forwards
                .iter()
                .filter(|read| read.commit == before.constitution.commit())
                .collect();
            let candidate: Vec<_> = forwards
                .iter()
                .filter(|read| read.commit != before.constitution.commit())
                .collect();
            assert_eq!(producing.len(), receipt.consumed);
            assert_eq!(
                actual.carried.as_ref(),
                Some(&producing.last().unwrap().end)
            );
            if receipt.comparison.is_some() || receipt.joint_comparison.is_some() {
                let probes = usize::from(receipt.comparison.is_some())
                    + usize::from(receipt.joint_comparison.is_some());
                assert_eq!(candidate.len(), probes * receipt.consumed);
                assert_eq!(producing[0].anchor, candidate[0].anchor);
                assert_eq!(producing[0].source, candidate[0].source);
                assert_eq!(producing[0].opening, candidate[0].opening);
                assert_eq!(producing[0].charts, candidate[0].charts);
                assert_eq!(
                    producing[0].material.landmarks(receiver),
                    candidate[0].material.landmarks(receiver)
                );
                assert_eq!(
                    producing[0].material.population(receiver),
                    candidate[0].material.population(receiver)
                );
            }
            let saved = actual.continuing_state(0).unwrap().to_text();
            let parsed = ContinuingState::from_text(&saved, actual.constitution.budget()).unwrap();
            let cold = reference
                .mount_continued(
                    &original.field,
                    &original.current,
                    original.constitution.clone(),
                    &parsed,
                )
                .unwrap();
            assert_eq!(cold.constitution, actual.constitution);
            assert_eq!(cold.current, actual.current);
            assert_eq!(cold.carried, actual.carried);
        }
    }

    #[test]
    fn shared_normal_absorption_continues_identically_after_complete_cold_restore() {
        let (reference, original, mut warm, mut warm_crib, pairing) = source_probe_opening();
        let first = [0, 1, 2, 3, 0, 2, 1, 3, 3, 1, 0, 2, 1, 3, 2, 0];
        reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut warm,
                &mut warm_crib,
                &pairing,
                &first,
                None,
                &[],
                false,
                &HostObservedEpochExecution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        let checkpoint = warm.continuing_state(0).unwrap().to_text();
        let crib_text = warm_crib.unplaced_checkpoint().unwrap();
        let parsed = ContinuingState::from_text(&checkpoint, warm.constitution.budget()).unwrap();
        let mut cold = reference
            .mount_continued(
                &original.field,
                &original.current,
                original.constitution.clone(),
                &parsed,
            )
            .unwrap();
        let expected_next = usize::try_from(cold.moments.values().next().unwrap().cells()).unwrap();
        let mut cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &cold.field,
            &cold.current,
            expected_next,
            &crib_text,
        )
        .unwrap();
        let next = [3, 2, 1, 0, 3, 1, 2, 0, 0, 2, 3, 1, 2, 0, 1, 3];
        let a = reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut warm,
                &mut warm_crib,
                &pairing,
                &next,
                None,
                &[],
                false,
                &HostObservedEpochExecution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        let b = reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut cold,
                &mut cold_crib,
                &pairing,
                &next,
                None,
                &[],
                false,
                &HostObservedEpochExecution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        assert_eq!(a.outcome, b.outcome);
        assert_eq!(a.publication_attempt, b.publication_attempt);
        assert_eq!(a.joint_directions, b.joint_directions);
        assert_eq!(a.joint_comparison, b.joint_comparison);
        assert_eq!(a.joint_stage_refusal, b.joint_stage_refusal);
        assert_eq!(a.whole_refusal, b.whole_refusal);
        assert_eq!(a.whole_stage_refusal, b.whole_stage_refusal);
        assert_eq!(a.comparison, b.comparison);
        assert_eq!(a.energy, b.energy);
        assert_eq!(
            warm.continuing_state(0).unwrap().to_text(),
            cold.continuing_state(0).unwrap().to_text()
        );
        assert_eq!(
            warm_crib.unplaced_checkpoint().unwrap(),
            cold_crib.unplaced_checkpoint().unwrap()
        );
    }

    fn series_values(series: &crate::hnn::constitution::EpochSeriesReading) -> Vec<Rat> {
        series
            .numerators
            .iter()
            .enumerate()
            .map(|(index, value)| {
                Rat::new(
                    value.clone(),
                    BigInt::from(series.row_odd_divisors[index / series.columns])
                        << series.exponent as usize,
                )
            })
            .collect()
    }

    /// Compare the complete staged value, restoring only the speed slot whose consumer
    /// explicitly overwrites it before preparation. This includes all metadata and samples.
    fn assert_epoch_contribution_matches_word(
        field: &Field,
        material: &Constitution,
        ratio: &PendingRatio,
        opening: &WordOpening,
        back: &WordReturn,
        targets: &[usize],
        steps: &[ReceivingStep],
    ) {
        let (pullback, ordinary) =
            compose(field, material, ratio, opening, back, targets, steps).unwrap();
        let complete = compose_return_view(
            field,
            material,
            &Diamond::opened(field, ratio.phases(), &opening.support(field)),
            ratio.anchor(),
            &ratio.current(field).unwrap(),
            ratio.moment(),
            back,
            ratio.view(),
        )
        .unwrap();
        assert_eq!(complete.pullback, pullback);
        assert_eq!(pullback.rings.len(), field.rings().len());
        assert_eq!(pullback.contacts.len(), field.contacts().len());
        let staged =
            compose_epoch_contribution(field, material, ratio, opening, back, targets, steps)
                .unwrap();
        assert_eq!(staged.factors().len(), ordinary.factors().len());
        let mut factors = staged.factors().to_vec();
        let mut pairs = 0;
        for (staged, full) in factors.iter_mut().zip(ordinary.factors()) {
            if let FactorGradient::PairPort { speed, .. } = &mut staged.gradient {
                assert_eq!(*speed, [Rat::zero(), Rat::zero()]);
                let FactorGradient::PairPort {
                    ring,
                    offset,
                    outputs,
                    current,
                    earlier,
                    speed: full_speed,
                } = &full.gradient
                else {
                    panic!("the pair direction remains in its ordinary order");
                };
                assert_eq!(
                    *full_speed,
                    pair_ray_speed(
                        field,
                        ratio.moment(),
                        *ring,
                        *offset,
                        material.pair_port(*ring, *offset).unwrap(),
                        [outputs, current, earlier],
                    )
                    .unwrap()
                );
                *speed = full_speed.clone();
                pairs += 1;
            }
            assert_eq!(staged, full);
        }
        assert!(pairs > 0, "the control reaches a pair contribution");
        let restored = Deposit::new(
            staged.commit(),
            staged.linear().to_vec(),
            factors,
            staged.loci(),
        )
        .with_reach(staged.reach().unwrap().clone())
        .with_landmarks(staged.landmarks().to_vec())
        .with_landmark_observations(
            staged
                .landmark_partition()
                .zip(staged.landmark_observations().map(|paths| paths.to_vec())),
        )
        .unwrap()
        .with_receiving(staged.receiving().to_vec());
        assert_eq!(restored, ordinary);
    }

    #[test]
    fn observed_epoch_reads_match_independent_carried_words_and_prequential_tree() {
        let (reference, mut resident, mut crib, pairing) = opening();
        let field = resident.field.clone();
        let phases = resident.admitted[0].clone();
        let boundary = PairedObservation::admit(&field, &resident.constitution, &pairing).unwrap();
        let encoded = boundary.encode(&[0; 32]).unwrap();
        let mut clock = resident.current.clone();
        let mut cells = 0;
        for at in 0..encoded.len() {
            cells = at + 1;
            if clock.step(&field, &encoded, at).unwrap().ticks[phases.ring()] != 0 {
                break;
            }
        }
        assert!(cells > 1);
        let opening_material = resident.constitution.clone();
        let mut sequential = resident.clone();
        let (moment, _) = reference
            .ingest(&mut sequential, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let mut tree = opening_material.landmarks(phases.ring()).unwrap().clone();
        let mut population = opening_material.population(phases.ring()).unwrap().clone();
        let mut expected = Vec::new();
        let width = field.ring(phases.ring()).width();
        let mut positive = vec![Rat::zero(); 2 * field.alphabet() * width];
        let mut foil = positive.clone();
        let mut phase = positive.clone();
        let partition = partition_exponent(
            crate::hnn::field::lattice_exponent(u128::from(phases.grain()), 1),
            cells as u64,
            0,
        )
        .unwrap();
        let mut first_prefix = None;
        for at in 0..cells {
            let (pending, refined) = reference.refine(&mut sequential, &moment, &phases).unwrap();
            let slot = sequential.pending.remove(&pending).unwrap();
            let address = slot.ratio.addresses(&[]).unwrap().remove(0);
            let face = tree.face(&address, phases.grain()).unwrap();
            let wave = refined.forward.into_present().unwrap();
            let combined = phases.combine(&wave, std::slice::from_ref(&face)).unwrap();
            let target = encoded.part(at..at + 1).unwrap();
            let anchors =
                target_phases(&field, slot.ratio.anchor(), phases.ring(), &target).unwrap();
            let holon = HolonRatio::compare(combined.clone(), &[0], &anchors).unwrap();
            let whole = holon.covector().unwrap().descent(0);
            let descent = holon.epoch_covector(partition).unwrap().0.descent(0);
            let feature = slot
                .kept
                .as_ref()
                .unwrap()
                .word
                .receiving_feature(phases.first_epoch(), phases.ring())
                .unwrap();
            assert!(feature.iter().all(|value| value.abs() <= Rat::one()));
            for row in 0..descent.len() {
                if row % 2 == 1 {
                    assert_eq!(descent[row], whole[row]);
                }
                for (column, value) in feature.iter().enumerate() {
                    let index = row * width + column;
                    if row % 2 == 0 {
                        let q = if row == 0 { Rat::one() } else { Rat::zero() };
                        positive[index] += &q * value;
                        foil[index] += (q - &descent[row]) * value;
                    } else {
                        phase[index] += &descent[row] * value;
                    }
                }
            }
            let scored =
                crate::hnn::receiving::score(&population, phases.ring(), &combined, &[face], &[0])
                    .unwrap();
            let word = slot.kept.unwrap().word.resume(&field);
            let back = word
                .pull_back(
                    &holon.epoch_covector(partition).unwrap().0,
                    opening_material.receiving_map(phases.ring()).unwrap(),
                    &phases,
                )
                .unwrap();
            assert_epoch_contribution_matches_word(
                &field,
                &opening_material,
                &slot.ratio,
                &slot.opening,
                &back,
                &[0],
                &scored.steps,
            );
            population.receive(&scored.steps[0].faces()).unwrap();
            tree.deposit(&address, 0).unwrap();
            reference
                .ingest(
                    &mut sequential,
                    Some(&moment),
                    &encoded.part(at..at + 1).unwrap(),
                )
                .unwrap();
            expected.push((
                wave,
                combined,
                scored.model[0].clone(),
                scored.tree[0].clone(),
            ));
            if at == 0 {
                first_prefix = Some((
                    sequential.current.clone(),
                    sequential.carried.clone(),
                    sequential.address.clone(),
                    tree.clone(),
                ));
            }
        }
        let receipt = reference
            .observe_epoch_continuing_at_cuts(
                &mut resident,
                &mut crib,
                &pairing,
                &[0; 32],
                None,
                &[1],
                false,
            )
            .unwrap();
        assert_eq!(receipt.consumed, cells);
        assert!(receipt.closed_section);
        assert!(!receipt.terminal_partial);
        assert_eq!(receipt.reads.len(), expected.len());
        let grouped = receipt
            .deposit
            .epoch
            .as_ref()
            .expect("actual native epoch telemetry");
        assert_eq!(grouped.heard_cells, cells as u64);
        assert_eq!(grouped.partition_exponent, partition);
        assert_eq!(series_values(&grouped.receiving.positive), positive);
        assert_eq!(series_values(&grouped.receiving.foil), foil);
        assert_eq!(series_values(&grouped.receiving.phase), phase);
        assert!(positive.iter().any(|value| !value.is_zero()));
        assert!(foil.iter().any(|value| !value.is_zero()));
        assert!(
            phase.iter().any(|value| !value.is_zero()),
            "the odd-period target actually reaches phase rows"
        );
        assert!(
            grouped
                .receiving
                .phase
                .row_odd_divisors
                .iter()
                .enumerate()
                .all(|(row, &divisor)| divisor == if row % 2 == 0 { 1 } else { 3 })
        );
        let receiving = grouped
            .loci
            .iter()
            .find(|locus| locus.locus == LinearLocus::Receiving(phases.ring()))
            .unwrap();
        assert_eq!(receiving.records, cells as u64);
        assert!(grouped.loci.iter().all(|locus| locus.fall >= Rat::zero()));
        let unit = Rat::new(
            BigInt::from(1),
            BigInt::from(1) << receipt.partition_exponent as usize,
        );
        for (actual, (wave, combined, code, tree)) in receipt.reads.iter().zip(expected) {
            assert_eq!(actual.prediction, wave);
            assert_eq!(actual.combined, combined);
            assert_eq!(actual.code, code);
            assert_eq!(actual.tree, Some(tree));
            assert!(
                actual
                    .released
                    .iter()
                    .all(|mass| *mass >= Rat::zero() && mass < &unit)
            );
        }
        let (_, prefix, prefix_crib) = &receipt.prefixes[0];
        let (current, carried, address, tree) = first_prefix.unwrap();
        assert_eq!(prefix.current, current);
        assert_eq!(prefix.carried, carried);
        assert_eq!(prefix.address, address);
        assert_eq!(
            prefix.constitution.receiving_map(phases.ring()),
            opening_material.receiving_map(phases.ring())
        );
        assert_eq!(prefix.constitution.landmarks(phases.ring()), Some(&tree));
        assert_eq!(prefix_crib.next_position(), 1);
        // The actual prefix constructor and release reread must expose the same complete
        // scored-face operands as the next independently heard cell, not only its target code.
        let mut drawing = prefix.clone();
        let (draw_moment, _) = drawing.continuing().unwrap();
        let draw_phases = drawing.admitted[0].clone();
        let (pending, _) = reference
            .refine(&mut drawing, &draw_moment, &draw_phases)
            .unwrap();
        let mut keys = crate::receiver::release::KeyStream::new(vec![0], 1).unwrap();
        let sampled = reference
            .release_cells(
                &mut drawing,
                &pending,
                crate::hnn::receiving::cells::CellLaw::Draw(&mut keys),
            )
            .unwrap()
            .forward
            .into_present()
            .unwrap();
        let decision = &sampled.cells[0];
        let heard_face = &receipt.reads[1].scored_face;
        assert_eq!(decision.scored_face.as_ref(), Some(heard_face));
        assert_eq!(decision.face, heard_face.masses_at(decision.bits).unwrap());
        assert_eq!(keys.keys_read(), 1);
        assert_eq!(resident.observed_epoch_ingress, Some((phases.ring(), 1)));
        // The resident's first-law comparison remains the final cell; the exterior series above
        // reports all cells and is never installed as a historical arrived operand.
        assert_eq!(resident.arrived.as_ref().unwrap().targets, vec![0]);
        assert_eq!(resident.ledger.balance().cells, cells as u64);
        assert_eq!(resident.ledger.balance().depositions, 1);
        assert_eq!(receipt.cells, cells as u64);
    }

    /// Independently stage one blind word and its native return, then invoke
    /// exactly one grouped deposit with k equal to this partial's heard count.
    fn one_cell_partial_deposit(
        reference: &Reference,
        resident: &Resident,
        pairing: &PairingDeclaration,
        class: usize,
    ) -> (Constitution, DepositReading, Deposit) {
        let field = &resident.field;
        let phases = &resident.admitted[0];
        let receiver = phases.ring();
        let boundary = PairedObservation::admit(field, &resident.constitution, pairing).unwrap();
        let mut staging = resident.clone();
        let (moment, _) = reference
            .ingest(&mut staging, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let (pending, refined) = reference.refine(&mut staging, &moment, phases).unwrap();
        let slot = staging.pending.remove(&pending).unwrap();
        let address = slot.ratio.addresses(&[]).unwrap().remove(0);
        let mut tree = resident.constitution.landmarks(receiver).unwrap().clone();
        let tree_face = tree.face(&address, phases.grain()).unwrap();
        let wave = refined.forward.into_present().unwrap();
        let combined = phases
            .combine(&wave, std::slice::from_ref(&tree_face))
            .unwrap();
        let target = boundary.encode(&[class]).unwrap();
        let anchors = target_phases(field, slot.ratio.anchor(), receiver, &target).unwrap();
        let holon = HolonRatio::compare(combined.clone(), &[class], &anchors).unwrap();
        let grain = crate::hnn::field::lattice_exponent(u128::from(phases.grain()), 1);
        let exponent = partition_exponent(grain, 1, 0).unwrap();
        let (covector, _) = holon.epoch_covector(exponent).unwrap();
        let descent = covector.descent(0);
        let scored = crate::hnn::receiving::score(
            resident.constitution.population(receiver).unwrap(),
            receiver,
            &combined,
            &[tree_face],
            &[class],
        )
        .unwrap();
        tree.deposit(&address, class).unwrap();
        let word = slot.kept.unwrap().word.resume(field);
        let back = word
            .pull_back(
                &covector,
                resident.constitution.receiving_map(receiver).unwrap(),
                phases,
            )
            .unwrap();
        let (_, deposit) = compose(
            field,
            &resident.constitution,
            &slot.ratio,
            &slot.opening,
            &back,
            &[class],
            &scored.steps,
        )
        .unwrap();
        let deposit = with_receiving_masses(
            deposit,
            receiver,
            &holon.faces().faces[0].odometer_masses().unwrap(),
            ObservedEpochDepositionScope::All,
        )
        .unwrap();
        let mut positive = vec![Rat::zero(); descent.len()];
        positive[2 * class] = Rat::one();
        let mut foil = positive.clone();
        let mut phase = vec![Rat::zero(); descent.len()];
        for row in 0..descent.len() {
            if row % 2 == 0 {
                foil[row] -= &descent[row];
            } else {
                phase[row] = descent[row].clone();
            }
        }
        let receiving: Vec<_> = deposit
            .linear()
            .iter()
            .filter(|step| step.locus == LinearLocus::Receiving(receiver))
            .flat_map(|step| &step.samples)
            .map(|sample| EpochReceivingRecord {
                feature: sample.feature.clone(),
                positive: positive.clone(),
                foil: foil.clone(),
                phase: phase.clone(),
            })
            .collect();
        let source = slot.ratio.moment();
        let speed =
            |ring, offset, pair: &crate::hnn::moment::PairPort, direction: [&[Vec<Rat>]; 3]| {
                pair_ray_speed(field, source, ring, offset, pair, direction)
            };
        let (material, reading) = resident
            .constitution
            .deposit_observed_epoch(
                std::slice::from_ref(&deposit),
                receiver,
                field.ring(receiver).period(),
                1,
                1,
                0,
                exponent,
                &resident.retention(),
                tree,
                &speed,
                &receiving,
                &mut |_| {},
            )
            .unwrap();
        (material, reading, deposit)
    }

    fn partial_conserves_each_normal_law(
        before: &Constitution,
        after: &Constitution,
        reading: &DepositReading,
        deposit: &Deposit,
        receiver: usize,
        period: u64,
    ) {
        use crate::hnn::constitution::epoch::{EpochFlow, EpochRecord};
        let normal = |material: &Constitution, locus| match locus {
            LinearLocus::SourcePort(ring) => material.source_law(ring).unwrap().clone(),
            LinearLocus::Contrast(ring) => material.contrast_law(ring).clone(),
            LinearLocus::Receiving(ring) => material.receiving_law(ring).unwrap().clone(),
        };
        let epoch = reading.epoch.as_ref().unwrap();
        assert_eq!(epoch.heard_cells, 1);
        assert_eq!(epoch.declared_cells, 1);
        assert_eq!(epoch.actual_receiving_ingress, 0);
        assert_eq!(
            epoch.partition_exponent,
            partition_exponent(epoch.receiver_partition_bits, 1, 0).unwrap()
        );
        for locus in &epoch.loci {
            let old = normal(before, locus.locus);
            let new = normal(after, locus.locus);
            let rows: Vec<_> = if locus.locus == LinearLocus::Receiving(receiver) {
                (1..old.map().rows()).step_by(2).collect()
            } else {
                Vec::new()
            };
            let records: Vec<_> = deposit
                .linear()
                .iter()
                .filter(|step| step.locus == locus.locus)
                .flat_map(|step| &step.samples)
                .map(|sample| {
                    if rows.is_empty() {
                        EpochRecord::from_sample(sample).unwrap()
                    } else {
                        EpochRecord::from_sample_with_phase_rows(sample, &rows, period).unwrap()
                    }
                })
                .collect();
            assert_eq!(locus.records, records.len() as u64);
            let flow = EpochFlow::from_records(
                old.map().rows(),
                old.map().columns(),
                epoch.receiver_partition_bits,
                1,
                0,
                1,
                &records,
            )
            .unwrap();
            let raw_g = flow.covector.to_matrix().unwrap();
            let raw_h = flow.gram.to_matrix().unwrap();
            let (g, h) = if let Some(symmetry) = old.symmetry() {
                let g = ExactRatMatrix::shaped(
                    raw_g.rows(),
                    raw_g.columns(),
                    (0..raw_g.rows())
                        .map(|i| {
                            (0..raw_g.columns())
                                .map(|j| match symmetry.columns()[j] {
                                    Some(partner) => {
                                        (raw_g.get(i, j).unwrap()
                                            + raw_g.get(symmetry.rows()[i], partner).unwrap())
                                            / rat(2, 1)
                                    }
                                    None => raw_g.get(i, j).unwrap().clone(),
                                })
                                .collect()
                        })
                        .collect(),
                )
                .unwrap();
                let h = ExactRatMatrix::shaped(
                    raw_h.rows(),
                    raw_h.columns(),
                    (0..raw_h.rows())
                        .map(|i| {
                            (0..raw_h.columns())
                                .map(|j| {
                                    (raw_h.get(i, j).unwrap()
                                        + raw_h
                                            .get(symmetry.column(i), symmetry.column(j))
                                            .unwrap())
                                        / rat(2, 1)
                                })
                                .collect()
                        })
                        .collect(),
                )
                .unwrap();
                (g, h)
            } else {
                (raw_g, raw_h)
            };
            let canonical = new.epoch_law().unwrap();
            let h_new = canonical.gram.to_matrix().unwrap();
            assert_eq!(h_new, old.gram().add(&h).unwrap());
            let old_news = old.epoch_law().map_or_else(
                || ExactRatMatrix::zero(old.map().rows(), old.map().columns()).unwrap(),
                |law| law.news.to_matrix().unwrap(),
            );
            let left = new
                .map()
                .multiply(&h_new)
                .unwrap()
                .add(&canonical.news.to_matrix().unwrap())
                .unwrap();
            let right = old
                .map()
                .multiply(&h_new)
                .unwrap()
                .add(&g.scaled(&locus.gamma))
                .unwrap()
                .add(&old_news)
                .unwrap();
            assert_eq!(
                left, right,
                "partial W_new H_new + R_new = W_old H_new + gamma G + R_old at {:?}",
                locus.locus
            );
            assert_eq!(locus.eta, Rat::one());
        }
    }

    fn assert_same_publication(
        actual: &Resident,
        expected: &Resident,
        read: &ObservedEpochReceipt,
        full: &ObservedEpochReceipt,
    ) {
        assert_eq!(read.consumed, full.consumed);
        assert_eq!(read.cells, full.cells);
        assert_eq!(read.comparison_commit, full.comparison_commit);
        assert_eq!(read.partition_exponent, full.partition_exponent);
        assert_eq!(read.closed_section, full.closed_section);
        assert_eq!(read.terminal_partial, full.terminal_partial);
        assert_eq!(read.carry_out, full.carry_out);
        assert_eq!(read.reads, full.reads);
        assert_eq!(read.deposit, full.deposit);
        assert_eq!(read.energy, full.energy);
        assert!(read.energy.closes());
        assert_eq!(read.energy.words.len(), read.consumed);
        assert_eq!(read.precision, full.precision);
        assert_eq!(actual.constitution, expected.constitution);
        assert_eq!(actual.current, expected.current);
        assert_eq!(actual.carried, expected.carried);
        assert_eq!(actual.address, expected.address);
        assert_eq!(
            actual.observed_epoch_ingress,
            expected.observed_epoch_ingress
        );
        assert_eq!(
            actual.observed_epoch_terminal,
            expected.observed_epoch_terminal
        );
        assert_eq!(actual.ledger.balance(), expected.ledger.balance());
    }

    fn standing_tube_opening() -> (Reference, Resident, ObservedCrib, PairingDeclaration) {
        use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
        let (reference, opening, crib, pairing) = opening();
        let field = &opening.field;
        let width = field.ring(0).width();
        let material = ResonatorMaterial::new(
            ExactRatMatrix::identity(width).unwrap().scaled(&rat(16, 1)),
            ExactRatMatrix::zero(width, width).unwrap(),
            ExactRatMatrix::zero(width, width).unwrap(),
            Some(
                PumpDeclaration::new(
                    rat(1, 8),
                    crate::holon::parametron::Carrier::new(Rat::one(), Rat::zero()).unwrap(),
                    PumpStep::Stand,
                )
                .unwrap(),
            ),
        )
        .unwrap()
        .with_symmetric_saturation(rat(1, 65536))
        .unwrap();
        let constitution = opening
            .constitution
            .clone()
            .with_ring_resonator(field, 0, material)
            .unwrap();
        // Keep the already declared receiving restriction, just as a restored
        // observed execution does. This test measures its actual word passage,
        // not a new nonlinear observability declaration.
        let resident = reference
            .mount_with_family(
                field,
                &opening.current,
                constitution,
                Some(opening.admitted.clone()),
            )
            .unwrap();
        (reference, resident, crib, pairing)
    }

    #[derive(Debug)]
    struct RefusedTubeWord {
        actual: Box<dyn ObservedEpochWord>,
    }

    impl ObservedEpochWord for RefusedTubeWord {
        fn charts(&self) -> Vec<crate::hnn::chart::ChartReading> {
            self.actual.charts()
        }

        fn tube_passages(&self) -> Result<Vec<crate::hnn::ring::TubePassage>, HnnError> {
            assert!(!self.actual.tube_passages()?.is_empty());
            Err(HnnError::Resonator {
                ring: 0,
                what: "the selected observed realization cannot read its actual saturated passage",
            })
        }

        fn return_at(
            self: Box<Self>,
            field: &Field,
            execution: &dyn ObservedEpochExecution,
            covector: &crate::hnn::ratio::RatioCovector,
            map: &ExactRatMatrix,
            phases: &ReceivingPhases,
        ) -> Result<crate::hnn::port::WordReturn, HnnError> {
            self.actual
                .return_at(field, execution, covector, map, phases)
        }
    }

    struct CheckedExecution {
        returns: std::sync::atomic::AtomicUsize,
        flows: std::sync::atomic::AtomicUsize,
        refusal: u8,
    }

    impl CheckedExecution {
        fn new(refusal: u8) -> Self {
            Self {
                returns: std::sync::atomic::AtomicUsize::new(0),
                flows: std::sync::atomic::AtomicUsize::new(0),
                refusal,
            }
        }
    }

    impl ObservedEpochExecution for CheckedExecution {
        fn forward(
            &self,
            field: &Field,
            constitution: &Constitution,
            ratio: &PendingRatio,
            charts: &mut Charts,
            opening: &WordOpening,
        ) -> Result<ObservedEpochForwardWord, HnnError> {
            if self.refusal == 5 {
                return Err(refusal("selected observed forward execution refused"));
            }
            HostObservedEpochExecution.forward(field, constitution, ratio, charts, opening)
        }

        fn forward_scoped(
            &self,
            context: &mut ObservedEpochForwardContext<'_, '_>,
            ratio: &PendingRatio,
            charts: &mut Charts,
            opening: &WordOpening,
        ) -> Result<ObservedEpochForwardWord, HnnError> {
            if self.refusal == 5 {
                return Err(refusal("selected observed forward execution refused"));
            }
            let mut forward =
                HostObservedEpochExecution.forward_scoped(context, ratio, charts, opening)?;
            if self.refusal == 6 {
                forward.producing_commit = forward.producing_commit.wrapping_add(1);
            }
            if self.refusal == 8 {
                forward.released.balances.clear();
            }
            if self.refusal == 9 {
                forward.released.power += Rat::one();
            }
            if self.refusal == 7 {
                forward.word = Box::new(RefusedTubeWord {
                    actual: forward.word,
                });
            }
            Ok(forward)
        }

        fn pull_back(
            &self,
            word: Word<'_>,
            covector: &crate::hnn::ratio::RatioCovector,
            map: &ExactRatMatrix,
            phases: &ReceivingPhases,
        ) -> Result<crate::hnn::port::WordReturn, HnnError> {
            self.returns
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if self.refusal == 1 {
                return Err(refusal("selected observed return execution refused"));
            }
            HostObservedEpochExecution.pull_back(word, covector, map, phases)
        }

        fn aggregate_records(
            &self,
            locus: LinearLocus,
            rows: usize,
            columns: usize,
            receiver_grain: u32,
            epoch_cells: u64,
            epoch: u64,
            heard_cells: u64,
            records: &[crate::hnn::constitution::EpochProducerRecordReading],
        ) -> Result<crate::hnn::constitution::EpochRecordFlowReading, HnnError> {
            let call = self
                .flows
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if self.refusal == 2 && call == 1 {
                return Err(refusal("selected observed grouped execution refused"));
            }
            let mut flow = HostObservedEpochExecution.aggregate_records(
                locus,
                rows,
                columns,
                receiver_grain,
                epoch_cells,
                epoch,
                heard_cells,
                records,
            )?;
            if self.refusal == 3 {
                flow.partition_exponent += 1;
            }
            if self.refusal == 4 && matches!(locus, LinearLocus::Receiving(_)) {
                // A successful but wrong numerical result must be consumed by the
                // native certificate, never discarded in favour of a host result.
                flow.covector.numerators[0] += BigInt::one();
            }
            Ok(flow)
        }
    }

    #[test]
    fn diagnosed_fatal_stage_reports_first_native_guard_and_preserves_atomic_opening() {
        let (reference, _, mut resident, mut crib, pairing) = source_probe_opening();
        let before = resident.continuing_state(0).unwrap();
        let old_crib = crib.clone();
        let execution = CheckedExecution::new(2);
        let mut failures = Vec::new();
        let error = reference
            .observe_epoch_continuing_at_cuts_with_scope_diagnosed(
                &mut resident,
                &mut crib,
                &pairing,
                &[0; 32],
                None,
                &[],
                false,
                &execution,
                ObservedEpochDepositionScope::NormalMaps,
                &mut |attempt, evidence| failures.push((attempt, evidence.clone())),
            )
            .unwrap_err();
        assert_eq!(
            failures.len(),
            1,
            "an executor refusal cannot be retried as receiving-only"
        );
        let (attempt, evidence) = &failures[0];
        assert_eq!(*attempt, EpochStageAttempt::Whole);
        assert_eq!(evidence.reason, error.to_string());
        assert_eq!(evidence.condition, EpochStageCondition::NativeOwner);
        assert_eq!(
            (evidence.locus, evidence.family),
            (
                Some(Locus::Element(0)),
                Some(crate::hnn::constitution::Family::Map)
            )
        );
        assert!(!evidence.seal_formed && !evidence.finite_probe_executed);
        assert_eq!(
            execution.flows.load(std::sync::atomic::Ordering::Relaxed),
            2
        );
        assert_eq!(resident.continuing_state(0).unwrap(), before);
        assert_eq!(crib, old_crib);
    }

    #[test]
    fn observed_epoch_energy_keeps_actual_series_and_zero_normal_work_at_producing_cut() {
        let (reference, _, opening, opening_crib, pairing) = source_probe_opening();
        let mut selected = opening.clone();
        let mut native = opening.clone();
        let mut selected_crib = opening_crib.clone();
        let mut native_crib = opening_crib;
        let execution = CheckedExecution::new(0);
        let read = reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut selected,
                &mut selected_crib,
                &pairing,
                &[0; 32],
                None,
                &[],
                false,
                &execution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        let control = reference
            .observe_epoch_continuing_at_cuts_with_scope(
                &mut native,
                &mut native_crib,
                &pairing,
                &[0; 32],
                None,
                &[],
                false,
                &HostObservedEpochExecution,
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap();
        assert_same_publication(&selected, &native, &read, &control);
        assert_eq!(selected_crib, native_crib);
        assert!(read.consumed > 1);
        assert_ne!(
            opening.constitution.source_port(0),
            selected.constitution.source_port(0),
            "nonzero learned E movement is distinct from physical constitutive work"
        );
        assert_eq!(read.outcome, ObservedEpochOutcome::Whole);
        assert!(
            read.comparison
                .as_ref()
                .unwrap()
                .objective_change
                .upper
                .is_negative()
        );
        assert_ne!(read.energy.producing_lift, read.energy.closing_lift);
        assert_eq!(read.energy.closing_lift, selected.current.lift());
        assert_eq!(read.energy.chained.len(), read.consumed - 1);
        assert!(!read.energy.physical_form_changed);
        assert_eq!(read.energy.deposition_work, Rat::zero());
        let cut = Current::at(&opening.field, read.energy.producing_lift.clone()).unwrap();
        let before =
            crate::hnn::word::PowerForm::read(&opening.field, &opening.constitution, &cut).unwrap();
        let after = crate::hnn::word::PowerForm::read(&opening.field, &selected.constitution, &cut)
            .unwrap();
        assert_eq!(before, after);
        let last = read.energy.words.last().unwrap();
        let held = before.held(&after, &last.change).unwrap();
        assert_eq!(held.deposition, read.energy.deposition_work);
        assert_eq!(last.commit.as_ref().unwrap().deposition, held.deposition);
        assert!(
            read.energy
                .words
                .iter()
                .all(crate::hnn::word::WordBalance::closes)
        );
    }

    #[test]
    fn observed_epoch_energy_refuses_missing_or_bad_selected_release_atomically() {
        let (reference, opening, opening_crib, pairing) = opening();
        for mode in [8, 9] {
            let mut resident = opening.clone();
            let mut crib = opening_crib.clone();
            let execution = CheckedExecution::new(mode);
            let error = reference
                .observe_epoch_continuing_at_cuts_with_execution(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    &[1],
                    None,
                    &[],
                    true,
                    &execution,
                )
                .unwrap_err();
            assert!(matches!(error, HnnError::Unadmitted { .. }));
            assert_eq!(resident.constitution, opening.constitution);
            assert_eq!(resident.current, opening.current);
            assert_eq!(resident.carried, opening.carried);
            assert_eq!(resident.ledger.balance(), opening.ledger.balance());
            assert_eq!(
                resident.continuing_state(0).unwrap().to_text(),
                opening.continuing_state(0).unwrap().to_text()
            );
            assert_eq!(crib, opening_crib);
            assert_eq!(
                execution.returns.load(std::sync::atomic::Ordering::Relaxed),
                0
            );
            assert_eq!(
                execution.flows.load(std::sync::atomic::Ordering::Relaxed),
                0
            );
        }
    }

    #[test]
    fn selected_observed_execution_consumes_actual_returns_and_grouped_flows() {
        let (reference, opening, opening_crib, pairing) = opening();
        let mut actual = opening.clone();
        let mut expected = opening.clone();
        let mut crib = opening_crib.clone();
        let mut expected_crib = opening_crib;
        let execution = CheckedExecution::new(0);
        let read = reference
            .observe_epoch_continuing_at_cuts_with_execution(
                &mut actual,
                &mut crib,
                &pairing,
                &[1],
                None,
                &[1],
                true,
                &execution,
            )
            .unwrap();
        let control = reference
            .observe_epoch_continuing_at_cuts(
                &mut expected,
                &mut expected_crib,
                &pairing,
                &[1],
                None,
                &[1],
                true,
            )
            .unwrap();
        assert_same_publication(&actual, &expected, &read, &control);
        assert_eq!(crib, expected_crib);
        assert_eq!(read.prefixes.len(), control.prefixes.len());
        assert_eq!(
            read.prefixes[0].1.continuing_state(0).unwrap().to_text(),
            control.prefixes[0].1.continuing_state(0).unwrap().to_text()
        );
        assert_eq!(read.prefixes[0].2, control.prefixes[0].2);
        assert_eq!(
            execution.returns.load(std::sync::atomic::Ordering::Relaxed),
            1
        );
        assert_eq!(
            execution.flows.load(std::sync::atomic::Ordering::Relaxed),
            read.deposit.epoch.as_ref().unwrap().loci.len()
        );
    }

    #[test]
    fn selected_observed_execution_chains_actual_words_and_cold_crossings() {
        let (reference, opening, opening_crib, pairing) = opening();
        let mut selected = opening.clone();
        let mut native = opening.clone();
        let mut selected_crib = opening_crib.clone();
        let mut native_crib = opening_crib;
        let execution = CheckedExecution::new(0);
        for crossing in 0..2 {
            if crossing != 0 {
                let saved = selected.continuing_state(0).unwrap().to_text();
                let state =
                    ContinuingState::from_text(&saved, opening.constitution().budget()).unwrap();
                selected = reference
                    .mount_continued(
                        &opening.field,
                        &Current::at_rest(&opening.field),
                        opening.constitution.clone(),
                        &state,
                    )
                    .unwrap();
            }
            let read = reference
                .observe_epoch_continuing_at_cuts_with_execution(
                    &mut selected,
                    &mut selected_crib,
                    &pairing,
                    &[0; 32],
                    None,
                    &[1],
                    false,
                    &execution,
                )
                .unwrap();
            let control = reference
                .observe_epoch_continuing_at_cuts(
                    &mut native,
                    &mut native_crib,
                    &pairing,
                    &[0; 32],
                    None,
                    &[1],
                    false,
                )
                .unwrap();
            assert!(read.consumed > 1);
            assert_same_publication(&selected, &native, &read, &control);
            assert_eq!(selected_crib, native_crib);
            assert_eq!(
                selected.continuing_state(0).unwrap().to_text(),
                native.continuing_state(0).unwrap().to_text()
            );
            assert_eq!(
                read.prefixes[0].1.continuing_state(0).unwrap().to_text(),
                control.prefixes[0].1.continuing_state(0).unwrap().to_text()
            );
        }
    }

    #[test]
    fn observed_tube_passages_are_the_actual_native_and_opaque_forward_readings() {
        let (reference, mut resident, _, pairing) = standing_tube_opening();
        let field = resident.field.clone();
        let boundary = PairedObservation::admit(&field, &resident.constitution, &pairing).unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let cells = boundary.encode(&[1; 32]).unwrap();
        let native = reference
            .read_epoch(&resident, &moment, &resident.admitted[0], &cells)
            .unwrap();
        let opaque = reference
            .read_epoch_at_cuts_with_execution(
                &resident,
                &moment,
                &resident.admitted[0],
                &cells,
                &[],
                &HostObservedEpochExecution,
            )
            .unwrap();
        assert!(native.reads.len() > 1);
        assert_eq!(native.reads.len(), opaque.reads.len());
        let mut moved = false;
        for (native, opaque) in native.reads.into_iter().zip(opaque.reads) {
            let actual = native.word.tube_passages().unwrap();
            assert!(!actual.is_empty());
            assert_eq!(opaque.word.tube_passages().unwrap(), actual);
            let word = native.word.resume(&field);
            assert_eq!(word.tube_passages().unwrap(), actual);
            moved |= actual.iter().any(|passage| {
                passage
                    .distance(crate::hnn::ring::TubeCentre::Origin)
                    .is_some_and(|distance| distance.is_positive())
            });
        }
        assert!(
            moved,
            "the received source actually displaces its saturated ring"
        );
    }

    #[test]
    fn observed_tube_passage_refusal_precedes_return_and_preserves_the_opening() {
        let (reference, opening, opening_crib, pairing) = standing_tube_opening();
        let mut resident = opening.clone();
        let mut crib = opening_crib.clone();
        let execution = CheckedExecution::new(7);
        let error = reference
            .observe_epoch_continuing_at_cuts_with_execution(
                &mut resident,
                &mut crib,
                &pairing,
                &[1],
                None,
                &[],
                true,
                &execution,
            )
            .unwrap_err();
        assert_eq!(
            error,
            HnnError::Resonator {
                ring: 0,
                what: "the selected observed realization cannot read its actual saturated passage",
            }
        );
        assert_eq!(resident.constitution, opening.constitution);
        assert_eq!(resident.current, opening.current);
        assert_eq!(resident.carried, opening.carried);
        assert_eq!(resident.address, opening.address);
        assert_eq!(resident.moments, opening.moments);
        assert_eq!(resident.charts, opening.charts);
        assert_eq!(resident.ledger.balance(), opening.ledger.balance());
        assert_eq!(resident.next, opening.next);
        assert_eq!(crib, opening_crib);
        assert_eq!(
            execution.returns.load(std::sync::atomic::Ordering::Relaxed),
            0
        );
        assert_eq!(
            execution.flows.load(std::sync::atomic::Ordering::Relaxed),
            0
        );
    }

    #[test]
    fn selected_observed_execution_refusals_leave_the_whole_opening_unchanged() {
        let (reference, opening, opening_crib, pairing) = opening();
        for mode in 1..=6 {
            let mut actual = opening.clone();
            let mut crib = opening_crib.clone();
            let execution = CheckedExecution::new(mode);
            assert!(
                reference
                    .observe_epoch_continuing_at_cuts_with_execution(
                        &mut actual,
                        &mut crib,
                        &pairing,
                        &[1],
                        None,
                        &[1],
                        true,
                        &execution,
                    )
                    .is_err()
            );
            assert_eq!(actual.constitution, opening.constitution);
            assert_eq!(actual.current, opening.current);
            assert_eq!(actual.address, opening.address);
            assert_eq!(actual.carried, opening.carried);
            assert_eq!(actual.moments, opening.moments);
            assert_eq!(actual.ledger.balance(), opening.ledger.balance());
            assert_eq!(
                actual.observed_epoch_ingress,
                opening.observed_epoch_ingress
            );
            assert_eq!(
                actual.observed_epoch_terminal,
                opening.observed_epoch_terminal
            );
            assert_eq!(crib, opening_crib);
            if mode == 1 {
                assert_eq!(
                    execution.flows.load(std::sync::atomic::Ordering::Relaxed),
                    0
                );
            }
        }
    }

    #[test]
    fn epoch_contribution_matches_ordinary_grouped_publication_partial_full_and_cold() {
        let (reference, opening, opening_crib, pairing) = opening();
        for terminal in [true, false] {
            let mut actual = opening.clone();
            let mut expected = opening.clone();
            let mut crib = opening_crib.clone();
            let mut full_crib = opening_crib.clone();
            let classes: &[usize] = if terminal { &[1] } else { &[0; 32] };
            let read = reference
                .observe_epoch_continuing_at_cuts(
                    &mut actual,
                    &mut crib,
                    &pairing,
                    classes,
                    None,
                    &[],
                    terminal,
                )
                .unwrap();
            let full = reference
                .observe_epoch_continuing_for(
                    &mut expected,
                    &mut full_crib,
                    &pairing,
                    classes,
                    None,
                    &[],
                    terminal,
                    ReturnConsumer::Word,
                )
                .unwrap();
            assert_same_publication(&actual, &expected, &read, &full);
            assert_eq!(crib, full_crib);
            assert_eq!(read.terminal_partial, terminal);
            if terminal {
                continue;
            }

            // A fresh mount drops transient word/chart state and reads only the continuing
            // constitution, source and carry. Its next grouped publication still matches Word.
            let saved = actual.continuing_state(0).unwrap().to_text();
            let parsed =
                ContinuingState::from_text(&saved, opening.constitution().budget()).unwrap();
            let mut cold = reference
                .mount_continued(
                    &opening.field,
                    &Current::at_rest(&opening.field),
                    opening.constitution.clone(),
                    &parsed,
                )
                .unwrap();
            let restored = reference
                .observe_epoch_continuing(&mut cold, &mut crib, &pairing, &[0; 32], None)
                .unwrap();
            let next_full = reference
                .observe_epoch_continuing_for(
                    &mut expected,
                    &mut full_crib,
                    &pairing,
                    &[0; 32],
                    None,
                    &[],
                    false,
                    ReturnConsumer::Word,
                )
                .unwrap();
            assert_same_publication(&cold, &expected, &restored, &next_full);
            assert_eq!(crib, full_crib);
            assert_eq!(
                cold.continuing_state(0).unwrap().to_text(),
                expected.continuing_state(0).unwrap().to_text()
            );
        }
    }

    #[test]
    fn observed_subphase_trace_preserves_independent_exact_publication() {
        let (reference, mut resident, mut crib, pairing) = opening();
        let (expected, expected_reading, _) =
            one_cell_partial_deposit(&reference, &resident, &pairing, 1);
        let receipt = reference
            .observe_epoch_continuing_at_cuts(
                &mut resident,
                &mut crib,
                &pairing,
                &[1],
                None,
                &[],
                true,
            )
            .unwrap();
        assert_rung_wall_receipt(&receipt);
        assert_eq!(resident.constitution, expected);
        assert_eq!(receipt.deposit, expected_reading);
        assert!(receipt.terminal_partial);
        let names: Vec<_> = receipt
            .wall
            .deposit_subphases
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        assert_eq!(names.first(), Some(&"GroupedInputs"));
        assert_eq!(names.last(), Some(&"Publication"));
        for locus in &receipt.deposit.epoch.as_ref().unwrap().loci {
            let flow = format!("Flow({:?})", locus.locus);
            let certificate = format!("Certificate({:?})", locus.locus);
            let at = names.iter().position(|name| *name == flow).unwrap();
            assert_eq!(names[at + 1], certificate);
        }
        assert_eq!(
            &names[names.len() - 5..],
            &[
                "PairDirections",
                "RegionPreparation",
                "JointCertificate",
                "CandidateStaged",
                "Publication"
            ]
        );
        assert!(
            receipt
                .wall
                .deposit_subphases
                .iter()
                .map(|(_, elapsed)| *elapsed)
                .sum::<Duration>()
                <= receipt.wall.grouped_deposit
        );
    }

    #[test]
    fn short_section_refuses_transactionally_and_terminal_partial_is_explicitly_sealed() {
        let (reference, mut resident, mut crib, pairing) = opening();
        let material = resident.constitution.clone();
        let current = resident.current.clone();
        let address = resident.address.clone();
        let before_crib = crib.clone();
        assert!(
            reference
                .observe_epoch_continuing(&mut resident, &mut crib, &pairing, &[1], None)
                .is_err()
        );
        assert_eq!(resident.constitution, material);
        assert_eq!(resident.current, current);
        assert_eq!(resident.address, address);
        assert_eq!(crib, before_crib);
        let (expected, expected_reading, staged) =
            one_cell_partial_deposit(&reference, &resident, &pairing, 1);
        let partial = reference
            .observe_epoch_continuing_at_cuts(
                &mut resident,
                &mut crib,
                &pairing,
                &[1],
                None,
                &[1],
                true,
            )
            .unwrap();
        assert_eq!(partial.consumed, 1);
        assert!(!partial.closed_section);
        assert!(!partial.carry_out);
        assert!(partial.terminal_partial);
        assert_eq!(resident.constitution, expected);
        assert_eq!(partial.deposit, expected_reading);
        assert_eq!(
            partial.partition_exponent,
            partition_exponent(
                crate::hnn::field::lattice_exponent(u128::from(resident.admitted[0].grain()), 1),
                1,
                0,
            )
            .unwrap()
        );
        partial_conserves_each_normal_law(
            &material,
            &resident.constitution,
            &partial.deposit,
            &staged,
            resident.admitted[0].ring(),
            resident.field.ring(resident.admitted[0].ring()).period(),
        );
        assert_eq!(resident.observed_epoch_ingress, Some((2, 0)));
        assert!(resident.observed_epoch_terminal);
        assert!(
            reference
                .observe_epoch_continuing(&mut resident, &mut crib, &pairing, &[0; 32], None)
                .is_err()
        );
        assert!(!partial.prefixes[0].1.observed_epoch_terminal);
        assert!(resident.continuing_state(0).is_err());
        let moment = *resident.moments.keys().next().unwrap();
        let phases = resident.admitted[0].clone();
        assert!(reference.refine(&mut resident, &moment, &phases).is_err());
        let encoded = PairedObservation::admit(&resident.field, &resident.constitution, &pairing)
            .unwrap()
            .encode(&[1])
            .unwrap();
        assert!(
            reference
                .ingest(&mut resident, Some(&moment), &encoded)
                .is_err()
        );
    }

    #[test]
    fn observed_epoch_cold_resume_preserves_grouped_state_ingress_and_next_crossing() {
        let (reference, mut uninterrupted, mut crib, pairing) = opening();
        let field = uninterrupted.field.clone();
        let opening_material = uninterrupted.constitution.clone();
        let first = reference
            .observe_epoch_continuing(&mut uninterrupted, &mut crib, &pairing, &[0; 32], None)
            .unwrap();
        assert!(first.closed_section);
        assert_eq!(uninterrupted.receiver_ingress_ticks(), Some((2, 1)));
        let state = uninterrupted.continuing_state(0).unwrap();
        let text = state.to_text();
        let parsed = ContinuingState::from_text(&text, opening_material.budget()).unwrap();
        assert_eq!(parsed.to_text(), text);
        let mut resumed = reference
            .mount_continued(&field, &Current::at_rest(&field), opening_material, &parsed)
            .unwrap();
        let mut resumed_crib = crib.clone();
        assert_eq!(resumed.continuing_state(0).unwrap().to_text(), text);
        assert_eq!(
            resumed.receiver_ingress_ticks(),
            uninterrupted.receiver_ingress_ticks()
        );
        assert_eq!(resumed.constitution, uninterrupted.constitution);
        assert_eq!(resumed.current, uninterrupted.current);
        assert_eq!(resumed.carried, uninterrupted.carried);
        assert_eq!(resumed.address, uninterrupted.address);
        assert_eq!(resumed.ledger.balance(), uninterrupted.ledger.balance());
        let next = reference
            .observe_epoch_continuing(&mut uninterrupted, &mut crib, &pairing, &[0; 32], None)
            .unwrap();
        let restored = reference
            .observe_epoch_continuing(&mut resumed, &mut resumed_crib, &pairing, &[0; 32], None)
            .unwrap();
        assert_eq!(restored.consumed, next.consumed);
        assert_eq!(restored.partition_exponent, next.partition_exponent);
        assert_eq!(restored.reads, next.reads);
        assert_eq!(restored.deposit, next.deposit);
        assert_eq!(resumed.constitution, uninterrupted.constitution);
        assert_eq!(resumed.current, uninterrupted.current);
        assert_eq!(resumed.carried, uninterrupted.carried);
        assert_eq!(resumed.charts, uninterrupted.charts);
        assert_eq!(resumed.address, uninterrupted.address);
        assert_eq!(resumed.ledger.balance(), uninterrupted.ledger.balance());
        assert_eq!(resumed_crib, crib);
        assert_eq!(
            resumed.continuing_state(0).unwrap().to_text(),
            uninterrupted.continuing_state(0).unwrap().to_text()
        );
    }

    #[test]
    fn fixed_medium_forward_reuses_published_normal_map_and_solver_view() {
        let (reference, mut resident, mut crib, pairing) = opening();
        reference
            .observe_epoch_continuing(&mut resident, &mut crib, &pairing, &[0; 32], None)
            .unwrap();
        let receiver = resident.admitted[0].ring();
        let law = resident.constitution.receiving_law(receiver).unwrap();
        assert!(law.epoch_storage().is_some());
        let before_law = law.clone();
        let view = law.map();
        let moment = *resident.moments.keys().next().unwrap();
        let boundary =
            PairedObservation::admit(&resident.field, &resident.constitution, &pairing).unwrap();
        let encoded = boundary.encode(&[0; 2]).unwrap();
        let forward = reference
            .read_epoch(&resident, &moment, &resident.admitted[0], &encoded)
            .unwrap();
        assert_eq!(forward.reads.len(), 2);
        let mut wide_scale = false;
        for read in forward.reads {
            assert_eq!(read.commit, resident.constitution.commit());
            let word = read.word.resume(&resident.field);
            let operands = word.operands();
            let chart_exponent = operands.lattice().unwrap().chart_exponent();
            // Verify the actual published operands against their declared carrier lattices.
            // A large denominator caused by an off-lattice factor would not justify widening.
            for (ring, actual) in operands.rings().iter().enumerate() {
                let lattice = resident.constitution.lattice(Locus::Element(ring)).unwrap();
                let factor = crate::hnn::field::ConstitutionRead::passive_factor(
                    &resident.constitution,
                    ring,
                );
                let slices =
                    crate::hnn::field::ConstitutionRead::slices(&resident.constitution, ring);
                assert!(factor.entries().iter().all(|value| lattice.contains(value)));
                assert!(
                    slices
                        .iter()
                        .flat_map(|(u, v)| u.iter().chain(v))
                        .all(|value| lattice.contains(value))
                );
                let matrix = crate::hnn::propagation::ring_operator(actual.element()).unwrap();
                let (_, denominator) = crate::ratio::linear::vector::integral(matrix.entries());
                let declared = BigInt::one() << (2 * lattice.exponent() + 1) as usize;
                assert!((&declared % &denominator).is_zero());
                eprintln!(
                    "observed_operator_provenance key=Ring({ring}) D={denominator} declared_factor_and_slice_lattice={} denominator_divides=2^{} L_c={chart_exponent}",
                    lattice.exponent(),
                    2 * lattice.exponent() + 1
                );
            }
            let contact = &operands.contacts()[0];
            let lattice = resident.constitution.lattice(Locus::Channel(0)).unwrap();
            for factor in [
                crate::hnn::field::ConstitutionRead::contact_storage(&resident.constitution, 0),
                crate::hnn::field::ConstitutionRead::contact_stiffness(&resident.constitution, 0),
                crate::hnn::field::ConstitutionRead::contact_dissipation(&resident.constitution, 0),
            ] {
                assert!(factor.entries().iter().all(|value| lattice.contains(value)));
            }
            if contact.exponent().carry == BigInt::from(-98) {
                assert_eq!(operands.step(), &Rat::one());
                assert_eq!(resident.field.contact(0).admittance(), &rat(2, 1));
                assert_eq!(
                    contact.conductance(),
                    &Rat::new(BigInt::one(), BigInt::one() << 97usize)
                );
                let identity = ExactRatMatrix::identity(contact.width()).unwrap();
                let (capacity, stiffness, dissipation) = contact.forms();
                assert_eq!(capacity, &identity);
                assert_eq!(stiffness, &identity.scaled(&rat(1, 4)));
                assert_eq!(dissipation, &identity.scaled(&rat(1, 4)));
                let (_, denominator) =
                    crate::ratio::linear::vector::integral(contact.operator().entries());
                assert_eq!(denominator, BigInt::one() << 101usize);
                assert_eq!(chart_exponent, 30);
                assert_eq!(
                    &denominator << chart_exponent as usize,
                    BigInt::one() << 131usize
                );
                let declared = BigInt::one() << (2 * lattice.exponent() + 99) as usize;
                assert!((&declared % &denominator).is_zero());
                eprintln!(
                    "observed_operator_provenance key=Contact(0,-98) D_power_of_two=101 D_odd_part=1 L_c={chart_exponent} factor_lattice={} h=1 Y=2 G=2^-97 C=I K=D=I/4 declared_denominator_divides=2^{}",
                    lattice.exponent(),
                    2 * lattice.exponent() + 99
                );
            }
            for chart in operands.charts() {
                if let Some(operator) = chart.operator {
                    eprintln!("observed_next_operator {operator:?}");
                    wide_scale |= operator.scale_bits > 127;
                }
            }
        }
        assert!(
            wide_scale,
            "the unchanged next-forward fixture reaches the formerly refused scale"
        );
        let after_law = resident.constitution.receiving_law(receiver).unwrap();
        assert!(std::ptr::eq(view, after_law.map()));
        assert_eq!(*after_law, before_law);
        assert_eq!(resident.constitution.receiving_map(receiver), Some(view));
    }

    #[test]
    fn epoch_objective_split_keeps_the_exact_components_and_original_decision() {
        let grain = 4;
        let tree = LandmarkFace {
            grain,
            probabilities: vec![rat(1, 4); 4],
            exponents: vec![BigInt::from(-8); 4],
        };
        let face = |logits| {
            Faces::of_reads(
                &[crate::hnn::receiving::ReceivingRead::of_logits(
                    logits, grain,
                )],
                grain,
            )
            .unwrap()
        };
        let mut before_logits = vec![rat(0, 1); 8];
        before_logits[1] = rat(2, 1); // target produced phase=1; target phase=0
        let before = face(before_logits);
        let mut after_logits = vec![rat(0, 1); 8];
        after_logits[0] = rat(-1, 65536);
        for class in 1..4 {
            after_logits[2 * class] = rat(1, 65536);
        }
        let after = face(after_logits);
        let comparison = EpochComparison {
            combined: before.clone(),
            trees: vec![tree.clone()],
            targets: vec![0],
            target_phases: vec![crate::hnn::ratio::TargetPhases {
                branch: BigInt::zero(),
                phases: vec![rat(0, 1)],
            }],
        };
        let population = crate::hnn::receiving::receiving_population();
        let held_population = population.clone();
        let reading = comparison
            .evaluate(&population, 2, &after, std::slice::from_ref(&tree))
            .unwrap();
        let class = reading.epoch_class_code_change.as_ref().unwrap();
        let phase = reading.epoch_phase_excess_change.as_ref().unwrap();
        assert!(
            class.lower > Rat::zero(),
            "possible class-code harm, not historical attribution"
        );
        assert_eq!(phase, &rat(-1, 2));
        assert_eq!(
            reading.objective_change,
            ExactInterval::new(&class.lower + phase, &class.upper + phase).unwrap()
        );
        let original_scores = crate::hnn::receiving::compare_scores_at(
            &population,
            2,
            &before,
            std::slice::from_ref(&tree),
            &after,
            std::slice::from_ref(&tree),
            &[0],
            reading.reading_bits,
        )
        .unwrap();
        assert_eq!(class, &original_scores.change);
        assert_eq!(
            reading.reading_bits,
            crate::hnn::receiving::cells::demand_ladder()[0]
        );
        assert_eq!(reading.refinement_rounds, 0);
        assert!(!reading.unchanged);
        assert!(reading.strictly_improved);
        assert!(!reading.needs_precision());
        assert_eq!(population, held_population);
        let same = comparison
            .evaluate(&population, 2, &before, std::slice::from_ref(&tree))
            .unwrap();
        assert_eq!(
            same.epoch_class_code_change,
            Some(ExactInterval::point(Rat::zero()))
        );
        assert_eq!(same.epoch_phase_excess_change, Some(Rat::zero()));
        assert_eq!(same.objective_change, ExactInterval::point(Rat::zero()));
        assert!(same.unchanged);
        assert!(!same.strictly_improved);
    }
    #[test]
    fn d_only_observed_scope_keeps_c_k_and_zero_producing_work() {
        let (reference, _, opening, mut crib, pairing) = source_probe_opening();
        let mut actual = opening.clone();
        let read = reference.observe_epoch_continuing_at_cuts_with_scope(
            &mut actual, &mut crib, &pairing, &[0; 32], None, &[], false,
            &HostObservedEpochExecution,
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation,
        ).unwrap();
        assert_eq!(read.deposition_scope, ObservedEpochDepositionScope::NormalMapsAndChannelDissipation);
        assert!(read.energy.closes());
        assert!(read.energy.deposition_work.is_zero());
        for contact in 0..opening.field.contacts().len() {
            assert_eq!(actual.constitution.contact_storage(contact), opening.constitution.contact_storage(contact));
            assert_eq!(actual.constitution.contact_stiffness(contact), opening.constitution.contact_stiffness(contact));
        }
        let before = actual.continuing_state(0).unwrap();
        let saved_crib = crib.clone();
        assert!(reference.observe_epoch_continuing_at_cuts_with_scope(
            &mut actual, &mut crib, &pairing, &[4], None, &[], false,
            &HostObservedEpochExecution,
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation,
        ).is_err());
        assert_eq!(actual.continuing_state(0).unwrap(), before);
        assert_eq!(crib, saved_crib);
    }

    #[test]
    fn grain_observed_continuation_uses_saved_receiver_ingress_and_preserves_energy() {
        let (reference, _, mut actual, mut crib, pairing) = source_probe_opening();
        let receiver = actual.field.receivers()[0].ring;
        // Synthetic saved ingress isolates the clock binding: absorption-window count and
        // source cells remain their fixture values, deliberately different from actual N.
        actual.observed_epoch_ingress = Some((receiver, 113));
        let opening = actual.clone();
        let read = reference.with_refining_grain().observe_epoch_continuing_at_cuts_with_scope(
            &mut actual, &mut crib, &pairing, &[0; 32], None, &[], false,
            &HostObservedEpochExecution,
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation,
        ).unwrap();
        assert_eq!(actual.observed_epoch_ingress, Some((receiver, 114)));
        assert!(read.energy.closes());
        assert!(read.energy.deposition_work.is_zero());
        if let Some(grain) = read.deposit.epoch.as_ref().unwrap().channel_grain.as_ref() {
            assert_eq!((grain.ingress_before, grain.ingress_after), (113, 114));
            assert_eq!(grain.grain_exponent, 3);
            for contact in &grain.contacts {
                assert_eq!(contact.target_exponent, actual.field.lattice(Locus::Channel(contact.contact)).unwrap().exponent()+3);
            }
        } else {
            assert_eq!(read.publication_attempt, EpochStageAttempt::ReceivingOnly);
            for contact in 0..opening.field.contacts().len() {
                assert_eq!(actual.constitution.contact_storage(contact), opening.constitution.contact_storage(contact));
                assert_eq!(actual.constitution.contact_stiffness(contact), opening.constitution.contact_stiffness(contact));
                assert_eq!(actual.constitution.lattice(Locus::Channel(contact)).unwrap(), opening.constitution.lattice(Locus::Channel(contact)).unwrap());
                assert_eq!(actual.constitution.clock(Locus::Channel(contact)), opening.constitution.clock(Locus::Channel(contact)));
            }
        }
    }

    #[test]
    fn grain_observed_terminal_without_tick_does_not_schedule_and_normal_scope_stays_explicit() {
        let (reference, _, mut actual, mut crib, pairing) = source_probe_opening();
        let receiver = actual.field.receivers()[0].ring;
        actual.observed_epoch_ingress = Some((receiver, 113));
        let before = actual.continuing_state(0).unwrap();
        let crib_before = crib.clone();
        let refining = reference.with_refining_grain();
        assert!(refining.observe_epoch_continuing_at_cuts_with_scope(
            &mut actual, &mut crib, &pairing, &[0; 32], None, &[], false,
            &HostObservedEpochExecution, ObservedEpochDepositionScope::NormalMaps,
        ).is_err());
        assert_eq!(actual.continuing_state(0).unwrap(), before);
        assert_eq!(crib, crib_before);
        let opening = actual.clone();
        let read = refining.observe_epoch_continuing_at_cuts_with_scope(
            &mut actual, &mut crib, &pairing, &[1], None, &[], true,
            &HostObservedEpochExecution, ObservedEpochDepositionScope::NormalMapsAndChannelDissipation,
        ).unwrap();
        assert!(read.terminal_partial);
        assert_eq!(actual.observed_epoch_ingress, Some((receiver, 113)));
        assert!(read.deposit.epoch.as_ref().unwrap().channel_grain.is_none());
        for contact in 0..opening.field.contacts().len() {
            assert_eq!(actual.constitution.lattice(Locus::Channel(contact)).unwrap(), opening.constitution.lattice(Locus::Channel(contact)).unwrap());
        }
        assert!(read.energy.closes());
    }

}
