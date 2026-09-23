//! The graph session of the extracted operator ([`super::extracted_operator`]): one mathematical
//! operation advances the complete resident operator ecology.
//!
//! This owner begins at the first operation of the full HNA1 graph.  It consumes ordinary row
//! addresses at the occurrence port, gathers those coefficient rows without leaving the device,
//! enacts the graph's laws, and returns its emission, trace, and move-owned successor ecology
//! together. No exterior verdict, answer lookup, candidate, or privileged commit intervenes.
//! The observed-passage chart may retain native numerical segments under their complete input
//! and morphology dependencies; native occurrences, chronology and local returns still enact.
//!
//! Under the contract of 2026-08-18 the cycle runs as segments (`operative_segment.rs`): each
//! segment is one passage bound whole, launched once, and read once through its census; the
//! successor projection is a midpoint seal fused into the graph; no section crosses to the host
//! but the terminal face at the declared receiver.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::resident_section::{
    Positions, ResidentGrain, ResidentRefusal, ResidentSection, TransferCensus,
};

use super::{
    ExtractedOperatorAdvance, ExtractedOperatorEmission, ExtractedOperatorOccurrence,
    ExtractedOperatorRefusal, ExtractedOperatorStep, ExtractedOperatorTrace, GraphTraceChart,
    NativeCarrierOrdinal, NativeFullOperatorEcology, NativeMorphologyDeposit,
    NativeOperationPrimitive, NativeOperatorNode, NativeOperatorResidence,
    NativeOperatorResidenceError, NativeReturnAperture, NativeTensorOrdinal,
    operative_backward::{NativeAdjointReturnTrace, ReturnDeed},
    operative_passage_return::{PassageCultivation, NativePassageReturn},
    operative_reuse::NativeForwardReuse,
    operative_intervention::DissectionStanding,
    operative_return::{OverlayAtom, ReturnMaterial, continuation_next_occurrences, enact_return},
    operative_scalars::projected_scale,
    operative_segment::{SegmentSite, SegmentWithdrawal, enact_segment, segments},
    operative_terminal::{TiledCarrier, stitch_intervals},
};

pub const NATIVE_FULL_OPERATION_STEP_SCHEMA: &str = "holonic-engine.native-full-operation-step.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag="kind",rename_all="kebab-case")]
pub enum NativeEmissionProjection { LastRow {source_rows:usize,row:usize} }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeEmissionReadout { Complete, LastRow }

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeMorphologyTransition {
    Unchanged,
    Changed {
        operation: u32,
        deposit: NativeMorphologyDeposit,
        adjoint: NativeAdjointReturnTrace,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeSuccessorProjection {
    Exact,
    Midpoint {
        nonpoint_coordinates: usize,
        widest_interval: u64,
    },
}

pub(super) struct ContemporaryCarrier<'chart> {
    pub(super) section: ResidentSection<'chart>,
    pub(super) bound_octaves: u32,
}

/// One operation's step inside a run: what the trace records of it.
pub(super) struct RunStep {
    pub(super) operation: NativeOperatorNode,
    pub(super) admitted_octaves: u32,
    pub(super) bound_octaves: u32,
    pub(super) projection: NativeSuccessorProjection,
    pub(super) numerical_origin: Option<super::NativeNumericalOrigin>,
    pub(super) census_before: TransferCensus,
    pub(super) census_after: TransferCensus,
}

/// The graph session of the extracted operator: the move-owned contemporary ecology. The
/// coefficient morphology is one borrowed resident standing (the constitution); every produced
/// carrier and the chronology belong to this successor line alone.
pub struct ExtractedOperatorSession<'residence, 'chart> {
    pub(super) ecology: &'residence NativeFullOperatorEcology,
    pub(super) residence: &'residence mut NativeOperatorResidence<'chart>,
    pub(super) carriers: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    pub(super) operation_at: usize,
    pub(super) generation: u64,
    pub(super) chronology: Vec<u64>,
    pub(super) grain: ResidentGrain,
    pub(super) positions: Option<Positions<'chart>>,
    pub(super) row_population: Option<usize>,
    pub(super) cycle_complete: bool,
    /// Carriers produced in one layer (or the prologue) and consumed in another: retained within
    /// the cycle as the checkpoints the return replays each layer from. A cycle boundary releases
    /// them (dissection keeps them for its probes of the same cycle).
    pub(super) cross_layer: BTreeSet<NativeCarrierOrdinal>,
    pub(super) checkpoints: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    /// The complete emitted face of the last cycle, held for its receiver (`carrier_intervals`)
    /// until the next occurrence enters. The return never reads it: it reads the contemporary
    /// constitution at `previous_context`.
    pub(super) terminal_carrier: Option<TiledCarrier<'chart>>,
    /// The reacted carrier of the tied boundary (`tanh`) and the carrier presented to the tied
    /// contraction, held only under dissection, whose probes read the same cycle.
    pub(super) terminal_reacted: Option<TiledCarrier<'chart>>,
    /// The tied contraction's own output at the receiver row, read to the host under dissection.
    pub(super) terminal_contracted: Option<Vec<(i64, i64)>>,
    pub(super) terminal_presented: Option<ContemporaryCarrier<'chart>>,
    /// The row addresses of the last cycle: the line the emitted face continued, and the only
    /// material a continuing return retains across the cycle boundary.
    pub(super) previous_context: Option<Vec<u32>>,
    /// The factorized overlay atoms deposited on each cross-section, keyed by its coefficient
    /// population, in deposit order.
    pub(super) overlay: BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>,
    /// The declared return apertures; `None` enacts no return.
    pub(super) aperture: Option<NativeReturnAperture>,
    pub(super) passage_cultivation: Option<PassageCultivation<'chart>>,
    pub(super) forward_reuse: Option<NativeForwardReuse<'chart>>,
    pub(super) progress: Option<NativeCycleProgress>,
    pub(super) interruption: Option<NativeCycleInterruption>,
    /// Last direct use in the immutable word; local-return retention adds its own actual edges.
    last_use: BTreeMap<NativeCarrierOrdinal, u32>,
    /// The dissection standing: the excitation's supports and face, when founded for dissection.
    pub(super) dissection: Option<DissectionStanding>,
    /// Whether the terminal's successor projection is fused; a receiver that declares the
    /// propagated remainder reads the face's enclosures instead.
    pub(super) terminal_seal: bool,
}

/// One whole recurrence of the graph: its output, and the successor that stays with the caller.
pub struct ExtractedOperatorCycle<'residence, 'chart> {
    pub output: ExtractedCycleOutput,
    pub successor: ExtractedOperatorSession<'residence, 'chart>,
}

/// Output of a recurrence whose unique session owner stays with the caller, including on error.
pub struct ExtractedCycleOutput {
    pub final_emission: ExtractedOperatorEmission,
    pub traces: Vec<ExtractedOperatorTrace<GraphTraceChart>>,
    pub passage_returns: Vec<NativePassageReturn>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeCycleProgress {
    pub occurrence: u64,
    pub row_addresses: Vec<u32>,
    /// Last carrier installed into current use, not a claim about uninstalled GPU temporaries.
    pub installed_through: Option<u32>,
    pub returned_through: Option<u32>,
    pub at_terminal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeCycleInterruption {
    pub progress: NativeCycleProgress,
    pub reason: String,
}

impl<'residence, 'chart> ExtractedOperatorSession<'residence, 'chart> {
    pub fn found(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
    ) -> Result<Self, ExtractedOperatorRefusal> {
        Self::found_with(ecology, residence, None)
    }

    /// Found the ecology with the declared return apertures: a continuing occurrence then meets
    /// the retained emission and deposits on the tied cross-section.
    pub fn found_with_return(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: NativeReturnAperture,
    ) -> Result<Self, ExtractedOperatorRefusal> {
        Self::found_with(ecology, residence, Some(aperture))
    }

    fn found_with(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        aperture: Option<NativeReturnAperture>,
    ) -> Result<Self, ExtractedOperatorRefusal> {
        ecology.validate()?;
        let mut producer: BTreeMap<NativeCarrierOrdinal, Option<u16>> = BTreeMap::new();
        for operation in &ecology.operations {
            producer.insert(operation.output, operation.layer);
        }
        let mut cross_layer = BTreeSet::new();
        for operation in &ecology.operations {
            for input in &operation.inputs {
                if producer.get(input).copied().flatten() != operation.layer
                    || producer.get(input).is_some_and(|layer| layer.is_none())
                {
                    cross_layer.insert(*input);
                }
            }
        }
        let mut grain = 0u32;
        let mut last_use = BTreeMap::new();
        for operation in &ecology.operations {
            for input in &operation.inputs { last_use.insert(*input, operation.ordinal); }
            if let NativeOperationPrimitive::Lookup { scale } = &operation.primitive {
                let coefficient = *operation
                    .coefficients
                    .first()
                    .ok_or(ExtractedOperatorRefusal::Operation)?;
                let scale = projected_scale(scale)?;
                let frame = residence.population_frame(coefficient)?.exponent;
                let exact = frame
                    .checked_add(scale.exponent)
                    .ok_or(ExtractedOperatorRefusal::Grain)?;
                grain =
                    grain.max(u32::try_from(-exact).map_err(|_| ExtractedOperatorRefusal::Grain)?);
            }
        }
        Ok(Self {
            ecology,
            residence,
            carriers: BTreeMap::new(),
            operation_at: 0,
            generation: 0,
            chronology: Vec::new(),
            grain: ResidentGrain(grain),
            positions: None,
            row_population: None,
            cycle_complete: false,
            cross_layer,
            checkpoints: BTreeMap::new(),
            terminal_carrier: None,
            terminal_reacted: None,
            terminal_contracted: None,
            terminal_presented: None,
            previous_context: None,
            overlay: BTreeMap::new(),
            aperture,
            passage_cultivation: None,
            forward_reuse: None,
            progress: None,
            interruption: None,
            last_use,
            dissection: None,
            terminal_seal: true,
        })
    }

    /// Declare that the receiver reads the terminal face unsealed: the emission's intervals are
    /// then the enclosures the terminal reactions propagate to every coordinate of the face, the
    /// apparatus's remainder at the receiver.  The selected face is read from midpoints as before.
    pub fn with_terminal_remainder(mut self) -> Self {
        self.terminal_seal = false;
        self
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn operation_at(&self) -> usize {
        self.operation_at
    }

    pub fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    pub fn carrier_population(&self) -> usize {
        self.carriers.len() + usize::from(self.terminal_carrier.is_some())
    }

    /// The current mounted input-workspace aperture, not a semantic maximum word length.
    pub fn lookup_input_capacity(&self) -> Result<usize, ExtractedOperatorRefusal> {
        let mut capacity = self.residence.receipt().addressed_occurrence_rows;
        for operation in &self.ecology.operations {
            if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
                capacity = capacity.min(self.residence.aligned_row_capacity(operation.coefficients[0])?);
            }
        }
        Ok(capacity)
    }

    pub fn missing_input_rows(&self, addresses: &[u32]) -> BTreeMap<u32,Vec<u32>> {
        let mut missing=BTreeMap::new();
        for operation in &self.ecology.operations {
            if matches!(operation.primitive,NativeOperationPrimitive::Lookup {..}) {
                let population=operation.coefficients[0];
                let absent:BTreeSet<_>=addresses.iter().copied().filter(|row|
                    !self.residence.has_input_row(population,*row)).collect();
                if !absent.is_empty() { missing.insert(population.0,absent.into_iter().collect()); }
            }
        }
        missing
    }

    /// Acquisition between ordinary operations preserves the same move owner and every held
    /// carrier/overlay. Old addressed words keep their numerical standing; a newly addressed
    /// row reopens dependencies when its ordinary occurrence enters.
    pub fn extend_input_rows(&mut self, additions: &[super::NativeInputRowExtension]) -> Result<(),ExtractedOperatorRefusal> {
        if self.interruption.is_some() { return Err(ExtractedOperatorRefusal::Interrupted); }
        if !self.cycle_complete && self.operation_at != 0 { return Err(ExtractedOperatorRefusal::Occurrence); }
        self.residence.extend_input_rows(self.ecology,additions,self.grain.0)
    }

    pub fn cycle_complete(&self) -> bool {
        self.cycle_complete
    }

    pub fn accepts_occurrence(&self, occurrence: &ExtractedOperatorOccurrence) -> bool {
        if self.interruption.is_some() { return false; }
        if occurrence.ordinal != self.generation || !occurrence.interaction_words.is_empty() {
            return false;
        }
        let at = if self.cycle_complete {
            0
        } else {
            self.operation_at
        };
        self.ecology.operations.get(at).is_some_and(|operation| {
            matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. })
                == !occurrence.row_addresses.is_empty()
        })
    }

    /// The total rank of the factorized overlay the ecology carries.
    pub fn morphology_overlay_rank(&self) -> usize {
        self.overlay.values().flatten().map(OverlayAtom::rank).sum()
    }

    pub fn return_aperture(&self) -> Option<NativeReturnAperture> {
        self.aperture
    }

    /// The surface's transfer census now: what has crossed between host and device since the
    /// surface was mounted, including the terminal face's egress.
    pub fn census(&self) -> TransferCensus {
        self.residence.surface().census()
    }

    pub fn forward_reuse_census(&self) -> Option<super::NativeForwardReuseCensus> {
        self.forward_reuse.as_ref().map(NativeForwardReuse::census)
    }

    /// Expanded execution receiver: discard numerical reuse only, never developmental standing.
    pub fn without_forward_reuse(mut self) -> Self {
        self.forward_reuse = None;
        self
    }

    pub fn interruption(&self) -> Option<&NativeCycleInterruption> {
        self.interruption.as_ref()
    }

    /// The return: if `entering` continues the last cycle's line, the contemporary constitution
    /// is read at that line — its forward and terminal boundary re-enacted from the retained
    /// occurrence alone — and the face meets the address that followed each of its rows; the
    /// deposit joins the overlay. Any other occurrence has no comparison and changes no
    /// morphology. Retention law: the session keeps the occurrence (`previous_context`), never a
    /// previous cycle's terminal cut, reacted carrier or checkpoints; the constitution cannot have
    /// changed since (only a return deposits), so the reading is the one that was emitted.
    fn return_on_continuation(
        &mut self,
        entering: &[u32],
    ) -> Result<NativeMorphologyTransition, ExtractedOperatorRefusal> {
        let Some(aperture) = self.aperture else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let Some(previous) = self.previous_context.clone() else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let Some(next) = continuation_next_occurrences(&previous, entering) else {
            return Ok(NativeMorphologyTransition::Unchanged);
        };
        let tied = self
            .ecology
            .operations
            .len()
            .checked_sub(5)
            .and_then(|at| self.ecology.operations.get(at))
            .and_then(|operation| operation.coefficients.first().copied())
            .ok_or(ExtractedOperatorRefusal::Operation)?;
        let (emission, reacted, presented) = self.contemporary_terminal(&previous)?;
        let surface = self.residence.surface();
        let (atom, mut deposit, differential) = enact_return(
            surface,
            ReturnMaterial {
                emission: &emission.sections,
                reacted: &reacted.sections,
                presented: &presented.section,
                presented_octaves: presented.bound_octaves,
                rows: emission.rows,
                width: emission.width,
                grain: emission.grain,
            },
            &next,
            aperture,
        )?;
        deposit.population = tied.0;
        // The receiver has consumed these terminal sections; the return now owns its
        // differential and staged atom. Their device storage is not part of the pullback.
        drop((emission, reacted, presented));
        let (adjoint, mut deposits) = self.adjoint_return(differential, ReturnDeed::Cultivate(aperture))?;
        deposits.entry(tied).or_default().push(atom);
        if let Some(reuse) = &mut self.forward_reuse { reuse.morphology_changed(deposits.keys().copied()); }
        for (population, atoms) in deposits {
            self.overlay.entry(population).or_default().extend(atoms);
        }
        Ok(NativeMorphologyTransition::Changed {
            operation: 0,
            deposit,
            adjoint,
        })
    }

    /// Read the contemporary constitution at a retained occurrence: enact the forward to the
    /// terminal boundary (keeping the cross-layer checkpoints the adjoint replays from) and the
    /// terminal boundary itself, returning the emitted face, the reacted carrier and the carrier
    /// presented to the tied contraction. Recomputation inside one return: no chronology,
    /// generation, trace or progress advances.
    fn contemporary_terminal(
        &mut self,
        rows: &[u32],
    ) -> Result<(TiledCarrier<'chart>, TiledCarrier<'chart>, ContemporaryCarrier<'chart>), ExtractedOperatorRefusal> {
        self.terminal_carrier = None;
        self.carriers.clear();
        self.checkpoints.clear();
        self.positions = None;
        self.row_population = None;
        let terminal_start = self.ecology.operations.len().saturating_sub(5);
        let progress = self.progress.take();
        let forward = self.enact_run(0, terminal_start, rows, &BTreeMap::new(), false, true);
        self.progress = progress;
        forward?;
        let operations = self.terminal_operations()?;
        let mut run = self.enact_terminal(&operations, None, [false, false, true, false, true])?;
        let presented = self
            .carriers
            .remove(&operations[0].inputs[0])
            .ok_or(ExtractedOperatorRefusal::Carrier)?;
        self.carriers.clear();
        let emitted = run.carriers[4].take().ok_or(ExtractedOperatorRefusal::Operation)?;
        let reacted = run.carriers[2].take().ok_or(ExtractedOperatorRefusal::Operation)?;
        Ok((emitted, reacted, presented))
    }

    /// Clear the previous cycle's standing when a new occurrence enters at operation zero.
    fn enter_cycle(&mut self, entering: &[u32]) -> Result<NativeMorphologyTransition, ExtractedOperatorRefusal> {
        let transition = self.return_on_continuation(entering)?;
        // Exact equality of this exterior occurrence chart permits reusing its numerical
        // realization; it does not identify the two native occurrences or skip their chronology.
        if self.previous_context.as_deref() != Some(entering) {
            if let Some(reuse) = &mut self.forward_reuse { reuse.occurrence_changed(); }
        }
        self.carriers.clear();
        self.checkpoints.clear();
        self.positions = None;
        self.row_population = None;
        self.terminal_carrier = None;
        self.terminal_reacted = None;
        self.terminal_contracted = None;
        self.terminal_presented = None;
        self.cycle_complete = false;
        if let Some(standing) = self.dissection.as_mut() {
            standing.clear();
        }
        Ok(transition)
    }

    /// Enact the operations `[from, to)` of the graph by segments on the contemporary carriers,
    /// each segment one passage.  With `retain_all` every produced carrier stays (the return's
    /// replay); otherwise a carrier no later operation reads is released, into the checkpoints
    /// when it crosses layers and `checkpoint` holds.  A counterfactual run (`checkpoint`
    /// false) leaves the session's checkpoints as the cycle left them.  `withdrawals` intervene
    /// on named operations' outputs.
    pub(super) fn enact_run(
        &mut self,
        from: usize,
        to: usize,
        row_addresses: &[u32],
        withdrawals: &BTreeMap<u32, SegmentWithdrawal<'_, 'chart>>,
        retain_all: bool,
        checkpoint: bool,
    ) -> Result<Vec<RunStep>, ExtractedOperatorRefusal> {
        let mut steps = Vec::with_capacity(to.saturating_sub(from));
        if from >= to {
            return Ok(steps);
        }
        if !row_addresses.is_empty() {
            self.ensure_row_population(row_addresses.len())?;
        }
        let operations: Vec<NativeOperatorNode> = self.ecology.operations[from..to].to_vec();
        let use_reuse = self.forward_reuse.is_some()
            && !retain_all
            && checkpoint
            && withdrawals.is_empty()
            && from == 0
            && to == self.ecology.operations.len().saturating_sub(5);
        for (start, end) in segments(&operations) {
            let mut cursor = start;
            let mut cached = if use_reuse {
                self.forward_reuse
                    .as_mut()
                    .and_then(|reuse| reuse.take_segment(start, end))
            } else {
                None
            };
            while cursor < end {
                let run = &operations[cursor..end];
                let (outcomes, census_before, census_after, origins) = if let Some((outcomes, origins)) = cached.take()
                {
                    let census = self.residence.surface().census();
                    (outcomes, census.clone(), census, Some(origins))
                } else {
                    loop {
                        let result = {
                            let site = SegmentSite {
                                residence: self.residence,
                                ecology: self.ecology,
                                carriers: &self.carriers,
                                checkpoints: &self.checkpoints,
                                positions: self.positions.as_ref(),
                                overlay: &self.overlay,
                                grain: self.grain,
                                row_addresses,
                                withdrawals,
                                tile_window: None,
                                seal: true,
                            };
                            enact_segment(&site, run)
                        };
                        match result {
                            Ok((outcomes, reading)) => {
                                break (outcomes, reading.census_before, reading.census_after, None)
                            }
                            Err(error) => {
                                // Numerical standing is optional apparatus. An allocation refusal before
                                // a successful segment can release it and retry the same pure segment;
                                // no local return, chronology or staged morphology has run yet.
                                if use_reuse
                                    && allocation_refusal(&error)
                                    && self
                                        .forward_reuse
                                        .as_mut()
                                        .is_some_and(|reuse| reuse.relieve_pressure())
                                {
                                    continue;
                                }
                                return Err(error);
                            }
                        }
                    }
                };
                if outcomes.is_empty() {
                    return Err(ExtractedOperatorRefusal::Operation);
                }
                cursor += outcomes.len();
                for (at, (outcome, operation)) in outcomes.into_iter().zip(run).enumerate() {
                    let numerical_origin = origins.as_ref().map(|origins| origins[at].clone());
                    if use_reuse && numerical_origin.is_none() {
                        if let Some(reuse) = &mut self.forward_reuse {
                            reuse.remember(&outcome, self.generation, operation.ordinal, row_addresses);
                        }
                    }
                    let bound_octaves = outcome.carrier.bound_octaves;
                    self.carriers.insert(outcome.output, outcome.carrier);
                    if let Some(progress) = &mut self.progress { progress.installed_through = Some(operation.ordinal); }
                    loop {
                        match self.return_joined_passage(operation.ordinal) {
                            Ok(()) => break,
                            Err(error)
                                if use_reuse
                                    && allocation_refusal(&error)
                                    && self
                                        .forward_reuse
                                        .as_mut()
                                        .is_some_and(|reuse| reuse.relieve_pressure()) => {}
                            Err(error) => return Err(error),
                        }
                    }
                    if let Some(progress) = &mut self.progress { progress.returned_through = Some(operation.ordinal); }
                    steps.push(RunStep {
                        operation: operation.clone(),
                        admitted_octaves: outcome.admitted_octaves,
                        bound_octaves,
                        projection: outcome.projection,
                        numerical_origin,
                        census_before: census_before.clone(),
                        census_after: census_after.clone(),
                    });
                    if retain_all {
                        continue;
                    }
                    let mut consumed = operation.inputs.clone();
                    if let Some(cultivation) = &self.passage_cultivation {
                        consumed.extend(cultivation.released_sources_at(operation.ordinal));
                    }
                    for input in &consumed {
                        if *input != operation.output
                            && !self
                                .passage_cultivation
                                .as_ref()
                                .is_some_and(|c| c.retains_source_after(*input, operation.ordinal))
                            && self
                                .last_use
                                .get(input)
                                .is_none_or(|last| *last <= operation.ordinal)
                        {
                            if let Some(carrier) = self.carriers.remove(input) {
                                if checkpoint && self.cross_layer.contains(input) {
                                    self.checkpoints.insert(*input, carrier);
                                } else if use_reuse {
                                    if let Some(reuse) = &mut self.forward_reuse {
                                        reuse.retain(*input, carrier);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(steps)
    }

    fn trace_of(
        &self,
        step: &RunStep,
        occurrence: &ExtractedOperatorOccurrence,
        morphology_transition: NativeMorphologyTransition,
        successor_generation: u64,
    ) -> ExtractedOperatorTrace<GraphTraceChart> {
        ExtractedOperatorTrace {
            schema: NATIVE_FULL_OPERATION_STEP_SCHEMA.to_owned(),
            predecessor_generation: successor_generation - 1,
            successor_generation,
            occurrence: occurrence.ordinal,
            successor_bound_octaves: step.bound_octaves,
            resident_coefficient_octets: self.residence.receipt().raw_coefficient_octets,
            census_before: step.census_before.clone(),
            census_after: step.census_after.clone(),
            chart: GraphTraceChart {
                row_addresses: occurrence.row_addresses.clone(),
                operation: step.operation.clone(),
                successor_projection: step.projection.clone(),
                morphology_transition,
                morphology_overlay_rank: self.morphology_overlay_rank(),
                admitted_octaves: step.admitted_octaves,
                numerical_origin: step.numerical_origin.clone(),
            },
        }
    }

    /// Enact the graph's current mathematical operation as a one-operation segment.  The
    /// emission names the successor carrier and carries no words: an intermediate section does
    /// not cross to the host.  The cycle owner (`advance_cycle`) runs whole segments.
    pub fn advance(
        mut self,
        occurrence: ExtractedOperatorOccurrence,
    ) -> Result<ExtractedOperatorStep<Self>, ExtractedOperatorRefusal> {
        if self.interruption.is_some() { return Err(ExtractedOperatorRefusal::Interrupted); }
        if self.passage_cultivation.is_some() {
            return Err(ExtractedOperatorRefusal::Contact("this chart advances complete cycles, not exposed primitive steps"));
        }
        if occurrence.ordinal != self.generation || !occurrence.interaction_words.is_empty() {
            return Err(ExtractedOperatorRefusal::Occurrence);
        }
        let mut morphology_transition = NativeMorphologyTransition::Unchanged;
        if self.cycle_complete {
            if self.operation_at != 0 || occurrence.row_addresses.is_empty() {
                return Err(ExtractedOperatorRefusal::Occurrence);
            }
            morphology_transition = self.enter_cycle(&occurrence.row_addresses)?;
        }
        let at = self.operation_at;
        let operation = self
            .ecology
            .operations
            .get(at)
            .cloned()
            .ok_or(ExtractedOperatorRefusal::Operation)?;
        if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
            self.previous_context = Some(occurrence.row_addresses.clone());
        }
        let steps = self.enact_run(at, at + 1, &occurrence.row_addresses, &BTreeMap::new(), false, true)?;
        let step = steps.into_iter().next().ok_or(ExtractedOperatorRefusal::Operation)?;
        let successor_generation = self
            .generation
            .checked_add(1)
            .ok_or(ExtractedOperatorRefusal::Generation)?;
        self.chronology.push(self.generation);
        self.operation_at += 1;
        if self.operation_at == self.ecology.operations.len() {
            self.operation_at = 0;
            self.cycle_complete = true;
        }
        self.generation = successor_generation;
        let carrier = self
            .carriers
            .get(&operation.output)
            .ok_or(ExtractedOperatorRefusal::Carrier)?;
        let emission = ExtractedOperatorEmission {
            generation: successor_generation,
            operation: operation.ordinal,
            carrier: operation.output,
            rows: carrier.section.rows(),
            width: carrier.section.width(),
            grain: carrier.section.grain().0,
            intervals: Vec::new(),
            projection: None,
        };
        let trace = self.trace_of(&step, &occurrence, morphology_transition, successor_generation);
        Ok(ExtractedOperatorStep {
            emission,
            trace,
            successor: self,
        })
    }

    /// Complete one whole operator recurrence from ordinary addressed occurrences, by segments,
    /// through the tiled terminal boundary.  The ecology's operation word decides which nodes
    /// consume the row population; an application cannot inspect or schedule internal primitive
    /// species.
    pub fn advance_cycle(
        mut self,
        row_addresses: &[u32],
    ) -> Result<ExtractedOperatorCycle<'residence, 'chart>, ExtractedOperatorRefusal> {
        let output = self.advance_cycle_retained(row_addresses)?;
        Ok(ExtractedOperatorCycle { output, successor: self })
    }

    /// The production ownership boundary: a refusal cannot drop the caller's ecology. Invalid
    /// input refuses before mutation. A later failure preserves the actual installed carriers and
    /// staged differences, with an explicit interruption that prevents a silent retry/replay.
    pub fn advance_cycle_retained(&mut self, row_addresses: &[u32]) -> Result<ExtractedCycleOutput, ExtractedOperatorRefusal> {
        self.advance_cycle_readout_retained(row_addresses,NativeEmissionReadout::Complete)
    }

    /// The readout changes only the exterior receiver, never the complete resident successor.
    pub fn advance_cycle_readout_retained(&mut self,row_addresses:&[u32],readout:NativeEmissionReadout)
        -> Result<ExtractedCycleOutput,ExtractedOperatorRefusal> {
        if self.interruption.is_some() { return Err(ExtractedOperatorRefusal::Interrupted); }
        if row_addresses.is_empty() || (self.operation_at != 0 && !self.cycle_complete) {
            return Err(ExtractedOperatorRefusal::Occurrence);
        }
        self.generation.checked_add(self.ecology.operations.len() as u64).ok_or(ExtractedOperatorRefusal::Generation)?;
        self.progress = Some(NativeCycleProgress { occurrence: self.generation, row_addresses: row_addresses.to_vec(),
            installed_through: None, returned_through: None, at_terminal: false });
        let result = self.advance_cycle_inner(row_addresses,readout);
        match &result {
            Ok(_) => self.progress = None,
            Err(error) => self.interruption = self.progress.clone().map(|progress|
                NativeCycleInterruption { progress, reason: error.to_string() }),
        }
        result
    }

    fn advance_cycle_inner(&mut self, row_addresses: &[u32],readout:NativeEmissionReadout) -> Result<ExtractedCycleOutput, ExtractedOperatorRefusal> {
        let mut morphology_transition = NativeMorphologyTransition::Unchanged;
        if self.cycle_complete {
            morphology_transition = self.enter_cycle(row_addresses)?;
        }
        let terminal_start = self.ecology.operations.len().saturating_sub(5);
        self.previous_context = Some(row_addresses.to_vec());
        let occurrence = ExtractedOperatorOccurrence::addressed(self.generation, row_addresses.to_vec());
        let steps = self.enact_run(0, terminal_start, row_addresses, &BTreeMap::new(), false, true)?;
        let mut traces = Vec::with_capacity(self.ecology.operations.len());
        for step in &steps {
            let successor_generation = self
                .generation
                .checked_add(1)
                .ok_or(ExtractedOperatorRefusal::Generation)?;
            let transition = std::mem::replace(&mut morphology_transition, NativeMorphologyTransition::Unchanged);
            traces.push(self.trace_of(step, &occurrence, transition, successor_generation));
            self.chronology.push(self.generation);
            self.generation = successor_generation;
            self.operation_at += 1;
        }
        let ordinal = self.generation;
        if let Some(progress) = &mut self.progress { progress.at_terminal = true; }
        let (mut emissions, mut terminal_traces) = self.advance_terminal_readout_retained(ExtractedOperatorOccurrence::internal(ordinal),readout)?;
        traces.append(&mut terminal_traces);
        let final_emission = emissions.pop()
            .ok_or(ExtractedOperatorRefusal::Operation)?;
        Ok(ExtractedCycleOutput {
            final_emission,
            traces,
            passage_returns: self.publish_passage_returns(),
        })
    }

    pub(super) fn ensure_row_population(&mut self, rows: usize) -> Result<(), ExtractedOperatorRefusal> {
        match self.row_population {
            Some(held) if held == rows => Ok(()),
            Some(_) => Err(ExtractedOperatorRefusal::Occurrence),
            None => {
                let positions = (0..rows)
                    .map(|position| {
                        u32::try_from(position).map_err(|_| ExtractedOperatorRefusal::Operation)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.positions = Some(self.residence.surface().mount_positions(&positions)?);
                self.row_population = Some(rows);
                Ok(())
            }
        }
    }

    /// The terminal receiver's copy: the one place a carrier crosses to the serial chart.
    pub fn carrier_intervals(
        &self,
        carrier: NativeCarrierOrdinal,
    ) -> Result<Vec<(i64, i64)>, ExtractedOperatorRefusal> {
        if let Some(held) = self.carriers.get(&carrier) {
            let intervals = self.residence.surface().read_out(&held.section)?;
            if intervals.is_empty() || held.bound_octaves == 0 {
                return Err(ExtractedOperatorRefusal::Carrier);
            }
            return Ok(intervals);
        }
        let held = self
            .terminal_carrier
            .as_ref()
            .filter(|held| held.carrier == carrier)
            .ok_or(ExtractedOperatorRefusal::Carrier)?;
        let tiles = held
            .sections
            .iter()
            .map(|section| self.residence.surface().read_out(section))
            .collect::<Result<Vec<_>, _>>()?;
        stitch_intervals(held.rows, &tiles)
    }
}

impl ExtractedOperatorAdvance for ExtractedOperatorSession<'_, '_> {
    type Operation = u32;
    type TraceChart = GraphTraceChart;

    fn generation(&self) -> u64 {
        self.generation
    }

    fn operation_at(&self) -> usize {
        self.operation_at
    }

    fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    fn advance_occurrence(
        self,
        occurrence: ExtractedOperatorOccurrence,
    ) -> Result<ExtractedOperatorStep<Self>, ExtractedOperatorRefusal> {
        self.advance(occurrence)
    }
}

pub(super) fn allocation_refusal(error: &ExtractedOperatorRefusal) -> bool {
    matches!(error,
        ExtractedOperatorRefusal::Resident(ResidentRefusal::MemoryAperture { .. })
        | ExtractedOperatorRefusal::Resident(ResidentRefusal::Driver { code: 2, .. })
        | ExtractedOperatorRefusal::Residence(NativeOperatorResidenceError::Allocation {
            source: ResidentRefusal::Driver { code: 2, .. }, .. }))
}

/// A contemporary carrier: produced in this cycle or replay, or retained as a checkpoint.
pub(super) fn carrier_of<'a, 'chart>(
    carriers: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    checkpoints: &'a BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    ordinal: &NativeCarrierOrdinal,
) -> Option<&'a ContemporaryCarrier<'chart>> {
    carriers.get(ordinal).or_else(|| checkpoints.get(ordinal))
}
