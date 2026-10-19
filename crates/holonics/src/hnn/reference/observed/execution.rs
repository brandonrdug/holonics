//! Execution of the actual observed return and its reached producer records.
//!
//! The shared observed owner retains the source/clock, tree/population, producing
//! ratio and transactional publication. An executor supplies the return and exact
//! grouped products; it never supplies a replacement constitution or certificate.
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartReading, Charts};
use crate::hnn::constitution::Constitution;
use crate::hnn::constitution::{
    EpochProducerRecordReading, EpochRecordFlowReading, LinearLocus, epoch_record_flow_reference,
};
use crate::hnn::field::Field;
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::WordReturn;
use crate::hnn::ratio::{Faces, RatioCovector};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::{KeptWord, ReceptionCarry, Released, Word, WordOpening};
use crate::ratio::linear::ExactRatMatrix;

/// The actual forward record stays with its executor until its own comparison
/// consumes it. A device implementation may keep only an actor address and record
/// key here; device buffers and contexts need never cross a thread boundary.
pub trait ObservedEpochWord: std::fmt::Debug + Send + Sync {
    fn charts(&self) -> Vec<ChartReading>;

    fn return_at(
        self: Box<Self>,
        field: &Field,
        execution: &dyn ObservedEpochExecution,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError>;
}

/// Exact readings of the same word whose opaque record the adjoint will consume.
/// None is reconstructed by running a second, native forward.
#[derive(Debug)]
pub struct ObservedEpochForwardWord {
    pub producing_commit: u64,
    pub word: Box<dyn ObservedEpochWord>,
    pub faces: Faces,
    pub anchors: Vec<Vec<crate::ratio::Rat>>,
    pub reception_end: ReceptionCarry,
    pub released: Released,
}

/// An immutable field/material scope shared by consecutive words. The private
/// native preparation cache changes no operand and is never required by a card
/// executor; the default dispatch passes its actual public field and material.
pub struct ObservedEpochForwardContext<'a, 'field> {
    scope: &'a mut crate::hnn::propagation::RingScope<'field>,
}

impl<'a, 'field> ObservedEpochForwardContext<'a, 'field> {
    pub(crate) fn new(scope: &'a mut crate::hnn::propagation::RingScope<'field>) -> Self {
        Self { scope }
    }

    pub fn field(&self) -> &'field Field {
        self.scope.field()
    }

    pub fn constitution(&self) -> &'field Constitution {
        self.scope.material()
    }

    /// Identity and lifetime of this immutable batch's execution scope. A
    /// backend may retain certified preparations through a weak token, validate
    /// their actual operands, and retire them when this scope ends. Token
    /// contents have no mathematical or continuing-state meaning.
    pub fn scope_token(&self) -> std::sync::Arc<()> {
        self.scope.execution_scope()
    }
}

#[derive(Debug)]
struct NativeEpochWord {
    word: KeptWord,
    charts: Vec<ChartReading>,
}

impl ObservedEpochWord for NativeEpochWord {
    fn charts(&self) -> Vec<ChartReading> {
        self.charts.clone()
    }

    fn return_at(
        self: Box<Self>,
        field: &Field,
        execution: &dyn ObservedEpochExecution,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        execution.pull_back(self.word.resume(field), covector, map, phases)
    }
}

/// An execution boundary, not a fallback policy. Implementations must return a
/// refusal when their selected realization cannot execute the actual operands.
/// The words are independent after their forward chain has reached its openings.
pub trait ObservedEpochExecution: Sync {
    /// Execute the actual producing ratio at its declared opening. The caller
    /// authenticates its observation against these anchors and faces, then chains
    /// this exact reception end into the next word's opening.
    fn forward(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError>;

    /// The same execution with the epoch's shared immutable scope. Native
    /// execution reuses its certified preparation; card implementations inherit
    /// direct dispatch to their explicitly selected `forward` method.
    fn forward_scoped(
        &self,
        context: &mut ObservedEpochForwardContext<'_, '_>,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        self.forward(
            context.field(),
            context.constitution(),
            ratio,
            charts,
            opening,
        )
    }

    fn pull_back(
        &self,
        word: Word<'_>,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError>;

    /// G = sum g f^T and deltaH = sum f f^T at this actual locus. A backend
    /// checks its arithmetic/status and reduction bounds before returning.
    #[allow(clippy::too_many_arguments)]
    fn aggregate_records(
        &self,
        locus: LinearLocus,
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochProducerRecordReading],
    ) -> Result<EpochRecordFlowReading, HnnError>;
}

/// The explicit native control. Selecting this executor executes the existing
/// Word return and record-flow law; it is never selected on device failure.
pub struct HostObservedEpochExecution;

impl ObservedEpochExecution for HostObservedEpochExecution {
    fn forward(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        let (word, faces) = ratio.read_on(field, constitution, charts, opening)?;
        keep_native(word, faces, ratio.phases(), ratio.commit())
    }

    fn forward_scoped(
        &self,
        context: &mut ObservedEpochForwardContext<'_, '_>,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        let (word, faces) = ratio.read_on_scoped(context.scope, charts, opening)?;
        keep_native(word, faces, ratio.phases(), ratio.commit())
    }

    fn pull_back(
        &self,
        word: Word<'_>,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        word.pull_back(covector, map, phases)
    }

    fn aggregate_records(
        &self,
        _locus: LinearLocus,
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochProducerRecordReading],
    ) -> Result<EpochRecordFlowReading, HnnError> {
        epoch_record_flow_reference(
            rows,
            columns,
            receiver_grain,
            epoch_cells,
            epoch,
            heard_cells,
            records,
        )
    }
}

fn keep_native(
    word: Word<'_>,
    faces: Faces,
    phases: &ReceivingPhases,
    producing_commit: u64,
) -> Result<ObservedEpochForwardWord, HnnError> {
    let anchors = word.receiving_anchors(phases)?;
    let reception_end = word.reception_end()?;
    let released = word.released()?;
    let charts = word.operands().charts();
    Ok(ObservedEpochForwardWord {
        producing_commit,
        word: Box::new(NativeEpochWord {
            word: word.keep(),
            charts,
        }),
        faces,
        anchors,
        reception_end,
        released,
    })
}
