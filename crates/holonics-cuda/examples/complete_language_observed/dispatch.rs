//! Receipts count successful calls to the selected card and its actual retained Word.
use holonics::hnn::HnnError;
use holonics::hnn::chart::{ChartReading, Charts};
use holonics::hnn::constitution::{
    Constitution, EpochProducerRecordReading, EpochRecordFlowReading, LinearLocus,
};
use holonics::hnn::field::Field;
use holonics::hnn::pending::PendingRatio;
use holonics::hnn::port::WordReturn;
use holonics::hnn::ratio::RatioCovector;
use holonics::hnn::receiving::ReceivingPhases;
use holonics::hnn::reference::observed::{
    ObservedEpochExecution, ObservedEpochForwardContext, ObservedEpochForwardWord,
    ObservedEpochWord,
};
use holonics::hnn::ring::TubePassage;
use holonics::hnn::word::{Word, WordOpening};
use holonics::ratio::linear::ExactRatMatrix;
use holonics_cuda::hnn::ObservedEpochDevice;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

#[derive(Default)]
struct Counts {
    forwards: AtomicUsize,
    returns: AtomicUsize,
    aggregates: AtomicUsize,
}
pub struct TracedCard {
    card: ObservedEpochDevice,
    counts: Arc<Counts>,
}
impl TracedCard {
    pub fn new(card: ObservedEpochDevice) -> Self {
        Self {
            card,
            counts: Arc::default(),
        }
    }
    fn retain(&self, mut reading: ObservedEpochForwardWord) -> ObservedEpochForwardWord {
        reading.word = Box::new(CountedWord {
            inner: reading.word,
            counts: self.counts.clone(),
        });
        self.counts.forwards.fetch_add(1, Ordering::Relaxed);
        reading
    }
    pub fn receipt(&self, completed: bool) -> String {
        format!(
            "{{\"backend\":\"cuda-observed-epoch-device0\",\"device_ordinal\":0,\"host_fallback\":false,\"completed\":{completed},\"successful_card_forwards\":{},\"successful_retained_card_returns\":{},\"successful_card_aggregates\":{},\"host_owned\":\"scalar faces/roots/normalization/scoring/certification; prefix diagnostics; exact decode; four output forks\"}}\n",
            self.counts.forwards.load(Ordering::Relaxed),
            self.counts.returns.load(Ordering::Relaxed),
            self.counts.aggregates.load(Ordering::Relaxed)
        )
    }
    pub fn require_actual_dispatch(&self) -> Result<(), HnnError> {
        if self.counts.forwards.load(Ordering::Relaxed) == 0
            || self.counts.returns.load(Ordering::Relaxed) == 0
            || self.counts.aggregates.load(Ordering::Relaxed) == 0
        {
            return Err(HnnError::Unadmitted {
                reason: "CUDA training produced no successful actual card forward, retained return or grouped statistic",
            });
        }
        Ok(())
    }
}
struct CountedWord {
    inner: Box<dyn ObservedEpochWord>,
    counts: Arc<Counts>,
}
impl std::fmt::Debug for CountedWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("CountedCardWord").field(&self.inner).finish()
    }
}
impl ObservedEpochWord for CountedWord {
    fn charts(&self) -> Vec<ChartReading> {
        self.inner.charts()
    }
    fn tube_passages(&self) -> Result<Vec<TubePassage>, HnnError> {
        self.inner.tube_passages()
    }
    fn return_at(
        self: Box<Self>,
        field: &Field,
        execution: &dyn ObservedEpochExecution,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        let result = self
            .inner
            .return_at(field, execution, covector, map, phases)?;
        self.counts.returns.fetch_add(1, Ordering::Relaxed);
        Ok(result)
    }
}
impl ObservedEpochExecution for TracedCard {
    fn forward(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        Ok(self.retain(
            self.card
                .forward(field, constitution, ratio, charts, opening)?,
        ))
    }
    fn forward_scoped(
        &self,
        context: &mut ObservedEpochForwardContext<'_, '_>,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        Ok(self.retain(self.card.forward_scoped(context, ratio, charts, opening)?))
    }
    fn pull_back(
        &self,
        word: Word<'_>,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        self.card.pull_back(word, covector, map, phases)
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
        records: &[EpochProducerRecordReading],
    ) -> Result<EpochRecordFlowReading, HnnError> {
        let result = self.card.aggregate_records(
            locus,
            rows,
            columns,
            receiver_grain,
            epoch_cells,
            epoch,
            heard_cells,
            records,
        )?;
        self.counts.aggregates.fetch_add(1, Ordering::Relaxed);
        Ok(result)
    }
}
