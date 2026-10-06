//! A continuing physical receiver of already admitted encoded sections.
//!
//! [definition; agent-inferred] The retained state is the contemporary constitution, the declared
//! source frame, the last physical reception carry and a cell-free producing chart. A source
//! section is placed relative to that frame; its station clock and the carry's absolute pump
//! clock remain distinct. No source occurrence, old Word or response column is retained.
//!
//! The consumer is `blind(section, Θ, frame, carry) -> receipt`, followed by an optional declared
//! comparison through that same Word, then `next(section', Θ', frame, receipt.carry)`. The callback
//! is called only after the blind forward law completes. It may publish the whole receipt before
//! obtaining an observation. The observation never enters the forward constructor. This is a
//! continuing owner of the existing physical laws, not another predictor or release rule.

use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, DepositReading};
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{Current, Field, ReceiverDeclaration};
use crate::hnn::port::Pullback;
use crate::hnn::prediction::{
    DamagedSection, PhysicalRepair, PhysicalSourceCertificate, PhysicalSourcePairing, PhysicalTeaching,
    PhysicalTeachingRefusal, predict_by_field,
};
use crate::hnn::ratio::HolonRatio;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::{Absorption, WordOpening};

/// One supported affine material relation per declared comparison; no coupled R/E ray.
#[derive(Clone, Copy, Debug)]
pub enum PhysicalLearning {
    Receiving,
    SourcePorts,
    PairOutputs,
}

/// An observation obtained after blind reception. Its encoded chart and station partition are
/// checked by the existing same-Word comparison consumer before any material is published.
pub struct PhysicalObservation {
    pub observed: Encoded,
    pub compared: Vec<bool>,
    pub learning: PhysicalLearning,
}

/// The comparison's external receipt; the successor constitution belongs to the resident.
#[derive(Debug)]
pub struct PhysicalPublication {
    pub ratio: HolonRatio,
    pub pullback: Pullback,
    pub publication: DepositReading,
    pub feature_energy: Vec<(crate::hnn::constitution::Locus, crate::ratio::Rat)>,
    pub source_certificate: Option<PhysicalSourceCertificate>,
    pub source_pairing: Option<PhysicalSourcePairing>,
}

/// The whole blind receipt and optional comparison result. A refused observation changes no
/// constitution, while its already executed physical end still becomes the next opening.
#[derive(Debug)]
pub struct PhysicalReception {
    pub prediction: PhysicalRepair,
    pub comparison: Result<Option<PhysicalPublication>, HnnError>,
}

/// A retained physical receiver. Construction accepts an explicit source frame and opening;
/// the first section and every later receiver are admitted by the existing physical forward law.
/// The chart, once admitted, cannot change between receptions. This owner makes no cold-restore
/// or external raw-data encoding claim: callers must supply genuinely constructed `Encoded` data.
pub struct PhysicalResident<'f> {
    field: &'f Field,
    constitution: Constitution,
    current: Current,
    opening: WordOpening,
    chart: Option<Encoded>,
}

impl<'f> PhysicalResident<'f> {
    pub fn new(
        field: &'f Field,
        constitution: Constitution,
        current: Current,
        opening: WordOpening,
    ) -> Self {
        Self {
            field,
            constitution,
            current,
            opening,
            chart: None,
        }
    }

    pub fn constitution(&self) -> &Constitution {
        &self.constitution
    }

    pub fn current(&self) -> &Current {
        &self.current
    }

    pub fn opening(&self) -> &WordOpening {
        &self.opening
    }

    /// Execute one unobserved query and retain its physical end without a deposition.
    pub fn read(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
    ) -> Result<PhysicalRepair, HnnError> {
        self.receive(section, receiver, |_| None)
            .map(|received| received.prediction)
    }

    /// Blind reception, then one optional observation, then continuation on the actual end.
    /// A forward refusal leaves the whole resident unchanged. A comparison refusal keeps the
    /// old material and advances the carry of the blind reception; it never silently resets it.
    pub fn receive(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair) -> Option<PhysicalObservation>,
    ) -> Result<PhysicalReception, HnnError> {
        let chart = section.chart();
        if self.chart.as_ref().is_some_and(|bound| bound != chart) {
            return Err(HnnError::Unadmitted {
                reason: "the continuing physical receiver's complete producing chart changed",
            });
        }
        let phases =
            ReceivingPhases::declare(self.field, &self.constitution, &self.current, receiver)?;
        let pending = predict_by_field(
            self.field,
            &self.constitution,
            &self.current,
            section,
            &self.opening,
            &phases,
        )?;
        let (prediction, comparison, successor) = match observation(pending.prediction()) {
            None => (pending.finish(), Ok(None), None),
            Some(observation) => {
                let result = match observation.learning {
                    PhysicalLearning::Receiving => pending.observe(
                        &self.constitution,
                        &observation.observed,
                        &observation.compared,
                    ),
                    PhysicalLearning::SourcePorts => pending.observe_source_ports(
                        &self.constitution,
                        &observation.observed,
                        &observation.compared,
                    ),
                    PhysicalLearning::PairOutputs => pending.observe_pair_outputs(
                        &self.constitution,
                        &observation.observed,
                        &observation.compared,
                    ),
                };
                match result {
                    Ok(PhysicalTeaching {
                        prediction,
                        ratio,
                        pullback,
                        constitution,
                        publication,
                        feature_energy,
                        source_certificate,
                        source_pairing,
                    }) => (
                        prediction,
                        Ok(Some(PhysicalPublication {
                            ratio,
                            pullback,
                            publication,
                            feature_energy,
                            source_certificate,
                            source_pairing,
                        })),
                        Some(constitution),
                    ),
                    Err(PhysicalTeachingRefusal { prediction, error }) => {
                        (prediction, Err(error), None)
                    }
                }
            }
        };
        if let Some(constitution) = successor {
            self.constitution = constitution;
        }
        self.chart = Some(chart.clone());
        self.opening = WordOpening::Received {
            carry: prediction.carry.clone(),
            absorption: Absorption::Nothing,
        };
        Ok(PhysicalReception {
            prediction,
            comparison,
        })
    }

    /// Move out the complete in-memory continuation, with no old Word or source passage.
    pub fn into_parts(self) -> (Constitution, Current, WordOpening, Option<Encoded>) {
        (self.constitution, self.current, self.opening, self.chart)
    }
}
