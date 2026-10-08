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
//! receiving view of the common circuit; the source section is not retained.
//! An explicitly admitted held-contact future retains the full material first variation in
//! that same Resident and consumes it in `communicate_contact`. Other views refuse that future
//! until their differential transport exists; no old Word or source passage is retained.

pub mod communication;
pub mod contact;
pub mod action;

use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, DepositReading};
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{Current, Field, ReceiverDeclaration};
use crate::hnn::port::Pullback;
use crate::hnn::prediction::{
    DamagedSection, PhysicalRepair, PhysicalSourceCertificate, PhysicalSourcePairing,
    PhysicalTeaching, PhysicalTeachingRefusal, predict_by_field, predict_sparse_by_field,
};
use crate::hnn::ratio::HolonRatio;
use crate::hnn::receiving::{DeclaringFace, ReceivingPhases};
use crate::hnn::word::WordOpening;
use crate::hnn::reference::{Reference, Resident};
use crate::holon::HolonState;

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
    pub receiving_diagnostic: Option<crate::hnn::prediction::PhysicalReceivingDiagnostic>,
    pub source_certificate: Option<PhysicalSourceCertificate>,
    pub source_pairing: Option<PhysicalSourcePairing>,
}

/// The whole blind receipt and optional comparison result. A refused observation changes no
/// constitution, while its already executed physical end still becomes the next opening.
#[derive(Debug)]
pub struct PhysicalReception {
    pub prediction: PhysicalRepair,
    pub comparison: Result<Option<PhysicalPublication>, HnnError>,
    /// This request reused an equal declaring medium, not an old source or receiving read.
    pub declaring_face_reused: bool,
    /// Opt-in exterior receiving features from the actual cached forward anchors.
    /// Available on blind probes as well; never installed in the resident's retained state.
    pub receiving_features: Option<Vec<Vec<crate::ratio::Rat>>>,
}

/// An exact receiving view of the common execution resident. Moving this view out returns
/// the same constitution, source clock, wave carry, chart and bounded port operands.
/// The receiver owns only its reusable declaring face; no second material/current is copied.
pub struct PhysicalReceiver<'f> {
    field: &'f Field,
    resident: Resident,
    declaring: DeclaringFace<'f>,
}

impl<'f> PhysicalReceiver<'f> {
    pub fn new(field: &'f Field, constitution: Constitution, current: Current,
        opening: WordOpening) -> Result<Self, HnnError> {
        Self::from_resident(field, Reference::mount_receiving(field, &current, constitution, opening)?)
    }

    pub fn from_resident(field: &'f Field, resident: Resident) -> Result<Self, HnnError> {
        resident.admit_receiving_view(field)?;
        Ok(Self { field, resident, declaring: DeclaringFace::new(field) })
    }

    pub fn constitution(&self) -> &Constitution { self.resident.constitution() }
    pub fn current(&self) -> &Current { self.resident.current() }
    /// Read the same retained current/material and its exact work/storage readings without
    /// remounting the receiver or dropping its already certified declaring-face cache.
    pub fn resident(&self) -> &Resident { &self.resident }
    pub fn opening(&self) -> WordOpening { self.resident.reception_opening() }

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
        self.receive_with(
            section,
            receiver,
            |blind, _phases| observation(blind),
            false,
        )
    }

    /// The same continuing receiver on an explicit sparse source, without a completion-domain
    /// certificate. A communicated complex face does not assert a completed class assignment.
    pub fn receive_sparse(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair, &ReceivingPhases) -> Option<PhysicalObservation>,
    ) -> Result<PhysicalReception, HnnError> {
        self.receive_with(section, receiver, observation, true)
    }

    /// The same sparse passage and deposition, additionally exposing the reached receiving
    /// operands in its transient exterior publication. Ordinary reception keeps this disabled.
    pub fn receive_sparse_with_receiving_diagnostic(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair, &ReceivingPhases) -> Option<PhysicalObservation>,
    ) -> Result<PhysicalReception, HnnError> {
        self.receive_with_diagnostic(section, receiver, observation, true, true)
    }

    fn receive_with(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair, &ReceivingPhases) -> Option<PhysicalObservation>,
        sparse: bool,
    ) -> Result<PhysicalReception, HnnError> {
        self.receive_with_diagnostic(section, receiver, observation, sparse, false)
    }

    fn receive_with_diagnostic(
        &mut self,
        section: &DamagedSection,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalRepair, &ReceivingPhases) -> Option<PhysicalObservation>,
        sparse: bool,
        read_receiving_operands: bool,
    ) -> Result<PhysicalReception, HnnError> {
        self.resident.admit_exact_current()?;
        let chart = section.chart();
        self.resident.admit_receiving_chart(chart)?;
        let opening = self.resident.reception_opening();
        let (phases, declaring_face_reused) =
            self.declaring.declare(self.resident.constitution(), self.resident.current(), receiver)?;
        let pending = if sparse {
            predict_sparse_by_field(
                self.field,
                self.resident.constitution(),
                self.resident.current(),
                section,
                &opening,
                &phases,
            )?
        } else {
            predict_by_field(
                self.field,
                self.resident.constitution(),
                self.resident.current(),
                section,
                &opening,
                &phases,
            )?
        };
        // The exact physical owner publishes only an accounted passage. This checks the
        // original exact receipts; it does not change the charted owner's split accounting.
        let blind = pending.prediction();
        if !blind.opening.closes()
            || !blind.word.closes()
            || blind.balances.iter().any(|balance| !balance.closes())
        {
            return Err(HnnError::Unadmitted {
                reason: "the exact physical passage does not close its declared work receipts",
            });
        }
        let receiving_features = read_receiving_operands.then(|| {
            (0..pending.prediction().reads.len()).map(|station| pending.receiving_feature(station))
                .collect::<Option<Vec<_>>>()
        }).flatten();
        let (prediction, mut comparison, successor) = match observation(pending.prediction(), &phases) {
            None => (pending.finish(), Ok(None), None),
            Some(observation) => {
                let result = match observation.learning {
                    PhysicalLearning::Receiving if read_receiving_operands => pending.observe_receiving_diagnostic(
                        self.resident.constitution(),
                        &observation.observed,
                        &observation.compared,
                    ),
                    PhysicalLearning::Receiving => pending.observe(
                        self.resident.constitution(),
                        &observation.observed,
                        &observation.compared,
                    ),
                    PhysicalLearning::SourcePorts => pending.observe_source_ports(
                        self.resident.constitution(),
                        &observation.observed,
                        &observation.compared,
                    ),
                    PhysicalLearning::PairOutputs => pending.observe_pair_outputs(
                        self.resident.constitution(),
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
                        receiving_diagnostic,
                        source_certificate,
                        source_pairing,
                    }) => (
                        prediction,
                        Ok(Some(PhysicalPublication {
                            ratio,
                            pullback,
                            publication,
                            feature_energy,
                            receiving_diagnostic,
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
        // R/E/pair publication keeps C and the loaded storage fixed. Material-coordinate
        // reactions must use their transported contact return, not this blind end unchanged.
        let commit = successor.as_ref().unwrap_or_else(|| self.resident.constitution()).commit();
        if let Err(error) = self.resident.publish_reception(successor,
            HolonState::at(prediction.carry.clone(), commit), None, None, chart) {
            // A failed publication keeps the old material but retains the accounted blind end.
            comparison = Err(error);
            let commit = self.resident.constitution().commit();
            self.resident.publish_reception(None,
                HolonState::at(prediction.carry.clone(), commit), None, None, chart)?;
        }
        Ok(PhysicalReception {
            prediction,
            comparison,
            declaring_face_reused,
            receiving_features,
        })
    }

    /// Return the same complete resident, without retaining an executed Word or source section.
    pub fn into_resident(self) -> Resident { self.resident }
}
