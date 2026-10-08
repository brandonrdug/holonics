//! The same circuit's complete contact reaction reaches its existing communication boundary.
//!
//! [agent-inferred] A complete source-opened Word executes all its declared ticks. Only after
//! its blind complex boundary is observed may a declared comparison return through that same
//! Word to every reached C/K/D factor. ContactCut transports the actual end at held Cw and charges
//! its work. The returned library HolonState is published into the common Resident; the next
//! existing communicate call consumes that material and carry. No target enters the opening,
//! no source is reinjected at deposition and no coordinate error is replaced by a work residual.

use super::communication::PhysicalBoundary;
use super::PhysicalReceiver;
use crate::hnn::HnnError;
use crate::hnn::constitution::DepositReading;
use crate::hnn::encoding::Encoded;
use crate::hnn::field::ReceiverDeclaration;
use crate::hnn::moment::SourceMoment;
use crate::hnn::port::{Deposit, WordReturn};
use crate::hnn::prediction::{DamagedSection, PhysicalRepair, RepairedCell, StationRead, Unresolved};
use crate::hnn::ratio::HolonRatio;
use crate::hnn::word::continuation::ContinuationReceipt;
use crate::hnn::word::{ FieldBalance, ReceptionCarry, SourceOpeningReceipt, Word, WordBalance};
use crate::holon::HolonState;
use std::sync::Arc;

/// The observed full consequence and its receiving partition. Prefix cells remain unclamped
/// by the comparison: they certify the producing source, not an additional desired answer.
pub struct ContactObservation {
    pub observed: Encoded,
    pub compared: Vec<bool>,
}

/// An ephemeral reached adjoint and actual finite material/work return, never resident history.
#[derive(Debug)]
pub struct ContactPublication {
    pub ratio: HolonRatio,
    pub pullback: WordReturn,
    /// The actual reached comparison return consumed by this deposition, exposed transiently
    /// so its direction/energy can be joined to the scale, certified step and applied factor.
    /// Neither this return nor its producing Word is installed in the common resident.
    pub comparison_return: Deposit,
    /// `stepped` includes normalization-statistic coordinates. Physical factor movement is
    /// the actual finite differences in `continuation.material`, not that aggregate count.
    pub publication: DepositReading,
    pub continuation: ContinuationReceipt,
}

/// Whole blind communication, then the comparison and the actual current it leaves behind.
/// `blind_carry` belongs to the forward receipt; `carry` may include the held-momentum material
/// reaction. The complex boundary is unchanged by any subsequent observation.
#[derive(Debug)]
pub struct ContactCommunication {
    pub boundary: PhysicalBoundary,
    pub opening: SourceOpeningReceipt,
    pub balances: Vec<FieldBalance>,
    pub word: WordBalance,
    pub blind_carry: ReceptionCarry,
    pub carry: ReceptionCarry,
    pub comparison: Result<Option<ContactPublication>, HnnError>,
}

impl ContactCommunication {
    pub fn closes(&self) -> bool {
        self.opening.closes() && self.word.closes()
            && self.balances.iter().all(FieldBalance::closes)
            && self.comparison.as_ref().ok().and_then(|p| p.as_ref()).is_none_or(|p| {
                &p.continuation.committed - &p.continuation.before == p.continuation.deposition_work
                    && &p.continuation.opening - &p.continuation.committed == p.continuation.opening_difference
            })
    }
}

impl PhysicalReceiver<'_> {
    /// A declared Field receiver observes a full-tick native passage, then optionally changes
    /// reached C/K/D through the existing contact return. The later communication is the ordinary
    /// receiver of the same common resident, not another contact experiment or saved Word.
    pub fn communicate_contact(
        &mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalBoundary) -> Option<ContactObservation>,
    ) -> Result<ContactCommunication, HnnError> {
        self.resident.admit_exact_current()?;
        let first = source.len();
        if first == 0 || first >= receiver.aperture {
            return Err(HnnError::Unadmitted {
                reason: "a complete contact communication needs source and future receiving stations",
            });
        }
        let receiver_index = self.field.receivers().iter().position(|r| r == receiver)
            .ok_or(HnnError::Unadmitted {
                reason: "the native contact return consumes an actually declared Field receiver",
            })?;
        let section = DamagedSection::of_runs(receiver.aperture, source, vec![(0, source.clone())])?;
        self.resident.admit_receiving_chart(section.chart())?;
        let (phases, _) = self.declaring.declare(
            self.resident.constitution(), self.resident.current(), receiver)?;
        section.admit(self.field, self.resident.constitution(), &phases)?;
        let mut moment = SourceMoment::open_with(
            self.field, self.resident.current(), self.resident.constitution())?;
        for &g in self.field.sources() {
            moment = moment.station_section(self.field, self.resident.current(), g, &section.placed())?;
        }
        let moment = Arc::new(moment);
        let (mut word, opening) = Word::open_source_exact_received(self.field,
            self.resident.constitution(), self.resident.current(), moment.clone(),
            &self.resident.reception_opening())?;
        let opened_at = word.opened_at();
        word.run(phases.junction_steps())?;
        let reads = phases.epochs().enumerate().map(|(station, crossing)| {
            Ok(StationRead { station, crossing, tick: opened_at + crossing,
                read: phases.read(self.field, self.resident.constitution(), self.resident.current(),
                    word.anchor(crossing, phases.ring()).ok_or(HnnError::WordEnded { ticks: word.ticks() })?)? })
        }).collect::<Result<Vec<_>, HnnError>>()?;
        let blind = PhysicalRepair {
            cells: section.placed().into_iter().map(|cell| match cell {
                Some(class) => RepairedCell::Intact(class),
                None => RepairedCell::Held { fibre: (0..self.field.alphabet()).collect(),
                    unresolved: Unresolved::UncertifiedDomain },
            }).collect(),
            reads, domains: vec![None; receiver.aperture], opening,
            balances: word.field_balances().to_vec(), word: WordBalance::of(&word.released()?),
            carry: word.reception_end()?,
        };
        if !blind.opening.closes() || !blind.word.closes()
            || blind.balances.iter().any(|b| !b.closes()) {
            return Err(HnnError::Unadmitted { reason: "the complete blind contact passage has unclosed work" });
        }
        let boundary = PhysicalBoundary::of_suffix(&blind, section.chart().clone(), first, phases.grain(), false);
        let mut comparison = Ok(None);
        if let Some(observed) = observation(&boundary) {
            let joined = (|| {
                if observed.observed.len() != receiver.aperture
                    || observed.observed.part(0..0)? != *section.chart()
                    || observed.observed.part(0..first)? != *source
                    || observed.compared.len() != receiver.aperture
                    || observed.compared[..first].iter().any(|x| *x)
                    || !observed.compared[first..].iter().any(|x| *x) {
                    return Err(HnnError::Unadmitted {
                        reason: "the native contact observation keeps its producing chart/source and requested partition",
                    });
                }
                let (ratio, returned) = word.compare_contacts(receiver_index,
                    &observed.observed, &observed.compared)?;
                let cut = returned.forward.into_present().ok_or(HnnError::Realization { what: "the reached contact cut" })?;
                let pullback = returned.pullback.into_present().ok_or(HnnError::Realization { what: "the reached contact covector" })?;
                let deposit = returned.deposit.into_present().ok_or(HnnError::Realization { what: "the reached contact deposition" })?;
                let mut charts = self.resident.reception_charts();
                let (material, returned) = cut.continue_deposited(self.field, self.resident.current(), &moment, &deposit, &mut charts)?;
                let next_word = returned.forward.into_present().ok_or(HnnError::Realization { what: "the held current" })?;
                let carry = next_word.reception_end()?;
                let publication = returned.deposit.into_present().ok_or(HnnError::Realization { what: "the finite material return" })?;
                let continuation = returned.receipt;
                self.resident.publish_reception(Some(material.clone()),
                    HolonState::at(carry, material.commit()), Some(charts), None, section.chart())?;
                Ok(ContactPublication { ratio, pullback, comparison_return: deposit, publication, continuation })
            })();
            comparison = joined.map(Some);
        }
        if !matches!(comparison, Ok(Some(_))) {
            let commit = self.resident.constitution().commit();
            self.resident.publish_reception(None, HolonState::at(blind.carry.clone(), commit),
                None, None, section.chart())?;
        }
        Ok(ContactCommunication { boundary, opening: blind.opening, balances: blind.balances,
            word: blind.word, blind_carry: blind.carry,
            carry: self.resident.carried().expect("the returned physical point was published").clone(), comparison })
    }
}
