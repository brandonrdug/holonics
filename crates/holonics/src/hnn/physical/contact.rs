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
use crate::hnn::word::continuation::{ContinuationReceipt, Landing};
use crate::hnn::word::{ FieldBalance, ReceptionCarry, SourceOpeningReceipt, Word, WordBalance};
use crate::hnn::word::variation::{HeldContactComparison, VariationBudget, VariationReading};
use crate::hnn::word::variation::gain::{ContactStationResponse, StationResponseReading};
use crate::holon::HolonState;
use std::sync::Arc;
use crate::ratio::linear::ExactRatMatrix;

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
    /// [agent-inferred, October 9; the medium-of-joints record §7] The finite-decrease landing
    /// this comparison issued: its declared exponents, its transient candidate's re-read (`L′`,
    /// `X′`, the candidate `θ′`, its committed reach) and the admission or its typed refusal, a
    /// measured outcome either way. When admitted, `publication` is the declared candidate's and
    /// `continuation.landing` carries `e = candidate_end − held`; when refused, including the
    /// post-admission refusal of the candidate's continuation (`LandingRefusal::Continuation`), the
    /// continuation is the certified one exactly as before. `ratio` is the producing comparison
    /// (`L`, `X`).
    pub landing: Landing,
}

/// The reached current+delayed covector's actual native material return. The existing loaded
/// ray, joint proposal and storage gates admit this supplied direction; they do not bound the
/// old trajectory's second variation or prove historical score decrease. The explicit P=I
/// identifies the realized applied-factor-translation action, not the learner-policy derivative.
#[derive(Debug)]
pub struct HeldContactPublication {
    pub comparison_return: Deposit,
    pub publication: DepositReading,
    pub continuation: ContinuationReceipt,
    pub parameter_transport: ExactRatMatrix,
    pub rebase: VariationReading,
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
    /// Opt-in continuing-material full differential at the actually producing material.
    pub held_comparison: Result<Option<HeldContactComparison>, HnnError>,
    pub held_publication: Result<Option<HeldContactPublication>, HnnError>,
    /// Actual transient raw-factor station matrix, independent of local RHS gain bounds.
    pub station_response: Option<ContactStationResponse>,
    pub compared_response: Option<StationResponseReading>,
}

impl ContactCommunication {
    pub fn closes(&self) -> bool {
        self.opening.closes() && self.word.closes()
            && self.balances.iter().all(FieldBalance::closes)
            && self.comparison.as_ref().ok().and_then(|p| p.as_ref()).is_none_or(|p| {
                &p.continuation.committed - &p.continuation.before == p.continuation.deposition_work
                    && &p.continuation.opening - &p.continuation.committed == p.continuation.opening_difference
            })
            && self.held_publication.as_ref().ok().and_then(|p| p.as_ref()).is_none_or(|p| {
                &p.continuation.committed - &p.continuation.before == p.continuation.deposition_work
                    && &p.continuation.opening - &p.continuation.committed == p.continuation.opening_difference
                    && p.rebase.next_tick==self.carry.ticks
            })
    }
}

impl PhysicalReceiver<'_> {
    pub fn begin_held_contact_variation(&mut self, budget:VariationBudget) -> Result<VariationReading,HnnError> {
        self.resident.begin_held_contact_variation(budget)
    }

    pub fn begin_continuing_contact_variation(&mut self,budget:VariationBudget) -> Result<VariationReading,HnnError> {
        self.resident.begin_continuing_contact_variation(budget)
    }

    pub fn end_held_contact_variation(&mut self) -> Option<VariationReading> {
        self.resident.end_held_contact_variation()
    }

    /// A declared Field receiver observes a full-tick native passage, then optionally changes
    /// reached C/K/D through the existing contact return. The later communication is the ordinary
    /// receiver of the same common resident, not another contact experiment or saved Word.
    pub fn communicate_contact(
        &mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalBoundary) -> Option<ContactObservation>,
    ) -> Result<ContactCommunication, HnnError> {
        self.resident.admit_no_participating_world()?;
        self.resident.admit_exact_current_point()?;
        let held = self.resident.held_contact_variation().cloned();
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
        // The opening this Word opens at; the landing reads the same value (a Word records none).
        let reception = self.resident.reception_opening();
        let (mut word, opening) = Word::open_source_exact_received(self.field,
            self.resident.constitution(), self.resident.current(), moment.clone(),
            &reception)?;
        let opened_at = word.opened_at();
        let held_opening = held.as_ref().map(|j| {
            j.admit_ticks(phases.junction_steps())?;
            j.opened(&word)
        }).transpose()?;
        word.run(phases.junction_steps())?;
        let held_response = held.as_ref().zip(held_opening.as_ref())
            .map(|(j,opened)| j.advanced_with_station_response(&word,opened,&phases,
                j.station_response_budget())).transpose()?;
        let (next_held, station_response) = match held_response {
            Some((next,response)) => (Some(next),Some(response)),
            None => (None,None),
        };
        let mut compared_response = None;
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
        let mut held_comparison = Ok(None);
        let mut held_publication = Ok(None);
        if let Some(observed) = observation(&boundary) {
            if let Some(held) = &held {
                let joined = (|| {
                    if observed.observed.len() != receiver.aperture
                        || observed.observed.part(0..0)? != *section.chart()
                        || observed.observed.part(0..first)? != *source
                        || observed.compared.len() != receiver.aperture
                        || observed.compared[..first].iter().any(|x| *x)
                        || !observed.compared[first..].iter().any(|x| *x) {
                        return Err(HnnError::Unadmitted {
                            reason:"the held observation keeps its producing chart/source and actual partition",
                        });
                    }
                    let credit = word.compare_contacts_held(receiver_index,&observed.observed,&observed.compared,
                        held,held_opening.as_ref().expect("the admitted held opening"),
                        next_held.as_ref().expect("the admitted next differential").reading().clone())?;
                    let response = station_response.as_ref().expect("the admitted station response");
                    response.check_pullback(&credit.ratio.covector()?,&credit.total)?;
                    compared_response = Some(response.select(&observed.compared)?);
                    Ok(credit)
                })();
                held_comparison = match joined {
                    Ok(mut credit) => {
                        if let Some((cut,deposit)) = credit.reaction.take() {
                            held_publication = (|| {
                                let mut charts = self.resident.reception_charts();
                                let (material,returned) = cut.continue_deposited(self.field,
                                    self.resident.current(),&moment,&deposit,&mut charts)?;
                                let next_word = returned.forward.into_present().ok_or(HnnError::Realization {
                                    what:"the continuing comparison's actual held current",
                                })?;
                                let carry = next_word.reception_end()?;
                                let publication = returned.deposit.into_present().ok_or(HnnError::Realization {
                                    what:"the continuing comparison's actual material publication",
                                })?;
                                // A declared action operand, never inferred from a finite delta.
                                // The realized applied increments are held as exterior controls.
                                let parameter_transport = ExactRatMatrix::identity(held.coordinates().len())?;
                                let rebased = next_held.as_ref().expect("the admitted next differential")
                                    .rebased(self.field,self.resident.current(),&material,
                                        &blind.carry,&carry,&parameter_transport)?;
                                let rebase = rebased.reading().clone();
                                self.resident.publish_reception_with_variation(Some(material.clone()),
                                    HolonState::at(carry,material.commit()),Some(charts),None,
                                    section.chart(),Some(rebased))?;
                                Ok(HeldContactPublication { comparison_return:deposit,publication,
                                    continuation:returned.receipt,parameter_transport,rebase })
                            })().map(Some);
                        }
                        Ok(Some(credit))
                    },
                    Err(error) => Err(error),
                };
            } else {
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
                // [agent-inferred, October 9; the medium-of-joints record §7] The same comparison
                // and return as `compare_contacts`, and the finite-decrease landing issued from its
                // cut: on exact operands, at Rest or on the received carry this Word opened on, one
                // declared candidate re-read on a transient Word from that opening entered through
                // `θ′` (the carry crossed at held momentum); charted operands issue none.
                let (ratio, returned, mut landing) = word.compare_contacts_landing(receiver_index,
                    &observed.observed, &observed.compared, &reception)?;
                let cut = returned.forward.into_present().ok_or(HnnError::Realization { what: "the reached contact cut" })?;
                let pullback = returned.pullback.into_present().ok_or(HnnError::Realization { what: "the reached contact covector" })?;
                let deposit = returned.deposit.into_present().ok_or(HnnError::Realization { what: "the reached contact deposition" })?;
                let mut charts = self.resident.reception_charts();
                // Admitted: the admitted continuation is prepared on the cut without consuming it.
                // A refusal there (the held law, a preservation or work check at θ′) is recorded as
                // the typed post-admission refusal, and the certified continuation then runs on the
                // same cut exactly as before; so does a refused landing. No step is tried twice.
                let admitted = match &landing.outcome {
                    Ok(admission) => Some(cut.prepare_admitted(self.field, self.resident.current(),
                        &moment, &deposit, admission, &charts)),
                    Err(_) => None,
                };
                let (material, returned) = match admitted {
                    Some(Ok(prepared)) => cut.finish(prepared, &mut charts),
                    Some(Err(refusal)) => {
                        landing.outcome = Err(refusal);
                        cut.continue_deposited(self.field, self.resident.current(), &moment,
                            &deposit, &mut charts)?
                    }
                    None => cut.continue_deposited(self.field, self.resident.current(), &moment,
                        &deposit, &mut charts)?,
                };
                let next_word = returned.forward.into_present().ok_or(HnnError::Realization { what: "the held current" })?;
                let carry = next_word.reception_end()?;
                let publication = returned.deposit.into_present().ok_or(HnnError::Realization { what: "the finite material return" })?;
                let continuation = returned.receipt;
                self.resident.publish_reception(Some(material.clone()),
                    HolonState::at(carry, material.commit()), Some(charts), None, section.chart())?;
                Ok(ContactPublication { ratio, pullback, comparison_return: deposit, publication, continuation,
                    landing })
            })();
            comparison = joined.map(Some);
            }
        }
        if !matches!(comparison, Ok(Some(_))) && !matches!(held_publication, Ok(Some(_))) {
            let commit = self.resident.constitution().commit();
            self.resident.publish_reception_with_variation(None,
                HolonState::at(blind.carry.clone(), commit),None,None,section.chart(),next_held)?;
        }
        Ok(ContactCommunication { boundary, opening: blind.opening, balances: blind.balances,
            word: blind.word, blind_carry: blind.carry,
            carry: self.resident.carried().expect("the returned physical point was published").clone(),
            comparison,held_comparison,held_publication,station_response,compared_response })
    }
}
