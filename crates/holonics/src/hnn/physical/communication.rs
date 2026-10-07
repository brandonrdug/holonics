//! Source-conditioned communication through the existing continuing physical receiver.
//!
//! [agent-inferred] For an encoded prefix u of n stations and a requested receiving aperture a>n,
//! At unit source transport, m_g = nu_hat(n) sum_(j<n) G_g(tau_g+1+j)^(-1) E_g(u_j)
//! plus each actual pair moment on its own population chart. Nonunit source transport uses
//! SourceMoment's existing end-framed age weights and exact carried population readings.
//! One exact sparse Word carries the entered interior and produces the receiving field
//! y_j = R G_R(tau_R) v_R(e_j), n<=j<a. No source datum is imposed at those future stations.
//! Its per-station complex faces carry the actual domain receipts and communication decisions.
//! Sparse forward provides no joint source-completion certificate, even for several stations.
//! An explicit one-future request instead consumes the existing full-domain owner: one shared
//! missing label passes through the first/pair source ports and native ticks. Its actual signed
//! receiving response, when certified, remains transient boundary data, not a symbolic source.
//! It emits no guessed classes or product of marginal draws.
//! Its source/chart/clock and normal return remain the existing owners; no task routine enters.
//!
//! The actual boundary reaches the caller before any observed response. Its complete source
//! prefix is preserved and only requested stations may be compared. The same Word's reached
//! comparison changes the contemporary constitution; the next request consumes it and the
//! actual carry. Neither the request nor Word is retained by the resident.

use super::{PhysicalObservation, PhysicalPublication, PhysicalResident};
use crate::hnn::HnnError;
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{FieldMaterial, ReceiverDeclaration};
use crate::hnn::prediction::{
    DamagedSection, PhysicalCompletionRead, PhysicalDomainRead, PhysicalRepair, RepairedCell,
    StationRead, Unresolved,
};
use crate::hnn::ratio::Faces;
use crate::hnn::word::{FieldBalance, ReceptionCarry, SourceOpeningReceipt, WordBalance};
use num_traits::One;

/// Per-station complex faces, domains and communication decisions from one common native Word,
/// in its complete cell-free producing chart. Sparse domains certify no joint completion;
/// the one-future route preserves its actual common-label response when the owner supplies it.
/// The readings keep their own station/crossing/absolute tick, grain cells and lifted phase.
/// They are neither an assertion of true future classes nor independent random draws.
#[derive(Clone, Debug, PartialEq)]
pub struct PhysicalBoundary {
    chart: Encoded,
    readings: Vec<StationRead>,
    decisions: Vec<RepairedCell>,
    domains: Vec<Option<PhysicalDomainRead>>,
    first: usize,
    grain: u64,
}

impl PhysicalBoundary {
    fn of_suffix(
        prediction: &PhysicalRepair,
        chart: Encoded,
        first: usize,
        grain: u64,
        unite_point: bool,
    ) -> Self {
        let decisions = prediction.cells[first..]
            .iter()
            .zip(&prediction.reads[first..])
            .zip(&prediction.domains[first..])
            .map(|((decision, point), domain)| {
                if unite_point {
                    communication_decision(decision, point, domain.as_ref())
                } else {
                    decision.clone()
                }
            })
            .collect();
        Self {
            chart,
            first,
            grain,
            readings: prediction.reads[first..].to_vec(),
            decisions,
            domains: prediction.domains[first..].to_vec(),
        }
    }
    pub fn chart(&self) -> &Encoded {
        &self.chart
    }
    pub fn readings(&self) -> &[StationRead] {
        &self.readings
    }
    /// Sparse forward keeps its actual Held/UncertifiedDomain decisions. One-future communication
    /// releases only when the producer releases and every blind grain leader agrees with it.
    /// Otherwise its fibre unites the completed leaders with the blind leaders. The point logits
    /// alone do not certify a decoded answer; `domains` retains the producer's completion receipt.
    pub fn decisions(&self) -> &[RepairedCell] {
        &self.decisions
    }
    /// The actual per-station completion receipts, including absence of a certificate.
    /// They are not independently sampled and their collection is not a joint completion law.
    pub fn domains(&self) -> &[Option<PhysicalDomainRead>] {
        &self.domains
    }

    /// Actual single-label completion consistency, when the producing owner certifies it.
    /// Its labels describe hypothetical full-population contents of the one future station,
    /// not the blind prefix-only prediction returned by `readings`. It can include self-echo.
    /// The domain intervals unite those completed images with the differently normalized sparse
    /// point. The communication's release fibre also unites the blind grain leaders with the
    /// completed leaders. A singleton union means class constancy at this grain, not constancy
    /// of the whole complex face or future-truth certainty.
    /// Absence supplies no signed-label certificate; the actual domain/decision remains available.
    pub fn completion_consistency(&self) -> Option<&PhysicalCompletionRead> {
        if self.readings.len() != 1 {
            return None;
        }
        self.domains.first()?.as_ref()?.completion.as_ref()
    }
    pub fn first_station(&self) -> usize {
        self.first
    }
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The existing exact receiving face for a downstream declared comparison. The full complex
    /// readings above retain its phase channel; this amplitude face alone is not the whole signal.
    pub fn faces(&self) -> Result<Faces, HnnError> {
        let reads = self
            .readings
            .iter()
            .map(|x| x.read.clone())
            .collect::<Vec<_>>();
        Faces::of_reads(&reads, self.grain)
    }
}

/// [agent-inferred] Completion and blind point use different source population charts. The
/// communication's release must agree on both: C_comm = C_complete ∪ leaders(y_blind). Restrict
/// the existing producer's release; never turn an uncertified point or held domain into release.
/// Erased-source repair still uses its original completed-source decision.
fn communication_decision(
    decision: &RepairedCell,
    point: &StationRead,
    domain: Option<&PhysicalDomainRead>,
) -> RepairedCell {
    let Some(domain) = domain else {
        return decision.clone();
    };
    let fibre = domain
        .classes
        .iter()
        .copied()
        .chain(point.leaders())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if matches!(decision, RepairedCell::Released(class) if fibre.as_slice() == [*class]) {
        decision.clone()
    } else {
        RepairedCell::Held {
            fibre,
            unresolved: Unresolved::PluralDomain,
        }
    }
}

/// The whole requested boundary and actual physical receipts, followed by an optional comparison.
/// No input `Intact` labels or authored symbolic answer stand in for the communicated field.
#[derive(Debug)]
pub struct PhysicalCommunication {
    pub boundary: PhysicalBoundary,
    pub opening: SourceOpeningReceipt,
    pub balances: Vec<FieldBalance>,
    pub word: WordBalance,
    pub carry: ReceptionCarry,
    pub comparison: Result<Option<PhysicalPublication>, HnnError>,
}

impl PhysicalCommunication {
    pub fn closes(&self) -> bool {
        self.opening.closes()
            && self.word.closes()
            && self.balances.iter().all(FieldBalance::closes)
    }
}

impl PhysicalResident<'_> {
    /// An intact request drives the same native field and releases its whole requested complex
    /// boundary. `receiver.aperture` contains the prefix followed by the future section; source
    /// and receiving axes use the existing admitted identity/station clock. No target is an input
    /// to the forward constructor. There is no unknown-truth reconstruction gate on this coface.
    pub fn communicate(
        &mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalBoundary) -> Option<PhysicalObservation>,
    ) -> Result<PhysicalCommunication, HnnError> {
        self.communicate_with(source, receiver, observation, false)
    }

    /// Communicate exactly one future station with the existing coupled completion-domain
    /// owner. The intact prefix supplies the source; no future class is an input. On its supported
    /// exact linear/unit route, one common label is carried through every first/pair port and
    /// native tick to `PhysicalCompletionRead::fixed_logits + label_logits[c]`.
    /// Admission is checked on this actual Word by the existing owner, not inherited from a
    /// previous fixture. A valid box remains a box; it is not a signed-label certificate.
    /// Missing domains keep the existing actual Held/absent-certificate receipt.
    /// The receiving projection may remain plural; its constancy is not future-truth fidelity.
    /// Multiple future stations need their joint mixed-slot law before this route is extended.
    pub fn communicate_one_future(
        &mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalBoundary) -> Option<PhysicalObservation>,
    ) -> Result<PhysicalCommunication, HnnError> {
        if source.len().checked_add(1) != Some(receiver.aperture) {
            return Err(HnnError::Unadmitted {
                reason: "the coupled future communication admits exactly one requested future station",
            });
        }
        self.communicate_with(source, receiver, observation, true)
    }

    fn communicate_with(
        &mut self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        observation: impl FnOnce(&PhysicalBoundary) -> Option<PhysicalObservation>,
        completion_domain: bool,
    ) -> Result<PhysicalCommunication, HnnError> {
        let first = source.len();
        let aperture = receiver.aperture;
        if first == 0 || first >= aperture {
            return Err(HnnError::Unadmitted {
                reason: "a physical communication needs a nonempty source and a requested future boundary",
            });
        }
        // A unit transport identifies addresses separated by the source period. This necessary
        // finite phase-section admission bars that wrap; it is not source-map injectivity.
        let span = u64::try_from(aperture).map_err(|_| HnnError::CountOverflow)?;
        for &ring in self.field.sources() {
            if self.constitution.transport(ring).is_one() && span > self.field.ring(ring).period() {
                return Err(HnnError::Unadmitted {
                    reason: "a unit-source communication aperture exceeds its producing phase period",
                });
            }
        }
        let chart = source.part(0..0)?;
        // An intact prefix followed by unforced stations is a request, not a cut of a known
        // answer. The producing Encoded chart is supplied by that actual prefix only.
        let section = DamagedSection::of_runs(aperture, source, vec![(0, source.clone())])?;
        let mut refused = None;
        let mut emitted = None;
        let observed_boundary =
            |blind: &PhysicalRepair, phases: &crate::hnn::receiving::ReceivingPhases| {
                // Consume the actual forward's phases and receipt once. No second rank/phase
                // declaration or post-observation reconstruction stands in for that boundary.
                let boundary = PhysicalBoundary::of_suffix(
                    blind,
                    chart,
                    first,
                    phases.grain(),
                    completion_domain,
                );
                let observed = observation(&boundary);
                emitted = Some(boundary);
                let observed = observed?;
                let prefix = observed.observed.part(0..first);
                if observed.compared.len() != aperture
                    || observed.compared.iter().take(first).any(|x| *x)
                    || !observed.compared.iter().skip(first).any(|x| *x)
                    || prefix.as_ref().map_or(true, |prefix| prefix != source)
                {
                    refused = Some(HnnError::Unadmitted {
                        reason: "the communication comparison changes its source prefix or requested partition",
                    });
                    return None;
                }
                Some(observed)
            };
        let received = if completion_domain {
            // This is the same producing Word/phase/observation consumer as physical reception.
            // Its actual domain travels with the blind suffix, without a second request or Word.
            self.receive_with(&section, receiver, observed_boundary, false)?
        } else {
            self.receive_sparse(&section, receiver, observed_boundary)?
        };
        let prediction = received.prediction;
        let boundary = emitted.ok_or(HnnError::Unadmitted {
            reason: "the physical communication produced no receiving boundary",
        })?;
        Ok(PhysicalCommunication {
            boundary,
            opening: prediction.opening,
            balances: prediction.balances,
            word: prediction.word,
            carry: prediction.carry,
            comparison: match refused {
                Some(error) => Err(error),
                None => received.comparison,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::receiving::ReceivingRead;
    use crate::ratio::algebraic::ExactInterval;
    use crate::ratio::integer;

    #[test]
    fn one_future_decision_unites_the_blind_grain_leaders_with_completed_leaders() {
        // A direct receiver-contract falsifier, not a claim that a selected material produces
        // these readings. All complete label columns lead class 1; the differently normalized
        // blind point can lead class 0, agree on class 1, or tie. No Word/target/search is used.
        let domain = PhysicalDomainRead {
            logits: vec![
                ExactInterval {
                    lower: integer(0),
                    upper: integer(1),
                },
                ExactInterval {
                    lower: integer(0),
                    upper: integer(0),
                },
                ExactInterval {
                    lower: integer(0),
                    upper: integer(1),
                },
                ExactInterval {
                    lower: integer(0),
                    upper: integer(0),
                },
            ],
            classes: vec![1],
            completion: Some(PhysicalCompletionRead {
                station: 2,
                fixed_logits: vec![integer(0), integer(0), integer(1), integer(0)],
                label_logits: vec![vec![integer(0); 4]; 2],
            }),
        };
        let point = |left, right| StationRead {
            station: 2,
            crossing: 2,
            tick: 2,
            read: ReceivingRead::of_logits(
                vec![integer(left), integer(0), integer(right), integer(0)],
                16,
            ),
        };
        let released = RepairedCell::Released(1);
        let plural = RepairedCell::Held {
            fibre: vec![0, 1],
            unresolved: Unresolved::PluralDomain,
        };
        assert_eq!(
            communication_decision(&released, &point(1, 0), Some(&domain)),
            plural
        );
        assert_eq!(
            communication_decision(&released, &point(1, 1), Some(&domain)),
            plural
        );
        assert_eq!(
            communication_decision(&released, &point(0, 1), Some(&domain)),
            released
        );
        let absent = RepairedCell::Held {
            fibre: vec![0, 1],
            unresolved: Unresolved::UncertifiedDomain,
        };
        assert_eq!(communication_decision(&absent, &point(0, 1), None), absent);
        let held = RepairedCell::Held {
            fibre: vec![1],
            unresolved: Unresolved::PluralDomain,
        };
        assert_eq!(
            communication_decision(&held, &point(0, 1), Some(&domain)),
            held
        );
        let mut boxed = domain.clone();
        boxed.completion = None;
        assert_eq!(
            communication_decision(&released, &point(1, 0), Some(&boxed)),
            plural
        );
        // Joining the communication decision cannot alter the producing completion certificate.
        assert_eq!(domain.classes, vec![1]);
        assert!(domain.completion.is_some());
    }
}
