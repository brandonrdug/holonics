//! Proposal, refusal, open-fibre, and resident admission ownership.

use super::*;

#[derive(Debug)]
pub struct ParticleProposal {
    pub(super) occurrence: String,
    pub(super) passage: PassageSelection,
    pub(super) owner_attempt: ProposalOwnerAttempt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ProposalOwnerAttempt {
    Licensed {
        /// Exact-owner evidence identity per licensed law.
        licenses: BTreeMap<EvolutionLawId, String>,
    },
    ExactOwnerRefused(ExactOwnerWitnessRefusal),
    TypingRefused(MathematicalParticleError),
    Open {
        fibre_occurrence: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParticleRefusal {
    pub(super) proposal: String,
    pub(super) obstruction: ProposalRefusal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposalRefusal {
    ExactOwner(ExactOwnerWitnessRefusal),
    Typing(MathematicalParticleError),
}

impl ParticleProposal {
    pub fn from_exact_owner_result(
        occurrence: impl Into<String>,
        passage: PassageSelection,
        returned: Result<Vec<ExactOwnerLicense>, ExactOwnerWitnessRefusal>,
    ) -> (Self, Option<ParticleRefusal>) {
        let occurrence = occurrence.into();
        match returned {
            Ok(licenses) => {
                let licenses = licenses
                    .into_iter()
                    .map(|license| {
                        (
                            license.constraint().law(),
                            license.evidence_sha256().to_owned(),
                        )
                    })
                    .collect();
                (
                    Self {
                        occurrence,
                        passage,
                        owner_attempt: ProposalOwnerAttempt::Licensed { licenses },
                    },
                    None,
                )
            }
            Err(refusal) => {
                let proposal = Self {
                    occurrence: occurrence.clone(),
                    passage,
                    owner_attempt: ProposalOwnerAttempt::ExactOwnerRefused(refusal.clone()),
                };
                let returned = ParticleRefusal {
                    proposal: occurrence,
                    obstruction: ProposalRefusal::ExactOwner(refusal),
                };
                (proposal, Some(returned))
            }
        }
    }

    pub fn open(
        occurrence: impl Into<String>,
        passage: PassageSelection,
        fibre_occurrence: impl Into<String>,
    ) -> Self {
        Self {
            occurrence: occurrence.into(),
            passage,
            owner_attempt: ProposalOwnerAttempt::Open {
                fibre_occurrence: fibre_occurrence.into(),
            },
        }
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }

    pub fn passage(&self) -> &PassageSelection {
        &self.passage
    }
}

impl ParticleRefusal {
    pub fn proposal(&self) -> &str {
        &self.proposal
    }

    pub fn obstruction(&self) -> &ProposalRefusal {
        &self.obstruction
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenParticleFiber {
    pub occurrence: String,
    pub question: String,
    pub candidates: BTreeSet<String>,
    pub would_be_decided_by: BTreeSet<String>,
}

#[derive(Debug)]
pub struct PresentationFiberOccurrence {
    pub occurrence: String,
    pub fibre: CoTestimonyFiber,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParticleAdmissionInput {
    pub proposal: String,
    pub typing_occurrence: String,
    pub exact_owner: ExactOwnerOccurrence,
    pub passage_receipt: Option<ExactOwnerDeedReceipt>,
}

#[derive(Debug)]
pub struct ParticleAdmission {
    pub(super) proposal: String,
    pub(super) typing_occurrence: String,
    pub(super) exact_owner: ExactOwnerOccurrence,
    pub(super) passage_receipt: ExactOwnerDeedReceipt,
    pub(super) bindings: Vec<BindingValidation>,
}

impl ParticleAdmission {
    pub fn proposal(&self) -> &str {
        &self.proposal
    }
    pub fn typing_occurrence(&self) -> &str {
        &self.typing_occurrence
    }
    pub fn bindings(&self) -> &[BindingValidation] {
        &self.bindings
    }
    pub fn exact_owner(&self) -> &ExactOwnerOccurrence {
        &self.exact_owner
    }
    pub fn passage_receipt(&self) -> &ExactOwnerDeedReceipt {
        &self.passage_receipt
    }
}
