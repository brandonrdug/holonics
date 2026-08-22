use super::*;

use holonic_engine::front_passage::ExactOwnerDeedReceipt;
use holonic_engine::receiver_exact_compression::{Partition, ReceiverExactCompression};
use num_bigint::BigUint;

use crate::causal_section::{SectionPresentationReading, SectionReconstructionFiber, SectionWork};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverHistoryRelation {
    pub(super) return_occurrence: String,
    pub(super) admitted_receivers: BTreeSet<String>,
    pub(super) admitted_interventions: BTreeSet<String>,
    /// Established equivalence carries the complete shared block.
    pub(super) shared_block: Option<BTreeSet<String>>,
    /// Separation carries the shortest intervention word and the receiver which saw it.
    pub(super) shortest_separator: Option<(Vec<String>, Option<String>, bool)>,
    /// OPEN carries every reconstruction candidate.
    pub(super) open_fibre: Option<BTreeSet<String>>,
    pub(super) witness: RelationWitness,
}

#[derive(Debug)]
pub struct ReceiverHistoryReturn {
    occurrence: String,
    reading: CausalSectionReading,
}

impl ReceiverHistoryReturn {
    /// Admit an owner-local causal-section reading. This raw seam is intentionally crate-local:
    /// an exterior caller may not author a block or separator and thereby assert a verdict.
    #[cfg(test)]
    pub(crate) fn found(
        occurrence: impl Into<String>,
        reading: CausalSectionReading,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() || reading.receivers.is_empty() {
            return Err(MathematicalParticleError::MalformedRelation(
                "receiver-history-equivalence",
            ));
        }
        Ok(Self {
            occurrence,
            reading,
        })
    }

    /// Return the history relation which one actual resident deed can support.
    ///
    /// One deed does not compare two presentation-specific successor histories, so it can only
    /// found an OPEN fibre. The opaque receipt supplies the addressed readback testimony; callers
    /// cannot provide blocks, separators, or a receiver verdict through this constructor.
    pub fn open_from_exact_deed(
        occurrence: impl Into<String>,
        left: &str,
        right: &str,
        deed: &ExactOwnerDeedReceipt,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty()
            || left.is_empty()
            || right.is_empty()
            || left == right
            || deed.address().is_empty()
            || deed.readbacks().is_empty()
            || deed.readbacks().values().any(Vec::is_empty)
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "receiver-history-equivalence",
            ));
        }
        let observations = deed
            .readbacks()
            .values()
            .try_fold(0_u64, |total, values| {
                let values = u64::try_from(values.len()).ok()?;
                total.checked_add(values)
            })
            .ok_or(MathematicalParticleError::MalformedRelation(
                "receiver-history-equivalence",
            ))?;
        let deed_address = deed.address().to_owned();
        let presentation = |identity: &str| SectionPresentationReading {
            identity: identity.to_owned(),
            lineage: deed_address.clone(),
            states: 1,
            sites: 1,
            bonds: 0,
            compounds: 0,
            contact_faces: BTreeSet::new(),
        };
        let open_population = BTreeSet::from([left.to_owned(), right.to_owned()]);
        let reading = CausalSectionReading {
            schema: format!("mathematical-particle.exact-deed-open:{deed_address}"),
            receivers: BTreeSet::from([format!("exact-owner-deed:{deed_address}")]),
            presentations: vec![presentation(left), presentation(right)],
            root_one_shot_blocks: Vec::new(),
            root_conduct_blocks: Vec::new(),
            reconstruction_fibers: vec![SectionReconstructionFiber {
                presentations: open_population,
                outside_declared_population_open: true,
            }],
            shortest_separators: Vec::new(),
            compression: ReceiverExactCompression {
                schema: "mathematical-particle.exact-deed-open".to_owned(),
                one_shot: Partition { blocks: Vec::new() },
                conduct: Partition { blocks: Vec::new() },
                rounds: 0,
                collapsed: Vec::new(),
            },
            work: SectionWork {
                presentations: 2,
                states: 2,
                contacts: 0,
                transitions: 0,
                observations,
                complete_state_pair_chart: BigUint::from(1_u8),
            },
        };
        Ok(Self {
            occurrence,
            reading,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }

    pub fn reading(&self) -> &CausalSectionReading {
        &self.reading
    }
}

impl ReceiverHistoryRelation {
    pub fn from_return(
        left: &str,
        right: &str,
        returned: &ReceiverHistoryReturn,
    ) -> Result<Self, MathematicalParticleError> {
        let reading_occurrence = returned.occurrence.clone();
        let reading = &returned.reading;
        let admitted_interventions = reading
            .shortest_separators
            .iter()
            .flat_map(|separator| separator.interventions.iter().cloned())
            .collect::<BTreeSet<_>>();
        let evidence = BTreeSet::from([reading_occurrence.clone()]);
        if let Some(block) = reading
            .root_conduct_blocks
            .iter()
            .find(|block| block.contains(left) && block.contains(right))
        {
            return Ok(Self {
                return_occurrence: reading_occurrence.clone(),
                admitted_receivers: reading.receivers.clone(),
                admitted_interventions,
                shared_block: Some(block.clone()),
                shortest_separator: None,
                open_fibre: None,
                witness: RelationWitness::established(evidence),
            });
        }
        if let Some(separator) = reading.shortest_separators.iter().find(|separator| {
            (separator.left == left && separator.right == right)
                || (separator.left == right && separator.right == left)
        }) {
            return Ok(Self {
                return_occurrence: reading_occurrence.clone(),
                admitted_receivers: reading.receivers.clone(),
                admitted_interventions,
                shared_block: None,
                shortest_separator: Some((
                    separator.interventions.clone(),
                    separator.receiver.clone(),
                    separator.separated_by_terminus,
                )),
                open_fibre: None,
                witness: RelationWitness::separated(reading_occurrence),
            });
        }
        let one_shot_separated = reading
            .root_one_shot_blocks
            .iter()
            .any(|block| block.contains(left))
            && reading
                .root_one_shot_blocks
                .iter()
                .any(|block| block.contains(right));
        if one_shot_separated {
            return Ok(Self {
                return_occurrence: reading_occurrence.clone(),
                admitted_receivers: reading.receivers.clone(),
                admitted_interventions,
                shared_block: None,
                shortest_separator: Some((Vec::new(), None, false)),
                open_fibre: None,
                witness: RelationWitness::separated(reading_occurrence),
            });
        }
        let mut open_fibre = reading
            .presentations
            .iter()
            .map(|presentation| presentation.identity.clone())
            .collect::<BTreeSet<_>>();
        open_fibre.insert(left.to_owned());
        open_fibre.insert(right.to_owned());
        Ok(Self {
            return_occurrence: reading_occurrence.clone(),
            admitted_receivers: reading.receivers.clone(),
            admitted_interventions,
            shared_block: None,
            shortest_separator: None,
            open_fibre: Some(open_fibre),
            witness: RelationWitness::open(
                "the actual reading did not place both occurrences in one declared block",
                evidence,
            ),
        })
    }

    pub fn witness(&self) -> &RelationWitness {
        &self.witness
    }
}

pub(super) fn validate_receiver_history(
    relation: &ReceiverHistoryRelation,
    left: &str,
    right: &str,
    evidence: &BTreeSet<String>,
) -> Result<(), MathematicalParticleError> {
    relation
        .witness
        .validate("receiver-history-equivalence", evidence)?;
    if relation.admitted_receivers.is_empty() {
        return Err(MathematicalParticleError::MalformedRelation(
            "receiver-history-equivalence",
        ));
    }
    let shape_holds = match &relation.witness {
        RelationWitness::Established { .. } => {
            relation
                .shared_block
                .as_ref()
                .is_some_and(|block| block.contains(left) && block.contains(right))
                && relation.shortest_separator.is_none()
                && relation.open_fibre.is_none()
        }
        RelationWitness::Separated { .. } => {
            relation.shared_block.is_none()
                && relation.open_fibre.is_none()
                && relation
                    .shortest_separator
                    .as_ref()
                    .is_some_and(|(word, receiver, terminus)| {
                        (word.is_empty()
                            || word
                                .iter()
                                .all(|input| relation.admitted_interventions.contains(input)))
                            && (receiver.as_ref().is_none_or(|receiver| {
                                relation.admitted_receivers.contains(receiver)
                            }) || *terminus)
                            && word
                                .iter()
                                .all(|input| relation.admitted_interventions.contains(input))
                    })
        }
        RelationWitness::Open { .. } => {
            relation.shared_block.is_none()
                && relation.shortest_separator.is_none()
                && relation
                    .open_fibre
                    .as_ref()
                    .is_some_and(|fiber| fiber.contains(left) && fiber.contains(right))
        }
    };
    shape_holds
        .then_some(())
        .ok_or(MathematicalParticleError::MalformedRelation(
            "receiver-history-equivalence",
        ))
}
