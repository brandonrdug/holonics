//! Addressed occurrence passages and witness-preserving serial composition.
//!
//! The extensional endpoint relation is emitted only as a receiver shadow.  The owned object keeps
//! the carrying event occurrence, both boundary maps, and every pullback join witness.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::evolution::EvolutionLawId;
use holonic_engine::interaction::{InteractionId, InteractionTemporality, OccurrencePort};
use holonic_engine::ported_operation::PortedOperationComplex;

use super::MathematicalParticleError;

/// One endpoint in the M1 passage. Exterior source populations remain addressed material;
/// resident endpoints are ordered typed-port words.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PassageEndpoint {
    Exterior(BTreeSet<String>),
    Ports(Vec<BoundaryId>),
}

impl PassageEndpoint {
    pub fn exterior(&self) -> Option<&BTreeSet<String>> {
        match self {
            Self::Exterior(sources) => Some(sources),
            Self::Ports(_) => None,
        }
    }

    pub fn ports(&self) -> Option<&[BoundaryId]> {
        match self {
            Self::Exterior(_) => None,
            Self::Ports(ports) => Some(ports),
        }
    }
}

/// One inhabitant of the occurrence population `W_f`, together with its two boundary readings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AddressedPassageOccurrence {
    occurrence: EventId,
    law: EvolutionLawId,
    source: PassageEndpoint,
    target: PassageEndpoint,
}

impl AddressedPassageOccurrence {
    pub fn occurrence(&self) -> EventId {
        self.occurrence
    }

    pub fn law(&self) -> EvolutionLawId {
        self.law
    }

    pub fn source(&self) -> &PassageEndpoint {
        &self.source
    }

    pub fn target(&self) -> &PassageEndpoint {
        &self.target
    }
}

/// One inhabited cell of `W_f x_Y W_g`. The shared endpoint is the joining equality's retained
/// value; interaction ids witness that the equality is enacted rather than inferred from labels.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PullbackJoinOccurrence {
    left: EventId,
    right: EventId,
    shared: PassageEndpoint,
    interactions: BTreeSet<InteractionId>,
}

impl PullbackJoinOccurrence {
    pub fn left(&self) -> EventId {
        self.left
    }

    pub fn right(&self) -> EventId {
        self.right
    }

    pub fn shared(&self) -> &PassageEndpoint {
        &self.shared
    }

    pub fn interactions(&self) -> &BTreeSet<InteractionId> {
        &self.interactions
    }
}

/// The deliberately lossy endpoint receiver. Its fibre is retained by [`AddressedPassage`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PassageRelationalShadow {
    source: PassageEndpoint,
    target: PassageEndpoint,
}

impl PassageRelationalShadow {
    pub fn source(&self) -> &PassageEndpoint {
        &self.source
    }

    pub fn target(&self) -> &PassageEndpoint {
        &self.target
    }
}

/// The lineage-bearing operation passage. This is a finite enacted chart of the span
/// `X <- W_f -> Y`; it is not the endpoint relation and is not a branch schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AddressedPassage {
    occurrences: BTreeMap<EventId, AddressedPassageOccurrence>,
    pullback_joins: BTreeSet<PullbackJoinOccurrence>,
    shadow_fibres: BTreeMap<PassageRelationalShadow, BTreeSet<EventId>>,
}

/// One iterated pullback in its bracket-free ordered normal form. Every adjacent join remains
/// inspectable, so a later receiver can choose a cut without reconstructing lineage from a shadow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageCompositeOccurrence {
    word: Vec<EventId>,
    source: PassageEndpoint,
    target: PassageEndpoint,
    joins: Vec<PullbackJoinOccurrence>,
}

impl PassageCompositeOccurrence {
    pub fn word(&self) -> &[EventId] {
        &self.word
    }

    pub fn source(&self) -> &PassageEndpoint {
        &self.source
    }

    pub fn target(&self) -> &PassageEndpoint {
        &self.target
    }

    pub fn joins(&self) -> &[PullbackJoinOccurrence] {
        &self.joins
    }
}

impl AddressedPassage {
    pub(super) fn from_parts(
        occurrences: BTreeMap<EventId, AddressedPassageOccurrence>,
        pullback_joins: BTreeSet<PullbackJoinOccurrence>,
    ) -> Result<Self, MathematicalParticleError> {
        if occurrences.is_empty() {
            return Err(MathematicalParticleError::AddressedPassageEmpty);
        }
        if occurrences
            .iter()
            .any(|(id, occurrence)| id != &occurrence.occurrence)
        {
            return Err(MathematicalParticleError::AddressedOccurrenceKeyDisagrees);
        }
        for join in &pullback_joins {
            let left = occurrences.get(&join.left).ok_or(
                MathematicalParticleError::PullbackOccurrenceUnknown(join.left),
            )?;
            let right = occurrences.get(&join.right).ok_or(
                MathematicalParticleError::PullbackOccurrenceUnknown(join.right),
            )?;
            if left.target != join.shared || right.source != join.shared {
                return Err(MathematicalParticleError::PullbackBoundaryDisagrees {
                    left: join.left,
                    right: join.right,
                });
            }
            if join.interactions.is_empty() {
                return Err(MathematicalParticleError::PullbackInteractionAbsent {
                    left: join.left,
                    right: join.right,
                });
            }
        }
        let mut shadow_fibres = BTreeMap::<_, BTreeSet<_>>::new();
        for occurrence in occurrences.values() {
            shadow_fibres
                .entry(PassageRelationalShadow {
                    source: occurrence.source.clone(),
                    target: occurrence.target.clone(),
                })
                .or_default()
                .insert(occurrence.occurrence);
        }
        Ok(Self {
            occurrences,
            pullback_joins,
            shadow_fibres,
        })
    }

    pub fn occurrences(&self) -> &BTreeMap<EventId, AddressedPassageOccurrence> {
        &self.occurrences
    }

    pub fn pullback_joins(&self) -> &BTreeSet<PullbackJoinOccurrence> {
        &self.pullback_joins
    }

    pub fn shadow_fibres(&self) -> &BTreeMap<PassageRelationalShadow, BTreeSet<EventId>> {
        &self.shadow_fibres
    }

    /// Split and rejoin a retained pullback occurrence. This is the executable anti-truncation
    /// control: no search through the endpoint relation is used.
    pub fn split_rejoin(
        &self,
        left: EventId,
        right: EventId,
    ) -> Result<&PullbackJoinOccurrence, MathematicalParticleError> {
        self.pullback_joins
            .iter()
            .find(|join| join.left == left && join.right == right)
            .ok_or(MathematicalParticleError::PullbackOccurrenceAbsent { left, right })
    }

    /// Compose an ordered event word from its retained pullback occurrences. Brackets do not enter
    /// this representation; every legal cut therefore reads the same outer boundary maps.
    pub fn compose_word(
        &self,
        word: &[EventId],
    ) -> Result<PassageCompositeOccurrence, MathematicalParticleError> {
        let first = word
            .first()
            .and_then(|event| self.occurrences.get(event))
            .ok_or(MathematicalParticleError::AddressedPassageEmpty)?;
        let last = word
            .last()
            .and_then(|event| self.occurrences.get(event))
            .ok_or(MathematicalParticleError::AddressedPassageEmpty)?;
        let joins = word
            .windows(2)
            .map(|pair| self.split_rejoin(pair[0], pair[1]).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        Ok(PassageCompositeOccurrence {
            word: word.to_vec(),
            source: first.source.clone(),
            target: last.target.clone(),
            joins,
        })
    }

    /// Runtime associativity receipt for two cuts of the same ordered pullback word.
    pub fn rebracketing_preserves_boundaries(
        &self,
        word: &[EventId],
        left_cut: usize,
        right_cut: usize,
    ) -> Result<bool, MathematicalParticleError> {
        if word.len() < 3
            || left_cut == 0
            || right_cut == 0
            || left_cut >= word.len()
            || right_cut >= word.len()
            || left_cut == right_cut
        {
            return Err(MathematicalParticleError::PassageRebracketingInvalid);
        }
        let whole = self.compose_word(word)?;
        let left_prefix = self.compose_word(&word[..left_cut])?;
        let left_suffix = self.compose_word(&word[left_cut..])?;
        let right_prefix = self.compose_word(&word[..right_cut])?;
        let right_suffix = self.compose_word(&word[right_cut..])?;
        self.split_rejoin(word[left_cut - 1], word[left_cut])?;
        self.split_rejoin(word[right_cut - 1], word[right_cut])?;
        Ok(left_prefix.source == whole.source
            && left_suffix.target == whole.target
            && right_prefix.source == whole.source
            && right_suffix.target == whole.target)
    }
}

/// A structural passage equivalence. Totality, bijectivity and both boundary squares are checked
/// when it is founded; the map is retained as testimony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageEquivalence {
    occurrence_map: BTreeMap<EventId, EventId>,
}

impl PassageEquivalence {
    pub fn found(
        left: &AddressedPassage,
        right: &AddressedPassage,
        occurrence_map: BTreeMap<EventId, EventId>,
    ) -> Result<Self, MathematicalParticleError> {
        if occurrence_map.keys().copied().collect::<BTreeSet<_>>()
            != left.occurrences.keys().copied().collect()
            || occurrence_map.values().copied().collect::<BTreeSet<_>>()
                != right.occurrences.keys().copied().collect()
            || occurrence_map.len() != right.occurrences.len()
        {
            return Err(MathematicalParticleError::PassageEquivalenceNotBijective);
        }
        for (source, target) in &occurrence_map {
            let left_occurrence = &left.occurrences[source];
            let right_occurrence = &right.occurrences[target];
            if left_occurrence.source != right_occurrence.source
                || left_occurrence.target != right_occurrence.target
            {
                return Err(MathematicalParticleError::PassageEquivalenceMovesBoundary {
                    left: *source,
                    right: *target,
                });
            }
        }
        Ok(Self { occurrence_map })
    }

    pub fn identity(passage: &AddressedPassage) -> Self {
        Self {
            occurrence_map: passage
                .occurrences
                .keys()
                .map(|occurrence| (*occurrence, *occurrence))
                .collect(),
        }
    }

    pub fn occurrence_map(&self) -> &BTreeMap<EventId, EventId> {
        &self.occurrence_map
    }
}

pub(super) fn operation_occurrence(
    event: EventId,
    source: PassageEndpoint,
    target: PassageEndpoint,
    operation: &PortedOperationComplex,
) -> Result<AddressedPassageOccurrence, MathematicalParticleError> {
    let occurrence = operation
        .shape
        .occurrences
        .get(&event)
        .ok_or(MathematicalParticleError::UnknownEvent(event))?;
    let law = operation
        .shape
        .laws
        .get(&occurrence.law)
        .ok_or(MathematicalParticleError::UnknownLaw(occurrence.law))?;
    if source.ports().is_some_and(|ports| ports != law.inputs)
        || target.ports().is_none_or(|ports| ports != law.outputs)
        || source.exterior().is_some() && !law.inputs.is_empty()
    {
        return Err(MathematicalParticleError::AddressedBoundaryOutsideLaw(
            event,
        ));
    }
    Ok(AddressedPassageOccurrence {
        occurrence: event,
        law: occurrence.law,
        source,
        target,
    })
}

pub(super) fn pullback_join(
    left: &AddressedPassageOccurrence,
    right: &AddressedPassageOccurrence,
    operation: &PortedOperationComplex,
) -> Result<PullbackJoinOccurrence, MathematicalParticleError> {
    if left.target != right.source {
        return Err(MathematicalParticleError::PullbackBoundaryDisagrees {
            left: left.occurrence,
            right: right.occurrence,
        });
    }
    let shared =
        left.target
            .ports()
            .ok_or(MathematicalParticleError::PullbackBoundaryDisagrees {
                left: left.occurrence,
                right: right.occurrence,
            })?;
    let mut interactions = BTreeSet::new();
    for (position, boundary) in shared.iter().enumerate() {
        let source = OccurrencePort::output(left.occurrence, position);
        let target = OccurrencePort::input(right.occurrence, position);
        let witnesses = operation
            .shape
            .interactions
            .iter()
            .filter_map(|(id, interaction)| {
                (interaction.temporality == InteractionTemporality::CarriesPrecedence
                    && interaction.boundary == *boundary
                    && interaction
                        .bonds
                        .iter()
                        .any(|bond| bond.source == source && bond.target == target))
                .then_some(*id)
            })
            .collect::<BTreeSet<_>>();
        if witnesses.is_empty() {
            return Err(MathematicalParticleError::PullbackInteractionAbsent {
                left: left.occurrence,
                right: right.occurrence,
            });
        }
        interactions.extend(witnesses);
    }
    Ok(PullbackJoinOccurrence {
        left: left.occurrence,
        right: right.occurrence,
        shared: left.target.clone(),
        interactions,
    })
}

#[cfg(test)]
pub(super) fn addressed_occurrence_for_control(
    event: EventId,
    law: EvolutionLawId,
    source: PassageEndpoint,
    target: PassageEndpoint,
) -> AddressedPassageOccurrence {
    AddressedPassageOccurrence {
        occurrence: event,
        law,
        source,
        target,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn two_cuts_of_one_three_occurrence_passage_keep_the_same_outer_boundaries() {
        let ports = [
            BoundaryId(21),
            BoundaryId(22),
            BoundaryId(23),
            BoundaryId(24),
        ];
        let events = [EventId(31), EventId(32), EventId(33)];
        let occurrences = BTreeMap::from([
            (
                events[0],
                addressed_occurrence_for_control(
                    events[0],
                    EvolutionLawId(41),
                    PassageEndpoint::Ports(vec![ports[0]]),
                    PassageEndpoint::Ports(vec![ports[1]]),
                ),
            ),
            (
                events[1],
                addressed_occurrence_for_control(
                    events[1],
                    EvolutionLawId(42),
                    PassageEndpoint::Ports(vec![ports[1]]),
                    PassageEndpoint::Ports(vec![ports[2]]),
                ),
            ),
            (
                events[2],
                addressed_occurrence_for_control(
                    events[2],
                    EvolutionLawId(43),
                    PassageEndpoint::Ports(vec![ports[2]]),
                    PassageEndpoint::Ports(vec![ports[3]]),
                ),
            ),
        ]);
        let joins = BTreeSet::from([
            PullbackJoinOccurrence {
                left: events[0],
                right: events[1],
                shared: PassageEndpoint::Ports(vec![ports[1]]),
                interactions: BTreeSet::from([InteractionId(51)]),
            },
            PullbackJoinOccurrence {
                left: events[1],
                right: events[2],
                shared: PassageEndpoint::Ports(vec![ports[2]]),
                interactions: BTreeSet::from([InteractionId(52)]),
            },
        ]);
        let passage = AddressedPassage::from_parts(occurrences, joins).unwrap();

        assert!(passage
            .rebracketing_preserves_boundaries(&events, 1, 2)
            .unwrap());
        let composite = passage.compose_word(&events).unwrap();
        assert_eq!(composite.source(), &PassageEndpoint::Ports(vec![ports[0]]));
        assert_eq!(composite.target(), &PassageEndpoint::Ports(vec![ports[3]]));
        assert_eq!(composite.joins().len(), 2);
    }
}
