use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MarkedDiagramRelation {
    pub(super) source_marks: BTreeMap<String, String>,
    pub(super) ports: BTreeMap<BoundaryId, BoundaryId>,
    pub(super) laws: BTreeMap<EvolutionLawId, EvolutionLawId>,
    pub(super) events: BTreeMap<EventId, EventId>,
    pub(super) interactions: BTreeMap<InteractionId, InteractionId>,
    pub(super) ordered_words: BTreeMap<String, String>,
    pub(super) obstruction_fibres: BTreeMap<String, String>,
    pub(super) witness: RelationWitness,
}

impl MarkedDiagramRelation {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        source_marks: BTreeMap<String, String>,
        ports: BTreeMap<BoundaryId, BoundaryId>,
        laws: BTreeMap<EvolutionLawId, EvolutionLawId>,
        events: BTreeMap<EventId, EventId>,
        interactions: BTreeMap<InteractionId, InteractionId>,
        ordered_words: BTreeMap<String, String>,
        obstruction_fibres: BTreeMap<String, String>,
        witness: RelationWitness,
        evidence: &BTreeSet<String>,
        source_occurrences: &BTreeSet<String>,
        operation: &PortedOperationComplex,
        passages: &[TypedPassage],
        presentation_fibres: &[PresentationFiberOccurrence],
        open_fibres: &[OpenParticleFiber],
    ) -> Result<Self, MathematicalParticleError> {
        let relation = Self {
            source_marks,
            ports,
            laws,
            events,
            interactions,
            ordered_words,
            obstruction_fibres,
            witness,
        };
        validate_diagram(
            &relation,
            evidence,
            source_occurrences,
            operation,
            passages,
            presentation_fibres,
            open_fibres,
        )?;
        Ok(relation)
    }
}

/// A doctrine equivalence carries its maps and both exact identity-composition defects. The
/// witness is beside those matrices and cannot replace them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DoctrineEquivalenceRelation {
    pub forward: PortedTransport,
    pub reverse: PortedTransport,
    pub left_identity_defect: ExactRatMatrix,
    pub right_identity_defect: ExactRatMatrix,
    pub witness: RelationWitness,
}

impl DoctrineEquivalenceRelation {
    pub fn from_transports(
        forward: PortedTransport,
        reverse: PortedTransport,
        witness: RelationWitness,
    ) -> Result<Self, MathematicalParticleError> {
        if forward.source_port != reverse.target_port || forward.target_port != reverse.source_port
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "doctrine-equivalence",
            ));
        }
        let left_identity = ExactRatMatrix::identity(forward.matrix.columns())
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let right_identity = ExactRatMatrix::identity(forward.matrix.rows())
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let left_identity_defect = reverse
            .matrix
            .multiply(&forward.matrix)
            .and_then(|product| product.subtract(&left_identity))
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let right_identity_defect = forward
            .matrix
            .multiply(&reverse.matrix)
            .and_then(|product| product.subtract(&right_identity))
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        Ok(Self {
            forward,
            reverse,
            left_identity_defect,
            right_identity_defect,
            witness,
        })
    }
}

pub(super) fn validate_diagram(
    relation: &MarkedDiagramRelation,
    evidence: &BTreeSet<String>,
    source_occurrences: &BTreeSet<String>,
    operation: &PortedOperationComplex,
    passages: &[TypedPassage],
    presentation_fibres: &[PresentationFiberOccurrence],
    open_fibres: &[OpenParticleFiber],
) -> Result<(), MathematicalParticleError> {
    relation
        .witness
        .validate("marked-diagram-isomorphism", evidence)?;
    if !relation.witness.is_established() {
        return Ok(());
    }
    let ports = operation
        .shape
        .boundaries
        .objects
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let laws = operation
        .shape
        .laws
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let events = operation
        .shape
        .occurrences
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let interactions = operation
        .shape
        .interactions
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    let words = passages
        .iter()
        .flat_map(|passage| passage.branches().values())
        .map(|word| (word.occurrence.clone(), word))
        .collect::<BTreeMap<_, _>>();
    let fibre_members = fibre_members(presentation_fibres, open_fibres);
    let fibres = fibre_members.keys().cloned().collect::<BTreeSet<_>>();
    if relation.source_marks.is_empty()
        || relation.ports.is_empty()
        || relation.laws.is_empty()
        || relation.ordered_words.is_empty()
        || !bijection(&relation.source_marks)
        || !bijection(&relation.ports)
        || !bijection(&relation.laws)
        || !bijection(&relation.events)
        || !bijection(&relation.interactions)
        || !bijection(&relation.ordered_words)
        || !bijection(&relation.obstruction_fibres)
        || relation
            .source_marks
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != *source_occurrences
        || relation
            .source_marks
            .values()
            .cloned()
            .collect::<BTreeSet<_>>()
            != *source_occurrences
        || relation.ports.keys().copied().collect::<BTreeSet<_>>() != ports
        || relation.ports.values().copied().collect::<BTreeSet<_>>() != ports
        || relation.laws.keys().copied().collect::<BTreeSet<_>>() != laws
        || relation.laws.values().copied().collect::<BTreeSet<_>>() != laws
        || relation.events.keys().copied().collect::<BTreeSet<_>>() != events
        || relation.events.values().copied().collect::<BTreeSet<_>>() != events
        || relation
            .interactions
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            != interactions
        || relation
            .interactions
            .values()
            .copied()
            .collect::<BTreeSet<_>>()
            != interactions
        || relation
            .ordered_words
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != words.keys().cloned().collect()
        || relation
            .ordered_words
            .values()
            .cloned()
            .collect::<BTreeSet<_>>()
            != words.keys().cloned().collect()
        || relation
            .obstruction_fibres
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != fibres
        || relation
            .obstruction_fibres
            .values()
            .cloned()
            .collect::<BTreeSet<_>>()
            != fibres
        || !relation
            .source_marks
            .iter()
            .all(|(left, right)| evidence.contains(left) && evidence.contains(right))
        || !relation
            .ports
            .iter()
            .all(|(left, right)| ports.contains(left) && ports.contains(right))
        || !relation
            .laws
            .iter()
            .all(|(left, right)| laws.contains(left) && laws.contains(right))
        || !relation
            .ordered_words
            .iter()
            .all(|(left, right)| words.contains_key(left) && words.contains_key(right))
        || !relation
            .obstruction_fibres
            .iter()
            .all(|(left, right)| evidence.contains(left) && evidence.contains(right))
    {
        return Err(MathematicalParticleError::MalformedRelation(
            "marked-diagram-isomorphism",
        ));
    }
    for (left, right) in &relation.laws {
        let left = &operation.shape.laws[left];
        let right = &operation.shape.laws[right];
        if left
            .inputs
            .iter()
            .map(|port| relation.ports[port])
            .collect::<Vec<_>>()
            != right.inputs
            || left
                .outputs
                .iter()
                .map(|port| relation.ports[port])
                .collect::<Vec<_>>()
                != right.outputs
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "marked-diagram-isomorphism",
            ));
        }
    }
    for (left, right) in &relation.events {
        if relation.laws[&operation.shape.occurrences[left].law]
            != operation.shape.occurrences[right].law
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "marked-diagram-isomorphism",
            ));
        }
    }
    let mapped_precedence = operation
        .shape
        .chronology
        .precedence
        .iter()
        .map(|(before, after)| (relation.events[before], relation.events[after]))
        .collect::<BTreeSet<_>>();
    if mapped_precedence != operation.shape.chronology.precedence {
        return Err(MathematicalParticleError::MalformedRelation(
            "marked-diagram-isomorphism",
        ));
    }
    for (left, right) in &relation.interactions {
        let left = &operation.shape.interactions[left];
        let right = &operation.shape.interactions[right];
        let mapped_bonds = left
            .bonds
            .iter()
            .map(|bond| {
                let mut mapped = bond.clone();
                mapped.source.event = relation.events[&bond.source.event];
                mapped.target.event = relation.events[&bond.target.event];
                mapped
            })
            .collect::<Vec<_>>();
        if left.temporality != right.temporality
            || relation.ports[&left.boundary] != right.boundary
            || mapped_bonds != right.bonds
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "marked-diagram-isomorphism",
            ));
        }
    }
    for (left, right) in &relation.ordered_words {
        let left = words[left];
        let right = words[right];
        if left.steps.len() != right.steps.len()
            || !left.steps.iter().zip(&right.steps).all(|(left, right)| {
                relation.events[&left.event] == right.event
                    && relation.laws[&left.law] == right.law
                    && left
                        .inputs
                        .iter()
                        .map(|port| relation.ports[port])
                        .collect::<Vec<_>>()
                        == right.inputs
                    && left
                        .outputs
                        .iter()
                        .map(|port| relation.ports[port])
                        .collect::<Vec<_>>()
                        == right.outputs
            })
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "marked-diagram-isomorphism",
            ));
        }
    }
    for (left, right) in &relation.obstruction_fibres {
        let mapped = fibre_members[left]
            .iter()
            .map(|member| {
                relation
                    .source_marks
                    .get(member)
                    .cloned()
                    .unwrap_or_else(|| member.clone())
            })
            .collect::<BTreeSet<_>>();
        if mapped != fibre_members[right] {
            return Err(MathematicalParticleError::MalformedRelation(
                "marked-diagram-isomorphism",
            ));
        }
    }
    Ok(())
}

fn fibre_members(
    presentations: &[PresentationFiberOccurrence],
    open: &[OpenParticleFiber],
) -> BTreeMap<String, BTreeSet<String>> {
    let mut fibres = BTreeMap::new();
    for occurrence in presentations {
        let fibre = &occurrence.fibre;
        fibres.insert(
            occurrence.occurrence.clone(),
            fibre
                .candidates
                .iter()
                .flat_map(|candidate| [candidate.left.clone(), candidate.right.clone()])
                .chain(fibre.unmatched_left.iter().cloned())
                .chain(fibre.unmatched_right.iter().cloned())
                .collect(),
        );
    }
    for occurrence in open {
        fibres.insert(occurrence.occurrence.clone(), occurrence.candidates.clone());
    }
    fibres
}

#[allow(clippy::too_many_arguments)]
pub(super) fn validate_doctrine(
    relation: &DoctrineEquivalenceRelation,
    evidence: &BTreeSet<String>,
    ports: &BTreeSet<BoundaryId>,
) -> Result<(), MathematicalParticleError> {
    relation
        .witness
        .validate("doctrine-equivalence", evidence)?;
    if !ports.contains(&relation.forward.source_port)
        || !ports.contains(&relation.forward.target_port)
        || !ports.contains(&relation.reverse.source_port)
        || !ports.contains(&relation.reverse.target_port)
    {
        return Err(MathematicalParticleError::MalformedRelation(
            "doctrine-equivalence",
        ));
    }
    let zero = |matrix: &ExactRatMatrix| {
        let zero = num_rational::BigRational::from_integer(0.into());
        matrix.entries().iter().all(|entry| entry == &zero)
    };
    validate_equality(
        zero(&relation.left_identity_defect) && zero(&relation.right_identity_defect),
        &relation.witness,
        "doctrine-equivalence",
        evidence,
    )
}

fn bijection<K: Ord, V: Ord>(map: &BTreeMap<K, V>) -> bool {
    map.values().collect::<BTreeSet<_>>().len() == map.len()
}
