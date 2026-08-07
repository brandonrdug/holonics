//! Abstract evolution shapes with typed occurrences and explicit incidence.
//!
//! The shape states admissible causal organization. Exact geometry, logical
//! resource analysis, and hardware execution are separate realizations of
//! this same object.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    BoundaryId, CategoryPresentation, CausalDiagram, DiagramError, EventId, InteractionBond,
    InteractionId, InteractionPattern, InteractionTemporality, OccurrencePort, PortHand,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EvolutionLawId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvolutionLaw {
    pub id: EvolutionLawId,
    pub name: String,
    pub inputs: Vec<BoundaryId>,
    pub outputs: Vec<BoundaryId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvolutionOccurrence {
    pub event: EventId,
    pub law: EvolutionLawId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvolutionShape {
    pub schema: String,
    pub boundaries: CategoryPresentation,
    pub chronology: CausalDiagram,
    pub laws: BTreeMap<EvolutionLawId, EvolutionLaw>,
    pub occurrences: BTreeMap<EventId, EvolutionOccurrence>,
    pub interactions: BTreeMap<InteractionId, InteractionPattern>,
    next_law: u64,
    next_interaction: u64,
}

impl Default for EvolutionShape {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.evolution-shape.v1".to_owned(),
            boundaries: CategoryPresentation::default(),
            chronology: CausalDiagram::default(),
            laws: BTreeMap::new(),
            occurrences: BTreeMap::new(),
            interactions: BTreeMap::new(),
            next_law: 1,
            next_interaction: 1,
        }
    }
}

impl EvolutionShape {
    pub fn add_boundary(&mut self, name: impl Into<String>) -> BoundaryId {
        self.boundaries.add_object(name)
    }

    pub fn add_law(
        &mut self,
        name: impl Into<String>,
        inputs: Vec<BoundaryId>,
        outputs: Vec<BoundaryId>,
    ) -> Result<EvolutionLawId, EvolutionError> {
        for boundary in inputs.iter().chain(&outputs) {
            if !self.boundaries.objects.contains_key(boundary) {
                return Err(EvolutionError::MissingBoundary(*boundary));
            }
        }
        let id = EvolutionLawId(self.next_law);
        self.next_law += 1;
        self.laws.insert(
            id,
            EvolutionLaw {
                id,
                name: name.into(),
                inputs,
                outputs,
            },
        );
        Ok(id)
    }

    pub fn add_occurrence(&mut self, law: EvolutionLawId) -> Result<EventId, EvolutionError> {
        let law_name = self
            .laws
            .get(&law)
            .ok_or(EvolutionError::MissingLaw(law))?
            .name
            .clone();
        let event = self.chronology.add_event(law_name);
        self.occurrences
            .insert(event, EvolutionOccurrence { event, law });
        Ok(event)
    }

    pub fn add_precedence(
        &mut self,
        before: EventId,
        after: EventId,
    ) -> Result<(), EvolutionError> {
        self.chronology.precedes(before, after)?;
        Ok(())
    }

    /// Admit one actual interaction.
    ///
    /// All bonds are checked before either the interaction or its chronology
    /// becomes visible. Repeated bonds remain repeated incidence.
    pub fn add_interaction(
        &mut self,
        mut interaction: InteractionPattern,
    ) -> Result<InteractionId, EvolutionError> {
        if interaction.bonds.is_empty() {
            return Err(EvolutionError::EmptyInteraction);
        }
        for bond in &interaction.bonds {
            self.validate_bond(interaction.boundary, bond)?;
        }
        let mut chronology = self.chronology.clone();
        if interaction.temporality == InteractionTemporality::CarriesPrecedence {
            for bond in &interaction.bonds {
                chronology.precedes(bond.source.event, bond.target.event)?;
            }
        }
        let id = InteractionId(self.next_interaction);
        self.next_interaction += 1;
        interaction.id = id;
        self.chronology = chronology;
        self.interactions.insert(id, interaction);
        Ok(id)
    }

    pub fn validate(&self) -> Result<(), EvolutionError> {
        for event in self.chronology.events.keys() {
            let occurrence = self
                .occurrences
                .get(event)
                .ok_or(EvolutionError::UnboundOccurrence(*event))?;
            if !self.laws.contains_key(&occurrence.law) {
                return Err(EvolutionError::MissingLaw(occurrence.law));
            }
        }
        for interaction in self.interactions.values() {
            if interaction.bonds.is_empty() {
                return Err(EvolutionError::EmptyInteraction);
            }
            for bond in &interaction.bonds {
                self.validate_bond(interaction.boundary, bond)?;
            }
        }
        self.chronology.layers()?;
        Ok(())
    }

    pub fn port_boundary(&self, port: OccurrencePort) -> Result<BoundaryId, EvolutionError> {
        let occurrence = self
            .occurrences
            .get(&port.event)
            .ok_or(EvolutionError::MissingOccurrence(port.event))?;
        let law = self
            .laws
            .get(&occurrence.law)
            .ok_or(EvolutionError::MissingLaw(occurrence.law))?;
        let ports = match port.hand {
            PortHand::Input => &law.inputs,
            PortHand::Output => &law.outputs,
        };
        ports
            .get(port.ordinal)
            .copied()
            .ok_or(EvolutionError::MissingPort(port))
    }

    fn validate_bond(
        &self,
        boundary: BoundaryId,
        bond: &InteractionBond,
    ) -> Result<(), EvolutionError> {
        if bond.source.hand != PortHand::Output || bond.target.hand != PortHand::Input {
            return Err(EvolutionError::InvalidHand {
                emitter: bond.source,
                target: bond.target,
            });
        }
        let source_boundary = self.port_boundary(bond.source)?;
        let target_boundary = self.port_boundary(bond.target)?;
        if source_boundary != boundary || target_boundary != boundary {
            return Err(EvolutionError::BoundaryMismatch {
                declared: boundary,
                emitted: source_boundary,
                target: target_boundary,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum EvolutionError {
    #[error("boundary {0:?} is absent from the evolution shape")]
    MissingBoundary(BoundaryId),
    #[error("evolution law {0:?} is absent")]
    MissingLaw(EvolutionLawId),
    #[error("evolution occurrence {0:?} is absent")]
    MissingOccurrence(EventId),
    #[error("event {0:?} has no law binding")]
    UnboundOccurrence(EventId),
    #[error("port {0:?} is absent from its occurrence law")]
    MissingPort(OccurrencePort),
    #[error("an interaction requires at least one explicit bond")]
    EmptyInteraction,
    #[error("interaction hand must conduct from an output port to an input port")]
    InvalidHand {
        emitter: OccurrencePort,
        target: OccurrencePort,
    },
    #[error(
        "interaction declares {declared:?}, but its source carries {emitted:?} and target carries {target:?}"
    )]
    BoundaryMismatch {
        declared: BoundaryId,
        emitted: BoundaryId,
        target: BoundaryId,
    },
    #[error(transparent)]
    Diagram(#[from] DiagramError),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn juxtaposed_occurrences_do_not_meet_until_an_interaction_is_admitted() {
        let mut shape = EvolutionShape::default();
        let current = shape.add_boundary("current");
        let emit = shape.add_law("emit", Vec::new(), vec![current]).unwrap();
        let receive = shape.add_law("receive", vec![current], Vec::new()).unwrap();
        let source = shape.add_occurrence(emit).unwrap();
        let target = shape.add_occurrence(receive).unwrap();
        assert_eq!(
            shape.chronology.layers().unwrap(),
            vec![vec![source, target]]
        );

        shape
            .add_interaction(InteractionPattern::new(
                "declared current hand",
                current,
                InteractionTemporality::CarriesPrecedence,
                vec![InteractionBond {
                    source: OccurrencePort::output(source, 0),
                    target: OccurrencePort::input(target, 0),
                }],
            ))
            .unwrap();
        assert_eq!(
            shape.chronology.layers().unwrap(),
            vec![vec![source], vec![target]]
        );
    }

    #[test]
    fn a_label_cannot_hide_an_interaction_boundary_mismatch() {
        let mut shape = EvolutionShape::default();
        let left = shape.add_boundary("same label");
        let right = shape.add_boundary("same label");
        let emit = shape.add_law("emit", Vec::new(), vec![left]).unwrap();
        let receive = shape.add_law("receive", vec![right], Vec::new()).unwrap();
        let source = shape.add_occurrence(emit).unwrap();
        let target = shape.add_occurrence(receive).unwrap();
        assert!(matches!(
            shape.add_interaction(InteractionPattern::new(
                "invalid meeting",
                left,
                InteractionTemporality::CarriesPrecedence,
                vec![InteractionBond {
                    source: OccurrencePort::output(source, 0),
                    target: OccurrencePort::input(target, 0),
                }],
            )),
            Err(EvolutionError::BoundaryMismatch { .. })
        ));
    }
}
