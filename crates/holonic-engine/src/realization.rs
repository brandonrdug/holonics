//! Exact realizations of one abstract evolution shape.
//!
//! A realization must account for every boundary species and every law in the
//! shape.  The output may be geometric, logical, physical, or another exact
//! domain face; executor choice is not allowed to alter the shape.

use std::collections::{BTreeMap, BTreeSet};

use relational_geometry::{Construction, EntityId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    BoundaryId, EventId, EvolutionError, EvolutionLawId, EvolutionShape, LogicalResourceReceipt,
    OccurrencePort, ReceiverError, ReceiverFace, ReceiverFaceSpec, receive_face_entities,
};

/// Addressed source/native passages assembled from the existing compression, chart, lineage and
/// apparatus owners.
pub mod passage;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RealizationWitness {
    pub schema: String,
    pub name: String,
    /// Exact domain carrier assigned to each abstract boundary species.
    pub boundary_carriers: BTreeMap<BoundaryId, String>,
    /// Exact domain operation assigned to each abstract evolution law.
    pub law_carriers: BTreeMap<EvolutionLawId, String>,
}

impl RealizationWitness {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            schema: "holonic-engine.realization-witness.v1".to_owned(),
            name: name.into(),
            boundary_carriers: BTreeMap::new(),
            law_carriers: BTreeMap::new(),
        }
    }

    pub fn bind_boundary(
        &mut self,
        boundary: BoundaryId,
        carrier: impl Into<String>,
    ) -> Option<String> {
        self.boundary_carriers.insert(boundary, carrier.into())
    }

    pub fn bind_law(&mut self, law: EvolutionLawId, carrier: impl Into<String>) -> Option<String> {
        self.law_carriers.insert(law, carrier.into())
    }

    pub fn validate(&self, shape: &EvolutionShape) -> Result<(), RealizationError> {
        shape.validate()?;
        for boundary in shape.boundaries.objects.keys() {
            if !self.boundary_carriers.contains_key(boundary) {
                return Err(RealizationError::MissingBoundaryCarrier(*boundary));
            }
        }
        for law in shape.laws.keys() {
            if !self.law_carriers.contains_key(law) {
                return Err(RealizationError::MissingLawCarrier(*law));
            }
        }
        for boundary in self.boundary_carriers.keys() {
            if !shape.boundaries.objects.contains_key(boundary) {
                return Err(RealizationError::ForeignBoundary(*boundary));
            }
        }
        for law in self.law_carriers.keys() {
            if !shape.laws.contains_key(law) {
                return Err(RealizationError::ForeignLaw(*law));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RealizationReceipt<T> {
    pub schema: String,
    pub shape_schema: String,
    pub witness: RealizationWitness,
    pub output: T,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverOperation {
    TransportPrimitive { entity: EntityId },
    AssembleContinuousFace,
}

impl ReceiverOperation {
    fn species(self) -> &'static str {
        match self {
            Self::TransportPrimitive { .. } => "transport-primitive",
            Self::AssembleContinuousFace => "assemble-continuous-face",
        }
    }
}

/// Executable assignment from every occurrence in one evolution shape to one
/// exact receiver operation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverProgram {
    pub schema: String,
    pub operations: BTreeMap<EventId, ReceiverOperation>,
}

impl Default for ReceiverProgram {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.receiver-program.v1".to_owned(),
            operations: BTreeMap::new(),
        }
    }
}

impl ReceiverProgram {
    pub fn bind(
        &mut self,
        occurrence: EventId,
        operation: ReceiverOperation,
    ) -> Option<ReceiverOperation> {
        self.operations.insert(occurrence, operation)
    }

    pub fn validate(
        &self,
        shape: &EvolutionShape,
        construction: &Construction,
    ) -> Result<BTreeSet<EntityId>, ReceiverProgramError> {
        shape.validate()?;
        for event in shape.occurrences.keys() {
            if !self.operations.contains_key(event) {
                return Err(ReceiverProgramError::MissingOperation(*event));
            }
        }
        for event in self.operations.keys() {
            if !shape.occurrences.contains_key(event) {
                return Err(ReceiverProgramError::ForeignOperation(*event));
            }
        }

        let mut law_species = BTreeMap::<EvolutionLawId, &'static str>::new();
        let mut assembled = Vec::new();
        let mut transported = BTreeSet::new();
        for (event, operation) in &self.operations {
            let occurrence = &shape.occurrences[event];
            let law = &shape.laws[&occurrence.law];
            let expected_signature = match operation {
                ReceiverOperation::TransportPrimitive { entity } => {
                    construction
                        .entities
                        .get(entity)
                        .ok_or(ReceiverProgramError::MissingEntity(*entity))?;
                    transported.insert(*entity);
                    (1, 1)
                }
                ReceiverOperation::AssembleContinuousFace => (law.inputs.len(), 1),
            };
            if law.inputs.len() != expected_signature.0 || law.outputs.len() != expected_signature.1
            {
                return Err(ReceiverProgramError::Signature {
                    event: *event,
                    operation: operation.species(),
                    inputs: law.inputs.len(),
                    outputs: law.outputs.len(),
                });
            }
            if let Some(existing) = law_species.insert(occurrence.law, operation.species())
                && existing != operation.species()
            {
                return Err(ReceiverProgramError::OneLawManySpecies(occurrence.law));
            }
            match operation {
                ReceiverOperation::AssembleContinuousFace => assembled.push(*event),
                ReceiverOperation::TransportPrimitive { .. } => {}
            }
        }
        if assembled.len() != 1 {
            return Err(ReceiverProgramError::FaceAssemblerCount(assembled.len()));
        }
        if transported.is_empty() {
            return Err(ReceiverProgramError::NoTransportedPrimitives);
        }

        let interaction_sources = shape
            .interactions
            .values()
            .flat_map(|interaction| &interaction.bonds)
            .map(|bond| bond.source)
            .collect::<BTreeSet<_>>();
        let interaction_targets = shape
            .interactions
            .values()
            .flat_map(|interaction| &interaction.bonds)
            .map(|bond| bond.target)
            .collect::<BTreeSet<_>>();
        let assembler = assembled[0];
        let assembly_law = &shape.laws[&shape.occurrences[&assembler].law];
        for input in 0..assembly_law.inputs.len() {
            if !interaction_targets.contains(&OccurrencePort::input(assembler, input)) {
                return Err(ReceiverProgramError::UncarriedAssemblyInput {
                    event: assembler,
                    input,
                });
            }
        }
        for (event, operation) in &self.operations {
            if matches!(operation, ReceiverOperation::TransportPrimitive { .. })
                && (!interaction_targets.contains(&OccurrencePort::input(*event, 0))
                    || !interaction_sources.contains(&OccurrencePort::output(*event, 0)))
            {
                return Err(ReceiverProgramError::UncarriedPrimitive(*event));
            }
        }

        let layers = shape.chronology.layers()?;
        let layer_of = layers
            .iter()
            .enumerate()
            .flat_map(|(layer, events)| events.iter().map(move |event| (*event, layer)))
            .collect::<BTreeMap<_, _>>();
        for (event, operation) in &self.operations {
            if matches!(operation, ReceiverOperation::TransportPrimitive { .. })
                && layer_of[event] >= layer_of[&assembler]
            {
                return Err(ReceiverProgramError::InvalidCausalPlacement(*event));
            }
        }
        Ok(transported)
    }
}

pub struct ReceiverRealization<'a> {
    pub witness: RealizationWitness,
    pub program: &'a ReceiverProgram,
    pub construction: &'a Construction,
    pub specification: &'a ReceiverFaceSpec,
}

impl ReceiverRealization<'_> {
    pub fn realize(
        &self,
        shape: &EvolutionShape,
    ) -> Result<RealizationReceipt<ReceiverFace>, ReceiverRealizationError> {
        self.witness.validate(shape)?;
        let entities = self.program.validate(shape, self.construction)?;
        let output = receive_face_entities(self.construction, self.specification, &entities)?;
        Ok(RealizationReceipt {
            schema: "holonic-engine.receiver-realization-receipt.v2".to_owned(),
            shape_schema: shape.schema.clone(),
            witness: self.witness.clone(),
            output,
        })
    }
}

pub struct LogicalRealization {
    pub witness: RealizationWitness,
}

impl LogicalRealization {
    pub fn realize(
        &self,
        shape: &EvolutionShape,
    ) -> Result<RealizationReceipt<LogicalResourceReceipt>, RealizationError> {
        self.witness.validate(shape)?;
        let output = LogicalResourceReceipt::from_diagram(&shape.chronology)?;
        Ok(RealizationReceipt {
            schema: "holonic-engine.logical-realization-receipt.v1".to_owned(),
            shape_schema: shape.schema.clone(),
            witness: self.witness.clone(),
            output,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RealizationError {
    #[error("realization has no carrier for boundary {0:?}")]
    MissingBoundaryCarrier(BoundaryId),
    #[error("realization has no carrier for evolution law {0:?}")]
    MissingLawCarrier(EvolutionLawId),
    #[error("realization names foreign boundary {0:?}")]
    ForeignBoundary(BoundaryId),
    #[error("realization names foreign evolution law {0:?}")]
    ForeignLaw(EvolutionLawId),
    #[error(transparent)]
    Evolution(#[from] EvolutionError),
    #[error(transparent)]
    Diagram(#[from] crate::DiagramError),
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverRealizationError {
    #[error(transparent)]
    Witness(#[from] RealizationError),
    #[error(transparent)]
    Program(#[from] ReceiverProgramError),
    #[error(transparent)]
    Receiver(#[from] ReceiverError),
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverProgramError {
    #[error("receiver program has no operation for occurrence {0:?}")]
    MissingOperation(EventId),
    #[error("receiver program names foreign occurrence {0:?}")]
    ForeignOperation(EventId),
    #[error("receiver program names absent entity {0:?}")]
    MissingEntity(EntityId),
    #[error(
        "occurrence {event:?} realizes {operation} but exposes {inputs} inputs and {outputs} outputs"
    )]
    Signature {
        event: EventId,
        operation: &'static str,
        inputs: usize,
        outputs: usize,
    },
    #[error("one abstract law {0:?} was assigned to incompatible operation species")]
    OneLawManySpecies(EvolutionLawId),
    #[error("receiver program requires exactly one continuous-face assembler, but found {0}")]
    FaceAssemblerCount(usize),
    #[error("receiver program has no caused primitives")]
    NoTransportedPrimitives,
    #[error("primitive transport occurrence {0:?} is not carried in and out")]
    UncarriedPrimitive(EventId),
    #[error("assembly occurrence {event:?} has no declared interaction at input {input}")]
    UncarriedAssemblyInput { event: EventId, input: usize },
    #[error("primitive transport occurrence {0:?} is not causally before face assembly")]
    InvalidCausalPlacement(EventId),
    #[error(transparent)]
    Evolution(#[from] EvolutionError),
    #[error(transparent)]
    Diagram(#[from] crate::DiagramError),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_realization_must_cover_the_complete_shape() {
        let mut shape = EvolutionShape::default();
        let source = shape.add_boundary("source");
        let target = shape.add_boundary("target");
        let law = shape.add_law("move", vec![source], vec![target]).unwrap();
        shape.add_occurrence(law).unwrap();

        let mut witness = RealizationWitness::new("incomplete");
        witness.bind_boundary(source, "exact source");
        witness.bind_law(law, "exact move");
        assert_eq!(
            witness.validate(&shape),
            Err(RealizationError::MissingBoundaryCarrier(target))
        );
    }
}
