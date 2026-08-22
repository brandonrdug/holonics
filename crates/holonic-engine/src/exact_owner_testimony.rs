//! Structural testimony from exact mathematical owners into the resident passage.
//!
//! This module does not recover a mathematical operation from source spelling.  It carries the
//! narrower seam the resident passage was missing: an exact owner has already returned a checked
//! constraint, and that constraint licenses one proposed operation at its nominal ports.  Source,
//! native-rest, and mathematical witnesses remain different occurrence species.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::category::BoundaryId;
use crate::exact_linear::ExactRatMatrix;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex};
use crate::quantity::{Dimension, DimensionMatrix};
use crate::source_occurrence::{BindingValidation, OccurrenceWitness, OccurrenceWitnessRefusal};

mod population;
mod typing;
pub use population::{exact_input_identity, exact_input_population_identity};
use typing::validate_contractions;
pub use typing::{
    TensorSlot, TensorSlotAddress, TensorSlotRole, TensorVariance, TypedMathematicalBoundary,
};

/// The exact owner which issued a resident constraint license.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ExactOwnerKind {
    ExactLinear,
    Quantity,
}

/// One exact constraint bound to the nominal ports of a proposed operation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PortBoundConstraint {
    law: crate::evolution::EvolutionLawId,
    operation: String,
    resident_law: String,
    species: OperationSpecies,
    inputs: Vec<TypedMathematicalBoundary>,
    outputs: Vec<TypedMathematicalBoundary>,
    matrix_sha256: String,
    matrix_rows: usize,
    matrix_columns: usize,
    input_rows: usize,
    input_width: usize,
    residual: Vec<Rat>,
    /// Quantity-only: which dimension-matrix column types each nominal boundary. Empty for other
    /// exact owners.
    boundary_columns: BTreeMap<BoundaryId, Vec<usize>>,
    quantity_kernel_word: Option<Vec<Rat>>,
    input_identity: String,
    semantic_parameters: BTreeMap<String, String>,
}

impl PortBoundConstraint {
    pub const fn law(&self) -> crate::evolution::EvolutionLawId {
        self.law
    }

    pub fn operation(&self) -> &str {
        &self.operation
    }

    pub fn resident_law(&self) -> &str {
        &self.resident_law
    }

    pub const fn species(&self) -> OperationSpecies {
        self.species
    }

    pub fn inputs(&self) -> &[TypedMathematicalBoundary] {
        &self.inputs
    }

    pub fn outputs(&self) -> &[TypedMathematicalBoundary] {
        &self.outputs
    }

    pub fn matrix_sha256(&self) -> &str {
        &self.matrix_sha256
    }

    pub const fn matrix_shape(&self) -> (usize, usize) {
        (self.matrix_rows, self.matrix_columns)
    }

    pub fn residual(&self) -> &[Rat] {
        &self.residual
    }

    pub const fn input_shape(&self) -> (usize, usize) {
        (self.input_rows, self.input_width)
    }

    pub fn boundary_columns(&self) -> &BTreeMap<BoundaryId, Vec<usize>> {
        &self.boundary_columns
    }

    pub fn quantity_kernel_word(&self) -> Option<&[Rat]> {
        self.quantity_kernel_word.as_deref()
    }

    pub fn input_identity(&self) -> &str {
        &self.input_identity
    }

    pub fn matches_matrix(&self, matrix: &ExactRatMatrix) -> bool {
        self.matrix_sha256 == matrix_identity(matrix)
    }

    pub fn semantic_parameters(&self) -> &BTreeMap<String, String> {
        &self.semantic_parameters
    }
}

/// A constraint plus the exact-owner receipt which founded it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactOwnerLicense {
    owner: ExactOwnerKind,
    constraint: PortBoundConstraint,
    evidence_sha256: String,
}

impl ExactOwnerLicense {
    /// Issue a license from `quantity`'s exact dimension matrix and checked kernel span.
    #[allow(clippy::too_many_arguments)]
    pub fn quantity(
        law: crate::evolution::EvolutionLawId,
        operation: impl Into<String>,
        resident_law: impl Into<String>,
        species: OperationSpecies,
        inputs: Vec<TypedMathematicalBoundary>,
        outputs: Vec<TypedMathematicalBoundary>,
        boundary_columns: BTreeMap<BoundaryId, Vec<usize>>,
        dimensions: &DimensionMatrix,
        kernel_word: &[Rat],
        semantic_parameters: BTreeMap<String, String>,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        if inputs.is_empty() {
            validate_quantity_boundary_columns(outputs.iter(), &boundary_columns, dimensions)?;
        } else {
            validate_quantity_boundary_columns(inputs.iter(), &boundary_columns, dimensions)?;
        }
        let groups = dimensions
            .buckingham()
            .map_err(|error| ExactOwnerWitnessRefusal::ExactOwnerRefused(error.to_string()))?;
        if !groups.contains(kernel_word) {
            return Err(ExactOwnerWitnessRefusal::QuantityWordOutsideKernel);
        }
        let matrix = dimensions
            .as_exact_matrix()
            .map_err(|error| ExactOwnerWitnessRefusal::ExactOwnerRefused(error.to_string()))?;
        let residual = matrix
            .apply(kernel_word)
            .map_err(|error| ExactOwnerWitnessRefusal::ExactOwnerRefused(error.to_string()))?;
        if residual.iter().any(|value| !value.is_zero()) {
            return Err(ExactOwnerWitnessRefusal::QuantityWordOutsideKernel);
        }
        let input_identity = exact_input_identity(kernel_word);
        Self::issued(
            ExactOwnerKind::Quantity,
            law,
            operation.into(),
            resident_law.into(),
            species,
            inputs,
            outputs,
            &matrix,
            residual,
            1,
            kernel_word.len(),
            boundary_columns,
            Some(kernel_word.to_vec()),
            input_identity,
            semantic_parameters,
            format!(
                "kernel={};rank={};smith={};transpose={}",
                rat_word(kernel_word),
                groups.rank,
                groups.rank_by_smith_normal_form,
                groups.rank_by_transpose
            ),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn issued(
        owner: ExactOwnerKind,
        law: crate::evolution::EvolutionLawId,
        operation: String,
        resident_law: String,
        species: OperationSpecies,
        inputs: Vec<TypedMathematicalBoundary>,
        outputs: Vec<TypedMathematicalBoundary>,
        matrix: &ExactRatMatrix,
        residual: Vec<Rat>,
        input_rows: usize,
        input_width: usize,
        boundary_columns: BTreeMap<BoundaryId, Vec<usize>>,
        quantity_kernel_word: Option<Vec<Rat>>,
        input_identity: String,
        semantic_parameters: BTreeMap<String, String>,
        evidence: String,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        if operation.trim().is_empty() || resident_law.trim().is_empty() {
            return Err(ExactOwnerWitnessRefusal::EmptyOperation);
        }
        let matrix_sha256 = matrix_identity(matrix);
        validate_contractions(inputs.iter().chain(&outputs))?;
        let constraint = PortBoundConstraint {
            law,
            operation,
            resident_law,
            species,
            inputs,
            outputs,
            matrix_sha256: matrix_sha256.clone(),
            matrix_rows: matrix.rows(),
            matrix_columns: matrix.columns(),
            input_rows,
            input_width,
            residual,
            boundary_columns,
            quantity_kernel_word,
            input_identity,
            semantic_parameters,
        };
        let evidence_sha256 = digest(format!(
            "owner={owner:?};law={law:?};resident-law={};species={species:?};inputs={:?};outputs={:?};matrix={matrix_sha256};input={};input-shape={}x{};{evidence};residual={};boundary-columns={:?};quantity-kernel={};semantic-parameters={:?}",
            constraint.resident_law,
            constraint.inputs,
            constraint.outputs,
            constraint.input_identity,
            constraint.input_rows,
            constraint.input_width,
            rat_word(&constraint.residual),
            constraint.boundary_columns,
            constraint
                .quantity_kernel_word
                .as_deref()
                .map(rat_word)
                .unwrap_or_else(|| "none".to_owned()),
            constraint.semantic_parameters,
        ));
        Ok(Self {
            owner,
            constraint,
            evidence_sha256,
        })
    }

    pub const fn owner(&self) -> ExactOwnerKind {
        self.owner
    }

    pub const fn constraint(&self) -> &PortBoundConstraint {
        &self.constraint
    }

    pub fn evidence_sha256(&self) -> &str {
        &self.evidence_sha256
    }
}

/// The exact-owner occurrence.  Life may bind M0/proposal lineage around this type; the engine
/// owns only the validation of resident operation testimony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactOwnerOccurrence {
    licenses: Vec<ExactOwnerLicense>,
}

impl ExactOwnerOccurrence {
    pub fn new(licenses: Vec<ExactOwnerLicense>) -> Result<Self, ExactOwnerWitnessRefusal> {
        if licenses.is_empty() {
            return Err(ExactOwnerWitnessRefusal::NoLicenses);
        }
        let mut laws = BTreeSet::new();
        for license in &licenses {
            let law = license.constraint.law;
            if !laws.insert(law) {
                return Err(ExactOwnerWitnessRefusal::DuplicateLicense { law });
            }
        }
        Ok(Self { licenses })
    }
}

impl OccurrenceWitness for ExactOwnerOccurrence {
    fn witness(&self) -> &'static str {
        "exact mathematical owners"
    }

    fn validate(
        &self,
        complex: &PortedOperationComplex,
    ) -> Result<Vec<BindingValidation>, OccurrenceWitnessRefusal> {
        let mut validated = Vec::with_capacity(complex.operations.len());
        let mut used = BTreeSet::new();
        for operation in complex.operations.values() {
            let law = complex
                .shape
                .laws
                .get(&operation.law)
                .ok_or(ExactOwnerWitnessRefusal::OperationAbsent)?;
            let license = self
                .licenses
                .iter()
                .find(|license| license.constraint.law == operation.law)
                .ok_or_else(|| ExactOwnerWitnessRefusal::LicenseAbsent { law: operation.law })?;
            let constraint = license.constraint();
            if constraint.species != operation.species {
                return Err(ExactOwnerWitnessRefusal::SpeciesDisagrees {
                    operation: law.name.clone(),
                }
                .into());
            }
            let input_ports = constraint
                .inputs
                .iter()
                .map(TypedMathematicalBoundary::boundary)
                .collect::<Vec<_>>();
            let output_ports = constraint
                .outputs
                .iter()
                .map(TypedMathematicalBoundary::boundary)
                .collect::<Vec<_>>();
            if input_ports != law.inputs || output_ports != law.outputs {
                return Err(ExactOwnerWitnessRefusal::PortsDisagree {
                    operation: law.name.clone(),
                    licensed_inputs: input_ports,
                    licensed_outputs: output_ports,
                    proposed_inputs: law.inputs.clone(),
                    proposed_outputs: law.outputs.clone(),
                }
                .into());
            }
            used.insert(operation.law);
            validated.push(BindingValidation {
                operation: law.name.clone(),
                species: operation.species,
                symbols: Vec::new(),
                fields: Vec::new(),
                shapes: Vec::new(),
                interventions: Vec::new(),
                descriptions: Vec::new(),
                exact_owner_licenses: vec![license.clone()],
            });
        }
        if let Some(extra) = self
            .licenses
            .iter()
            .map(|license| license.constraint.law)
            .find(|law| !used.contains(law))
        {
            return Err(ExactOwnerWitnessRefusal::LicenseNamesNoOperation { law: extra }.into());
        }
        Ok(validated)
    }
}

fn validate_quantity_boundary_columns<'a>(
    boundaries: impl Iterator<Item = &'a TypedMathematicalBoundary>,
    columns: &BTreeMap<BoundaryId, Vec<usize>>,
    dimensions: &DimensionMatrix,
) -> Result<(), ExactOwnerWitnessRefusal> {
    let boundaries = boundaries.collect::<Vec<_>>();
    let required = boundaries
        .iter()
        .map(|boundary| boundary.boundary())
        .collect::<BTreeSet<_>>();
    if columns.keys().copied().collect::<BTreeSet<_>>() != required {
        return Err(ExactOwnerWitnessRefusal::QuantityBoundaryColumnsDisagree);
    }
    let mut covered = BTreeSet::new();
    for boundary in boundaries {
        let word = &columns[&boundary.boundary()];
        if word.len() != boundary.dimensions().len() {
            return Err(ExactOwnerWitnessRefusal::QuantityBoundaryWidthDisagrees {
                boundary: boundary.boundary(),
                coordinates: boundary.dimensions().len(),
                columns: word.len(),
            });
        }
        for (coordinate, column) in word.iter().copied().enumerate() {
            if !covered.insert(column) {
                return Err(ExactOwnerWitnessRefusal::QuantityBoundaryColumnsOverlap { column });
            }
            let dimension = dimensions.dimensions().get(column).ok_or(
                ExactOwnerWitnessRefusal::QuantityBoundaryColumnOutside {
                    boundary: boundary.boundary(),
                    column,
                },
            )?;
            if boundary.dimensions()[coordinate] != *dimension {
                return Err(
                    ExactOwnerWitnessRefusal::QuantityBoundaryDimensionDisagrees {
                        boundary: boundary.boundary(),
                        coordinate,
                        column,
                    },
                );
            }
        }
    }
    if covered != (0..dimensions.extent()).collect::<BTreeSet<_>>() {
        return Err(ExactOwnerWitnessRefusal::QuantityBoundaryColumnsDisagree);
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactOwnerWitnessRefusal {
    #[error("an exact-owner witness carries no license")]
    NoLicenses,
    #[error("an exact-owner license has no operation or resident law")]
    EmptyOperation,
    #[error("boundary {boundary:?} has no algebraic carrier")]
    EmptyCarrier { boundary: BoundaryId },
    #[error("boundary {boundary:?} repeats one tensor-slot ordinal")]
    DuplicateTensorSlot { boundary: BoundaryId },
    #[error("tensor slot {slot:?} names absent contraction partner {partner:?}")]
    ContractionPartnerAbsent {
        slot: TensorSlotAddress,
        partner: TensorSlotAddress,
    },
    #[error("tensor slots {slot:?}/{partner:?} do not form an opposite-variance pair")]
    ContractionDoesNotPair {
        slot: TensorSlotAddress,
        partner: TensorSlotAddress,
    },
    #[error("the exact owner refused: {0}")]
    ExactOwnerRefused(String),
    #[error("{entries} aligned entries do not form rows of {columns} columns")]
    AlignedMatrixExtent { entries: usize, columns: usize },
    #[error("the exact-linear constraint returned nonzero residual {residual:?}")]
    ExactLinearResidualNonzero { residual: Vec<Rat> },
    #[error("an exact-linear transport must preserve its ordered free tensor-slot word")]
    ExactLinearFreeTensorWordDisagrees,
    #[error(
        "exact-linear transport coordinate words are input {input_coordinates}, output {output_coordinates}, but its matrix is {matrix_rows}x{matrix_columns}"
    )]
    ExactLinearCoordinateExtentDisagrees {
        input_coordinates: usize,
        output_coordinates: usize,
        matrix_rows: usize,
        matrix_columns: usize,
    },
    #[error(
        "an exact-linear transport cannot close a tensor contraction without typed coefficient standing"
    )]
    ExactLinearTensorContractionOpen,
    #[error(
        "exact-linear population is {rows}x{width} over {values} values, matrix expects width {matrix_columns}"
    )]
    ExactLinearPopulationExtent {
        rows: usize,
        width: usize,
        values: usize,
        matrix_columns: usize,
    },
    #[error("exact input population is {rows}x{width} over {values} values")]
    ExactInputPopulationExtent {
        rows: usize,
        width: usize,
        values: usize,
    },
    #[error("the quantity constraint word is outside the dimension matrix kernel")]
    QuantityWordOutsideKernel,
    #[error("the quantity boundary-to-column map does not cover exactly the licensed boundaries")]
    QuantityBoundaryColumnsDisagree,
    #[error("boundary {boundary:?} maps to absent dimension column {column}")]
    QuantityBoundaryColumnOutside { boundary: BoundaryId, column: usize },
    #[error("boundary {boundary:?} carries {coordinates} coordinates but maps {columns} columns")]
    QuantityBoundaryWidthDisagrees {
        boundary: BoundaryId,
        coordinates: usize,
        columns: usize,
    },
    #[error("dimension column {column} is mapped more than once")]
    QuantityBoundaryColumnsOverlap { column: usize },
    #[error(
        "boundary {boundary:?} coordinate {coordinate} dimension disagrees with mapped column {column}"
    )]
    QuantityBoundaryDimensionDisagrees {
        boundary: BoundaryId,
        coordinate: usize,
        column: usize,
    },
    #[error("two exact-owner licenses name law {law:?}")]
    DuplicateLicense {
        law: crate::evolution::EvolutionLawId,
    },
    #[error("the proposed operation is absent from the evolution shape")]
    OperationAbsent,
    #[error("law {law:?} has no exact-owner license")]
    LicenseAbsent {
        law: crate::evolution::EvolutionLawId,
    },
    #[error("operation {operation}'s exact-owner species disagrees")]
    SpeciesDisagrees { operation: String },
    #[error("operation {operation}'s exact-owner ports disagree")]
    PortsDisagree {
        operation: String,
        licensed_inputs: Vec<BoundaryId>,
        licensed_outputs: Vec<BoundaryId>,
        proposed_inputs: Vec<BoundaryId>,
        proposed_outputs: Vec<BoundaryId>,
    },
    #[error("exact-owner license for law {law:?} names no proposed operation")]
    LicenseNamesNoOperation {
        law: crate::evolution::EvolutionLawId,
    },
}

/// Content identity shared by an exact owner and the aligned resident mouth.
pub fn matrix_identity(matrix: &ExactRatMatrix) -> String {
    let mut carried = format!("{}x{};", matrix.rows(), matrix.columns());
    for row in matrix.to_rows() {
        carried.push_str(&rat_word(&row));
        carried.push(';');
    }
    digest(carried)
}

/// Read an aligned resident map back into the exact rational chart and take the same identity.
pub fn aligned_matrix_identity(
    material: &crate::embedding_fiber::AlignedMaterial,
    columns: usize,
) -> Result<String, ExactOwnerWitnessRefusal> {
    if columns == 0 || material.entries.len() % columns != 0 {
        return Err(ExactOwnerWitnessRefusal::AlignedMatrixExtent {
            entries: material.entries.len(),
            columns,
        });
    }
    let scale = if material.exponent >= 0 {
        Rat::from_integer(BigInt::from(1u8) << material.exponent as usize)
    } else {
        Rat::new(
            BigInt::from(1u8),
            BigInt::from(1u8) << material.exponent.unsigned_abs() as usize,
        )
    };
    let rows = material
        .entries
        .chunks(columns)
        .map(|row| {
            row.iter()
                .map(|entry| Rat::from_integer(BigInt::from(*entry)) * &scale)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let matrix = ExactRatMatrix::new(rows)
        .map_err(|error| ExactOwnerWitnessRefusal::ExactOwnerRefused(error.to_string()))?;
    Ok(matrix_identity(&matrix))
}

fn rat_word(values: &[Rat]) -> String {
    values
        .iter()
        .map(|value| format!("{}/{}", value.numer(), value.denom()))
        .collect::<Vec<_>>()
        .join(",")
}

fn digest(value: impl AsRef<[u8]>) -> String {
    Sha256::digest(value.as_ref())
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

#[cfg(test)]
mod tests;
