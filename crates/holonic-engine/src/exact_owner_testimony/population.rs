//! Exact-linear population licensing and the shared resident entering identity.

use super::*;

impl ExactOwnerLicense {
    /// Issue a license from an exact matrix application. The residual is computed here; callers
    /// cannot supply the value the owner allegedly returned.
    #[allow(clippy::too_many_arguments)]
    pub fn exact_linear(
        law: crate::evolution::EvolutionLawId,
        operation: impl Into<String>,
        resident_law: impl Into<String>,
        species: OperationSpecies,
        inputs: Vec<TypedMathematicalBoundary>,
        outputs: Vec<TypedMathematicalBoundary>,
        matrix: &ExactRatMatrix,
        standing: &[Rat],
        semantic_parameters: BTreeMap<String, String>,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        Self::exact_linear_population(
            law,
            operation,
            resident_law,
            species,
            inputs,
            outputs,
            matrix,
            1,
            standing.len(),
            standing,
            semantic_parameters,
        )
    }

    /// Issue an exact-linear licence over the complete ordered entering population. Every row is
    /// applied and every residual is retained; one bad row refuses the whole licence.
    #[allow(clippy::too_many_arguments)]
    pub fn exact_linear_population(
        law: crate::evolution::EvolutionLawId,
        operation: impl Into<String>,
        resident_law: impl Into<String>,
        species: OperationSpecies,
        inputs: Vec<TypedMathematicalBoundary>,
        outputs: Vec<TypedMathematicalBoundary>,
        matrix: &ExactRatMatrix,
        rows: usize,
        width: usize,
        standing: &[Rat],
        semantic_parameters: BTreeMap<String, String>,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        if rows == 0
            || width == 0
            || rows.checked_mul(width) != Some(standing.len())
            || width != matrix.columns()
        {
            return Err(ExactOwnerWitnessRefusal::ExactLinearPopulationExtent {
                rows,
                width,
                values: standing.len(),
                matrix_columns: matrix.columns(),
            });
        }
        validate_transport_coordinate_extents(species, &inputs, &outputs, matrix)?;
        validate_transport_tensor_word(species, &inputs, &outputs)?;
        let mut residual = Vec::new();
        for row in standing.chunks(width) {
            residual.extend(
                matrix.apply(row).map_err(|error| {
                    ExactOwnerWitnessRefusal::ExactOwnerRefused(error.to_string())
                })?,
            );
        }
        if residual.iter().any(|value| !value.is_zero()) {
            return Err(ExactOwnerWitnessRefusal::ExactLinearResidualNonzero { residual });
        }
        let input_identity = exact_input_population_identity(rows, width, standing)?;
        Self::issued(
            ExactOwnerKind::ExactLinear,
            law,
            operation.into(),
            resident_law.into(),
            species,
            inputs,
            outputs,
            matrix,
            residual,
            rows,
            width,
            BTreeMap::new(),
            None,
            input_identity,
            semantic_parameters,
            format!(
                "standing-population={}x{}:{}",
                rows,
                width,
                rat_word(standing)
            ),
        )
    }
}

fn validate_transport_coordinate_extents(
    species: OperationSpecies,
    inputs: &[TypedMathematicalBoundary],
    outputs: &[TypedMathematicalBoundary],
    matrix: &ExactRatMatrix,
) -> Result<(), ExactOwnerWitnessRefusal> {
    if species != OperationSpecies::Transport || inputs.is_empty() {
        return Ok(());
    }
    let input_coordinates = inputs
        .iter()
        .map(|boundary| boundary.dimensions().len())
        .sum();
    let output_coordinates = outputs
        .iter()
        .map(|boundary| boundary.dimensions().len())
        .sum();
    if input_coordinates != matrix.columns() || output_coordinates != matrix.rows() {
        return Err(
            ExactOwnerWitnessRefusal::ExactLinearCoordinateExtentDisagrees {
                input_coordinates,
                output_coordinates,
                matrix_rows: matrix.rows(),
                matrix_columns: matrix.columns(),
            },
        );
    }
    Ok(())
}

fn validate_transport_tensor_word(
    species: OperationSpecies,
    inputs: &[TypedMathematicalBoundary],
    outputs: &[TypedMathematicalBoundary],
) -> Result<(), ExactOwnerWitnessRefusal> {
    if species != OperationSpecies::Transport || inputs.is_empty() {
        return Ok(());
    }
    if inputs
        .iter()
        .chain(outputs)
        .flat_map(TypedMathematicalBoundary::tensor_slots)
        .any(|slot| matches!(slot.role, TensorSlotRole::ContractedWith(_)))
    {
        return Err(ExactOwnerWitnessRefusal::ExactLinearTensorContractionOpen);
    }
    let word = |boundaries: &[TypedMathematicalBoundary]| {
        boundaries
            .iter()
            .flat_map(TypedMathematicalBoundary::tensor_slots)
            .filter(|slot| slot.role == TensorSlotRole::Free)
            .map(|slot| (slot.ordinal, slot.binder, slot.variance))
            .collect::<Vec<_>>()
    };
    if word(inputs) != word(outputs) {
        return Err(ExactOwnerWitnessRefusal::ExactLinearFreeTensorWordDisagrees);
    }
    Ok(())
}

/// Content identity of one exact entering/query word. The same function is used by the owner
/// license and by the resident mouth after decoding its actual material.
pub fn exact_input_identity(values: &[Rat]) -> String {
    exact_input_population_identity(1, values.len(), values)
        .expect("one row with its own width is a valid population")
}

pub fn exact_input_population_identity(
    rows: usize,
    width: usize,
    values: &[Rat],
) -> Result<String, ExactOwnerWitnessRefusal> {
    if rows == 0 || width == 0 || rows.checked_mul(width) != Some(values.len()) {
        return Err(ExactOwnerWitnessRefusal::ExactInputPopulationExtent {
            rows,
            width,
            values: values.len(),
        });
    }
    Ok(digest(format!(
        "exact-input:{rows}x{width}:{}",
        rat_word(values)
    )))
}
