//! Owner-local radiation seam: validation and utilities.

use super::super::ReturnedAffineLaboratoryRest;
use super::*;
use holonic_engine::receiver_history_compression::{
    ProjectiveCurrentSection, ProjectiveIntegralCurrentRay,
};
use holonic_engine::AddressedCurrentSection;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use thiserror::Error;
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeRadiationError {
    #[error("the rested radiation standing refused: {0}")]
    Standing(String),
    #[error("the predeclared radiation aperture refused: {0}")]
    Aperture(String),
    #[error("the exterior caused population is malformed")]
    Exterior,
    #[error("the exterior caused population escaped its exact carrier")]
    Extent,
    #[error("the native radiation does not descend from the crossing and resident return")]
    Radiation,
    #[error("the native radiation section refused: {0}")]
    RadiationDetail(String),
    #[error("the exterior radiation codec refused: {0}")]
    Render(String),
    #[error("the radiation receipt could not be serialized: {0}")]
    Wire(String),
}

pub(super) fn first_founded_contact(
    rest: &ReturnedAffineLaboratoryRest,
) -> Result<(String, String), NativeRadiationError> {
    for (left_at, left) in rest.affine_cells().iter().enumerate() {
        let support = left
            .landmark_factors
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if let Some(right) = rest.affine_cells().iter().skip(left_at + 1).find(|right| {
            right
                .landmark_factors
                .iter()
                .any(|factor| support.contains(factor))
        }) {
            return Ok((left.cell_address.clone(), right.cell_address.clone()));
        }
    }
    Err(NativeRadiationError::Aperture(
        "the rested affine base has no founded shared contact".to_owned(),
    ))
}

pub(super) fn found_aperture(
    rest_identity: &str,
    potential: &super::super::native_relational_potential::NativeRelationalPotentialComplex,
    codec: &super::super::native_relational_potential::NativeRelationalCodec,
    affine_cells: &[super::super::LaboratoryCellAffineSection],
) -> Result<NativeRadiationAperture, NativeRadiationError> {
    let seeds = potential
        .addressed_participant_subject_faces()
        .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
    let (closure, _) = potential
        .participant_closure(&seeds)
        .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
    let relational_cell_indices = potential
        .cells
        .iter()
        .enumerate()
        .filter_map(|(at, cell)| {
            (closure.contains(&cell.subject) || closure.contains(&cell.object)).then_some(at)
        })
        .collect::<Vec<_>>();
    if relational_cell_indices.is_empty() {
        return Err(NativeRadiationError::Aperture(
            "the addressed receiver port has no incident relational 2-cell".to_owned(),
        ));
    }
    let relational_cell_addresses = relational_cell_indices
        .iter()
        .map(|at| potential.cells[*at].address.clone())
        .collect::<Vec<_>>();
    let relational_cell_boundaries = relational_cell_indices
        .iter()
        .map(|at| {
            let cell = &potential.cells[*at];
            let mut boundary = vec![cell.subject, cell.relation, cell.object];
            boundary.extend(cell.modality);
            boundary.sort_unstable();
            boundary.dedup();
            boundary
        })
        .collect::<Vec<_>>();
    let (left_contact_cell, right_contact_cell) = first_founded_contact_cells(affine_cells)?;
    let receiver_port_faces = closure.into_iter().collect::<Vec<_>>();
    let participant_receiver_charts = derive_participant_receiver_charts(codec, potential, &seeds)?;
    let relation_receiver_charts = derive_relation_receiver_charts(codec, potential)?;
    let identity_sha256 = digest(&(
        NATIVE_RADIATION_SCHEMA,
        rest_identity,
        &receiver_port_faces,
        &participant_receiver_charts,
        &relation_receiver_charts,
        &relational_cell_indices,
        &relational_cell_addresses,
        &relational_cell_boundaries,
        &left_contact_cell,
        &right_contact_cell,
    ))?;
    Ok(NativeRadiationAperture {
        schema: NATIVE_RADIATION_SCHEMA.to_owned(),
        rested_identity_sha256: rest_identity.to_owned(),
        receiver_port_faces,
        participant_receiver_charts,
        relation_receiver_charts,
        relational_cell_indices,
        relational_cell_addresses,
        relational_cell_boundaries,
        left_contact_cell,
        right_contact_cell,
        target_query_was_visible_when_frozen: false,
        deed_or_semantic_mode_supplied: false,
        identity_sha256,
    })
}

fn first_founded_contact_cells(
    cells: &[super::super::LaboratoryCellAffineSection],
) -> Result<(String, String), NativeRadiationError> {
    for (left_at, left) in cells.iter().enumerate() {
        let support = left
            .landmark_factors
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if let Some(right) = cells.iter().skip(left_at + 1).find(|right| {
            right
                .landmark_factors
                .iter()
                .any(|factor| support.contains(factor))
        }) {
            return Ok((left.cell_address.clone(), right.cell_address.clone()));
        }
    }
    Err(NativeRadiationError::Aperture(
        "the rested affine base has no founded shared contact".to_owned(),
    ))
}

/// Apparatus-only identity of the exact consequence seen by the presently declared quadratic
/// receiver. The reconstruction DAG, sparse factor presentation, timings, and device testimony
/// are deliberately absent: those remain the complete exterior fibre rather than hot recurrence
/// coordinates.
pub(super) fn digest(value: &impl Serialize) -> Result<String, NativeRadiationError> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| NativeRadiationError::Wire(error.to_string()))
}

pub(super) fn projective_current_section(
    factor_population: u32,
    contexts: &[AddressedCurrentSection],
) -> Result<ProjectiveCurrentSection, NativeRadiationError> {
    ProjectiveCurrentSection::found(
        factor_population,
        contexts
            .iter()
            .map(|context| {
                (
                    context.quadratic_weight.clone(),
                    context.factor_current.clone(),
                )
            })
            .collect(),
    )
    .map_err(|error| NativeRadiationError::RadiationDetail(error.to_string()))
}

pub(super) fn exterior_current_quadratic_lift(
    current: &ExactComplexWaveCurrent,
) -> Result<ExteriorCurrentQuadraticLift, NativeRadiationError> {
    let real_denominator = BigUint::try_from(current.real.denom().clone())
        .map_err(|_| NativeRadiationError::Extent)?;
    let imaginary_denominator = BigUint::try_from(current.imaginary.denom().clone())
        .map_err(|_| NativeRadiationError::Extent)?;
    let divisor = exact_biguint_gcd(real_denominator.clone(), imaginary_denominator.clone());
    let common_denominator = (&real_denominator / divisor) * &imaginary_denominator;
    let integral_real =
        current.real.numer() * BigInt::from(&common_denominator / &real_denominator);
    let integral_imaginary =
        current.imaginary.numer() * BigInt::from(&common_denominator / &imaginary_denominator);
    let quadratic_numerator = BigUint::try_from(
        &integral_real * &integral_real + &integral_imaginary * &integral_imaginary,
    )
    .map_err(|_| NativeRadiationError::Extent)?;
    if quadratic_numerator == BigUint::from(0_u8) {
        return Err(NativeRadiationError::Exterior);
    }
    Ok(ExteriorCurrentQuadraticLift {
        quadratic_denominator: &common_denominator * &common_denominator,
        common_denominator,
        integral_real,
        integral_imaginary,
        quadratic_numerator,
    })
}

pub(super) fn canonical_projective_rays(
    section: &ProjectiveCurrentSection,
) -> Vec<ProjectiveIntegralCurrentRay> {
    let mut rays = section.rays.clone();
    rays.sort();
    rays
}

pub(super) fn exact_biguint_gcd(
    mut left: num_bigint::BigUint,
    mut right: num_bigint::BigUint,
) -> num_bigint::BigUint {
    while right != num_bigint::BigUint::from(0_u8) {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

pub(super) fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
