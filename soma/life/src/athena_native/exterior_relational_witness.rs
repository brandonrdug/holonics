//! Cold one-way witness for the UAR0 developmental-chart quotient.
//!
//! This module may read the rejected ALP5 wrapper in order to sever it.  Its output witness is
//! exterior testimony only: the successor [`SourceNeutralAthenaRest`] contains no pointer back to
//! it and no method accepts it during conduct.

use holonic_engine::native_spool::{
    NativeSituatedSpoolBundle, NativeThreadDepositBatchReceipt, NativeThreadDepositReceipt,
};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::source_neutral_cold;
use super::{
    GranularNativeProjectiveCurrent, NativeAcousticProductionMorphology, NativeGranularPotential,
    NativeOpticalProductionMorphology, OpticalAthenaRest, SourceNeutralAcousticMorphology,
    SourceNeutralAthenaError, SourceNeutralAthenaRest, SourceNeutralCultivationBranch,
    SourceNeutralOpticalMorphology, SourceNeutralReturnedDeposit, SourceNeutralReturnedEcology,
};

pub const EXTERIOR_RELATIONAL_WITNESS_SCHEMA: &str = "soma-life.exterior-relational-witness.v1";
pub const SOURCE_NEUTRAL_SEVERING_RECEIPT_SCHEMA: &str =
    "soma-life.source-neutral-severing-receipt.v4";
pub const SOURCE_NEUTRAL_EXTERIOR_INGRESS_WITNESS_SCHEMA: &str =
    "soma-life.source-neutral-exterior-ingress-witness.v1";

#[derive(Debug, Error)]
pub enum SourceNeutralSeveringError {
    #[error("the contaminated predecessor could not be validated or withdrawn: {0}")]
    Predecessor(String),
    #[error("the source-neutral successor could not be founded: {0}")]
    Successor(String),
    #[error("the exterior witness is malformed")]
    Witness,
}

/// Exterior proof that one rejected predecessor wire was quotiented into one native successor.
/// The predecessor bytes remain at their separately named cold artifact; they are not copied here.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorRelationalWitness {
    schema: String,
    predecessor_rest_identity_sha256: String,
    predecessor_wire_sha256: String,
    predecessor_wire_octets: u64,
    native_successor_identity_sha256: String,
    quotient_passage_identity_sha256: String,
    predecessor_wire_retained_inside_successor: bool,
    reciprocal_hot_witness_handle_present: bool,
    identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralSeveringReceipt {
    pub schema: String,
    pub predecessor_rest_identity_sha256: String,
    pub predecessor_wire_sha256: String,
    pub native_successor_identity_sha256: String,
    pub inherited_granular_identity_sha256: String,
    pub source_neutral_relational_identity_sha256: String,
    pub source_neutral_realization_identity_sha256: String,
    pub source_neutral_realization_face_population: usize,
    pub source_neutral_realization_cell_population: usize,
    pub source_neutral_realization_site_population: usize,
    pub source_neutral_realization_factor_population: usize,
    pub source_neutral_realization_transition_population: usize,
    pub developmental_realization_transition_population: u64,
    pub developmental_relational_face_population: u64,
    pub source_neutral_relational_face_population: usize,
    pub developmental_relational_cell_population: u64,
    pub source_neutral_relational_cell_population: usize,
    pub relational_refinement_order: u64,
    pub inherited_acoustic_morphology_identity_sha256: String,
    pub inherited_optical_morphology_identity_sha256: String,
    pub source_neutral_acoustic_identity_sha256: String,
    pub source_neutral_optical_identity_sha256: String,
    pub exterior_witness_identity_sha256: String,
    pub source_payload_retained_in_successor: bool,
    pub source_codec_reachable_from_successor: bool,
    pub reconstruction_method_reachable_from_successor: bool,
}

/// Receipt for the direct move-owned construction. It deliberately carries no predecessor path,
/// predecessor wire address, output locator, or checksum registry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralDirectConstructionReceipt {
    pub predecessor_identity_sha256: String,
    pub successor_identity_sha256: String,
    pub relational_refinement_order: u64,
    pub source_owner_consumed: bool,
    pub predecessor_wire_read: bool,
    pub historical_output_read: bool,
    pub compatibility_driver_called: bool,
}

/// Cold exterior reconstruction fibre for one source-neutral ingress.  The exact bytes and their
/// locator remain available to the exterior receiver, but this type is neither stored by nor
/// accepted by [`SourceNeutralAthenaRest`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorIngressWitness {
    pub schema: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub exact_source_fibre: Vec<u8>,
    pub native_current_identity_sha256: String,
    pub identity_sha256: String,
}

/// Transduce raw exterior material into one source-neutral native current plus its physically
/// separate cold reconstruction fibre.  Only the first return may cross the productive body.
pub fn transduce_source_neutral_exterior(
    rest: &SourceNeutralAthenaRest,
    occurrence: &str,
    payload: &[u8],
) -> Result<
    (
        GranularNativeProjectiveCurrent,
        SourceNeutralExteriorIngressWitness,
    ),
    SourceNeutralSeveringError,
> {
    let passage = rest
        .granular()
        .cross_exterior_projective_current(occurrence, payload)
        .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let mut witness = SourceNeutralExteriorIngressWitness {
        schema: SOURCE_NEUTRAL_EXTERIOR_INGRESS_WITNESS_SCHEMA.to_owned(),
        exterior_occurrence: passage.exterior_fibre.exterior_occurrence,
        exterior_source_sha256: passage.exterior_fibre.exterior_source_sha256,
        exact_source_fibre: passage.exterior_fibre.exact_source_fibre,
        native_current_identity_sha256: passage.native.identity_sha256.clone(),
        identity_sha256: String::new(),
    };
    witness.identity_sha256 = digest(&(
        SOURCE_NEUTRAL_EXTERIOR_INGRESS_WITNESS_SCHEMA,
        &witness.exterior_occurrence,
        &witness.exterior_source_sha256,
        &witness.exact_source_fibre,
        &witness.native_current_identity_sha256,
    ));
    Ok((passage.native, witness))
}

impl ExteriorRelationalWitness {
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SourceNeutralSeveringError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|_| SourceNeutralSeveringError::Witness)
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    fn validate(&self) -> Result<(), SourceNeutralSeveringError> {
        if self.schema != EXTERIOR_RELATIONAL_WITNESS_SCHEMA
            || !is_digest(&self.predecessor_rest_identity_sha256)
            || !is_digest(&self.predecessor_wire_sha256)
            || self.predecessor_wire_octets == 0
            || !is_digest(&self.native_successor_identity_sha256)
            || !is_digest(&self.quotient_passage_identity_sha256)
            || self.predecessor_wire_retained_inside_successor
            || self.reciprocal_hot_witness_handle_present
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralSeveringError::Witness);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> String {
        digest(&(
            EXTERIOR_RELATIONAL_WITNESS_SCHEMA,
            &self.predecessor_rest_identity_sha256,
            &self.predecessor_wire_sha256,
            self.predecessor_wire_octets,
            &self.native_successor_identity_sha256,
            &self.quotient_passage_identity_sha256,
            self.predecessor_wire_retained_inside_successor,
            self.reciprocal_hot_witness_handle_present,
        ))
    }
}

#[derive(Deserialize)]
struct DevelopmentalOpticalRest {
    body: DevelopmentalAcousticRest,
    production: NativeOpticalProductionMorphology,
    identity_sha256: String,
}

#[derive(Deserialize)]
struct DevelopmentalAcousticRest {
    body: DevelopmentalGranularRest,
    production: NativeAcousticProductionMorphology,
}

#[derive(Deserialize)]
struct DevelopmentalGranularRest {
    body: DevelopmentalAffineRest,
    granular: serde_json::Value,
}

#[derive(Deserialize)]
struct DevelopmentalAffineRest {
    body: DevelopmentalReturnedEcology,
    potential: serde_json::Value,
    codec: serde_json::Value,
}

#[derive(Deserialize)]
struct DevelopmentalReturnedEcology {
    ecology: NativeSituatedSpoolBundle,
    branches: Vec<DevelopmentalCultivationBranch>,
    predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    returned_deposits: Vec<DevelopmentalReturnedDeposit>,
}

#[derive(Deserialize)]
struct DevelopmentalCultivationBranch {
    branch: usize,
    k3_pullback_address: String,
    thread_address: String,
    returned_source_covector: Vec<Rat>,
    local_population: usize,
    exact_fibre_population: usize,
    return_operator_identity_sha256: String,
    #[serde(rename = "occurrence_population_identity_sha256")]
    _delivery_population_identity: String,
}

#[derive(Deserialize)]
struct DevelopmentalReturnedDeposit {
    difference_identity_sha256: String,
    thread_address: String,
    winding_coefficients: Vec<Rat>,
    return_operator_identity_sha256: String,
    #[serde(rename = "occurrence_population_identity_sha256")]
    _delivery_population_identity: String,
    native_receipt: NativeThreadDepositReceipt,
}

/// Consume a current typed optical Athena owner directly into its source-neutral organs. No
/// historical output, predecessor wire, compatibility driver, or filesystem path participates.
/// Serialization is available only after this construction through `canonical_bytes`.
pub fn construct_source_neutral_athena_rest(
    predecessor: OpticalAthenaRest,
) -> Result<
    (
        SourceNeutralAthenaRest,
        SourceNeutralDirectConstructionReceipt,
    ),
    SourceNeutralSeveringError,
> {
    let predecessor_identity_sha256 = predecessor.identity().to_owned();
    let (acoustic_body, optical_withdrawal, _) = predecessor
        .withdraw_production()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let optical = optical_withdrawal
        .into_source_neutral_morphology()
        .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let (granular_body, acoustic_withdrawal, _) = acoustic_body
        .withdraw_production()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let acoustic = acoustic_withdrawal
        .into_source_neutral_morphology()
        .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let (affine_body, granular_withdrawal) = granular_body
        .withdraw()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let granular = granular_withdrawal
        .into_source_neutral_potential()
        .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let (returned_body, potential, codec) = affine_body
        .into_source_neutral_parts()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let (ecology, branches, predecessor_deposit_receipt, returned_deposits) = returned_body
        .into_source_neutral_parts()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let (relational, realization, relational_refinement_order) =
        source_neutral_cold::read_developmental_predecessor(
            potential,
            codec,
        )
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let branches = branches
        .into_iter()
        .map(|branch| SourceNeutralCultivationBranch {
            branch: branch.branch,
            k3_pullback_address: branch.k3_pullback_address,
            thread_address: branch.thread_address,
            returned_covector: branch.returned_source_covector,
            local_population: branch.local_population,
            exact_fibre_population: branch.exact_fibre_population,
            return_operator_identity_sha256: branch.return_operator_identity_sha256,
        })
        .collect();
    let returned_deposits = returned_deposits
        .into_iter()
        .map(|deposit| SourceNeutralReturnedDeposit {
            difference_identity_sha256: deposit.difference_identity_sha256,
            thread_address: deposit.thread_address,
            winding_coefficients: deposit.winding_coefficients,
            return_operator_identity_sha256: deposit.return_operator_identity_sha256,
            native_receipt: deposit.native_receipt,
        })
        .collect();
    let body = SourceNeutralReturnedEcology::found(
        ecology,
        branches,
        predecessor_deposit_receipt,
        returned_deposits,
    )
    .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let successor =
        SourceNeutralAthenaRest::found(body, granular, relational, realization, acoustic, optical)
            .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let receipt = SourceNeutralDirectConstructionReceipt {
        predecessor_identity_sha256,
        successor_identity_sha256: successor.identity().to_owned(),
        relational_refinement_order,
        source_owner_consumed: true,
        predecessor_wire_read: false,
        historical_output_read: false,
        compatibility_driver_called: false,
    };
    Ok((successor, receipt))
}

/// Consume the sole contaminated ALP5 wire and return one source-neutral successor plus cold
/// one-way testimony. The developmental parser is local to this cold passage; none of its wrapper
/// types or discarded coordinates occur in the successor dependency closure.
pub fn sever_source_bearing_athena_rest(
    predecessor_wire: &[u8],
) -> Result<
    (
        SourceNeutralAthenaRest,
        ExteriorRelationalWitness,
        SourceNeutralSeveringReceipt,
    ),
    SourceNeutralSeveringError,
> {
    let predecessor_wire_sha256 = digest_octets(predecessor_wire);
    let predecessor_wire_octets =
        u64::try_from(predecessor_wire.len()).map_err(|_| SourceNeutralSeveringError::Witness)?;
    if predecessor_wire_octets == 0 {
        return Err(SourceNeutralSeveringError::Witness);
    }
    let developmental: DevelopmentalOpticalRest = serde_json::from_slice(predecessor_wire)
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    if !is_digest(&developmental.identity_sha256) {
        return Err(SourceNeutralSeveringError::Witness);
    }
    developmental
        .production
        .validate()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    developmental
        .body
        .production
        .validate()
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let predecessor_rest_identity_sha256 = developmental.identity_sha256;
    let inherited_optical = developmental.production;
    let inherited_optical_morphology_identity_sha256 = inherited_optical.identity_sha256.clone();
    let optical = SourceNeutralOpticalMorphology::found(
        inherited_optical.ordered_ports,
        inherited_optical.lattice_width,
        inherited_optical.lattice_height_per_order,
        inherited_optical.scale_spans,
    )
    .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;

    let inherited_acoustic = developmental.body.production;
    let inherited_acoustic_morphology_identity_sha256 = inherited_acoustic.identity_sha256.clone();
    let acoustic = SourceNeutralAcousticMorphology::found(
        inherited_acoustic.ordered_ports,
        inherited_acoustic.quadrature_population,
        inherited_acoustic.phase_extent,
    )
    .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;

    let granular =
        NativeGranularPotential::read_developmental_predecessor(developmental.body.body.granular)
            .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let inherited_granular_identity_sha256 = granular.identity().to_owned();
    let developmental_relational_potential = developmental.body.body.body.potential;
    let developmental_relational_codec = developmental.body.body.body.codec;
    let developmental_relational_face_population = developmental_relational_potential
        .get("faces")
        .and_then(serde_json::Value::as_array)
        .and_then(|faces| u64::try_from(faces.len()).ok())
        .ok_or(SourceNeutralSeveringError::Witness)?;
    let developmental_relational_cell_population = developmental_relational_potential
        .get("cells")
        .and_then(serde_json::Value::as_array)
        .and_then(|cells| u64::try_from(cells.len()).ok())
        .ok_or(SourceNeutralSeveringError::Witness)?;
    let (relational, realization, relational_refinement_order) =
        source_neutral_cold::read_developmental_predecessor(
            developmental_relational_potential,
            developmental_relational_codec,
        )
        .map_err(|error| SourceNeutralSeveringError::Predecessor(error.to_string()))?;
    let source_neutral_relational_identity_sha256 = relational.identity().to_owned();
    let source_neutral_realization_identity_sha256 = realization.identity().to_owned();
    let source_neutral_realization_face_population = realization.face_population();
    let source_neutral_realization_cell_population = realization.cell_population();
    let source_neutral_realization_site_population = realization.site_population();
    let source_neutral_realization_factor_population = realization.factor_population();
    let source_neutral_realization_transition_population = realization.transition_population();
    let developmental_realization_transition_population =
        realization.developmental_transition_population();
    let source_neutral_relational_face_population = relational.face_population();
    let source_neutral_relational_cell_population = relational.cell_population();
    let developmental_body = developmental.body.body.body.body;
    let branches = developmental_body
        .branches
        .into_iter()
        .map(|branch| SourceNeutralCultivationBranch {
            branch: branch.branch,
            k3_pullback_address: branch.k3_pullback_address,
            thread_address: branch.thread_address,
            returned_covector: branch.returned_source_covector,
            local_population: branch.local_population,
            exact_fibre_population: branch.exact_fibre_population,
            return_operator_identity_sha256: branch.return_operator_identity_sha256,
        })
        .collect();
    let returned_deposits = developmental_body
        .returned_deposits
        .into_iter()
        .map(|deposit| SourceNeutralReturnedDeposit {
            difference_identity_sha256: deposit.difference_identity_sha256,
            thread_address: deposit.thread_address,
            winding_coefficients: deposit.winding_coefficients,
            return_operator_identity_sha256: deposit.return_operator_identity_sha256,
            native_receipt: deposit.native_receipt,
        })
        .collect();
    let body = SourceNeutralReturnedEcology::found(
        developmental_body.ecology,
        branches,
        developmental_body.predecessor_deposit_receipt,
        returned_deposits,
    )
    .map_err(|error| SourceNeutralSeveringError::Successor(error.to_string()))?;
    let successor =
        SourceNeutralAthenaRest::found(body, granular, relational, realization, acoustic, optical)
            .map_err(|error: SourceNeutralAthenaError| {
                SourceNeutralSeveringError::Successor(error.to_string())
            })?;
    let quotient_passage_identity_sha256 = digest(&(
        SOURCE_NEUTRAL_SEVERING_RECEIPT_SCHEMA,
        &predecessor_rest_identity_sha256,
        &predecessor_wire_sha256,
        successor.identity(),
        &inherited_granular_identity_sha256,
    ));
    let mut witness = ExteriorRelationalWitness {
        schema: EXTERIOR_RELATIONAL_WITNESS_SCHEMA.to_owned(),
        predecessor_rest_identity_sha256: predecessor_rest_identity_sha256.clone(),
        predecessor_wire_sha256: predecessor_wire_sha256.clone(),
        predecessor_wire_octets,
        native_successor_identity_sha256: successor.identity().to_owned(),
        quotient_passage_identity_sha256,
        predecessor_wire_retained_inside_successor: false,
        reciprocal_hot_witness_handle_present: false,
        identity_sha256: String::new(),
    };
    witness.identity_sha256 = witness.rederived_identity();
    witness.validate()?;
    let receipt = SourceNeutralSeveringReceipt {
        schema: SOURCE_NEUTRAL_SEVERING_RECEIPT_SCHEMA.to_owned(),
        predecessor_rest_identity_sha256,
        predecessor_wire_sha256,
        native_successor_identity_sha256: successor.identity().to_owned(),
        inherited_granular_identity_sha256,
        source_neutral_relational_identity_sha256,
        source_neutral_realization_identity_sha256,
        source_neutral_realization_face_population,
        source_neutral_realization_cell_population,
        source_neutral_realization_site_population,
        source_neutral_realization_factor_population,
        source_neutral_realization_transition_population,
        developmental_realization_transition_population,
        developmental_relational_face_population,
        source_neutral_relational_face_population,
        developmental_relational_cell_population,
        source_neutral_relational_cell_population,
        relational_refinement_order,
        inherited_acoustic_morphology_identity_sha256,
        inherited_optical_morphology_identity_sha256,
        source_neutral_acoustic_identity_sha256: successor.acoustic().identity().to_owned(),
        source_neutral_optical_identity_sha256: successor.optical().identity().to_owned(),
        exterior_witness_identity_sha256: witness.identity().to_owned(),
        source_payload_retained_in_successor: false,
        source_codec_reachable_from_successor: false,
        reconstruction_method_reachable_from_successor: false,
    };
    Ok((successor, witness, receipt))
}

fn digest(value: &impl Serialize) -> String {
    let bytes = serde_json::to_vec(value).expect("fixed severing identity tuple serializes");
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn digest_octets(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

use holonic_engine::is_sha256_digest as is_digest;

#[cfg(test)]
mod direct_construction_tests {
    use super::*;

    #[test]
    fn direct_constructor_consumes_a_typed_owner_not_a_wire_or_path() {
        let _constructor: fn(
            OpticalAthenaRest,
        ) -> Result<
            (
                SourceNeutralAthenaRest,
                SourceNeutralDirectConstructionReceipt,
            ),
            SourceNeutralSeveringError,
        > = construct_source_neutral_athena_rest;
    }
}
