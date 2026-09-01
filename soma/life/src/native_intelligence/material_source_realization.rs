//! Exterior source-code faces of one native material consequence.
//!
//! This is the missing L6 boundary relation.  It borrows the already-founded native operation
//! complex and renders that same causal population law through Rust or Lean.  The codec name is
//! never admitted into operation identity, factor support, or the continuing Athena topology.

use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{CausalPopulationLaw, MaterialNativeFactorization};

pub const MATERIAL_SOURCE_REALIZATION_SCHEMA: &str = "soma-life.material-source-realization.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum MaterialSourceCodec {
    Rust,
    Lean,
}

/// One exterior source artifact causally downstream of a native mathematical consequence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialSourceRealization {
    pub schema: String,
    pub truth_status: String,
    pub factorization_occurrence: String,
    pub native_operation_identity_sha256: String,
    pub source_boundary_occurrences: Vec<String>,
    pub target_boundary_occurrences: Vec<String>,
    pub codec: MaterialSourceCodec,
    pub media_type: String,
    pub suggested_extension: String,
    pub payload: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub exterior_codec_routes_native_law: bool,
    pub open_exterior: Vec<String>,
}

/// One declared exterior boundary perturbation.  The emitted prefix is the complete candidate;
/// the withheld suffix is retained as a reconstruction fibre rather than silently discarded.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialSourceBoundaryDefect {
    pub schema: String,
    pub occurrence: String,
    pub complete_source_sha256: String,
    pub candidate: MaterialSourceRealization,
    pub withheld_boundary_fibre: String,
    pub open_exterior: Vec<String>,
}

/// Exterior compiler/kernel testimony returning the missing boundary to the same emitted source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialSourceBoundaryWorldReturn {
    pub occurrence: String,
    pub predecessor_defect_occurrence: String,
    pub apparatus_face: String,
    pub candidate_accepted: bool,
    pub returned_boundary: String,
    pub returned_testimony_sha256: String,
}

/// Exact source revision caused by one returned exterior boundary difference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialSourceRevisionReceipt {
    pub defect_occurrence: String,
    pub world_return_occurrence: String,
    pub candidate_payload_sha256: String,
    pub revised_payload_sha256: String,
    pub returned_boundary_octets: u64,
    pub exact_complete_source_restored: bool,
}

impl MaterialSourceRealization {
    pub fn validate(&self) -> Result<(), MaterialSourceRealizationError> {
        if self.schema != MATERIAL_SOURCE_REALIZATION_SCHEMA
            || self.truth_status != "implemented-exact"
            || self.factorization_occurrence.is_empty()
            || !is_digest(&self.native_operation_identity_sha256)
            || self.source_boundary_occurrences.is_empty()
            || self.target_boundary_occurrences.is_empty()
            || self
                .source_boundary_occurrences
                .iter()
                .any(String::is_empty)
            || self
                .target_boundary_occurrences
                .iter()
                .any(String::is_empty)
            || self.media_type.is_empty()
            || self.suggested_extension.is_empty()
            || self.payload.is_empty()
            || self.payload_sha256 != digest_bytes(self.payload.as_bytes())
            || self.payload_octets != self.payload.len() as u64
            || self.exterior_codec_routes_native_law
        {
            return Err(MaterialSourceRealizationError::Malformed);
        }
        Ok(())
    }

    /// Withhold only the terminal source boundary as a controlled exterior intervention.  Native
    /// operation identity and every causal boundary occurrence remain unchanged.
    pub fn withhold_terminal_boundary(
        mut self,
        occurrence: impl Into<String>,
    ) -> Result<MaterialSourceBoundaryDefect, MaterialSourceRealizationError> {
        self.validate()?;
        let occurrence = occurrence.into();
        if occurrence.is_empty() {
            return Err(MaterialSourceRealizationError::Malformed);
        }
        let terminal = match self.codec {
            MaterialSourceCodec::Rust => "}\n",
            MaterialSourceCodec::Lean => "end AthenaMaterial\n",
        };
        if !self.payload.ends_with(terminal) {
            return Err(MaterialSourceRealizationError::Malformed);
        }
        let complete_source_sha256 = self.payload_sha256.clone();
        let prefix_len = self
            .payload
            .len()
            .checked_sub(terminal.len())
            .ok_or(MaterialSourceRealizationError::Extent)?;
        self.payload.truncate(prefix_len);
        self.payload_sha256 = digest_bytes(self.payload.as_bytes());
        self.payload_octets = u64::try_from(self.payload.len())
            .map_err(|_| MaterialSourceRealizationError::Extent)?;
        self.validate()?;
        Ok(MaterialSourceBoundaryDefect {
            schema: "soma-life.material-source-boundary-defect.v1".to_owned(),
            occurrence,
            complete_source_sha256,
            candidate: self,
            withheld_boundary_fibre: terminal.to_owned(),
            open_exterior: vec![
                "the exterior source is incomplete until compiler/kernel testimony returns the terminal boundary"
                    .to_owned(),
            ],
        })
    }
}

impl MaterialSourceBoundaryDefect {
    /// Apply the returned boundary difference and recover the exact complete source realization.
    pub fn receive_world_return(
        mut self,
        returned: MaterialSourceBoundaryWorldReturn,
    ) -> Result<
        (MaterialSourceRealization, MaterialSourceRevisionReceipt),
        MaterialSourceRealizationError,
    > {
        if self.schema != "soma-life.material-source-boundary-defect.v1"
            || self.occurrence.is_empty()
            || !is_digest(&self.complete_source_sha256)
            || self.withheld_boundary_fibre.is_empty()
            || returned.occurrence.is_empty()
            || returned.predecessor_defect_occurrence != self.occurrence
            || returned.apparatus_face.is_empty()
            || returned.candidate_accepted
            || returned.returned_boundary != self.withheld_boundary_fibre
            || !is_digest(&returned.returned_testimony_sha256)
        {
            return Err(MaterialSourceRealizationError::WorldReturn);
        }
        let candidate_payload_sha256 = self.candidate.payload_sha256.clone();
        self.candidate.payload.push_str(&returned.returned_boundary);
        self.candidate.payload_sha256 = digest_bytes(self.candidate.payload.as_bytes());
        self.candidate.payload_octets = u64::try_from(self.candidate.payload.len())
            .map_err(|_| MaterialSourceRealizationError::Extent)?;
        self.candidate.validate()?;
        let exact_complete_source_restored =
            self.candidate.payload_sha256 == self.complete_source_sha256;
        if !exact_complete_source_restored {
            return Err(MaterialSourceRealizationError::WorldReturn);
        }
        let receipt = MaterialSourceRevisionReceipt {
            defect_occurrence: self.occurrence,
            world_return_occurrence: returned.occurrence,
            candidate_payload_sha256,
            revised_payload_sha256: self.candidate.payload_sha256.clone(),
            returned_boundary_octets: u64::try_from(returned.returned_boundary.len())
                .map_err(|_| MaterialSourceRealizationError::Extent)?,
            exact_complete_source_restored,
        };
        Ok((self.candidate, receipt))
    }
}

/// Render one native operation through a declared exterior source language.  Language chooses
/// only notation; the operation branch was already fixed by the native incidence invariant.
pub fn realize_material_source(
    factorization: &MaterialNativeFactorization,
    codec: MaterialSourceCodec,
) -> Result<MaterialSourceRealization, MaterialSourceRealizationError> {
    let identity = factorization
        .invariant
        .identity_sha256()
        .map_err(|error| MaterialSourceRealizationError::Native(error.to_string()))?;
    if identity != factorization.native_operation_identity_sha256
        || factorization
            .mathematical_complex
            .operation_cells
            .is_empty()
        || factorization
            .mathematical_complex
            .operation_cells
            .iter()
            .any(|cell| cell.source_boundary.is_empty() || cell.target_boundary.is_empty())
        || factorization
            .mathematical_complex
            .constraint_cells
            .iter()
            .any(|cell| !cell.held || cell.exact_residual != 0)
    {
        return Err(MaterialSourceRealizationError::Native(
            "the material consequence is not an exact source-realizable operation complex"
                .to_owned(),
        ));
    }

    let (payload, media_type, suggested_extension) = match codec {
        MaterialSourceCodec::Rust => (
            rust_surface(factorization.invariant.law),
            "text/x-rust",
            "rs",
        ),
        MaterialSourceCodec::Lean => (
            lean_surface(factorization.invariant.law),
            "text/x-lean",
            "lean",
        ),
    };
    let mut open_exterior = factorization.open_exterior.clone();
    open_exterior.push(
        "compiler or kernel acceptance is a later world return, not native identity".to_owned(),
    );
    open_exterior.sort();
    open_exterior.dedup();
    let mut realization = MaterialSourceRealization {
        schema: MATERIAL_SOURCE_REALIZATION_SCHEMA.to_owned(),
        truth_status: "implemented-exact".to_owned(),
        factorization_occurrence: factorization.occurrence.clone(),
        native_operation_identity_sha256: identity,
        source_boundary_occurrences: factorization
            .mathematical_complex
            .operation_cells
            .iter()
            .map(|cell| cell.source_boundary.clone())
            .collect(),
        target_boundary_occurrences: factorization
            .mathematical_complex
            .operation_cells
            .iter()
            .map(|cell| cell.target_boundary.clone())
            .collect(),
        codec,
        media_type: media_type.to_owned(),
        suggested_extension: suggested_extension.to_owned(),
        payload,
        payload_sha256: String::new(),
        payload_octets: 0,
        exterior_codec_routes_native_law: false,
        open_exterior,
    };
    realization.payload_sha256 = digest_bytes(realization.payload.as_bytes());
    realization.payload_octets = u64::try_from(realization.payload.len())
        .map_err(|_| MaterialSourceRealizationError::Extent)?;
    realization.validate()?;
    Ok(realization)
}

fn rust_surface(law: CausalPopulationLaw) -> String {
    let operation = match law {
        CausalPopulationLaw::DisjointUnion => "left.checked_add(right)",
        CausalPopulationLaw::IndependentProduct => "left.checked_mul(right)",
    };
    format!(
        "#![forbid(unsafe_code)]\n\
         /// Receiver shadow of one native causal population law.\n\
         pub fn causal_returned_population(left: usize, right: usize) -> Option<usize> {{\n\
         \x20   {operation}\n\
         }}\n"
    )
}

fn lean_surface(law: CausalPopulationLaw) -> String {
    let operation = match law {
        CausalPopulationLaw::DisjointUnion => "left + right",
        CausalPopulationLaw::IndependentProduct => "left * right",
    };
    format!(
        "import Mathlib\n\n\
         namespace AthenaMaterial\n\n\
         /-- Receiver shadow of one native causal population law. -/\n\
         def causalReturnedPopulation (left right : Nat) : Nat := {operation}\n\n\
         theorem causalReturnedPopulation_spec (left right : Nat) :\n\
         \x20   causalReturnedPopulation left right = {operation} := rfl\n\n\
         end AthenaMaterial\n"
    )
}

fn digest_bytes(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

use holonic_engine::is_sha256_digest as is_digest;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MaterialSourceRealizationError {
    #[error("the native material consequence refused source realization: {0}")]
    Native(String),
    #[error("the exterior source realization is malformed")]
    Malformed,
    #[error("the source realization extent overflowed")]
    Extent,
    #[error("the exterior source boundary world return is malformed")]
    WorldReturn,
}
