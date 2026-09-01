//! Returned exchange differences as one exact free-module boundary cover.
//!
//! An opaque receiver observation is a basis face, never a scalar.  For each addressed exchange
//! section the cultivation defect is the chain boundary
//!
//! ```text
//!     sum(returned receiver faces) - sum(sealed native candidate faces).
//! ```
//!
//! Candidate and return occupy different typed summands even when their opaque observation
//! coordinates happen to agree.  The coefficient arithmetic is therefore causal incidence, not
//! subtraction, averaging, or ordering of observation ordinals.  Source sections occupy disjoint
//! domain columns, so their complete all-pairs interchange is retained as one exact support-family
//! receipt rather than a quadratic enumeration.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    derived_factor_cover::{DefectMetrics, DerivedFactorCover, SupportedDefectSection},
    exact_linear::ExactRatMatrix,
    receiver_exact_compression::{ItemId, Observation, ReceiverId},
    receiver_history_compression::NativeStateId,
    EventId,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    CompleteExchangeNativeRealizationPassage, NativeCandidateProductState, NativeSectionAddress,
};

pub const COMPLETE_EXCHANGE_CULTIVATION_COVER_SCHEMA: &str =
    "soma-life.complete-exchange-cultivation-cover.v1";
const FREE_MODULE_CHART: &str = "native-intelligence.complete-exchange-boundary-free-module.v1";

/// One generator of the common defect codomain.  These variants are distinct typed faces.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "summand", rename_all = "kebab-case", deny_unknown_fields)]
pub enum ExchangeDefectBasisFace {
    SealedCandidate {
        seed_section: NativeSectionAddress,
        entering_native: NativeStateId,
        emitting_native: NativeStateId,
        receiver: ReceiverId,
        observation: Observation,
    },
    ReturnedReceiver {
        receiver: ReceiverId,
        observation: Observation,
    },
}

/// Exterior coordinate testimony for one domain column.  It never selects native conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceColumnAddress {
    pub source: ItemId,
    pub column: usize,
}

/// The addressed bridge from one sealed candidate occurrence to its later return boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeDefectSectionReceipt {
    pub source: ItemId,
    pub native: NativeStateId,
    pub candidate_seal_sha256: String,
    pub candidate_event: EventId,
    pub return_event: EventId,
    pub support_rows: Vec<usize>,
    pub support_column: usize,
    pub defect_address: String,
}

/// Sparse gluing of every local boundary column into one free-module section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompactBoundaryAssemblyReceipt {
    pub chart: String,
    pub ambient_rows: usize,
    pub ambient_columns: usize,
    pub member_defects: Vec<String>,
    pub support_columns: Vec<usize>,
    pub nonzero_coefficient_population: usize,
    pub assembled_support_sha256: String,
    pub exact_disjoint_union: bool,
}

/// The one-time H2N factor cover over the complete exchange population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompleteExchangeCultivationCover {
    pub schema: String,
    pub predecessor_rest_wire_sha256: String,
    pub free_module_chart: String,
    pub codomain_basis: Vec<ExchangeDefectBasisFace>,
    pub source_columns: Vec<SourceColumnAddress>,
    pub sections: Vec<ExchangeDefectSectionReceipt>,
    pub assembly: CompactBoundaryAssemblyReceipt,
    pub cover: DerivedFactorCover,
    pub open_exterior: Vec<String>,
}

impl CompleteExchangeCultivationCover {
    pub fn derive(passage: &CompleteExchangeNativeRealizationPassage) -> Result<Self, String> {
        passage.validate()?;
        let candidates = passage
            .candidate
            .sections
            .iter()
            .map(|section| (section.history.source, section))
            .collect::<BTreeMap<_, _>>();
        let returned = passage
            .returned
            .iter()
            .map(|section| (section.source, section))
            .collect::<BTreeMap<_, _>>();

        let mut basis_set = BTreeSet::new();
        for source in &passage.native.source_population {
            let candidate = candidates
                .get(source)
                .ok_or_else(|| format!("source {source:?} has no sealed candidate"))?;
            let later = returned
                .get(source)
                .ok_or_else(|| format!("source {source:?} has no later return"))?;
            basis_set.extend(candidate.product_states.iter().map(candidate_face));
            basis_set.extend(later.receiver_faces.iter().map(|factor| {
                ExchangeDefectBasisFace::ReturnedReceiver {
                    receiver: factor.receiver,
                    observation: factor.observation,
                }
            }));
        }
        let codomain_basis = basis_set.into_iter().collect::<Vec<_>>();
        let basis_index = codomain_basis
            .iter()
            .enumerate()
            .map(|(row, face)| (face.clone(), row))
            .collect::<BTreeMap<_, _>>();
        let source_columns = passage
            .native
            .source_population
            .iter()
            .copied()
            .enumerate()
            .map(|(column, source)| SourceColumnAddress { source, column })
            .collect::<Vec<_>>();
        let successor_word = passage
            .native
            .generators
            .iter()
            .map(|square| digest_json(&("native-generator-square/v1", square)))
            .collect::<Result<Vec<_>, _>>()?;
        let receiver_family = digest_json(&(
            "complete-returned-receiver-family/v1",
            passage
                .native
                .receiver_factors
                .iter()
                .map(|factor| factor.receiver)
                .collect::<BTreeSet<_>>(),
        ))?;

        let mut receipts = Vec::with_capacity(source_columns.len());
        let mut defects = Vec::with_capacity(source_columns.len());
        for coordinate in &source_columns {
            let candidate = candidates[&coordinate.source];
            let later = returned[&coordinate.source];
            let candidate_faces = candidate
                .product_states
                .iter()
                .map(candidate_face)
                .collect::<Vec<_>>();
            let returned_faces = later
                .receiver_faces
                .iter()
                .map(|factor| ExchangeDefectBasisFace::ReturnedReceiver {
                    receiver: factor.receiver,
                    observation: factor.observation,
                })
                .collect::<Vec<_>>();
            let (support_rows, supported) =
                boundary_column(&candidate_faces, &returned_faces, &basis_index)?;
            let defect_address = digest_json(&(
                "complete-exchange-defect-section/v1",
                &candidate.seal_sha256,
                later.native,
                later.candidate_event,
                later.return_event,
                &candidate_faces,
                &returned_faces,
                &successor_word,
            ))?;
            defects.push(SupportedDefectSection {
                address: format!("defect:{defect_address}"),
                parent_candidate: candidate.seal_sha256.clone(),
                receiver: format!("receiver-family:{receiver_family}"),
                successor_word: successor_word.clone(),
                chart: FREE_MODULE_CHART.to_owned(),
                ambient_rows: codomain_basis.len(),
                ambient_columns: source_columns.len(),
                support_rows: support_rows.clone(),
                support_columns: vec![coordinate.column],
                metrics: DefectMetrics {
                    domain: ExactRatMatrix::identity(1).map_err(display)?,
                    codomain: ExactRatMatrix::identity(support_rows.len()).map_err(display)?,
                },
                supported,
            });
            receipts.push(ExchangeDefectSectionReceipt {
                source: coordinate.source,
                native: later.native,
                candidate_seal_sha256: candidate.seal_sha256.clone(),
                candidate_event: later.candidate_event,
                return_event: later.return_event,
                support_rows,
                support_column: coordinate.column,
                defect_address: format!("defect:{defect_address}"),
            });
        }
        let cover = DerivedFactorCover::derive(defects).map_err(display)?;
        let support_columns = receipts
            .iter()
            .map(|receipt| receipt.support_column)
            .collect::<Vec<_>>();
        let member_defects = receipts
            .iter()
            .map(|receipt| receipt.defect_address.clone())
            .collect::<Vec<_>>();
        let nonzero_coefficient_population = cover
            .locals
            .iter()
            .map(|local| local.section.supported.entries().len())
            .sum();
        let assembled_support_sha256 = digest_json(&(
            "complete-exchange-compact-boundary-assembly/v1",
            FREE_MODULE_CHART,
            codomain_basis.len(),
            source_columns.len(),
            &member_defects,
            &support_columns,
            nonzero_coefficient_population,
        ))?;
        let assembly = CompactBoundaryAssemblyReceipt {
            chart: FREE_MODULE_CHART.to_owned(),
            ambient_rows: codomain_basis.len(),
            ambient_columns: source_columns.len(),
            member_defects,
            support_columns,
            nonzero_coefficient_population,
            assembled_support_sha256,
            exact_disjoint_union: true,
        };
        let product = Self {
            schema: COMPLETE_EXCHANGE_CULTIVATION_COVER_SCHEMA.to_owned(),
            predecessor_rest_wire_sha256: passage.candidate.predecessor_rest_wire_sha256.clone(),
            free_module_chart: FREE_MODULE_CHART.to_owned(),
            codomain_basis,
            source_columns,
            sections: receipts,
            assembly,
            cover,
            open_exterior: vec![
                "receiver families outside the complete exchange aperture remain open".to_owned(),
                "the exact cover has not yet been deposited into continuing Athena morphology"
                    .to_owned(),
            ],
        };
        product.validate()?;
        Ok(product)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let product: Self = serde_json::from_slice(bytes).map_err(display)?;
        product.validate()?;
        Ok(product)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        serde_json::to_vec(self).map_err(display)
    }

    pub fn validate(&self) -> Result<(), String> {
        self.cover.validate().map_err(display)?;
        if self.schema != COMPLETE_EXCHANGE_CULTIVATION_COVER_SCHEMA
            || self.free_module_chart != FREE_MODULE_CHART
            || self.predecessor_rest_wire_sha256.len() != 64
            || self.codomain_basis.is_empty()
            || self.source_columns.is_empty()
            || self.source_columns.len() != self.sections.len()
            || self.cover.locals.len() != self.sections.len()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err("the complete exchange cultivation cover is malformed".to_owned());
        }
        if self
            .codomain_basis
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
            || self
                .source_columns
                .iter()
                .enumerate()
                .any(|(column, coordinate)| coordinate.column != column)
        {
            return Err("the cultivation free-module chart is not canonical".to_owned());
        }
        let expected_members = self
            .sections
            .iter()
            .map(|section| section.defect_address.clone())
            .collect::<Vec<_>>();
        let expected_columns = self
            .source_columns
            .iter()
            .map(|coordinate| coordinate.column)
            .collect::<Vec<_>>();
        let expected_nonzero = self
            .cover
            .locals
            .iter()
            .map(|local| local.section.supported.entries().len())
            .sum::<usize>();
        let expected_assembly_sha = digest_json(&(
            "complete-exchange-compact-boundary-assembly/v1",
            FREE_MODULE_CHART,
            self.codomain_basis.len(),
            self.source_columns.len(),
            &expected_members,
            &expected_columns,
            expected_nonzero,
        ))?;
        if self.assembly.chart != self.free_module_chart
            || self.assembly.ambient_rows != self.codomain_basis.len()
            || self.assembly.ambient_columns != self.source_columns.len()
            || self.assembly.member_defects != expected_members
            || self.assembly.support_columns != expected_columns
            || self.assembly.nonzero_coefficient_population != expected_nonzero
            || self.assembly.assembled_support_sha256 != expected_assembly_sha
            || !self.assembly.exact_disjoint_union
        {
            return Err(
                "the compact boundary assembly does not reconstruct from its local cover"
                    .to_owned(),
            );
        }
        for ((coordinate, receipt), local) in self
            .source_columns
            .iter()
            .zip(&self.sections)
            .zip(&self.cover.locals)
        {
            if receipt.source != coordinate.source
                || receipt.support_column != coordinate.column
                || receipt.candidate_event == receipt.return_event
                || receipt.defect_address != local.section.address
                || receipt.candidate_seal_sha256 != local.section.parent_candidate
                || local.section.chart != self.free_module_chart
                || local.section.ambient_rows != self.codomain_basis.len()
                || local.section.ambient_columns != self.source_columns.len()
                || local.section.support_rows != receipt.support_rows
                || local.section.support_columns != vec![coordinate.column]
                || local.derived_rank != 1
                || local.factors.len() != 1
                || local.reconstructed_defect != local.section.supported
            {
                return Err(
                    "one exchange defect does not reconstruct from its typed boundary".to_owned(),
                );
            }
        }
        if self.cover.compact_interchange_families.len() != 1 || !self.cover.overlaps.is_empty() {
            return Err(
                "the disjoint exchange columns did not return one compact interchange family"
                    .to_owned(),
            );
        }
        Ok(())
    }
}

fn candidate_face(state: &NativeCandidateProductState) -> ExchangeDefectBasisFace {
    ExchangeDefectBasisFace::SealedCandidate {
        seed_section: state.seed_section.clone(),
        entering_native: state.entering_native,
        emitting_native: state.emitting_native,
        receiver: state.receiver,
        observation: state.observation,
    }
}

fn boundary_column(
    candidate: &[ExchangeDefectBasisFace],
    returned: &[ExchangeDefectBasisFace],
    basis: &BTreeMap<ExchangeDefectBasisFace, usize>,
) -> Result<(Vec<usize>, ExactRatMatrix), String> {
    if candidate.is_empty() || returned.is_empty() {
        return Err("a cultivation boundary requires both candidate and return faces".to_owned());
    }
    let mut coefficients = BTreeMap::<usize, i64>::new();
    for (faces, orientation) in [(candidate, -1_i64), (returned, 1_i64)] {
        for face in faces {
            let row = *basis.get(face).ok_or_else(|| {
                "a defect face lies outside the common free-module basis".to_owned()
            })?;
            *coefficients.entry(row).or_default() += orientation;
        }
    }
    coefficients.retain(|_, coefficient| *coefficient != 0);
    if coefficients.is_empty() {
        return Err("the candidate/return boundary collapsed without a typed defect".to_owned());
    }
    let support_rows = coefficients.keys().copied().collect::<Vec<_>>();
    let supported = ExactRatMatrix::new(
        coefficients
            .into_values()
            .map(|coefficient| vec![Rat::from_integer(BigInt::from(coefficient))])
            .collect(),
    )
    .map_err(display)?;
    Ok((support_rows, supported))
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    let bytes = serde_json::to_vec(value).map_err(display)?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate(observation: u64) -> ExchangeDefectBasisFace {
        ExchangeDefectBasisFace::SealedCandidate {
            seed_section: NativeSectionAddress {
                spool: "spool".into(),
                thread: "thread".into(),
                occurrence: EventId(1),
            },
            entering_native: NativeStateId(2),
            emitting_native: NativeStateId(3),
            receiver: ReceiverId(4),
            observation: Observation(observation),
        }
    }

    fn returned(observation: u64) -> ExchangeDefectBasisFace {
        ExchangeDefectBasisFace::ReturnedReceiver {
            receiver: ReceiverId(4),
            observation: Observation(observation),
        }
    }

    #[test]
    fn opaque_equal_coordinates_remain_distinct_typed_faces() {
        let candidate = candidate(9);
        let returned = returned(9);
        let basis = [candidate.clone(), returned.clone()]
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(row, face)| (face, row))
            .collect::<BTreeMap<_, _>>();
        let (rows, defect) = boundary_column(&[candidate], &[returned], &basis).expect("boundary");
        assert_eq!(rows.len(), 2);
        assert_eq!(
            defect
                .entries()
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
            ["-1".to_owned(), "1".to_owned()].into_iter().collect()
        );
    }

    #[test]
    fn changing_a_later_return_changes_only_the_returned_basis_face() {
        let candidate_face = candidate(9);
        let left = returned(10);
        let right = returned(11);
        assert_eq!(candidate_face, candidate(9));
        assert_ne!(left, right);
        assert!(matches!(
            left,
            ExchangeDefectBasisFace::ReturnedReceiver { .. }
        ));
        assert!(matches!(
            right,
            ExchangeDefectBasisFace::ReturnedReceiver { .. }
        ));
    }
}
