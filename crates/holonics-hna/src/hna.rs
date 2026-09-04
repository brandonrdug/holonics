//! A small serializable application seam over the complete recurrent native operator.
//!
//! This is a run/session receipt, not a trained checkpoint.  It owns no tokenizer, answer
//! selection, persistence, or new inference law: occurrences are already native row addresses and
//! the full operator owns every operation and successor.

use std::path::{Path, PathBuf};

use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperationError, NativeFullOperatorEcology, NativeFullOperatorSession,
        NativeMorphologyTransition, NativeOperatorResidence, NativeReturnAperture,
        dismantle_full_native_operator, face_of_last_row,
    },
    resident_section::TransferCensus,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonic_engine::native_ecology::holonic_intelligence::NativeConeRestrictedEcology;

pub const HNA_RUN_SCHEMA: &str = "org.holonics.hna.run.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum HnaSourceKind {
    ResidentOperatorDirectory,
    NativeRestrictedRest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum HnaSource {
    ResidentOperatorDirectory { root: PathBuf },
    NativeRestrictedRest { path: PathBuf, class: Option<usize> },
}

impl HnaSource {
    pub fn kind(&self) -> HnaSourceKind {
        match self {
            Self::ResidentOperatorDirectory { .. } => HnaSourceKind::ResidentOperatorDirectory,
            Self::NativeRestrictedRest { .. } => HnaSourceKind::NativeRestrictedRest,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaCultivationAperture {
    pub learning_shift: u32,
    pub series_terms: u32,
}

impl From<HnaCultivationAperture> for NativeReturnAperture {
    fn from(value: HnaCultivationAperture) -> Self {
        Self {
            learning_shift: value.learning_shift,
            series_terms: value.series_terms,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaOccurrence {
    /// Ordered native row addresses consumed by the lookup occurrence.
    pub row_addresses: Vec<u32>,
    /// Declared history appended to the executed occurrence and checked against an SKE domain.
    #[serde(default)]
    pub history: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaRunRequest {
    pub source: HnaSource,
    pub receiver: String,
    pub occurrences: Vec<HnaOccurrence>,
    pub cultivation: Option<HnaCultivationAperture>,
    /// Include the full native morphology trace instead of only its declared summary.
    #[serde(default)]
    pub include_trace: bool,
}

impl HnaRunRequest {
    pub fn validate_shape(&self) -> Result<(), HnaError> {
        if self.receiver != "terminal-face" {
            return Err(HnaError::InvalidRequest(
                "the supported receiver is terminal-face",
            ));
        }
        if self.occurrences.is_empty() {
            return Err(HnaError::InvalidRequest(
                "receiver and occurrences must be non-empty",
            ));
        }
        if self
            .occurrences
            .iter()
            .any(|occurrence| occurrence.row_addresses.is_empty())
        {
            return Err(HnaError::InvalidRequest(
                "every occurrence must have a non-empty row population",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HnaCycleReceipt {
    pub ordinal: usize,
    pub predecessor_generation: u64,
    pub successor_generation: u64,
    pub receiver: String,
    pub emission_carrier: u32,
    pub emission_rows: usize,
    pub emission_width: usize,
    pub emission_grain: u32,
    pub selected_face: holonic_engine::native_ecology::holonic_intelligence::NativeReceiverFace,
    pub morphology_changed: bool,
    pub returned_operations: usize,
    pub deposited_populations: Vec<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub morphology_trace: Option<NativeMorphologyTransition>,
    pub predecessor_overlay_rank: usize,
    pub successor_overlay_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HnaRunReceipt {
    pub schema: String,
    pub source: HnaSourceKind,
    pub receiver: String,
    pub cycles: Vec<HnaCycleReceipt>,
    pub final_generation: u64,
    pub final_overlay_rank: usize,
    pub final_census: TransferCensus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HnaRestrictedInspection {
    pub schema: String,
    pub source: HnaSourceKind,
    pub classes: usize,
    pub histories: usize,
    pub operations: usize,
    pub coefficient_populations: usize,
    pub cross_sections: usize,
    pub sites: usize,
    pub extent_population: usize,
}

#[derive(Debug, Error)]
pub enum HnaError {
    #[error("invalid HNA request: {0}")]
    InvalidRequest(&'static str),
    #[error("source: {0}")]
    Source(String),
    #[error("native operator: {0}")]
    Operator(#[from] NativeFullOperationError),
    #[error("resident apparatus: {0}")]
    Resident(String),
    #[error("receiver face was not emitted")]
    Face,
}

/// Inspect the native restricted artifact header without opening a CUDA readout.
pub fn inspect_native_restricted_rest(path: &Path) -> Result<HnaRestrictedInspection, HnaError> {
    let restricted = NativeConeRestrictedEcology::read_rest_header(path)
        .map_err(|error| HnaError::Source(error.to_string()))?;
    // Header inspection is deliberately GPU-free and the header has no codewords yet; the full
    // `validate` law is applied by `run_hna` after `read_rest` restores the retained sections.
    Ok(HnaRestrictedInspection {
        schema: restricted.schema,
        source: HnaSourceKind::NativeRestrictedRest,
        classes: restricted.classes.len(),
        histories: restricted.histories.len(),
        operations: restricted.ecology.operations.len(),
        coefficient_populations: restricted.ecology.coefficient_populations.len(),
        cross_sections: restricted.cross_sections.len(),
        sites: restricted.sites,
        extent_population: restricted.extent_population,
    })
}

/// Run one continuing full-operator session.  The final emission intervals stay local so the
/// ordinary receipt remains compact; callers needing the complete face can use the operation owner
/// directly or add a callback at the application boundary.
pub fn run_hna(request: HnaRunRequest) -> Result<HnaRunReceipt, HnaError> {
    request.validate_shape()?;
    let source = request.source.clone();
    match source {
        HnaSource::ResidentOperatorDirectory { root } => {
            let returned = dismantle_full_native_operator(&root)
                .map_err(|error| HnaError::Source(error.to_string()))?;
            let readout =
                ResidentReadout::new().map_err(|error| HnaError::Resident(error.to_string()))?;
            let surface =
                holonic_engine::native_ecology::holonic_intelligence::mount_operator_surface(
                    &readout,
                )
                .map_err(|error| HnaError::Resident(error.to_string()))?;
            let mut residence =
                NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)
                    .map_err(|error| HnaError::Resident(error.to_string()))?;
            run_mounted(
                &request,
                HnaSourceKind::ResidentOperatorDirectory,
                &returned.native,
                &mut residence,
            )
        }
        HnaSource::NativeRestrictedRest { path, class } => {
            let restricted = NativeConeRestrictedEcology::read_rest(&path)
                .map_err(|error| HnaError::Source(error.to_string()))?;
            restricted
                .validate()
                .map_err(|error| HnaError::Source(error.to_string()))?;
            for occurrence in &request.occurrences {
                let admitted = restricted
                    .admit(&occurrence.row_addresses, &occurrence.history)
                    .map_err(|error| {
                        HnaError::Source(format!("restricted admission: {error:?}"))
                    })?;
                if class.is_some_and(|expected| expected != admitted.ordinal) {
                    return Err(HnaError::Source(
                        "occurrence is outside requested restricted class".to_owned(),
                    ));
                }
            }
            let mut intake = restricted
                .intake(class)
                .map_err(|error| HnaError::Source(error.to_string()))?;
            let readout =
                ResidentReadout::new().map_err(|error| HnaError::Resident(error.to_string()))?;
            let surface =
                holonic_engine::native_ecology::holonic_intelligence::mount_operator_surface(
                    &readout,
                )
                .map_err(|error| HnaError::Resident(error.to_string()))?;
            let mut residence = NativeOperatorResidence::mount_from_intake(
                &surface,
                &restricted.ecology,
                &mut intake,
            )
            .map_err(|error| HnaError::Resident(error.to_string()))?;
            run_mounted(
                &request,
                HnaSourceKind::NativeRestrictedRest,
                &restricted.ecology,
                &mut residence,
            )
        }
    }
}

fn run_mounted(
    request: &HnaRunRequest,
    source: HnaSourceKind,
    ecology: &NativeFullOperatorEcology,
    residence: &mut NativeOperatorResidence<'_>,
) -> Result<HnaRunReceipt, HnaError> {
    let mut session = match request.cultivation {
        Some(aperture) => {
            NativeFullOperatorSession::found_with_return(ecology, residence, aperture.into())?
        }
        None => NativeFullOperatorSession::found(ecology, residence)?,
    };
    let mut cycles = Vec::with_capacity(request.occurrences.len());
    for (ordinal, occurrence) in request.occurrences.iter().enumerate() {
        let predecessor_generation = session.generation();
        let predecessor_overlay_rank = session.morphology_overlay_rank();
        let addresses = occurrence_addresses(occurrence);
        let cycle = session.advance_cycle(&addresses)?;
        let emission = &cycle.final_emission;
        let selected_face = face_of_last_row(&emission.intervals, emission.rows, emission.width)
            .ok_or(HnaError::Face)?;
        let morphology_transition = cycle
            .traces
            .iter()
            .find_map(|trace| match &trace.morphology_transition {
                NativeMorphologyTransition::Unchanged => None,
                changed => Some(changed.clone()),
            })
            .unwrap_or(NativeMorphologyTransition::Unchanged);
        let (morphology_changed, returned_operations, deposited_populations) =
            match &morphology_transition {
                NativeMorphologyTransition::Unchanged => (false, 0, Vec::new()),
                NativeMorphologyTransition::Changed {
                    deposit, adjoint, ..
                } => {
                    let mut populations = adjoint.populations_deposited.clone();
                    populations.push(deposit.population);
                    populations.sort_unstable();
                    populations.dedup();
                    (true, adjoint.operations_returned, populations)
                }
            };
        let successor_generation = cycle.successor.generation();
        let successor_overlay_rank = cycle.successor.morphology_overlay_rank();
        cycles.push(HnaCycleReceipt {
            ordinal,
            predecessor_generation,
            successor_generation,
            receiver: request.receiver.clone(),
            emission_carrier: emission.carrier.0,
            emission_rows: emission.rows,
            emission_width: emission.width,
            emission_grain: emission.grain,
            selected_face,
            morphology_changed,
            returned_operations,
            deposited_populations,
            morphology_trace: request.include_trace.then_some(morphology_transition),
            predecessor_overlay_rank,
            successor_overlay_rank,
        });
        session = cycle.successor;
    }
    Ok(HnaRunReceipt {
        schema: HNA_RUN_SCHEMA.to_owned(),
        source,
        receiver: request.receiver.clone(),
        final_generation: session.generation(),
        final_overlay_rank: session.morphology_overlay_rank(),
        final_census: session.census(),
        cycles,
    })
}

fn occurrence_addresses(occurrence: &HnaOccurrence) -> Vec<u32> {
    occurrence
        .row_addresses
        .iter()
        .chain(&occurrence.history)
        .copied()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_admitted_history_is_part_of_the_executed_occurrence() {
        assert_eq!(
            occurrence_addresses(&HnaOccurrence {
                row_addresses: vec![7, 8],
                history: vec![9, 10],
            }),
            vec![7, 8, 9, 10]
        );
    }

    #[test]
    fn an_unimplemented_receiver_refuses_before_source_access() {
        let mut value = request(vec![HnaOccurrence {
            row_addresses: vec![1],
            history: vec![],
        }]);
        value.receiver = "arbitrary-other-reader".into();
        assert!(value.validate_shape().is_err());
    }

    fn request(occurrences: Vec<HnaOccurrence>) -> HnaRunRequest {
        HnaRunRequest {
            source: HnaSource::NativeRestrictedRest {
                path: PathBuf::from("restricted.rest"),
                class: None,
            },
            receiver: "terminal-face".to_owned(),
            occurrences,
            cultivation: Some(HnaCultivationAperture {
                learning_shift: 8,
                series_terms: 14,
            }),
            include_trace: false,
        }
    }

    #[test]
    fn request_schema_round_trips_and_aperture_is_typed() {
        let value = request(vec![HnaOccurrence {
            row_addresses: vec![1, 2],
            history: vec![],
        }]);
        let wire = serde_json::to_vec(&value).expect("request wire");
        let recovered: HnaRunRequest = serde_json::from_slice(&wire).expect("request");
        assert_eq!(recovered, value);
        assert_eq!(
            NativeReturnAperture::from(value.cultivation.unwrap()).series_terms,
            14
        );
    }

    #[test]
    fn empty_sequence_is_refused_before_source_access() {
        let error = request(Vec::new()).validate_shape().expect_err("empty");
        assert!(error.to_string().contains("occurrences"));
    }

    #[test]
    fn empty_occurrences_are_refused() {
        let empty = request(vec![HnaOccurrence {
            row_addresses: Vec::new(),
            history: Vec::new(),
        }]);
        assert!(empty.validate_shape().is_err());
    }
}
