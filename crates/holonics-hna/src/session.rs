//! Continuing public HNA session over one native owner. File, domain and process concerns stay
//! here; the native operation owns current, reaction and developmental successor formation.

use crate::{
    read_checkpoint, save_checkpoint_new, CheckpointError, HnaBaseDependency, HnaCheckpointReceipt,
    HnaCultivationAperture, HnaOccurrence,
};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        mount_operator_surface, NativeConeRestrictedEcology, NativeCycleInterruption,
        NativeForwardReuseCensus, NativeFullCycleOutput, NativeFullOperationError,
        NativeFullOperatorSession, NativeFullSessionRest, NativeOperatorResidence,
        NativeSessionRestError,
    },
};
use serde::Serialize;
use std::{io::BufReader, path::Path};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HnaSessionError {
    #[error("native base: {0}")]
    Base(String),
    #[error("occurrence admission: {0}")]
    Admission(String),
    #[error("native operation: {0}")]
    Native(#[from] NativeFullOperationError),
    #[error("native rest: {0}")]
    Rest(#[from] NativeSessionRestError),
    #[error("checkpoint: {0}")]
    Checkpoint(#[from] CheckpointError),
}

/// Immutable admitted material and an optional durable starting state. This is not a running
/// ecology. The callback below gives each continuing execution exactly one move owner.
pub struct HnaModel {
    material: NativeConeRestrictedEcology,
    dependency: HnaBaseDependency,
    initial: Option<NativeFullSessionRest>,
    aperture: Option<HnaCultivationAperture>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HnaDeclaredOccurrence {
    pub class: usize,
    pub ordinal: usize,
    pub occurrence: HnaOccurrence,
}

impl HnaModel {
    pub fn from_native_rest(
        path: impl AsRef<Path>,
        class: Option<usize>,
        aperture: HnaCultivationAperture,
    ) -> Result<Self, HnaSessionError> {
        let dependency = HnaBaseDependency::capture(path, class)?;
        let mut input = BufReader::new(dependency.open_verified(None)?);
        let material = NativeConeRestrictedEcology::read_rest_from(&mut input)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        material
            .intake(class)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        Ok(Self {
            material,
            dependency,
            initial: None,
            aperture: Some(aperture),
        })
    }

    pub fn from_checkpoint(
        path: impl AsRef<Path>,
        base_override: Option<&Path>,
    ) -> Result<Self, HnaSessionError> {
        let (mut dependency, initial) = read_checkpoint(path)?;
        let mut input = BufReader::new(dependency.open_verified(base_override)?);
        let material = NativeConeRestrictedEcology::read_rest_from(&mut input)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        if initial.header.ecology != material.ecology {
            return Err(HnaSessionError::Base(
                "checkpoint operator chart differs".into(),
            ));
        }
        material
            .intake(dependency.class)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        if let Some(path) = base_override {
            dependency.path = path
                .canonicalize()
                .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        }
        Ok(Self {
            material,
            dependency,
            initial: Some(initial),
            aperture: None,
        })
    }

    pub fn dependency(&self) -> &HnaBaseDependency {
        &self.dependency
    }

    /// The existing admitted family, with its actual occurrence and history records. Equal
    /// entering words are not deduplicated into a claimed semantic occurrence identity.
    pub fn declared_occurrences(&self) -> Vec<HnaDeclaredOccurrence> {
        self.material.classes.iter().filter(|class|
            self.dependency.class.is_none_or(|selected| selected == class.ordinal))
            .flat_map(|class| class.fibre.iter().flat_map(move |held|
                self.material.histories.iter().map(move |history| HnaDeclaredOccurrence {
                    class: class.ordinal, ordinal: held.occurrence,
                    occurrence: HnaOccurrence { row_addresses: held.addresses.clone(), history: history.clone() }
                }))).collect()
    }

    /// Keep this callback open across the exposure/output stream: the base is mounted once and
    /// the same session advances for every request. Returning closes the runtime; checkpoint
    /// explicitly before returning if its development must outlive the process. No tokenizer or
    /// old context is re-opened/re-encoded by an advance call.
    pub fn with_session<T>(
        &self,
        body: impl FnOnce(&mut HnaSession<'_, '_>) -> Result<T, HnaSessionError>,
    ) -> Result<T, HnaSessionError> {
        let readout = ResidentReadout::new().map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let surface =
            mount_operator_surface(&readout).map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let mut intake = self
            .material
            .intake(self.dependency.class)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let mut residence = NativeOperatorResidence::mount_from_intake(
            &surface,
            &self.material.ecology,
            &mut intake,
        )
        .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let native = match &self.initial {
            Some(state) => NativeFullOperatorSession::remount_rest(
                &self.material.ecology,
                &mut residence,
                state,
            )?,
            None => NativeFullOperatorSession::found_with_passage_return(
                &self.material.ecology,
                &mut residence,
                self.aperture
                    .ok_or_else(|| HnaSessionError::Base("initial native aperture absent".into()))?
                    .into(),
            )?,
        };
        let mut session = HnaSession {
            native,
            material: &self.material,
            dependency: &self.dependency,
        };
        body(&mut session)
    }
}

pub struct HnaSession<'residence, 'chart> {
    native: NativeFullOperatorSession<'residence, 'chart>,
    material: &'residence NativeConeRestrictedEcology,
    dependency: &'residence HnaBaseDependency,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "state", rename_all = "kebab-case")]
pub enum HnaSessionStatus {
    AwaitingOccurrence,
    PendingNativeOccurrence {
        generation: u64,
        operation_at: usize,
    },
    Interrupted {
        boundary: NativeCycleInterruption,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HnaSessionAnatomy {
    pub schema: String,
    pub generation: u64,
    pub operations: usize,
    pub coefficient_populations: usize,
    pub retained_base_codewords: u64,
    pub morphology_factor_extent: usize,
    pub held_carriers: usize,
    pub declared_occurrences: usize,
    pub status: HnaSessionStatus,
    pub operation_profile: String,
    pub reuse: Option<NativeForwardReuseCensus>,
}

impl HnaSession<'_, '_> {
    pub fn status(&self) -> HnaSessionStatus {
        match self.native.interruption() {
            Some(boundary) => HnaSessionStatus::Interrupted {
                boundary: boundary.clone(),
            },
            None if self.native.operation_at() != 0 && !self.native.cycle_complete() => {
                HnaSessionStatus::PendingNativeOccurrence {
                    generation: self.native.generation(),
                    operation_at: self.native.operation_at(),
                }
            }
            None => HnaSessionStatus::AwaitingOccurrence,
        }
    }

    /// The declared Soulkiller family remains distinct from broader native definability and
    /// useful-task evidence. This interface does not silently erase inherited admission checks.
    pub fn advance(
        &mut self,
        occurrence: &HnaOccurrence,
    ) -> Result<NativeFullCycleOutput, HnaSessionError> {
        let admitted = self
            .material
            .admit(&occurrence.row_addresses, &occurrence.history)
            .map_err(|e| HnaSessionError::Admission(format!("{e:?}")))?;
        if self
            .dependency
            .class
            .is_some_and(|class| class != admitted.ordinal)
        {
            return Err(HnaSessionError::Admission(
                "occurrence is outside the selected native class".into(),
            ));
        }
        let mut entering = occurrence.row_addresses.clone();
        entering.extend_from_slice(&occurrence.history);
        Ok(self.native.advance_cycle_retained(&entering)?)
    }

    /// A publication failure leaves this session owned and inspectable. A successful checkpoint
    /// names its exact external base dependency; it is not labeled self-contained.
    pub fn checkpoint(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<HnaCheckpointReceipt, HnaSessionError> {
        let state = self.native.detach_rest()?;
        Ok(save_checkpoint_new(path, self.dependency, &state)?)
    }

    pub fn anatomy(&self) -> HnaSessionAnatomy {
        HnaSessionAnatomy {
            schema: "org.holonics.hna.session-anatomy.v1".into(),
            generation: self.native.generation(),
            operations: self.material.ecology.operations.len(),
            coefficient_populations: self.material.ecology.coefficient_populations.len(),
            retained_base_codewords: self
                .material
                .cross_sections
                .iter()
                .map(|s| s.words.len() as u64)
                .sum(),
            morphology_factor_extent: self.native.morphology_overlay_rank(),
            held_carriers: self.native.carrier_population(),
            declared_occurrences: self.material.classes.iter().map(|c| c.fibre.len()).sum(),
            operation_profile: if self.native.joined_passage_population() > 0 {
                "observed-passage"
            } else if self.native.return_aperture().is_some() {
                "prefix-continuation"
            } else {
                "frozen"
            }
            .into(),
            status: self.status(),
            reuse: self.native.forward_reuse_census(),
        }
    }
}
