//! Continuing public HNA session over one native owner. File, domain and process concerns stay
//! here; the native operation owns current, reaction and developmental successor formation.

use crate::{
    read_session_checkpoint, save_checkpoint_new, save_stream_checkpoint_new, CheckpointError,
    HnaBaseDependency, HnaCheckpointReceipt, HnaCultivationAperture, HnaOccurrence,
};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        mount_operator_surface, NativeConeRestrictedEcology, NativeCycleInterruption,
        NativeForwardReuseCensus, NativeFullCycleOutput, NativeFullOperationError,
        NativeFullOperatorSession, NativeFullSessionRest, NativeInputExtendedIntake,
        NativeInputRowExtension, NativeOperatorResidence, NativeSessionRestError,
    },
};
use serde::Serialize;
use std::collections::BTreeMap;
use std::{io::BufReader, path::Path};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HnaSessionError {
    #[error("native base: {0}")]
    Base(String),
    #[error("occurrence admission: {0}")]
    Admission(String),
    #[error("input sections absent at native populations: {rows:?}")]
    MissingInput { rows: BTreeMap<u32, Vec<u32>> },
    #[error("native operation: {0}")]
    Native(#[from] NativeFullOperationError),
    #[error("native rest: {0}")]
    Rest(#[from] NativeSessionRestError),
    #[error("checkpoint: {0}")]
    Checkpoint(#[from] CheckpointError),
    #[error("stream: {0}")]
    Stream(#[from] crate::HnaStreamError),
}

/// Immutable admitted material and an optional durable starting state. This is not a running
/// ecology. The callback below gives each continuing execution exactly one move owner.
pub struct HnaModel {
    material: NativeConeRestrictedEcology,
    dependency: HnaBaseDependency,
    initial: Option<NativeFullSessionRest>,
    aperture: Option<HnaCultivationAperture>,
    transport: Option<crate::HnaStreamState>,
    input_material: Vec<NativeInputRowExtension>,
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
        let (dependency, file) = HnaBaseDependency::capture_with_open_handle(path, class)?;
        let mut input = BufReader::new(file);
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
            transport: None,
            input_material: Vec::new(),
        })
    }

    pub fn from_checkpoint(
        path: impl AsRef<Path>,
        base_override: Option<&Path>,
    ) -> Result<Self, HnaSessionError> {
        let saved = read_session_checkpoint(path)?;
        Self::from_saved(saved, base_override)
    }

    pub fn from_checkpoint_reference(
        reference: &crate::HnaFileDependency,
        base_override: Option<&Path>,
    ) -> Result<Self, HnaSessionError> {
        let saved = crate::checkpoint::read_session_checkpoint_file(reference.open_verified()?)?;
        Self::from_saved(saved, base_override)
    }

    fn from_saved(
        saved: crate::HnaSavedSession,
        base_override: Option<&Path>,
    ) -> Result<Self, HnaSessionError> {
        let mut dependency = saved.dependency;
        let initial = saved.state;
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
        let input_material = crate::input_material::load(&dependency)?;
        NativeInputExtendedIntake::new(
            material
                .intake(dependency.class)
                .map_err(|e| HnaSessionError::Base(e.to_string()))?,
            &input_material,
        )
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
            transport: saved.transport,
            input_material,
        })
    }

    pub fn dependency(&self) -> &HnaBaseDependency {
        &self.dependency
    }

    pub fn starting_generation(&self) -> u64 {
        self.initial
            .as_ref()
            .map_or(0, |rest| rest.header.generation)
    }

    /// Acquire only missing input rows through the exterior source chart. This saves independent
    /// material; it does not alter this model, run source inference or claim a new Soulkiller lift.
    pub fn acquire_input_material(
        &self,
        source_root: &Path,
        addresses: &[u32],
        output: &Path,
    ) -> Result<crate::HnaInputAcquisitionReceipt, HnaSessionError> {
        crate::input_material::acquire(
            &self.material,
            &self.dependency,
            &self.input_material,
            source_root,
            addresses,
            output,
        )
    }

    /// Compose an immutable material extension before mounting. Native development/rest is kept;
    /// the original family remains unchanged and is not silently expanded by this operation.
    pub fn with_input_material(mut self, path: impl AsRef<Path>) -> Result<Self, HnaSessionError> {
        self.dependency
            .input_material
            .push(crate::HnaInputMaterialDependency::capture(path)?);
        let input_material = crate::input_material::load(&self.dependency)?;
        NativeInputExtendedIntake::new(
            self.material
                .intake(self.dependency.class)
                .map_err(|e| HnaSessionError::Base(e.to_string()))?,
            &input_material,
        )
        .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        self.input_material = input_material;
        Ok(self)
    }

    /// The existing admitted family, with its actual occurrence and history records. Equal
    /// entering words are not deduplicated into a claimed semantic occurrence identity.
    pub fn declared_occurrences(&self) -> Vec<HnaDeclaredOccurrence> {
        self.material
            .classes
            .iter()
            .filter(|class| {
                self.dependency
                    .class
                    .is_none_or(|selected| selected == class.ordinal)
            })
            .flat_map(|class| {
                class.fibre.iter().flat_map(move |held| {
                    self.material
                        .histories
                        .iter()
                        .map(move |history| HnaDeclaredOccurrence {
                            class: class.ordinal,
                            ordinal: held.occurrence,
                            occurrence: HnaOccurrence {
                                row_addresses: held.addresses.clone(),
                                history: history.clone(),
                            },
                        })
                })
            })
            .collect()
    }

    /// Keep this callback open across the exposure/output stream: the base is mounted once and
    /// the same session advances for every request. Returning closes the runtime; checkpoint
    /// explicitly before returning if its development must outlive the process. No tokenizer or
    /// old context is re-opened/re-encoded by an advance call.
    pub fn with_session<T>(
        &self,
        body: impl FnOnce(&mut HnaSession<'_, '_>) -> Result<T, HnaSessionError>,
    ) -> Result<T, HnaSessionError> {
        if self.transport.is_some() {
            return Err(HnaSessionError::Base(
                "checkpoint carries transport state; use with_stream_session".into(),
            ));
        }
        self.with_native(body)
    }

    /// Restore both the continuing native owner and its exterior delivery state. The caller
    /// explicitly opens a new connection if a pending response must be replayed there.
    pub fn with_stream_session<T>(
        &self,
        body: impl FnOnce(&mut HnaSession<'_, '_>, &mut crate::HnaStream) -> Result<T, HnaSessionError>,
    ) -> Result<T, HnaSessionError> {
        let mut stream = crate::HnaStream::from_state(self.transport.clone().unwrap_or_default())?;
        self.with_native(|session| body(session, &mut stream))
    }

    fn with_native<T>(
        &self,
        body: impl FnOnce(&mut HnaSession<'_, '_>) -> Result<T, HnaSessionError>,
    ) -> Result<T, HnaSessionError> {
        let readout = ResidentReadout::new().map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let surface =
            mount_operator_surface(&readout).map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let intake = self
            .material
            .intake(self.dependency.class)
            .map_err(|e| HnaSessionError::Base(e.to_string()))?;
        let mut intake = NativeInputExtendedIntake::new(intake, &self.input_material)
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
            dependency: self.dependency.clone(),
            additional_input_codewords: self
                .input_material
                .iter()
                .map(|section| section.words.len() as u64)
                .sum(),
        };
        body(&mut session)
    }
}

pub struct HnaSession<'residence, 'chart> {
    native: NativeFullOperatorSession<'residence, 'chart>,
    material: &'residence NativeConeRestrictedEcology,
    dependency: HnaBaseDependency,
    additional_input_codewords: u64,
}

/// Domain testimony attached to an explicitly native continuation. Membership records only
/// the original comparison family, not fidelity of a subsequently cultivated successor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HnaNativeAdmission {
    pub original_family_class: Option<usize>,
    pub supplied_input_rows: usize,
    pub mounted_input_capacity: usize,
}

pub struct HnaNativeCycle {
    pub admission: HnaNativeAdmission,
    pub output: NativeFullCycleOutput,
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
    pub additional_input_codewords: u64,
    pub morphology_factor_extent: usize,
    pub held_carriers: usize,
    pub declared_occurrences: usize,
    pub status: HnaSessionStatus,
    pub operation_profile: String,
    pub reuse: Option<NativeForwardReuseCensus>,
}

impl HnaSession<'_, '_> {
    pub fn transfer_census(&self)->holonic_engine::resident_section::TransferCensus {self.native.census()}
    pub fn terminal_width(&self) -> Option<usize> {
        use holonic_engine::native_ecology::holonic_intelligence::NativeCarrierAxis;
        let output = self.material.ecology.operations.last()?.output;
        match self
            .material
            .ecology
            .carriers
            .get(output.0 as usize)?
            .axes
            .as_slice()
        {
            [NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(width)] => Some(*width),
            _ => None,
        }
    }
    pub fn missing_input_rows(&self, addresses: &[u32]) -> BTreeMap<u32, Vec<u32>> {
        self.native.missing_input_rows(addresses)
    }

    /// The application acquires exact input codewords outside the engine, then supplies them at
    /// the same continuing owner's operation boundary. It never calls the source as an emitter.
    pub fn acquire_input_material(
        &mut self,
        source_root: &Path,
        addresses: &[u32],
        output: &Path,
    ) -> Result<crate::HnaInputAcquisitionReceipt, HnaSessionError> {
        let missing = self.native.missing_input_rows(addresses);
        let receipt = crate::input_material::acquire_missing(
            self.material,
            &self.dependency,
            source_root,
            missing,
            output,
        )?;
        self.supply_input_material(output)?;
        Ok(receipt)
    }

    /// A failure before publication leaves the existing native material and dependency set
    /// unchanged. A separately published material file may remain available for explicit retry.
    pub fn supply_input_material(&mut self, path: impl AsRef<Path>) -> Result<(), HnaSessionError> {
        let pin = crate::HnaInputMaterialDependency::capture(path)?;
        let mut incoming = self.dependency.clone();
        incoming.input_material = vec![pin.clone()];
        let additions = crate::input_material::load(&incoming)?;
        let count = additions
            .iter()
            .try_fold(self.additional_input_codewords, |sum, section| {
                sum.checked_add(section.words.len() as u64)
            })
            .ok_or_else(|| HnaSessionError::Base("input material extent".into()))?;
        self.dependency
            .input_material
            .try_reserve(1)
            .map_err(|error| HnaSessionError::Base(error.to_string()))?;
        self.native.extend_input_rows(&additions)?;
        self.dependency.input_material.push(pin);
        self.additional_input_codewords = count;
        Ok(())
    }
    /// Explicit native-domain recurrence, separate from the old inherited-family admission
    /// receiver. The same native operation develops the same successor; this is not another
    /// training mode. Every entering row must have actual material at every lookup port.
    pub fn advance_native(
        &mut self,
        occurrence: &HnaOccurrence,
    ) -> Result<HnaNativeCycle, HnaSessionError> {
        self.advance_native_readout(occurrence,crate::NativeEmissionReadout::Complete)
    }

    pub fn advance_native_readout(&mut self,occurrence:&HnaOccurrence,readout:crate::NativeEmissionReadout)
        -> Result<HnaNativeCycle,HnaSessionError> {self.advance_native_receiver(occurrence,false,readout)}

    /// Explicit fixed-morphology comparison of the same native owner, not production inference.
    pub fn observe_native(
        &mut self,
        occurrence: &HnaOccurrence,
    ) -> Result<HnaNativeCycle, HnaSessionError> {
        self.observe_native_readout(occurrence,crate::NativeEmissionReadout::Complete)
    }

    pub fn observe_native_readout(&mut self,occurrence:&HnaOccurrence,readout:crate::NativeEmissionReadout)
        -> Result<HnaNativeCycle,HnaSessionError> {self.advance_native_receiver(occurrence,true,readout)}

    fn advance_native_receiver(
        &mut self,
        occurrence: &HnaOccurrence,
        observe: bool,
        readout:crate::NativeEmissionReadout,
    ) -> Result<HnaNativeCycle, HnaSessionError> {
        if self.native.joined_passage_population() == 0 {
            return Err(HnaSessionError::Admission(
                "native continuation requires the observed-passage law".into(),
            ));
        }
        let mut entering = occurrence.row_addresses.clone();
        entering.extend_from_slice(&occurrence.history);
        let capacity = self.native.lookup_input_capacity()?;
        if entering.is_empty() || entering.len() > capacity {
            return Err(HnaSessionError::Admission(format!(
                "input rows {} exceed mounted aperture {capacity}, or are empty",
                entering.len()
            )));
        }
        let missing = self.native.missing_input_rows(&entering);
        if !missing.is_empty() {
            return Err(HnaSessionError::MissingInput { rows: missing });
        }
        let original_family_class = self
            .material
            .admit(&occurrence.row_addresses, &occurrence.history)
            .ok()
            .filter(|class| {
                self.dependency
                    .class
                    .is_none_or(|selected| selected == class.ordinal)
            })
            .map(|class| class.ordinal);
        let output = if observe {
            self.native.observe_passage_readout_retained(&entering,readout)?
        } else {
            self.native.advance_cycle_readout_retained(&entering,readout)?
        };
        Ok(HnaNativeCycle {
            admission: HnaNativeAdmission {
                original_family_class,
                supplied_input_rows: entering.len(),
                mounted_input_capacity: capacity,
            },
            output,
        })
    }
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
        Ok(save_checkpoint_new(path, &self.dependency, &state)?)
    }

    pub fn checkpoint_stream(
        &self,
        path: impl AsRef<Path>,
        transport: &crate::HnaStreamState,
    ) -> Result<HnaCheckpointReceipt, HnaSessionError> {
        let state = self.native.detach_rest()?;
        Ok(save_stream_checkpoint_new(
            path,
            &self.dependency,
            &state,
            transport,
        )?)
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
            additional_input_codewords: self.additional_input_codewords,
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
