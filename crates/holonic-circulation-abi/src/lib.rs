//! Versioned, length-delimited exterior ABI for live holonic circulation.
//!
//! The ABI owns only opaque process handles and JSON message transport. Native morphology,
//! inference, cultivation, diffusion, and persistence remain in `life`; no Rust layout, trait
//! object, foreign executor, model label, or semantic registry crosses this boundary.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use holonic_engine::native_ecology::holonic_intelligence::NativeInferenceRequest;
use holonic_engine::receiver_history_compression::NativeStateId;
use holonic_engine::{
    diffusion::{DiffusionBoundaryTransferReceipt, DiffusionCurrent, DiffusionNodeBalance},
    CurrentBranchId, CurrentNodeId, EventId,
};
use life::native_intelligence::{
    NativeCirculationBoundary, NativeCirculationConfiguration, NativeCirculationEvent,
    NativeCirculationSession, NativeCirculationSnapshot, NativeCultivationCandidate,
    NativeDeclineReceipt, NativeDiffusionIngress, NativeDiffusionLaw, NativeDiffusionStanding,
    NativeMorphologyCommit, NativeMorphologyArtifact, NativeOwnedInferenceAddress,
    NativeSessionError, NativeWorldFace, NativeWorldObstruction, NativeWorldStage,
};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

pub const HOLONICS_CIRCULATION_ABI_SCHEMA: &str = "org.holonics.circulation-abi.v2";

static NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
static SESSIONS: OnceLock<Mutex<BTreeMap<u64, NativeCirculationSession>>> = OnceLock::new();

fn sessions() -> &'static Mutex<BTreeMap<u64, NativeCirculationSession>> {
    SESSIONS.get_or_init(|| Mutex::new(BTreeMap::new()))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiEnvelope {
    pub schema: String,
    pub request_id: u64,
    pub command: AbiCommand,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "command", rename_all = "kebab-case")]
pub enum AbiCommand {
    Open {
        package_wire: Vec<u8>,
        configuration: NativeCirculationConfiguration,
    },
    Remount {
        snapshot: NativeCirculationSnapshot,
    },
    Conduct {
        handle: u64,
        request: NativeInferenceRequest,
    },
    Continue {
        handle: u64,
        boundary: NativeCirculationBoundary,
        successor: NativeOwnedInferenceAddress,
    },
    Return {
        handle: u64,
        boundary: NativeCirculationBoundary,
        faces: Vec<NativeWorldFace>,
        returned_occurrence: EventId,
    },
    Commit {
        handle: u64,
        candidate: NativeCultivationCandidate,
    },
    Decline {
        handle: u64,
        boundary: NativeCirculationBoundary,
    },
    Snapshot {
        handle: u64,
    },
    Diffuse {
        handle: u64,
        law: AbiDiffusionLaw,
        standing: AbiDiffusionStanding,
        ingress: AbiDiffusionIngress,
    },
    Close {
        handle: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiDiffusionLaw {
    pub spool_address: String,
    pub capacities: Vec<(NativeStateId, Rat)>,
    pub conductances: Vec<(EventId, Rat)>,
    pub boundary: Vec<NativeStateId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiDiffusionStanding {
    pub content: Vec<(NativeStateId, Rat)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiDiffusionIngress {
    pub occurrence: EventId,
    pub interval: Rat,
    pub source: Vec<(NativeStateId, Rat)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiResponse {
    pub schema: String,
    pub request_id: u64,
    pub disposition: AbiDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "disposition", rename_all = "kebab-case")]
pub enum AbiDisposition {
    Opened {
        handle: u64,
        generation: u64,
    },
    Boundary {
        boundary: NativeCirculationBoundary,
    },
    Candidate {
        candidate: NativeCultivationCandidate,
    },
    WorldObstruction {
        obstruction: NativeWorldObstruction,
    },
    Committed {
        handle: u64,
        generation: u64,
        commit: NativeMorphologyCommit,
    },
    Declined {
        handle: u64,
        receipt: NativeDeclineReceipt,
    },
    Snapshot {
        snapshot: NativeCirculationSnapshot,
    },
    Diffused {
        boundary: AbiDiffusiveBoundary,
    },
    Closed {
        handle: u64,
    },
    Refused {
        code: AbiRefusalCode,
        detail: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AbiRefusalCode {
    MalformedMessage,
    InvalidHandle,
    Configuration,
    Conduct,
    StaleBoundary,
    WorldFace,
    Ingress,
    FalseSuccessor,
    NonlaterReturn,
    Commit,
    Snapshot,
    InternalPanic,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiDiffusionReceipt {
    pub schema: String,
    pub interval: Rat,
    pub potential_before: Vec<(CurrentNodeId, Rat)>,
    pub potential_after: Vec<(CurrentNodeId, Rat)>,
    pub currents: Vec<DiffusionCurrent>,
    pub balances: Vec<DiffusionNodeBalance>,
    pub total_before: Rat,
    pub total_source: Rat,
    pub total_after: Rat,
    pub conservation_residual: Rat,
    pub stored_energy_before: Rat,
    pub stored_energy_after: Rat,
    pub energy_departed: Rat,
    pub transfer: DiffusionBoundaryTransferReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AbiDiffusiveBoundary {
    pub schema: String,
    pub generation: u64,
    pub configuration: life::native_intelligence::InferenceConfigurationAddress,
    pub spool_address: String,
    pub ingress: AbiDiffusionIngress,
    pub standing_before: AbiDiffusionStanding,
    pub standing_after: AbiDiffusionStanding,
    pub emission_occurrence: EventId,
    pub emission_receiver: holonic_engine::receiver_exact_compression::ReceiverId,
    pub boundary_content: Vec<(NativeStateId, Rat)>,
    pub boundary_potential: Vec<(NativeStateId, Rat)>,
    pub native_to_node: Vec<(NativeStateId, CurrentNodeId)>,
    pub branch_to_occurrence: Vec<(CurrentBranchId, EventId)>,
    pub receipt: AbiDiffusionReceipt,
    pub open_obligations: Vec<life::native_intelligence::NativeOwnedOpenObligation>,
}

impl AbiDiffusiveBoundary {
    pub fn from_event(event: NativeCirculationEvent) -> Result<Self, NativeSessionError> {
        let NativeCirculationEvent::ConstitutedDiffusion(boundary) = event else {
            return Err(NativeSessionError::Conduct(
                "the ABI diffusion return was not a diffusive boundary".to_owned(),
            ));
        };
        let receipt = boundary.receipt;
        Ok(Self {
            schema: boundary.schema,
            generation: boundary.generation,
            configuration: boundary.configuration,
            spool_address: boundary.spool_address,
            ingress: AbiDiffusionIngress {
                occurrence: boundary.ingress.occurrence,
                interval: boundary.ingress.interval,
                source: boundary.ingress.source.into_iter().collect(),
            },
            standing_before: AbiDiffusionStanding {
                content: boundary.standing_before.content.into_iter().collect(),
            },
            standing_after: AbiDiffusionStanding {
                content: boundary.standing_after.content.into_iter().collect(),
            },
            emission_occurrence: boundary.emission.occurrence,
            emission_receiver: boundary.emission.receiver,
            boundary_content: boundary.emission.boundary_content.into_iter().collect(),
            boundary_potential: boundary.emission.boundary_potential.into_iter().collect(),
            native_to_node: boundary.native_to_node.into_iter().collect(),
            branch_to_occurrence: boundary.branch_to_occurrence.into_iter().collect(),
            receipt: AbiDiffusionReceipt {
                schema: receipt.schema,
                interval: receipt.interval,
                potential_before: receipt.potential_before.into_iter().collect(),
                potential_after: receipt.potential_after.into_iter().collect(),
                currents: receipt.currents,
                balances: receipt.balances,
                total_before: receipt.total_before,
                total_source: receipt.total_source,
                total_after: receipt.total_after,
                conservation_residual: receipt.conservation_residual,
                stored_energy_before: receipt.stored_energy_before,
                stored_energy_after: receipt.stored_energy_after,
                energy_departed: receipt.energy_departed,
                transfer: receipt.transfer,
            },
            open_obligations: boundary.open_obligations,
        })
    }
}

pub fn dispatch_bytes(input: &[u8]) -> Vec<u8> {
    let result = catch_unwind(AssertUnwindSafe(|| dispatch_inner(input)));
    let response = match result {
        Ok(response) => response,
        Err(_) => AbiResponse {
            schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
            request_id: 0,
            disposition: AbiDisposition::Refused {
                code: AbiRefusalCode::InternalPanic,
                detail: "the circulation ABI caught an internal panic".to_owned(),
            },
        },
    };
    serde_json::to_vec(&response).unwrap_or_else(|_| {
        br#"{"schema":"org.holonics.circulation-abi.v2","request_id":0,"disposition":"refused","code":"malformed-message","detail":"response serialization failed"}"#.to_vec()
    })
}

fn dispatch_inner(input: &[u8]) -> AbiResponse {
    let envelope: AbiEnvelope = match serde_json::from_slice::<AbiEnvelope>(input) {
        Ok(envelope) if envelope.schema == HOLONICS_CIRCULATION_ABI_SCHEMA => envelope,
        Ok(envelope) => {
            return refused(
                envelope.request_id,
                AbiRefusalCode::MalformedMessage,
                "unknown circulation ABI schema",
            );
        }
        Err(error) => {
            return refused(0, AbiRefusalCode::MalformedMessage, &error.to_string());
        }
    };
    let request_id = envelope.request_id;
    match dispatch_command(envelope.command) {
        Ok(disposition) => AbiResponse {
            schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
            request_id,
            disposition,
        },
        Err((code, detail)) => refused(request_id, code, &detail),
    }
}

fn dispatch_command(command: AbiCommand) -> Result<AbiDisposition, (AbiRefusalCode, String)> {
    match command {
        AbiCommand::Open {
            package_wire,
            configuration,
        } => {
            let package = NativeMorphologyArtifact::read(&package_wire)
                .map_err(NativeSessionError::from)
                .map_err(session_error)?;
            let session =
                NativeCirculationSession::mount(package, configuration).map_err(session_error)?;
            insert_session(session)
        }
        AbiCommand::Remount { snapshot } => {
            let session = NativeCirculationSession::remount(snapshot).map_err(session_error)?;
            insert_session(session)
        }
        AbiCommand::Conduct { handle, request } => with_session(handle, |session| {
            session
                .conduct(request)
                .map(|boundary| AbiDisposition::Boundary { boundary })
        }),
        AbiCommand::Continue {
            handle,
            boundary,
            successor,
        } => with_session(handle, |session| {
            session
                .continue_from(&boundary, &successor)
                .map(|boundary| AbiDisposition::Boundary { boundary })
        }),
        AbiCommand::Return {
            handle,
            boundary,
            faces,
            returned_occurrence,
        } => with_session(handle, |session| {
            session
                .stage_world_return(&boundary, faces, returned_occurrence)
                .map(|stage| match stage {
                    NativeWorldStage::Candidate { candidate, .. } => {
                        AbiDisposition::Candidate { candidate }
                    }
                    NativeWorldStage::Obstructed(obstruction) => {
                        AbiDisposition::WorldObstruction { obstruction }
                    }
                })
        }),
        AbiCommand::Commit { handle, candidate } => mutate_session(handle, |session| {
            session.commit(candidate).map(|(session, commit)| {
                let generation = session.generation();
                (
                    session,
                    AbiDisposition::Committed {
                        handle,
                        generation,
                        commit,
                    },
                )
            })
        }),
        AbiCommand::Decline { handle, boundary } => mutate_session(handle, |session| {
            session
                .decline(&boundary)
                .map(|(session, receipt)| (session, AbiDisposition::Declined { handle, receipt }))
        }),
        AbiCommand::Snapshot { handle } => with_session(handle, |session| {
            session
                .snapshot()
                .map(|snapshot| AbiDisposition::Snapshot { snapshot })
        }),
        AbiCommand::Diffuse {
            handle,
            law,
            standing,
            ingress,
        } => with_session(handle, |session| {
            let capacities = exact_map(law.capacities, "duplicate diffusion capacity")?;
            let conductances = exact_map(law.conductances, "duplicate diffusion conductance")?;
            let boundary = law.boundary.into_iter().collect::<BTreeSet<_>>();
            let standing = NativeDiffusionStanding {
                content: exact_map(standing.content, "duplicate diffusion standing")?,
            };
            let ingress = NativeDiffusionIngress {
                occurrence: ingress.occurrence,
                interval: ingress.interval,
                source: exact_map(ingress.source, "duplicate diffusion source")?,
            };
            let law = NativeDiffusionLaw::found(
                session.package().hot().native(),
                &law.spool_address,
                capacities,
                conductances,
                boundary,
            )?;
            session
                .diffuse(&law, &standing, ingress)
                .and_then(AbiDiffusiveBoundary::from_event)
                .map(|boundary| AbiDisposition::Diffused { boundary })
        }),
        AbiCommand::Close { handle } => {
            let removed = sessions()
                .lock()
                .map_err(|_| internal_registry())?
                .remove(&handle);
            if removed.is_none() {
                return Err(invalid_handle(handle));
            }
            Ok(AbiDisposition::Closed { handle })
        }
    }
}

fn insert_session(
    session: NativeCirculationSession,
) -> Result<AbiDisposition, (AbiRefusalCode, String)> {
    let handle = NEXT_HANDLE.fetch_add(1, Ordering::Relaxed);
    if handle == 0 {
        return Err((
            AbiRefusalCode::Commit,
            "opaque handle space exhausted".to_owned(),
        ));
    }
    let generation = session.generation();
    sessions()
        .lock()
        .map_err(|_| internal_registry())?
        .insert(handle, session);
    Ok(AbiDisposition::Opened { handle, generation })
}

fn with_session(
    handle: u64,
    operation: impl FnOnce(&NativeCirculationSession) -> Result<AbiDisposition, NativeSessionError>,
) -> Result<AbiDisposition, (AbiRefusalCode, String)> {
    let registry = sessions().lock().map_err(|_| internal_registry())?;
    let session = registry
        .get(&handle)
        .ok_or_else(|| invalid_handle(handle))?;
    operation(session).map_err(session_error)
}

/// Perform a consuming mutation with exact snapshot recovery on refusal.
fn mutate_session(
    handle: u64,
    operation: impl FnOnce(
        NativeCirculationSession,
    )
        -> Result<(NativeCirculationSession, AbiDisposition), NativeSessionError>,
) -> Result<AbiDisposition, (AbiRefusalCode, String)> {
    let mut registry = sessions().lock().map_err(|_| internal_registry())?;
    let session = registry
        .remove(&handle)
        .ok_or_else(|| invalid_handle(handle))?;
    let recovery = session.snapshot().map_err(session_error)?;
    match operation(session) {
        Ok((session, disposition)) => {
            registry.insert(handle, session);
            Ok(disposition)
        }
        Err(error) => {
            let restored = NativeCirculationSession::remount(recovery).map_err(session_error)?;
            registry.insert(handle, restored);
            Err(session_error(error))
        }
    }
}

fn session_error(error: NativeSessionError) -> (AbiRefusalCode, String) {
    let code = match &error {
        NativeSessionError::Configuration => AbiRefusalCode::Configuration,
        NativeSessionError::Conduct(_) => AbiRefusalCode::Conduct,
        NativeSessionError::Boundary => AbiRefusalCode::StaleBoundary,
        NativeSessionError::WorldFace => AbiRefusalCode::WorldFace,
        NativeSessionError::Ingress(_) => AbiRefusalCode::Ingress,
        NativeSessionError::FalseSuccessor => AbiRefusalCode::FalseSuccessor,
        NativeSessionError::Return => AbiRefusalCode::NonlaterReturn,
        NativeSessionError::Commit(_) => AbiRefusalCode::Commit,
        NativeSessionError::Snapshot(_) | NativeSessionError::Package(_) => {
            AbiRefusalCode::Snapshot
        }
    };
    (code, error.to_string())
}

fn invalid_handle(handle: u64) -> (AbiRefusalCode, String) {
    (
        AbiRefusalCode::InvalidHandle,
        format!("opaque circulation handle {handle} is not open"),
    )
}

fn internal_registry() -> (AbiRefusalCode, String) {
    (
        AbiRefusalCode::Commit,
        "opaque circulation handle table is unavailable".to_owned(),
    )
}

fn exact_map<Key: Ord, Value>(
    pairs: Vec<(Key, Value)>,
    duplicate: &str,
) -> Result<BTreeMap<Key, Value>, NativeSessionError> {
    let supplied = pairs.len();
    let map = pairs.into_iter().collect::<BTreeMap<_, _>>();
    if map.len() != supplied {
        return Err(NativeSessionError::Conduct(duplicate.to_owned()));
    }
    Ok(map)
}

fn refused(request_id: u64, code: AbiRefusalCode, detail: &str) -> AbiResponse {
    AbiResponse {
        schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
        request_id,
        disposition: AbiDisposition::Refused {
            code,
            detail: detail.to_owned(),
        },
    }
}

#[repr(C)]
pub struct HolonicsAbiBytes {
    pub ptr: *mut u8,
    pub len: usize,
    pub capacity: usize,
}

impl HolonicsAbiBytes {
    fn from_vec(mut bytes: Vec<u8>) -> Self {
        let returned = Self {
            ptr: bytes.as_mut_ptr(),
            len: bytes.len(),
            capacity: bytes.capacity(),
        };
        std::mem::forget(bytes);
        returned
    }
}

/// Dispatch one complete versioned command message.
///
/// # Safety
///
/// `input` must point to `length` readable bytes for the duration of this call. The returned bytes
/// must be released exactly once with [`holonics_circulation_bytes_free`].
#[no_mangle]
pub unsafe extern "C" fn holonics_circulation_dispatch(
    input: *const u8,
    length: usize,
) -> HolonicsAbiBytes {
    let bytes = if length == 0 {
        &[]
    } else if input.is_null() {
        return HolonicsAbiBytes::from_vec(dispatch_bytes(&[]));
    } else {
        // SAFETY: the caller promises a readable length-delimited input region.
        unsafe { std::slice::from_raw_parts(input, length) }
    };
    HolonicsAbiBytes::from_vec(dispatch_bytes(bytes))
}

/// Release one buffer returned by [`holonics_circulation_dispatch`].
///
/// # Safety
///
/// `bytes` must be an unmodified buffer returned by this library and not previously released.
#[no_mangle]
pub unsafe extern "C" fn holonics_circulation_bytes_free(bytes: HolonicsAbiBytes) {
    if !bytes.ptr.is_null() {
        // SAFETY: the caller returns the exact pointer/length/capacity triple allocated above.
        unsafe {
            drop(Vec::from_raw_parts(bytes.ptr, bytes.len, bytes.capacity));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        native_ecology::holonic_intelligence::NativeInferenceAddress, native_spool::fixture,
    };
    use life::native_intelligence::{
        consume_dismantling_return, InferenceConfigurationAddress, MorphologyLineage,
    };
    use num_rational::BigRational as Rat;
    use num_traits::{One, Zero};

    fn fixture() -> (
        Vec<u8>,
        NativeCirculationConfiguration,
        NativeInferenceRequest,
    ) {
        let (hot, _) = consume_dismantling_return(fixture::returned()).expect("hot");
        let package = NativeMorphologyArtifact::found(
            hot,
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        let native = package.hot().native();
        let request = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: native.spools[0].address.clone(),
                thread: native.spools[0].threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: fixture::FIXTURE_RECEIVER,
        };
        let configuration = NativeCirculationConfiguration::found(InferenceConfigurationAddress {
            ingress_aperture: "native-addressed-occurrence".to_owned(),
            occurrence: EventId(1),
            receiver: fixture::FIXTURE_RECEIVER,
            continuation_receiver: "exterior-receiver-decision".to_owned(),
            world_return_law: "genuinely-later-return".to_owned(),
            emission_codec: "owned-structural-boundary".to_owned(),
            apparatus: "circulation-abi".to_owned(),
            stochastic_current: None,
        })
        .expect("configuration");
        (
            package.canonical_bytes().expect("package wire"),
            configuration,
            request,
        )
    }

    fn dispatch(request_id: u64, command: AbiCommand) -> AbiResponse {
        let envelope = AbiEnvelope {
            schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
            request_id,
            command,
        };
        serde_json::from_slice(&dispatch_bytes(
            &serde_json::to_vec(&envelope).expect("request wire"),
        ))
        .expect("response wire")
    }

    #[test]
    fn abi_and_direct_conduct_return_the_same_owned_boundary() {
        let (package_wire, configuration, request) = fixture();
        let direct_session = NativeCirculationSession::mount(
            NativeMorphologyArtifact::read(&package_wire).expect("direct package"),
            configuration.clone(),
        )
        .expect("direct session");
        let direct = direct_session
            .conduct(request.clone())
            .expect("direct boundary");
        let opened = dispatch(
            1,
            AbiCommand::Open {
                package_wire,
                configuration,
            },
        );
        let AbiDisposition::Opened { handle, .. } = opened.disposition else {
            panic!("open response");
        };
        let response = dispatch(2, AbiCommand::Conduct { handle, request });
        let AbiDisposition::Boundary { boundary } = response.disposition else {
            panic!("boundary response");
        };
        assert_eq!(boundary, direct);
        let successor = boundary.actual_successors[0].address.clone();
        let direct_next = direct_session
            .continue_from(&direct, &successor)
            .expect("direct continuation");
        let AbiDisposition::Boundary { boundary: next } = dispatch(
            3,
            AbiCommand::Continue {
                handle,
                boundary,
                successor,
            },
        )
        .disposition
        else {
            panic!("continue response");
        };
        assert_eq!(next, direct_next);

        let spool = &direct_session.package().hot().native().spools[0];
        let law_wire = AbiDiffusionLaw {
            spool_address: spool.address.clone(),
            capacities: spool
                .native_population
                .iter()
                .map(|native| (*native, Rat::one()))
                .collect::<Vec<_>>(),
            conductances: spool
                .threads
                .iter()
                .flat_map(|thread| &thread.incidence)
                .map(|term| (term.occurrence, Rat::one()))
                .collect::<Vec<_>>(),
            boundary: spool.native_population.iter().copied().collect(),
        };
        let first_native = *spool.native_population.iter().next().expect("native");
        let standing = AbiDiffusionStanding {
            content: spool
                .native_population
                .iter()
                .map(|native| {
                    (
                        *native,
                        if *native == first_native {
                            Rat::one()
                        } else {
                            Rat::zero()
                        },
                    )
                })
                .collect::<Vec<_>>(),
        };
        let direct_law = NativeDiffusionLaw::found(
            direct_session.package().hot().native(),
            &law_wire.spool_address,
            law_wire.capacities.iter().cloned().collect(),
            law_wire.conductances.iter().cloned().collect(),
            law_wire.boundary.iter().copied().collect(),
        )
        .expect("direct diffusion law");
        let ingress = AbiDiffusionIngress {
            occurrence: EventId(50),
            interval: Rat::one(),
            source: Vec::new(),
        };
        let direct_standing = NativeDiffusionStanding {
            content: standing.content.iter().cloned().collect(),
        };
        let direct_ingress = NativeDiffusionIngress {
            occurrence: ingress.occurrence,
            interval: ingress.interval.clone(),
            source: BTreeMap::new(),
        };
        let direct_diffusion = direct_session
            .diffuse(&direct_law, &direct_standing, direct_ingress)
            .expect("direct diffusion");
        let direct_diffusion =
            AbiDiffusiveBoundary::from_event(direct_diffusion).expect("direct ABI diffusion");
        let diffused = dispatch(
            4,
            AbiCommand::Diffuse {
                handle,
                law: law_wire,
                standing,
                ingress,
            },
        );
        let AbiDisposition::Diffused { boundary: event } = diffused.disposition else {
            panic!("diffusion response: {diffused:?}");
        };
        assert_eq!(event, direct_diffusion);
        assert!(matches!(
            dispatch(5, AbiCommand::Close { handle }).disposition,
            AbiDisposition::Closed { .. }
        ));
    }

    #[test]
    fn return_commit_snapshot_remount_decline_and_invalid_handle_refusal() {
        let (package_wire, configuration, request) = fixture();
        let opened = dispatch(
            10,
            AbiCommand::Open {
                package_wire,
                configuration,
            },
        );
        let AbiDisposition::Opened { handle, .. } = opened.disposition else {
            panic!("open response");
        };
        let AbiDisposition::Boundary { boundary } = dispatch(
            11,
            AbiCommand::Conduct {
                handle,
                request: request.clone(),
            },
        )
        .disposition
        else {
            panic!("boundary response");
        };
        let faces = boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    true,
                    issued.support().clone(),
                    b"abi-world-admitted".to_vec(),
                )
                .expect("world face")
            })
            .collect();
        let AbiDisposition::Candidate { candidate } = dispatch(
            12,
            AbiCommand::Return {
                handle,
                boundary: boundary.clone(),
                faces,
                returned_occurrence: EventId(100),
            },
        )
        .disposition
        else {
            panic!("candidate response");
        };
        assert!(matches!(
            dispatch(13, AbiCommand::Commit { handle, candidate }).disposition,
            AbiDisposition::Committed { generation: 1, .. }
        ));
        let AbiDisposition::Snapshot { snapshot } =
            dispatch(14, AbiCommand::Snapshot { handle }).disposition
        else {
            panic!("snapshot response");
        };
        assert!(matches!(
            dispatch(15, AbiCommand::Close { handle }).disposition,
            AbiDisposition::Closed { .. }
        ));
        let AbiDisposition::Opened {
            handle: remounted,
            generation: 1,
        } = dispatch(16, AbiCommand::Remount { snapshot }).disposition
        else {
            panic!("remount response");
        };
        let AbiDisposition::Boundary { boundary } = dispatch(
            17,
            AbiCommand::Conduct {
                handle: remounted,
                request: NativeInferenceRequest {
                    address: NativeInferenceAddress {
                        spool: request.address.spool,
                        thread: "thread/returned-interaction-100".to_owned(),
                        occurrence: EventId(100),
                    },
                    receiver: fixture::FIXTURE_RECEIVER,
                },
            },
        )
        .disposition
        else {
            panic!("remounted conduct response");
        };
        assert!(matches!(
            dispatch(
                18,
                AbiCommand::Decline {
                    handle: remounted,
                    boundary,
                }
            )
            .disposition,
            AbiDisposition::Declined { .. }
        ));
        assert!(matches!(
            dispatch(19, AbiCommand::Close { handle: remounted }).disposition,
            AbiDisposition::Closed { .. }
        ));
        assert!(matches!(
            dispatch(20, AbiCommand::Snapshot { handle: remounted }).disposition,
            AbiDisposition::Refused {
                code: AbiRefusalCode::InvalidHandle,
                ..
            }
        ));
    }

    #[test]
    fn exported_length_delimited_entry_returns_owned_bytes() {
        let input = serde_json::to_vec(&AbiEnvelope {
            schema: HOLONICS_CIRCULATION_ABI_SCHEMA.to_owned(),
            request_id: 30,
            command: AbiCommand::Close { handle: u64::MAX },
        })
        .expect("input");
        // SAFETY: the input remains live for the call and the exact returned allocation is freed.
        let output = unsafe { holonics_circulation_dispatch(input.as_ptr(), input.len()) };
        assert!(!output.ptr.is_null());
        // SAFETY: the returned length-delimited region remains owned by the ABI until free.
        let response: AbiResponse = unsafe {
            serde_json::from_slice(std::slice::from_raw_parts(output.ptr, output.len))
                .expect("response")
        };
        assert!(matches!(
            response.disposition,
            AbiDisposition::Refused {
                code: AbiRefusalCode::InvalidHandle,
                ..
            }
        ));
        // SAFETY: this is the exact unmodified allocation returned above.
        unsafe { holonics_circulation_bytes_free(output) };
    }
}
