use std::collections::BTreeMap;
use std::path::PathBuf;
use std::str::FromStr;

use holonics_hna::{addressed_ingress, declared_diffusion_law, AthenaAlphaApplication};
use holonic_engine::{receiver_exact_compression::ReceiverId, EventId};
use life::native_intelligence::{
    export_morphology, ExportCodecKind, ExportPurpose, MorphologyExportRequest,
    MorphologyExportReturn, NativeCirculationBoundary, NativeCirculationEvent, NativeDiffusionIngress, NativeDiffusionStanding,
    NativeWorldFace, NativeWorldStage,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Zero};
use serde_json::{json, Value};
use thiserror::Error;

use crate::adapters;
use crate::store;
use crate::{
    AthenaCommand, DiagnosticCommand, EventLevel, ExportCodecArgument, WorkbenchCommand,
    WorkbenchEvent,
};

#[derive(Debug)]
struct SessionEntry {
    application: AthenaAlphaApplication,
    boundary: Option<NativeCirculationBoundary>,
}

#[derive(Debug, Default)]
pub struct WorkbenchRuntime {
    sessions: BTreeMap<String, SessionEntry>,
    history: Vec<WorkbenchEvent>,
    next_sequence: u64,
}

#[derive(Debug, Error)]
pub enum WorkbenchError {
    #[error("session {0:?} is not open")]
    MissingSession(String),
    #[error("session {0:?} is already open")]
    ExistingSession(String),
    #[error("session {0:?} has no current conduct boundary")]
    MissingBoundary(String),
    #[error("successor index {requested} is outside the returned population {available}")]
    Successor { requested: usize, available: usize },
    #[error("invalid exact rational {0:?}")]
    Rational(String),
    #[error("{path}: {reason}")]
    Io { path: PathBuf, reason: String },
    #[error("the application owner refused: {0}")]
    Owner(String),
    #[error("this command is not wired in the current workbench phase: {0}")]
    Unwired(String),
}

impl WorkbenchError {
    pub fn code(&self) -> &'static str {
        match self {
            Self::MissingSession(_) => "missing-session",
            Self::ExistingSession(_) => "existing-session",
            Self::MissingBoundary(_) => "missing-boundary",
            Self::Successor { .. } => "invalid-successor",
            Self::Rational(_) => "invalid-rational",
            Self::Io { .. } => "io-refusal",
            Self::Owner(_) => "owner-refusal",
            Self::Unwired(_) => "unwired-command",
        }
    }
}

impl WorkbenchRuntime {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn history(&self) -> &[WorkbenchEvent] {
        &self.history
    }

    pub fn session_names(&self) -> Vec<&str> {
        self.sessions.keys().map(String::as_str).collect()
    }

    pub fn next_session_name(&self, prefix: &str) -> String {
        if !self.sessions.contains_key(prefix) {
            return prefix.to_owned();
        }
        (2u64..)
            .map(|ordinal| format!("{prefix}-{ordinal}"))
            .find(|candidate| !self.sessions.contains_key(candidate))
            .expect("the finite session map cannot exhaust u64 names")
    }

    pub fn recommended_conduct_command(
        &self,
        session: &str,
    ) -> Result<WorkbenchCommand, WorkbenchError> {
        let entry = self.session(session)?;
        let package = entry.application.package();
        let address = package
            .hot()
            .realization()
            .ingress_sections
            .first()
            .ok_or_else(|| WorkbenchError::Owner("session has no ingress section".to_owned()))?;
        let receiver = package
            .manifest
            .receiver_capability
            .native_receiver_family
            .first()
            .ok_or_else(|| WorkbenchError::Owner("session has no native receiver".to_owned()))?;
        Ok(WorkbenchCommand::Diagnostic(DiagnosticCommand::Athena(
            AthenaCommand::Conduct {
                session: session.to_owned(),
                spool: address.spool.clone(),
                thread: address.thread.clone(),
                occurrence: address.occurrence.0,
                receiver: receiver.0,
            },
        )))
    }

    pub fn execute(&mut self, command: WorkbenchCommand) -> Vec<WorkbenchEvent> {
        let result = match command {
            WorkbenchCommand::Hna(command) => {
                adapters::hna::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            WorkbenchCommand::Workspace(command) => {
                adapters::workspace::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            WorkbenchCommand::Diagnostic(command) => self.execute_diagnostic(command),
        };
        let events = match result {
            Ok(events) => events,
            Err(error) => {
                let code = error.code();
                vec![self
                    .event(
                        EventLevel::Obstruction,
                        "workbench",
                        error.to_string(),
                        None,
                    )
                    .with_code(code)]
            }
        };
        self.history.extend(events.iter().cloned());
        events
    }

    fn execute_diagnostic(
        &mut self,
        command: DiagnosticCommand,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        match command {
            DiagnosticCommand::Athena(command) => self.execute_athena(command),
            DiagnosticCommand::Status => Ok(vec![self.adapter(adapters::engine::status())]),
            DiagnosticCommand::Capabilities => {
                Ok(vec![self.adapter(adapters::engine::capabilities())])
            }
            DiagnosticCommand::Eros(command) => {
                adapters::eros::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            DiagnosticCommand::Soulkiller(command) => {
                adapters::soulkiller::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            DiagnosticCommand::Engine(command) => {
                adapters::engine::execute(command).map(|returned| vec![self.adapter(returned)])
            }
        }
    }

    fn execute_athena(
        &mut self,
        command: AthenaCommand,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        match command {
            AthenaCommand::Open { session, snapshot } => self.athena_open(session, snapshot),
            AthenaCommand::Inspect { session } => self.athena_inspect(&session),
            AthenaCommand::Conduct {
                session,
                spool,
                thread,
                occurrence,
                receiver,
            } => self.athena_conduct(
                &session,
                addressed_ingress(spool, thread, EventId(occurrence), ReceiverId(receiver)),
            ),
            AthenaCommand::Continue { session, successor } => {
                self.athena_continue(&session, successor)
            }
            AthenaCommand::Return {
                session,
                occurrence,
                admitted,
                diagnostic,
            } => self.athena_return(&session, EventId(occurrence), admitted, diagnostic.into_bytes()),
            AthenaCommand::Decline { session } => self.athena_decline(&session),
            AthenaCommand::DiffuseDemo {
                session,
                occurrence,
                interval,
            } => self.athena_diffuse_demo(&session, EventId(occurrence), parse_rat(&interval)?),
            AthenaCommand::Snapshot { session, path } => self.athena_snapshot(&session, path),
            AthenaCommand::Export {
                session,
                codec,
                path,
            } => self.athena_export(&session, codec, path),
        }
    }

    fn athena_open(
        &mut self,
        session: String,
        path: PathBuf,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        self.require_new_session(&session)?;
        let snapshot =
            life::native_intelligence::NativeCirculationSnapshot::read(&store::read(&path)?)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let application = AthenaAlphaApplication::remount(snapshot)
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let payload = session_payload(&session, &application);
        self.sessions.insert(
            session.clone(),
            SessionEntry {
                application,
                boundary: None,
            },
        );
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}"),
            format!("remounted snapshot from {}", path.display()),
            Some(payload),
        )])
    }

    fn athena_inspect(&mut self, session: &str) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let entry = self.session(session)?;
        let payload = session_payload(session, &entry.application);
        Ok(vec![self.event(
            EventLevel::Information,
            format!("athena/{session}"),
            "inspected native morphology anatomy and ingress population",
            Some(payload),
        )])
    }

    fn athena_conduct(
        &mut self,
        session: &str,
        request: holonic_engine::native_ecology::holonic_intelligence::NativeInferenceRequest,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let boundary = self
            .session(session)?
            .application
            .conduct(request)
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let summary = format!(
            "generation {} emitted {} future grain(s) and {} actual successor(s)",
            boundary.generation,
            boundary.futures.len(),
            boundary.actual_successors.len()
        );
        self.sessions
            .get_mut(session)
            .expect("session checked")
            .boundary = Some(boundary.clone());
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/conduct"),
            summary,
            Some(to_value(&boundary)?),
        )])
    }

    fn athena_continue(
        &mut self,
        session: &str,
        successor: usize,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let entry = self.session(session)?;
        let boundary = entry
            .boundary
            .as_ref()
            .ok_or_else(|| WorkbenchError::MissingBoundary(session.to_owned()))?;
        let address = boundary
            .actual_successors
            .get(successor)
            .ok_or(WorkbenchError::Successor {
                requested: successor,
                available: boundary.actual_successors.len(),
            })?
            .address
            .clone();
        let next = entry
            .application
            .continue_from(boundary, &address)
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        self.sessions
            .get_mut(session)
            .expect("session checked")
            .boundary = Some(next.clone());
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/continue"),
            format!("continued through actual successor {successor}"),
            Some(to_value(&next)?),
        )])
    }

    fn athena_return(
        &mut self,
        session: &str,
        occurrence: EventId,
        admitted: bool,
        diagnostic: Vec<u8>,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let standing = self.session(session)?;
        let recovery = standing
            .application
            .snapshot()
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let boundary = standing
            .boundary
            .clone()
            .ok_or_else(|| WorkbenchError::MissingBoundary(session.to_owned()))?;
        let entry = self
            .sessions
            .remove(session)
            .expect("session and boundary checked before ownership transfer");
        let faces = boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    admitted,
                    issued.support().clone(),
                    diagnostic.clone(),
                )
                .map_err(|error| WorkbenchError::Owner(error.to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = (|| {
            let stage = entry
                .application
                .stage_world_return(&boundary, faces, occurrence)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            match stage {
                NativeWorldStage::Candidate { candidate, .. } => entry
                    .application
                    .commit(candidate)
                    .map(Some)
                    .map_err(|error| WorkbenchError::Owner(error.to_string())),
                NativeWorldStage::Obstructed(_obstruction) => Ok(None),
            }
        })();
        match result {
            Ok(Some((application, commit))) => {
                let generation = application.generation();
                self.sessions.insert(
                    session.to_owned(),
                    SessionEntry {
                        application,
                        boundary: None,
                    },
                );
                Ok(vec![self.event(
                    EventLevel::Consequence,
                    format!("athena/{session}/commit"),
                    format!(
                        "committed returned occurrence {} as generation {generation}",
                        commit.returned_occurrence.0
                    ),
                    Some(to_value(&commit)?),
                )])
            }
            Ok(None) => {
                let application = AthenaAlphaApplication::remount(recovery)
                    .map_err(|restore| WorkbenchError::Owner(restore.to_string()))?;
                self.sessions.insert(
                    session.to_owned(),
                    SessionEntry {
                        application,
                        boundary: Some(boundary),
                    },
                );
                Ok(vec![self.event(
                    EventLevel::Obstruction,
                    format!("athena/{session}/world-return"),
                    "the complete world-face family founded no local cultivation candidate",
                    None,
                )])
            }
            Err(error) => {
                let application = AthenaAlphaApplication::remount(recovery)
                    .map_err(|restore| WorkbenchError::Owner(restore.to_string()))?;
                self.sessions.insert(
                    session.to_owned(),
                    SessionEntry {
                        application,
                        boundary: Some(boundary),
                    },
                );
                Err(error)
            }
        }
    }

    fn athena_decline(&mut self, session: &str) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let standing = self.session(session)?;
        let recovery = standing
            .application
            .snapshot()
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let boundary = standing
            .boundary
            .clone()
            .ok_or_else(|| WorkbenchError::MissingBoundary(session.to_owned()))?;
        let entry = self
            .sessions
            .remove(session)
            .expect("session and boundary checked before ownership transfer");
        match entry.application.decline(&boundary) {
            Ok((application, receipt)) => {
                self.sessions.insert(
                    session.to_owned(),
                    SessionEntry {
                        application,
                        boundary: None,
                    },
                );
                Ok(vec![self.event(
                    EventLevel::Consequence,
                    format!("athena/{session}/decline"),
                    "declined the current boundary without changing morphology",
                    Some(to_value(&receipt)?),
                )])
            }
            Err(error) => {
                let application = AthenaAlphaApplication::remount(recovery)
                    .map_err(|restore| WorkbenchError::Owner(restore.to_string()))?;
                self.sessions.insert(
                    session.to_owned(),
                    SessionEntry {
                        application,
                        boundary: Some(boundary),
                    },
                );
                Err(WorkbenchError::Owner(error.to_string()))
            }
        }
    }

    fn athena_diffuse_demo(
        &mut self,
        session: &str,
        occurrence: EventId,
        interval: Rat,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let entry = self.session(session)?;
        let native = entry.application.package().hot().native();
        let spool = native
            .spools
            .first()
            .ok_or_else(|| WorkbenchError::Owner("package has no spool".to_owned()))?;
        let law = declared_diffusion_law(
            native,
            &spool.address,
            spool
                .native_population
                .iter()
                .map(|native| (*native, Rat::one()))
                .collect(),
            spool
                .threads
                .iter()
                .flat_map(|thread| &thread.incidence)
                .map(|term| (term.occurrence, Rat::one()))
                .collect(),
            spool.native_population.clone(),
        )
        .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let first = *spool
            .native_population
            .iter()
            .next()
            .ok_or_else(|| WorkbenchError::Owner("spool has no native state".to_owned()))?;
        let standing = NativeDiffusionStanding {
            content: spool
                .native_population
                .iter()
                .map(|native| {
                    (
                        *native,
                        if *native == first {
                            Rat::one()
                        } else {
                            Rat::zero()
                        },
                    )
                })
                .collect(),
        };
        let event = entry
            .application
            .diffuse(
                &law,
                &standing,
                NativeDiffusionIngress {
                    occurrence,
                    interval,
                    source: BTreeMap::new(),
                },
            )
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let NativeCirculationEvent::ConstitutedDiffusion(boundary) = &event else {
            return Err(WorkbenchError::Owner(
                "diffusion returned another event species".to_owned(),
            ));
        };
        let nonzero_currents = boundary
            .receipt
            .currents
            .iter()
            .filter(|current| !current.current.is_zero())
            .count();
        let certificate = &boundary.receipt.transfer.certificate;
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/diffusion"),
            format!(
                "closed unit-law diffusion probe returned {nonzero_currents}/{} nonzero branch current(s); session state unchanged",
                boundary.receipt.currents.len(),
            ),
            Some(json!({
                "view": {
                    "kind": "closed-unit-diffusion-probe",
                    "session_state_changed": false,
                    "generation": boundary.generation,
                    "law": {
                        "capacity": "unit at every native state",
                        "conductance": "unit at every incidence occurrence",
                        "source": "none",
                        "initial_standing": "unit content at the first native state",
                    },
                    "topology": {
                        "native_nodes": boundary.native_to_node.len(),
                        "incidence_branches": boundary.receipt.currents.len(),
                        "nonzero_currents": nonzero_currents,
                        "boundary_nodes": certificate.boundary.len(),
                        "interior_nodes": certificate.interior.len(),
                    },
                    "interval": boundary.ingress.interval,
                    "receiver": boundary.emission.receiver,
                    "total_before": boundary.receipt.total_before,
                    "total_source": boundary.receipt.total_source,
                    "total_after": boundary.receipt.total_after,
                    "conservation_residual": boundary.receipt.conservation_residual,
                    "stored_energy_before": boundary.receipt.stored_energy_before,
                    "stored_energy_after": boundary.receipt.stored_energy_after,
                    "energy_departed": boundary.receipt.energy_departed,
                    "factorization_reused": boundary.receipt.transfer.reused_factorization,
                },
                "exact": event,
            })),
        )])
    }

    fn athena_snapshot(
        &mut self,
        session: &str,
        path: PathBuf,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let snapshot = self
            .session(session)?
            .application
            .snapshot()
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let wire = snapshot
            .canonical_bytes()
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        store::write(&path, &wire)?;
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/snapshot"),
            format!("wrote {} octets to {}", wire.len(), path.display()),
            Some(json!({
                "path": path,
                "generation": self.session(session)?.application.generation(),
                "commit_population": snapshot.commits.len(),
                "octets": wire.len()
            })),
        )])
    }

    fn athena_export(
        &mut self,
        session: &str,
        codec: ExportCodecArgument,
        path: PathBuf,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let package = self.session(session)?.application.package();
        let receiver_family = package
            .manifest
            .receiver_capability
            .native_receiver_family
            .clone();
        let returned = export_morphology(
            package,
            MorphologyExportRequest {
                codec: export_codec(codec),
                receiver_family,
                purpose: ExportPurpose::RestedInference,
            },
        )
        .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let MorphologyExportReturn::Exact(exact) = returned else {
            return Err(WorkbenchError::Owner(format!(
                "morphology export returned {returned:?}"
            )));
        };
        store::write(&path, &exact.artifact.bytes)?;
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/export"),
            format!(
                "wrote exact {}-octet {:?} export to {}",
                exact.artifact.bytes.len(),
                exact.artifact.codec,
                path.display()
            ),
            Some(to_value(&exact)?),
        )])
    }

    fn session(&self, session: &str) -> Result<&SessionEntry, WorkbenchError> {
        self.sessions
            .get(session)
            .ok_or_else(|| WorkbenchError::MissingSession(session.to_owned()))
    }

    fn require_new_session(&self, session: &str) -> Result<(), WorkbenchError> {
        if session.is_empty() {
            return Err(WorkbenchError::MissingSession(session.to_owned()));
        }
        if self.sessions.contains_key(session) {
            return Err(WorkbenchError::ExistingSession(session.to_owned()));
        }
        Ok(())
    }

    fn event(
        &mut self,
        level: EventLevel,
        subject: impl Into<String>,
        summary: impl Into<String>,
        payload: Option<Value>,
    ) -> WorkbenchEvent {
        let sequence = self.next_sequence;
        self.next_sequence = self.next_sequence.saturating_add(1);
        WorkbenchEvent::new(sequence, level, subject, summary, payload)
    }

    fn adapter(&mut self, returned: adapters::AdapterReturn) -> WorkbenchEvent {
        self.event(
            returned.level,
            returned.subject,
            returned.summary,
            returned.payload,
        )
    }
}

fn session_payload(session: &str, application: &AthenaAlphaApplication) -> Value {
    let package = application.package();
    let ingress = package
        .hot()
        .realization()
        .ingress_sections
        .iter()
        .map(|address| {
            json!({
                "spool": address.spool,
                "thread": address.thread,
                "occurrence": address.occurrence
            })
        })
        .collect::<Vec<_>>();
    json!({
        "session": session,
        "generation": application.generation(),
        "anatomy": package.manifest.anatomy,
        "receivers": package.manifest.receiver_capability.native_receiver_family,
        "ingress": ingress,
        "open_obligations": package.testimony.open_obligations,
    })
}

pub(crate) fn parse_rat(text: &str) -> Result<Rat, WorkbenchError> {
    if let Some((numerator, denominator)) = text.split_once('/') {
        let numerator =
            BigInt::from_str(numerator).map_err(|_| WorkbenchError::Rational(text.to_owned()))?;
        let denominator =
            BigInt::from_str(denominator).map_err(|_| WorkbenchError::Rational(text.to_owned()))?;
        if denominator.is_zero() {
            return Err(WorkbenchError::Rational(text.to_owned()));
        }
        Ok(Rat::new(numerator, denominator))
    } else {
        BigInt::from_str(text)
            .map(Rat::from_integer)
            .map_err(|_| WorkbenchError::Rational(text.to_owned()))
    }
}

fn export_codec(codec: ExportCodecArgument) -> ExportCodecKind {
    match codec {
        ExportCodecArgument::Onnx => ExportCodecKind::Onnx,
        ExportCodecArgument::Safetensors => ExportCodecKind::Safetensors,
    }
}

fn to_value<T: serde::Serialize>(value: &T) -> Result<Value, WorkbenchError> {
    serde_json::to_value(value).map_err(|error| WorkbenchError::Owner(error.to_string()))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use holonic_engine::native_spool::fixture;
    use life::native_intelligence::NativeCirculationConfiguration;
    use tempfile::tempdir;

    use super::*;

    fn command(runtime: &mut WorkbenchRuntime, command: AthenaCommand) -> Vec<WorkbenchEvent> {
        runtime.execute(WorkbenchCommand::Diagnostic(DiagnosticCommand::Athena(
            command,
        )))
    }

    /// Write one generation-zero snapshot of the declared native body so a session can be opened
    /// the same way an operator opens any other snapshot.
    fn declared_snapshot(path: &Path) {
        let mut configuration: NativeCirculationConfiguration =
            serde_json::from_str(holonics_hna::BASE_CONFIGURATION).expect("configuration");
        configuration.address.receiver = fixture::FIXTURE_RECEIVER;
        let admission = AthenaAlphaApplication::from_dismantling_return(
            fixture::detached_returned(),
            configuration,
        )
        .expect("declared admission");
        std::fs::write(
            path,
            admission
                .application
                .snapshot()
                .expect("snapshot")
                .canonical_bytes()
                .expect("snapshot wire"),
        )
        .expect("snapshot file");
    }

    fn open_declared(runtime: &mut WorkbenchRuntime, session: &str, path: &Path) -> Vec<WorkbenchEvent> {
        declared_snapshot(path);
        command(
            runtime,
            AthenaCommand::Open {
                session: session.to_owned(),
                snapshot: path.to_path_buf(),
            },
        )
    }

    #[test]
    fn named_session_conducts_commits_snapshots_remounts_diffuses_and_exports() {
        let temporary = tempdir().expect("temporary");
        let declared = temporary.path().join("declared.snapshot.json");
        let snapshot = temporary.path().join("alpha.snapshot.json");
        let export = temporary.path().join("alpha.safetensors");
        let mut runtime = WorkbenchRuntime::new();

        assert_eq!(
            open_declared(&mut runtime, "alpha", &declared)[0].level,
            EventLevel::Consequence
        );
        let inspect = command(
            &mut runtime,
            AthenaCommand::Inspect {
                session: "alpha".to_owned(),
            },
        );
        let ingress = inspect[0].payload.as_ref().expect("payload")["ingress"]
            .as_array()
            .expect("ingress");
        let first = &ingress[0];
        let conduct = command(
            &mut runtime,
            AthenaCommand::Conduct {
                session: "alpha".to_owned(),
                spool: first["spool"].as_str().expect("spool").to_owned(),
                thread: first["thread"].as_str().expect("thread").to_owned(),
                occurrence: first["occurrence"].as_u64().expect("occurrence"),
                receiver: fixture::FIXTURE_RECEIVER.0,
            },
        );
        assert_eq!(conduct[0].level, EventLevel::Consequence);
        let committed = command(
            &mut runtime,
            AthenaCommand::Return {
                session: "alpha".to_owned(),
                occurrence: 100,
                admitted: true,
                diagnostic: "bounded-test-world-admitted".to_owned(),
            },
        );
        assert!(committed[0].summary.contains("generation 1"));
        let before_diffusion = runtime
            .session("alpha")
            .expect("session")
            .application
            .snapshot()
            .expect("snapshot")
            .canonical_bytes()
            .expect("snapshot wire");
        let diffusion = command(
            &mut runtime,
            AthenaCommand::DiffuseDemo {
                session: "alpha".to_owned(),
                occurrence: 200,
                interval: "1".to_owned(),
            },
        );
        assert_eq!(diffusion[0].level, EventLevel::Consequence);
        let view = &diffusion[0].payload.as_ref().expect("diffusion payload")["view"];
        assert_eq!(view["kind"], "closed-unit-diffusion-probe");
        assert_eq!(view["session_state_changed"], false);
        assert_eq!(view["topology"]["native_nodes"], 5);
        assert_eq!(view["topology"]["incidence_branches"], 4);
        assert_eq!(view["topology"]["nonzero_currents"], 2);
        assert_eq!(
            view["total_before"],
            serde_json::json!([[1, [1]], [1, [1]]])
        );
        assert_eq!(view["total_after"], serde_json::json!([[1, [1]], [1, [1]]]));
        assert_eq!(
            view["conservation_residual"],
            serde_json::json!([[0, []], [1, [1]]])
        );
        assert!(
            crate::presentation::summary(&diffusion[0]).contains("Session state         unchanged")
        );
        assert!(crate::presentation::structure(&diffusion[0]).contains("NODE BALANCES"));
        let after_diffusion = runtime
            .session("alpha")
            .expect("session")
            .application
            .snapshot()
            .expect("snapshot")
            .canonical_bytes()
            .expect("snapshot wire");
        assert_eq!(after_diffusion, before_diffusion);
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Snapshot {
                    session: "alpha".to_owned(),
                    path: snapshot.clone(),
                }
            )[0]
            .level,
            EventLevel::Consequence
        );
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Export {
                    session: "alpha".to_owned(),
                    codec: ExportCodecArgument::Safetensors,
                    path: export.clone(),
                }
            )[0]
            .level,
            EventLevel::Consequence
        );
        assert!(snapshot.is_file());
        assert!(export.is_file());
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Open {
                    session: "remounted".to_owned(),
                    snapshot,
                }
            )[0]
            .level,
            EventLevel::Consequence
        );
        assert_eq!(runtime.session_names(), vec!["alpha", "remounted"]);
    }

    #[test]
    fn missing_session_boundary_false_successor_and_invalid_rational_refuse() {
        let temporary = tempdir().expect("temporary");
        let declared = temporary.path().join("declared.snapshot.json");
        let mut runtime = WorkbenchRuntime::new();
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Inspect {
                    session: "absent".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
        assert!(runtime.session_names().is_empty());
        open_declared(&mut runtime, "alpha", &declared);
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Continue {
                    session: "alpha".to_owned(),
                    successor: 0,
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Return {
                    session: "alpha".to_owned(),
                    occurrence: 100,
                    admitted: true,
                    diagnostic: "no-boundary".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
        assert_eq!(runtime.session_names(), vec!["alpha"]);
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Decline {
                    session: "alpha".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
        assert_eq!(runtime.session_names(), vec!["alpha"]);
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Inspect {
                    session: "alpha".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Information
        );
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::Return {
                    session: "alpha".to_owned(),
                    occurrence: 100,
                    admitted: true,
                    diagnostic: "still-no-boundary".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
        assert_eq!(runtime.session_names(), vec!["alpha"]);
    }
}
