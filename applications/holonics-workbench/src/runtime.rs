use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::str::FromStr;

use athena_alpha::{
    addressed_ingress, declared_diffusion_law, returned_local_interaction, AthenaAlphaApplication,
    BASE_CONFIGURATION,
};
use holonic_engine::{
    native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
    BoundaryId, EventId, ExactComplexWaveCurrent,
};
use life::native_intelligence::{
    export_morphology, ExportCodecKind, ExportPurpose, MorphologyExportRequest,
    MorphologyExportReturn, NativeCirculationBoundary, NativeCirculationConfiguration,
    NativeCirculationEvent, NativeDiffusionIngress, NativeDiffusionStanding,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Zero};
use serde_json::{json, Value};
use thiserror::Error;

use crate::adapters;
use crate::store;
use crate::{AthenaCommand, EventLevel, ExportCodecArgument, WorkbenchCommand, WorkbenchEvent};

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

    pub fn execute(&mut self, command: WorkbenchCommand) -> Vec<WorkbenchEvent> {
        let result = match command {
            WorkbenchCommand::Athena(command) => self.execute_athena(command),
            WorkbenchCommand::Status => Ok(vec![self.adapter(adapters::engine::status())]),
            WorkbenchCommand::Capabilities => {
                Ok(vec![self.adapter(adapters::engine::capabilities())])
            }
            WorkbenchCommand::Eros(command) => {
                adapters::eros::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            WorkbenchCommand::Soulkiller(command) => {
                adapters::soulkiller::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            WorkbenchCommand::Engine(command) => {
                adapters::engine::execute(command).map(|returned| vec![self.adapter(returned)])
            }
        };
        let events = match result {
            Ok(events) => events,
            Err(error) => vec![self.event(
                EventLevel::Obstruction,
                "workbench",
                error.to_string(),
                None,
            )],
        };
        self.history.extend(events.iter().cloned());
        events
    }

    fn execute_athena(
        &mut self,
        command: AthenaCommand,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        match command {
            AthenaCommand::DemoOpen { session } => self.athena_demo_open(session),
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
                boundary,
                real,
                imaginary,
                storage,
            } => self.athena_return(
                &session,
                EventId(occurrence),
                BoundaryId(boundary),
                parse_rat(&real)?,
                parse_rat(&imaginary)?,
                parse_rat(&storage)?,
            ),
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

    fn athena_demo_open(&mut self, session: String) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        self.require_new_session(&session)?;
        let configuration: NativeCirculationConfiguration =
            serde_json::from_str(BASE_CONFIGURATION)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![
                demo_excitation(1, None, 0x3f80, 0x4000),
                demo_excitation(2, Some(1), 0x4000, 0x4040),
                demo_excitation(3, None, 0x4080, 0x40a0),
            ],
        })
        .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let admission = AthenaAlphaApplication::from_dismantling_return(returned, configuration)
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let payload = session_payload(&session, &admission.application);
        self.sessions.insert(
            session.clone(),
            SessionEntry {
                application: admission.application,
                boundary: None,
            },
        );
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}"),
            "opened bounded source-neutral demo morphology at generation 0",
            Some(payload),
        )])
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
        boundary_address: BoundaryId,
        real: Rat,
        imaginary: Rat,
        storage: Rat,
    ) -> Result<Vec<WorkbenchEvent>, WorkbenchError> {
        let mut entry = self
            .sessions
            .remove(session)
            .ok_or_else(|| WorkbenchError::MissingSession(session.to_owned()))?;
        let recovery = entry
            .application
            .snapshot()
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
        let boundary = entry
            .boundary
            .take()
            .ok_or_else(|| WorkbenchError::MissingBoundary(session.to_owned()))?;
        let result = (|| {
            let returned = returned_local_interaction(
                boundary.emission.address.clone(),
                occurrence,
                boundary_address,
                ExactComplexWaveCurrent::new(real, imaginary),
                storage,
                BTreeSet::new(),
            )
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            let candidate = entry
                .application
                .stage_return(&boundary, returned)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            entry
                .application
                .commit(candidate)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))
        })();
        match result {
            Ok((application, commit)) => {
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
        let mut entry = self
            .sessions
            .remove(session)
            .ok_or_else(|| WorkbenchError::MissingSession(session.to_owned()))?;
        let boundary = entry
            .boundary
            .take()
            .ok_or_else(|| WorkbenchError::MissingBoundary(session.to_owned()))?;
        let (application, receipt) = entry
            .application
            .decline(&boundary)
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
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
        Ok(vec![self.event(
            EventLevel::Consequence,
            format!("athena/{session}/diffusion"),
            format!(
                "diffused {} current branch(es) with conservation residual {}",
                boundary.receipt.currents.len(),
                boundary.receipt.conservation_residual
            ),
            Some(to_value(&event)?),
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
        "open_obligations": package.reconstruction.open_obligations,
    })
}

fn demo_excitation(
    event: u64,
    predecessor: Option<u64>,
    entering: u16,
    returned: u16,
) -> ForeignBf16Excitation {
    ForeignBf16Excitation {
        event: EventId(event),
        predecessor: predecessor.map(EventId),
        entering_boundary: BoundaryId(event * 2),
        emitting_boundary: BoundaryId(event * 2 + 1),
        source_occurrence: format!("workbench-demo/{event}"),
        exterior_modality: ExteriorModality::Text,
        entering_codewords: vec![entering],
        returned_codewords: vec![returned],
        interventions: BTreeSet::from([format!("workbench-demo-intervention/{event}")]),
        receiver_consequences: BTreeSet::from([format!("workbench-demo-consequence/{event}")]),
    }
}

fn parse_rat(text: &str) -> Result<Rat, WorkbenchError> {
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
    use super::*;
    use tempfile::tempdir;

    fn command(runtime: &mut WorkbenchRuntime, command: AthenaCommand) -> Vec<WorkbenchEvent> {
        runtime.execute(WorkbenchCommand::Athena(command))
    }

    #[test]
    fn named_session_conducts_commits_snapshots_remounts_diffuses_and_exports() {
        let temporary = tempdir().expect("temporary");
        let snapshot = temporary.path().join("alpha.snapshot.json");
        let export = temporary.path().join("alpha.safetensors");
        let mut runtime = WorkbenchRuntime::new();

        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::DemoOpen {
                    session: "alpha".to_owned(),
                }
            )[0]
            .level,
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
                receiver: 7,
            },
        );
        assert_eq!(conduct[0].level, EventLevel::Consequence);
        let committed = command(
            &mut runtime,
            AthenaCommand::Return {
                session: "alpha".to_owned(),
                occurrence: 100,
                boundary: 200,
                real: "1".to_owned(),
                imaginary: "1/2".to_owned(),
                storage: "1".to_owned(),
            },
        );
        assert!(committed[0].summary.contains("generation 1"));
        assert_eq!(
            command(
                &mut runtime,
                AthenaCommand::DiffuseDemo {
                    session: "alpha".to_owned(),
                    occurrence: 200,
                    interval: "1".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Consequence
        );
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
        command(
            &mut runtime,
            AthenaCommand::DemoOpen {
                session: "alpha".to_owned(),
            },
        );
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
                    boundary: 200,
                    real: "not-rational".to_owned(),
                    imaginary: "0".to_owned(),
                    storage: "1".to_owned(),
                }
            )[0]
            .level,
            EventLevel::Obstruction
        );
    }
}
