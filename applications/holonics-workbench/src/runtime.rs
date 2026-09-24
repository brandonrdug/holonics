use std::path::PathBuf;

use serde_json::Value;
use thiserror::Error;

use crate::adapters;
use crate::{DiagnosticCommand, EventLevel, WorkbenchCommand, WorkbenchEvent};

#[derive(Debug, Default)]
pub struct WorkbenchRuntime {
    history: Vec<WorkbenchEvent>,
    next_sequence: u64,
}

#[derive(Debug, Error)]
pub enum WorkbenchError {
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

    pub fn execute(&mut self, command: WorkbenchCommand) -> Vec<WorkbenchEvent> {
        let result = match command {
            WorkbenchCommand::Hna(command) => {
                adapters::hna::execute(command).map(|returned| vec![self.adapter(returned)])
            }
            WorkbenchCommand::Diagnostic(command) => self.execute_diagnostic(command),
        };
        let events = match result {
            Ok(events) => events,
            Err(error) => {
                let code = error.code();
                vec![self
                    .event(EventLevel::Obstruction, "workbench", error.to_string(), None)
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
            DiagnosticCommand::Status => Ok(vec![self.adapter(adapters::diagnostic::status())]),
            DiagnosticCommand::Capabilities => {
                Ok(vec![self.adapter(adapters::diagnostic::capabilities())])
            }
            DiagnosticCommand::Soulkiller(command) => {
                adapters::soulkiller::execute(command).map(|returned| vec![self.adapter(returned)])
            }
        }
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
        self.event(returned.level, returned.subject, returned.summary, returned.payload)
    }
}
