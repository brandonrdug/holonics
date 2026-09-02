use serde::{Deserialize, Serialize};

use crate::{EventLevel, WorkbenchCommand, WorkbenchEvent};

pub const WORKBENCH_REQUEST_SCHEMA: &str = "org.holonics.workbench.request.v3";
pub const WORKBENCH_RESPONSE_SCHEMA: &str = "org.holonics.workbench.response.v3";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkbenchRequest {
    pub schema: String,
    pub command: WorkbenchCommand,
}

impl WorkbenchRequest {
    pub fn new(command: WorkbenchCommand) -> Self {
        Self {
            schema: WORKBENCH_REQUEST_SCHEMA.to_owned(),
            command,
        }
    }

    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let request: Self = serde_json::from_slice(bytes)
            .map_err(|error| format!("invalid Workbench request JSON: {error}"))?;
        if request.schema != WORKBENCH_REQUEST_SCHEMA {
            return Err(format!(
                "request schema {:?} is not {:?}",
                request.schema, WORKBENCH_REQUEST_SCHEMA
            ));
        }
        Ok(request)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WorkbenchDisposition {
    Consequence,
    Obstruction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkbenchResponse {
    pub schema: String,
    pub command: Option<WorkbenchCommand>,
    pub disposition: WorkbenchDisposition,
    pub events: Vec<WorkbenchEvent>,
}

impl WorkbenchResponse {
    pub fn new(command: WorkbenchCommand, events: Vec<WorkbenchEvent>) -> Self {
        Self::from_parts(Some(command), events)
    }

    pub fn input_obstruction(events: Vec<WorkbenchEvent>) -> Self {
        Self::from_parts(None, events)
    }

    fn from_parts(command: Option<WorkbenchCommand>, events: Vec<WorkbenchEvent>) -> Self {
        let disposition = if events
            .iter()
            .any(|event| event.level == EventLevel::Obstruction)
        {
            WorkbenchDisposition::Obstruction
        } else {
            WorkbenchDisposition::Consequence
        };
        Self {
            schema: WORKBENCH_RESPONSE_SCHEMA.to_owned(),
            command,
            disposition,
            events,
        }
    }

    pub fn obstructed(&self) -> bool {
        self.disposition == WorkbenchDisposition::Obstruction
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_and_response_are_one_versioned_io_envelope() {
        let request = WorkbenchRequest::new(WorkbenchCommand::Diagnostic(
            crate::DiagnosticCommand::Status,
        ));
        let wire = serde_json::to_vec(&request).expect("request wire");
        assert_eq!(WorkbenchRequest::read(&wire).expect("request"), request);
        let response = WorkbenchResponse::new(
            WorkbenchCommand::Diagnostic(crate::DiagnosticCommand::Status),
            vec![WorkbenchEvent::new(
                0,
                EventLevel::Consequence,
                "engine/status",
                "returned",
                None,
            )],
        );
        assert!(!response.obstructed());
        assert_eq!(response.schema, WORKBENCH_RESPONSE_SCHEMA);
    }
}
