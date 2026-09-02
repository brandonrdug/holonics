use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::WORKBENCH_SCHEMA;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EventLevel {
    Information,
    Consequence,
    Obstruction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkbenchEvent {
    pub schema: String,
    pub sequence: u64,
    pub level: EventLevel,
    pub code: Option<String>,
    pub subject: String,
    pub summary: String,
    pub payload: Option<Value>,
}

impl WorkbenchEvent {
    pub fn new(
        sequence: u64,
        level: EventLevel,
        subject: impl Into<String>,
        summary: impl Into<String>,
        payload: Option<Value>,
    ) -> Self {
        Self {
            schema: WORKBENCH_SCHEMA.to_owned(),
            sequence,
            level,
            code: None,
            subject: subject.into(),
            summary: summary.into(),
            payload,
        }
    }

    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }
}
