pub mod engine;
pub mod hna;
pub mod eros;
pub mod soulkiller;
pub mod workspace;

use serde_json::Value;

use crate::EventLevel;

pub struct AdapterReturn {
    pub level: EventLevel,
    pub subject: String,
    pub summary: String,
    pub payload: Option<Value>,
}

impl AdapterReturn {
    pub fn consequence(
        subject: impl Into<String>,
        summary: impl Into<String>,
        payload: Value,
    ) -> Self {
        Self {
            level: EventLevel::Consequence,
            subject: subject.into(),
            summary: summary.into(),
            payload: Some(payload),
        }
    }
}
