//! Holonics Workbench shared command/event application.
//!
//! The high-level CLI composes `holonics-application`; low-level diagnostic commands retain the
//! bounded Workbench event protocol without becoming the model-building interface.

mod adapters;
pub mod cli;
pub mod command;
pub mod event;
pub mod presentation;
pub mod protocol;
pub mod render;
pub mod runtime;
mod session_stream;
mod store;

pub use cli::{parse_cli, Cli, OutputFormat, WorkbenchInvocation};
pub use command::{
    AthenaCommand, DiagnosticCommand, EngineCommand, ErosCommand, ExportCodecArgument, HnaCommand,
    SoulkillerCommand, WorkbenchCommand, WorkspaceCommand,
};
pub use event::{EventLevel, WorkbenchEvent};
pub use protocol::{
    WorkbenchDisposition, WorkbenchRequest, WorkbenchResponse, WORKBENCH_REQUEST_SCHEMA,
    WORKBENCH_RESPONSE_SCHEMA,
};
pub use render::{render_human, render_json, render_json_lines};
pub use runtime::{WorkbenchError, WorkbenchRuntime};
pub use session_stream::{run_hna_session_stream, HnaStreamProcessReceipt};

pub const WORKBENCH_SCHEMA: &str = "org.holonics.workbench.event.v4";
