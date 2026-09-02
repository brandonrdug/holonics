//! Holonics Workbench shared command/event application.
//!
//! CLI and Ratatui are two exterior presentations over the same `WorkbenchRuntime`. Product and
//! navigation names in this crate never select native engine conduct.

mod adapters;
pub mod cli;
pub mod command;
pub mod discovery;
pub mod event;
pub mod protocol;
pub mod render;
pub mod runtime;
mod store;
pub mod tui;

pub use cli::{parse_cli, Cli, OutputFormat, WorkbenchInvocation};
pub use command::{
    AthenaCommand, EngineCommand, ErosCommand, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand,
};
pub use discovery::{WorkbenchDiscovery, WorkbenchResource, WorkbenchResourceKind};
pub use event::{EventLevel, WorkbenchEvent};
pub use protocol::{
    WorkbenchDisposition, WorkbenchRequest, WorkbenchResponse, WORKBENCH_REQUEST_SCHEMA,
    WORKBENCH_RESPONSE_SCHEMA,
};
pub use render::{render_human, render_json, render_json_lines};
pub use runtime::{
    WorkbenchError, WorkbenchIngressView, WorkbenchRuntime, WorkbenchSessionView,
    WorkbenchSuccessorView,
};
pub use tui::{run_tui, WorkbenchTui};

pub const WORKBENCH_SCHEMA: &str = "org.holonics.workbench.event.v2";
