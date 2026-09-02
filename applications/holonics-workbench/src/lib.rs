//! Holonics Workbench shared command/event application.
//!
//! CLI and Ratatui are two exterior presentations over the same `WorkbenchRuntime`. Product and
//! navigation names in this crate never select native engine conduct.

pub mod cli;
pub mod command;
pub mod event;
pub mod render;

pub use cli::{parse_cli, Cli, WorkbenchInvocation};
pub use command::{
    AthenaCommand, EngineCommand, ErosCommand, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand,
};
pub use event::{EventLevel, WorkbenchEvent};
pub use render::{render_human, render_json_lines};

pub const WORKBENCH_SCHEMA: &str = "org.holonics.workbench.v1";
