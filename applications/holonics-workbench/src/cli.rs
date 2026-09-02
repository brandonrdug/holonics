use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Args, Parser, Subcommand, ValueEnum};

use crate::{
    AthenaCommand, EngineCommand, ErosCommand, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand,
};

#[derive(Clone, Debug, Parser)]
#[command(name = "holonics", version, about = "Holonics operator workbench")]
pub struct Cli {
    /// Emit newline-delimited structured events.
    #[arg(long, global = true)]
    pub json: bool,
    #[command(subcommand)]
    pub command: Option<CliCommand>,
}

#[derive(Clone, Debug, Subcommand)]
pub enum CliCommand {
    /// Open the interactive Ratatui workbench.
    Tui,
    Status,
    Capabilities,
    Athena {
        #[command(subcommand)]
        command: AthenaCli,
    },
    Eros {
        #[command(subcommand)]
        command: ErosCli,
    },
    Soulkiller {
        #[command(subcommand)]
        command: SoulkillerCli,
    },
    Engine {
        #[command(subcommand)]
        command: EngineCli,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum AthenaCli {
    DemoOpen(SessionName),
    Open {
        session: String,
        snapshot: PathBuf,
    },
    Inspect(SessionName),
    Conduct {
        session: String,
        spool: String,
        thread: String,
        occurrence: u64,
        receiver: u64,
    },
    Continue {
        session: String,
        successor: usize,
    },
    Return {
        session: String,
        occurrence: u64,
        boundary: u64,
        #[arg(allow_hyphen_values = true)]
        real: String,
        #[arg(allow_hyphen_values = true)]
        imaginary: String,
        #[arg(allow_hyphen_values = true)]
        storage: String,
    },
    Decline(SessionName),
    DiffuseDemo {
        session: String,
        occurrence: u64,
        interval: String,
    },
    Snapshot {
        session: String,
        path: PathBuf,
    },
    Export {
        session: String,
        codec: CodecCli,
        path: PathBuf,
    },
}

#[derive(Clone, Debug, Args)]
pub struct SessionName {
    pub session: String,
}

#[derive(Clone, Debug, Subcommand)]
pub enum ErosCli {
    Mouth {
        directory: PathBuf,
        #[arg(long, default_value = "md")]
        extension: String,
        #[arg(long, default_value_t = 3)]
        radius: usize,
        #[arg(long, default_value_t = 3)]
        scales: usize,
        #[arg(long, default_value_t = 3_000_000)]
        octet_budget: usize,
    },
    Atlas {
        directory: PathBuf,
        #[arg(long, default_value = "md")]
        extension: String,
        #[arg(long, default_value_t = 3_000_000)]
        octet_budget: usize,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum SoulkillerCli {
    Config { path: PathBuf },
    Index { path: PathBuf },
    Onnx { path: PathBuf },
}

#[derive(Clone, Debug, Subcommand)]
pub enum EngineCli {
    Package {
        path: PathBuf,
    },
    Export {
        package: PathBuf,
        codec: CodecCli,
        path: PathBuf,
    },
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum CodecCli {
    Onnx,
    Safetensors,
}

impl From<CodecCli> for ExportCodecArgument {
    fn from(codec: CodecCli) -> Self {
        match codec {
            CodecCli::Onnx => Self::Onnx,
            CodecCli::Safetensors => Self::Safetensors,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkbenchInvocation {
    pub json: bool,
    pub tui: bool,
    pub command: Option<WorkbenchCommand>,
}

impl Cli {
    pub fn invocation(self) -> WorkbenchInvocation {
        let (tui, command) = match self.command {
            None | Some(CliCommand::Tui) => (true, None),
            Some(CliCommand::Status) => (false, Some(WorkbenchCommand::Status)),
            Some(CliCommand::Capabilities) => (false, Some(WorkbenchCommand::Capabilities)),
            Some(CliCommand::Athena { command }) => {
                (false, Some(WorkbenchCommand::Athena(command.into())))
            }
            Some(CliCommand::Eros { command }) => {
                (false, Some(WorkbenchCommand::Eros(command.into())))
            }
            Some(CliCommand::Soulkiller { command }) => {
                (false, Some(WorkbenchCommand::Soulkiller(command.into())))
            }
            Some(CliCommand::Engine { command }) => {
                (false, Some(WorkbenchCommand::Engine(command.into())))
            }
        };
        WorkbenchInvocation {
            json: self.json,
            tui,
            command,
        }
    }
}

pub fn parse_cli<I, T>(arguments: I) -> Result<WorkbenchInvocation, clap::Error>
where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
{
    Cli::try_parse_from(arguments).map(Cli::invocation)
}

impl From<AthenaCli> for AthenaCommand {
    fn from(command: AthenaCli) -> Self {
        match command {
            AthenaCli::DemoOpen(value) => Self::DemoOpen {
                session: value.session,
            },
            AthenaCli::Open { session, snapshot } => Self::Open { session, snapshot },
            AthenaCli::Inspect(value) => Self::Inspect {
                session: value.session,
            },
            AthenaCli::Conduct {
                session,
                spool,
                thread,
                occurrence,
                receiver,
            } => Self::Conduct {
                session,
                spool,
                thread,
                occurrence,
                receiver,
            },
            AthenaCli::Continue { session, successor } => Self::Continue { session, successor },
            AthenaCli::Return {
                session,
                occurrence,
                boundary,
                real,
                imaginary,
                storage,
            } => Self::Return {
                session,
                occurrence,
                boundary,
                real,
                imaginary,
                storage,
            },
            AthenaCli::Decline(value) => Self::Decline {
                session: value.session,
            },
            AthenaCli::DiffuseDemo {
                session,
                occurrence,
                interval,
            } => Self::DiffuseDemo {
                session,
                occurrence,
                interval,
            },
            AthenaCli::Snapshot { session, path } => Self::Snapshot { session, path },
            AthenaCli::Export {
                session,
                codec,
                path,
            } => Self::Export {
                session,
                codec: codec.into(),
                path,
            },
        }
    }
}

impl From<ErosCli> for ErosCommand {
    fn from(command: ErosCli) -> Self {
        match command {
            ErosCli::Mouth {
                directory,
                extension,
                radius,
                scales,
                octet_budget,
            } => Self::Mouth {
                directory,
                extension,
                radius,
                scales,
                octet_budget,
            },
            ErosCli::Atlas {
                directory,
                extension,
                octet_budget,
            } => Self::Atlas {
                directory,
                extension,
                octet_budget,
            },
        }
    }
}

impl From<SoulkillerCli> for SoulkillerCommand {
    fn from(command: SoulkillerCli) -> Self {
        match command {
            SoulkillerCli::Config { path } => Self::Config { path },
            SoulkillerCli::Index { path } => Self::Index { path },
            SoulkillerCli::Onnx { path } => Self::Onnx { path },
        }
    }
}

impl From<EngineCli> for EngineCommand {
    fn from(command: EngineCli) -> Self {
        match command {
            EngineCli::Package { path } => Self::Package { path },
            EngineCli::Export {
                package,
                codec,
                path,
            } => Self::Export {
                package,
                codec: codec.into(),
                path,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_nested_command_parses_to_the_shared_protocol() {
        let parsed = parse_cli([
            "holonics", "athena", "return", "alpha", "100", "200", "3/2", "-1/4", "2",
        ])
        .expect("parse");
        assert_eq!(
            parsed.command,
            Some(WorkbenchCommand::Athena(AthenaCommand::Return {
                session: "alpha".to_owned(),
                occurrence: 100,
                boundary: 200,
                real: "3/2".to_owned(),
                imaginary: "-1/4".to_owned(),
                storage: "2".to_owned(),
            }))
        );
    }

    #[test]
    fn command_wire_round_trips_and_malformed_input_refuses() {
        let command = WorkbenchCommand::Soulkiller(SoulkillerCommand::Config {
            path: PathBuf::from("config.json"),
        });
        let wire = serde_json::to_vec(&command).expect("wire");
        assert_eq!(
            serde_json::from_slice::<WorkbenchCommand>(&wire).expect("round trip"),
            command
        );
        assert!(parse_cli(["holonics", "athena", "not-a-command"]).is_err());
    }
}
