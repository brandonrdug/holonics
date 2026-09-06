use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Args, Parser, Subcommand, ValueEnum};

use crate::{
    AthenaCommand, DiagnosticCommand, EngineCommand, ErosCommand, ExportCodecArgument, HnaCommand,
    SoulkillerCommand, WorkbenchCommand, WorkspaceCommand,
};

#[derive(Clone, Debug, Parser)]
#[command(
    name = "holonics",
    version,
    about = "Holonic Neural Network runtime, model interoperability and variant workspace"
)]
pub struct Cli {
    /// Select typed human, one-envelope JSON, or event-stream JSONL output.
    #[arg(long, global = true, value_enum, default_value_t = OutputFormat::Human)]
    pub format: OutputFormat,
    #[command(subcommand)]
    pub command: Option<CliCommand>,
}

#[derive(Clone, Debug, Subcommand)]
pub enum CliCommand {
    /// Run the current full native HNA operator or inspect a Soulkiller native rest.
    Hna {
        #[command(subcommand)]
        command: HnaCli,
    },
    /// Create, lift, cultivate, evaluate, and export a persistent morphology variant.
    Workspace {
        #[command(subcommand)]
        command: WorkspaceCli,
    },
    /// Execute one versioned Workbench request from a JSON file or standard input (`-`).
    Run {
        #[arg(default_value = "-")]
        input: String,
    },
    /// Low-level bounded mechanisms and probes; not the model-building interface.
    Diagnostic {
        #[command(subcommand)]
        command: DiagnosticCli,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum HnaCli {
    /// Execute ordered native occurrences from a HnaRunRequest JSON file in one session.
    Run { request: PathBuf },
    /// Inspect the header of a restricted Soulkiller rest without initializing CUDA.
    Inspect { rest: PathBuf },
    /// Emit one native selected face for a text occurrence (not a complete chat response).
    Infer { model: PathBuf, text: String },
    /// Develop one session from cumulative text prefixes in a JSON string array; returns a run receipt, not a checkpoint.
    Train {
        model: PathBuf,
        sequence: PathBuf,
        #[arg(long, default_value_t = 16)]
        learning_shift: u32,
        #[arg(long, default_value_t = 14)]
        series_terms: u32,
    },
    /// Stream JSONL occurrences through a checkpointed native session.
    Session {
        /// Source model or native rest path.
        source: PathBuf,
        /// Resume an existing checkpoint rather than opening a fresh source.
        #[arg(long, conflicts_with = "class")]
        resume: bool,
        /// Optional verified base override used only while resuming.
        #[arg(long = "base", requires = "resume")]
        base_override: Option<PathBuf>,
        /// Additional native input sections; checkpoints retain their explicit dependencies.
        #[arg(long)]
        input_material: Vec<PathBuf>,
        /// Optional retained class used for a fresh session.
        #[arg(long, conflicts_with = "resume")]
        class: Option<usize>,
        /// JSONL input path, or `-` for standard input.
        #[arg(long, default_value = "-")]
        input: PathBuf,
        /// Destination checkpoint path.
        #[arg(long)]
        checkpoint: PathBuf,
        /// Fresh-session aperture; resumed sessions keep their saved native law.
        #[arg(long, default_value_t = 16, conflicts_with = "resume")]
        learning_shift: u32,
        #[arg(long, default_value_t = 14, conflicts_with = "resume")]
        series_terms: u32,
    },
    /// Live native phase session, with a seed or resumed native checkpoint.
    NativeSession {
        /// Native model specification JSON, or a native checkpoint when resuming.
        source: PathBuf,
        /// Resume the positional source as an existing native checkpoint.
        #[arg(long)]
        resume: bool,
        /// JSONL input path, or `-` for standard input.
        #[arg(long, default_value = "-")]
        input: PathBuf,
        /// Destination native checkpoint; it must not already exist.
        #[arg(long)]
        checkpoint: PathBuf,
    },
    /// Run the declared native wave-control adapter from a JSON specification.
    WaveControl {
        /// Wave-control specification JSON, or a native wave checkpoint when resuming.
        source: PathBuf,
        /// Resume the positional source as a native wave checkpoint.
        #[arg(long, requires = "checkpoint")]
        resume: bool,
        /// Optional cycle limit override.
        #[arg(long)]
        cycles: Option<usize>,
        /// Optional destination native wave checkpoint.
        #[arg(long)]
        checkpoint: Option<PathBuf>,
    },
}

impl From<HnaCli> for HnaCommand {
    fn from(command: HnaCli) -> Self {
        match command {
            HnaCli::Run { request } => Self::Run { request },
            HnaCli::Inspect { rest } => Self::Inspect { rest },
            HnaCli::Infer { model, text } => Self::Infer { model, text },
            HnaCli::Train {
                model,
                sequence,
                learning_shift,
                series_terms,
            } => Self::Train {
                model,
                sequence,
                learning_shift,
                series_terms,
            },
            HnaCli::Session {
                source,
                resume,
                base_override,
                input_material,
                class,
                input,
                checkpoint,
                learning_shift,
                series_terms,
            } => Self::Session {
                source,
                resume,
                base_override,
                input_material,
                class,
                input,
                checkpoint,
                learning_shift,
                series_terms,
            },
            HnaCli::NativeSession {
                source,
                resume,
                input,
                checkpoint,
            } => Self::NativeSession {
                source,
                resume,
                input,
                checkpoint,
            },
            HnaCli::WaveControl {
                source,
                resume,
                cycles,
                checkpoint,
            } => Self::WaveControl {
                source,
                resume,
                cycles,
                checkpoint,
            },
        }
    }
}

#[derive(Clone, Debug, Subcommand)]
pub enum WorkspaceCli {
    /// Create an empty workspace at an explicit root; no model is fabricated.
    Create {
        /// Explicit artifact and state root.
        root: PathBuf,
        /// Human-facing variant workspace label.
        label: String,
    },
    /// Inspect the complete manifest and print the absolute current snapshot path.
    Inspect {
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Found the workspace from an existing valid native circulation snapshot.
    ImportSnapshot {
        /// Existing native circulation snapshot.
        snapshot: PathBuf,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Resolve and store one exact native ingress/receiver experiment.
    DefineExperiment {
        /// Stable experiment name used by conduct and evaluate.
        name: String,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
        /// Ordinal of the current morphology's admitted ingress section.
        #[arg(long, default_value_t = 0)]
        ingress: usize,
        /// Receiver override; defaults to the current snapshot receiver.
        #[arg(long)]
        receiver: Option<u64>,
    },
    /// Conduct a stored experiment and persist its complete active boundary.
    Conduct {
        /// Stored experiment name.
        experiment: String,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Continue the active run through one returned actual-successor ordinal.
    Continue {
        /// Ordinal shown in the active boundary's actual-successor population.
        successor: usize,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Report one complete world-face family without authoring native current or storage.
    StageReturn {
        /// Returned exterior occurrence identifier.
        occurrence: u64,
        /// Whether the exterior world admitted every issued grain.
        #[arg(long)]
        admitted: bool,
        /// Exact diagnostic octets, supplied here as UTF-8 command input.
        #[arg(long, default_value = "")]
        diagnostic: String,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Commit the staged candidate and atomically advance the current snapshot.
    Commit {
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Decline the active boundary/candidate without changing the current snapshot.
    Decline {
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Compare current, latest-withdrawn, and replay-restored conduct non-mutatively.
    Evaluate {
        /// Stored experiment name.
        experiment: String,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
    /// Write an exact rested-inference ONNX or Safetensors artifact beneath the root.
    Export {
        /// Exact exterior codec.
        codec: CodecCli,
        /// Workspace root; defaults to the current directory.
        #[arg(long, default_value = ".", value_name = "PATH")]
        root: PathBuf,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum DiagnosticCli {
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
        #[arg(long)]
        admitted: bool,
        #[arg(long, default_value = "")]
        diagnostic: String,
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
        #[arg(default_value = ".")]
        directory: PathBuf,
        #[arg(long, default_value = "auto")]
        extension: String,
        #[arg(long, default_value_t = 3)]
        radius: usize,
        #[arg(long, default_value_t = 3)]
        scales: usize,
        #[arg(long, default_value_t = 3_000_000)]
        octet_budget: usize,
    },
    Atlas {
        #[arg(default_value = ".")]
        directory: PathBuf,
        #[arg(long, default_value = "auto")]
        extension: String,
        #[arg(long, default_value_t = 3_000_000)]
        octet_budget: usize,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum SoulkillerCli {
    Inspect { path: PathBuf },
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

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum OutputFormat {
    #[default]
    Human,
    Json,
    Jsonl,
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
    pub format: OutputFormat,
    pub command: Option<WorkbenchCommand>,
    pub request_input: Option<String>,
}

impl Cli {
    pub fn invocation(self) -> WorkbenchInvocation {
        let (command, request_input) = match self.command {
            None => (None, None),
            Some(CliCommand::Hna { command }) => {
                (Some(WorkbenchCommand::Hna(command.into())), None)
            }
            Some(CliCommand::Run { input }) => (None, Some(input)),
            Some(CliCommand::Workspace { command }) => {
                (Some(WorkbenchCommand::Workspace(command.into())), None)
            }
            Some(CliCommand::Diagnostic { command }) => {
                (Some(WorkbenchCommand::Diagnostic(command.into())), None)
            }
        };
        WorkbenchInvocation {
            format: self.format,
            command,
            request_input,
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

impl From<WorkspaceCli> for WorkspaceCommand {
    fn from(command: WorkspaceCli) -> Self {
        match command {
            WorkspaceCli::Create { root, label } => Self::Create { root, label },
            WorkspaceCli::Inspect { root } => Self::Inspect { root },
            WorkspaceCli::ImportSnapshot { root, snapshot } => {
                Self::ImportSnapshot { root, snapshot }
            }
            WorkspaceCli::DefineExperiment {
                root,
                name,
                ingress,
                receiver,
            } => Self::DefineExperiment {
                root,
                name,
                ingress,
                receiver,
            },
            WorkspaceCli::Conduct { root, experiment } => Self::Conduct { root, experiment },
            WorkspaceCli::Continue { root, successor } => Self::Continue { root, successor },
            WorkspaceCli::StageReturn {
                root,
                occurrence,
                admitted,
                diagnostic,
            } => Self::StageReturn {
                root,
                occurrence,
                admitted,
                diagnostic,
            },
            WorkspaceCli::Commit { root } => Self::Commit { root },
            WorkspaceCli::Decline { root } => Self::Decline { root },
            WorkspaceCli::Evaluate { root, experiment } => Self::Evaluate { root, experiment },
            WorkspaceCli::Export { root, codec } => Self::Export {
                root,
                codec: codec.into(),
            },
        }
    }
}

impl From<DiagnosticCli> for DiagnosticCommand {
    fn from(command: DiagnosticCli) -> Self {
        match command {
            DiagnosticCli::Status => Self::Status,
            DiagnosticCli::Capabilities => Self::Capabilities,
            DiagnosticCli::Athena { command } => Self::Athena(command.into()),
            DiagnosticCli::Eros { command } => Self::Eros(command.into()),
            DiagnosticCli::Soulkiller { command } => Self::Soulkiller(command.into()),
            DiagnosticCli::Engine { command } => Self::Engine(command.into()),
        }
    }
}

impl From<AthenaCli> for AthenaCommand {
    fn from(command: AthenaCli) -> Self {
        match command {
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
                admitted,
                diagnostic,
            } => Self::Return {
                session,
                occurrence,
                admitted,
                diagnostic,
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
            SoulkillerCli::Inspect { path } => Self::Inspect { path },
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
    fn high_level_workspace_and_nested_diagnostic_commands_parse() {
        let workspace = parse_cli([
            "holonics",
            "workspace",
            "stage-return",
            "100",
            "--admitted",
            "--diagnostic",
            "world-admitted",
        ])
        .expect("workspace parse");
        assert!(matches!(
            workspace.command,
            Some(WorkbenchCommand::Workspace(
                WorkspaceCommand::StageReturn { ref root, .. }
            ))
            if root == &PathBuf::from(".")
        ));
        let diagnostic = parse_cli(["holonics", "diagnostic", "status"]).expect("diagnostic parse");
        assert_eq!(
            diagnostic.command,
            Some(WorkbenchCommand::Diagnostic(DiagnosticCommand::Status))
        );
    }

    #[test]
    fn command_wire_round_trips_and_malformed_input_refuses() {
        let command = WorkbenchCommand::Workspace(WorkspaceCommand::Inspect {
            root: PathBuf::from("variant"),
        });
        let wire = serde_json::to_vec(&command).expect("wire");
        assert_eq!(
            serde_json::from_slice::<WorkbenchCommand>(&wire).expect("round trip"),
            command
        );
        assert!(parse_cli(["holonics", "workspace", "not-a-command"]).is_err());
    }

    #[test]
    fn hna_session_parses_checkpoint_and_mode_constraints() {
        let material=parse_cli(["holonics","hna","session","model.hna","--resume",
            "--checkpoint","next.hna","--input-material","inputs.safetensors"]).unwrap();
        assert!(matches!(material.command,Some(WorkbenchCommand::Hna(HnaCommand::Session {input_material,..}))
            if input_material==vec![PathBuf::from("inputs.safetensors")]));
        assert!(parse_cli([
            "holonics",
            "hna",
            "session",
            "saved.hna",
            "--resume",
            "--base",
            "base.rest",
            "--checkpoint",
            "next.hna"
        ])
        .is_ok());
        assert!(parse_cli([
            "holonics",
            "hna",
            "session",
            "saved.hna",
            "--resume",
            "--learning-shift",
            "9",
            "--checkpoint",
            "next.hna"
        ])
        .is_err());
        let invocation = parse_cli([
            "holonics",
            "hna",
            "session",
            "source.rest",
            "--checkpoint",
            "next.hna",
            "--input",
            "events.jsonl",
            "--learning-shift",
            "9",
        ])
        .expect("session parse");
        assert!(matches!(
            invocation.command,
            Some(WorkbenchCommand::Hna(HnaCommand::Session {
                source, resume: false, base_override: None, class: None, input, checkpoint,
                learning_shift: 9, series_terms: 14, ..
            })) if source == PathBuf::from("source.rest")
                && input == PathBuf::from("events.jsonl")
                && checkpoint == PathBuf::from("next.hna")
        ));
        assert!(parse_cli(["holonics", "hna", "session", "source", "--input", "-"]).is_err());
        assert!(parse_cli([
            "holonics",
            "hna",
            "session",
            "source",
            "--checkpoint",
            "next",
            "--base",
            "base"
        ])
        .is_err());
        assert!(parse_cli([
            "holonics",
            "hna",
            "session",
            "source",
            "--checkpoint",
            "next",
            "--resume",
            "--class",
            "1"
        ])
        .is_err());
    }

    #[test]
    fn native_session_and_wave_control_parse_their_positional_specs() {
        let earlier: HnaCommand=serde_json::from_str(r#"{"action":"wave-control","spec":"wave.json"}"#).unwrap();
        assert!(matches!(earlier,HnaCommand::WaveControl {resume:false,cycles:None,checkpoint:None,..}));
        let native = parse_cli([
            "holonics",
            "hna",
            "native-session",
            "seed.json",
            "--checkpoint",
            "next.hna",
        ])
            .expect("native session parse");
        assert!(matches!(
            native.command,
            Some(WorkbenchCommand::Hna(HnaCommand::NativeSession {
                ref source, resume: false, ref input, ref checkpoint
            }))
            if source == &PathBuf::from("seed.json")
                && input == &PathBuf::from("-")
                && checkpoint == &PathBuf::from("next.hna")
        ));
        let native_input = parse_cli([
            "holonics",
            "hna",
            "native-session",
            "seed.json",
            "--input",
            "events.jsonl",
            "--checkpoint",
            "next.hna",
        ])
        .expect("native session input parse");
        assert!(matches!(
            native_input.command,
            Some(WorkbenchCommand::Hna(HnaCommand::NativeSession { ref input, .. }))
            if input == &PathBuf::from("events.jsonl")
        ));
        let resumed = parse_cli([
            "holonics",
            "hna",
            "native-session",
            "saved.hna",
            "--resume",
            "--checkpoint",
            "next.hna",
        ])
        .expect("native session resume parse");
        assert!(matches!(
            resumed.command,
            Some(WorkbenchCommand::Hna(HnaCommand::NativeSession {
                ref source, resume: true, ref checkpoint, ..
            }))
            if source == &PathBuf::from("saved.hna")
                && checkpoint == &PathBuf::from("next.hna")
        ));
        assert!(parse_cli(["holonics", "hna", "native-session", "seed.json"]).is_err());
        let wave = parse_cli(["holonics", "hna", "wave-control", "wave.json"])
            .expect("wave control parse");
        assert!(matches!(
            wave.command,
            Some(WorkbenchCommand::Hna(HnaCommand::WaveControl {
                ref source, resume: false, cycles: None, checkpoint: None
            }))
            if source == &PathBuf::from("wave.json")
        ));
        let resumed = parse_cli([
            "holonics",
            "hna",
            "wave-control",
            "saved.hna",
            "--resume",
            "--cycles",
            "3",
            "--checkpoint",
            "next.hna",
        ])
        .expect("wave control resume parse");
        assert!(matches!(
            resumed.command,
            Some(WorkbenchCommand::Hna(HnaCommand::WaveControl {
                ref source, resume: true, cycles: Some(3), ref checkpoint
            }))
            if source == &PathBuf::from("saved.hna")
                && checkpoint == &Some(PathBuf::from("next.hna"))
        ));
        assert!(parse_cli([
            "holonics",
            "hna",
            "wave-control",
            "saved.hna",
            "--resume"
        ])
        .is_err());
    }
}
