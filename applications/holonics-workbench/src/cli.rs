use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Parser, Subcommand, ValueEnum};

use crate::{DiagnosticCommand, HnaCommand, SoulkillerCommand, WorkbenchCommand};

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
    /// Stream mathematical requests through a caller-constructed native HNN session.
    MathematicalSession {
        /// JSONL input path, or `-` for standard input.
        #[arg(long, default_value = "-")]
        input: PathBuf,
    },
    /// Stream JSONL wave emissions through a completed packet-1 model or saved wave session.
    WaveSession {
        /// Completed packet-1 directory, or a saved wave session when resuming.
        source: PathBuf,
        /// Resume the positional source as a saved wave session artifact.
        #[arg(long)]
        resume: bool,
        /// Treat the source as an applied-wave seed specification.
        #[arg(long, conflicts_with = "resume")]
        seed: bool,
        /// JSONL input path, or `-` for standard input.
        #[arg(long, default_value = "-")]
        input: PathBuf,
        /// Destination wave session checkpoint; it must not already exist.
        #[arg(long)]
        checkpoint: PathBuf,
    },
    /// Continue a coupled wave through its native source and projected symbol receivers.
    CoupledWaveSession {
        source:PathBuf,
        #[arg(long)] resume:bool,
        #[arg(long,default_value="-")] input:PathBuf,
        #[arg(long)] checkpoint:PathBuf,
        #[arg(long,conflicts_with="resume")] member:Option<usize>,
        #[arg(long,value_parser=["direct","unit-real-sum"],conflicts_with="resume")] receiver:Option<String>,
    },
    /// Stream field sections through an operative native field session.
    FieldSession {
        /// FieldSessionSpec JSON, or a saved field checkpoint when resuming.
        #[arg(long = "source", required_unless_present = "resume", conflicts_with = "resume")]
        source: Option<PathBuf>,
        /// Resume an existing field checkpoint.
        #[arg(long, required_unless_present = "source", conflicts_with = "source")]
        resume: Option<PathBuf>,
        /// JSONL field request input, or `-` for standard input.
        #[arg(long, default_value = "-")]
        input: PathBuf,
        /// Destination field checkpoint path.
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
            HnaCli::MathematicalSession { input } => Self::MathematicalSession { input },
            HnaCli::WaveSession {
                source,
                resume,
                seed,
                input,
                checkpoint,
            } => Self::WaveSession {
                source,
                resume,
                seed,
                input,
                checkpoint,
            },
            HnaCli::CoupledWaveSession{source,resume,input,checkpoint,member,receiver}=>Self::CoupledWaveSession{source,resume,input,checkpoint,member,receiver},
            HnaCli::FieldSession { source, resume, input, checkpoint } => Self::FieldSession {
                source: source.or(resume.clone()).expect("clap requires source or resume"),
                resume: resume.is_some(),
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
pub enum DiagnosticCli {
    Status,
    Capabilities,
    Soulkiller {
        #[command(subcommand)]
        command: SoulkillerCli,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum SoulkillerCli {
    Inspect { path: PathBuf },
    Config { path: PathBuf },
    Index { path: PathBuf },
    Onnx { path: PathBuf },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum OutputFormat {
    #[default]
    Human,
    Json,
    Jsonl,
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

impl From<DiagnosticCli> for DiagnosticCommand {
    fn from(command: DiagnosticCli) -> Self {
        match command {
            DiagnosticCli::Status => Self::Status,
            DiagnosticCli::Capabilities => Self::Capabilities,
            DiagnosticCli::Soulkiller { command } => Self::Soulkiller(command.into()),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_session_selects_one_source_and_keeps_its_checkpoint() {
        let invocation=parse_cli(["holonics","hna","field-session","--source","field.json","--checkpoint","next.session"]).unwrap();
        assert!(matches!(invocation.command,Some(WorkbenchCommand::Hna(HnaCommand::FieldSession{resume:false,..}))));
        let invocation=parse_cli(["holonics","hna","field-session","--resume","old.session","--checkpoint","next.session"]).unwrap();
        assert!(matches!(invocation.command,Some(WorkbenchCommand::Hna(HnaCommand::FieldSession{resume:true,..}))));
        assert!(parse_cli(["holonics","hna","field-session","--checkpoint","next.session"]).is_err());
        assert!(parse_cli(["holonics","hna","field-session","--source","field.json","--resume","old.session","--checkpoint","next.session"]).is_err());
    }

    #[test]
    fn nested_diagnostic_commands_parse() {
        let diagnostic = parse_cli(["holonics", "diagnostic", "status"]).expect("diagnostic parse");
        assert_eq!(
            diagnostic.command,
            Some(WorkbenchCommand::Diagnostic(DiagnosticCommand::Status))
        );
    }

    #[test]
    fn command_wire_round_trips_and_malformed_input_refuses() {
        let command = WorkbenchCommand::Diagnostic(DiagnosticCommand::Soulkiller(
            SoulkillerCommand::Inspect { path: PathBuf::from("model") },
        ));
        let wire = serde_json::to_vec(&command).expect("wire");
        assert_eq!(
            serde_json::from_slice::<WorkbenchCommand>(&wire).expect("round trip"),
            command
        );
        assert!(parse_cli(["holonics", "diagnostic", "not-a-command"]).is_err());
    }

    #[test]
    fn hna_session_parses_checkpoint_and_mode_constraints() {
        let material = parse_cli([
            "holonics",
            "hna",
            "session",
            "model.hna",
            "--resume",
            "--checkpoint",
            "next.hna",
            "--input-material",
            "inputs.safetensors",
        ])
        .unwrap();
        assert!(
            matches!(material.command,Some(WorkbenchCommand::Hna(HnaCommand::Session {input_material,..}))
            if input_material==vec![PathBuf::from("inputs.safetensors")])
        );
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
        let earlier: HnaCommand =
            serde_json::from_str(r#"{"action":"wave-control","spec":"wave.json"}"#).unwrap();
        assert!(matches!(
            earlier,
            HnaCommand::WaveControl {
                resume: false,
                cycles: None,
                checkpoint: None,
                ..
            }
        ));
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
        assert!(parse_cli(["holonics", "hna", "wave-control", "saved.hna", "--resume"]).is_err());
    }

    #[test]
    fn mathematical_session_parses_jsonl_input_without_checkpointing() {
        let invocation = parse_cli(["holonics", "hna", "mathematical-session", "--input", "requests.jsonl"]).unwrap();
        assert!(matches!(invocation.command, Some(WorkbenchCommand::Hna(HnaCommand::MathematicalSession { ref input })) if input == &PathBuf::from("requests.jsonl")));
        assert!(parse_cli(["holonics", "hna", "mathematical-session", "--checkpoint", "saved"]).is_err());
    }

    #[test]
    fn wave_session_parses_packet_one_source_and_resume_input() {
        let fresh = parse_cli([
            "holonics",
            "hna",
            "wave-session",
            "packet-one",
            "--input",
            "events.jsonl",
            "--checkpoint",
            "saved.wave",
        ])
        .expect("wave session parse");
        assert!(matches!(
            fresh.command,
            Some(WorkbenchCommand::Hna(HnaCommand::WaveSession {
                ref source, resume: false, seed: false, ref input, ref checkpoint
            })) if source == &PathBuf::from("packet-one")
                && input == &PathBuf::from("events.jsonl")
                && checkpoint == &PathBuf::from("saved.wave")
        ));
        let resumed = parse_cli([
            "holonics",
            "hna",
            "wave-session",
            "saved.wave",
            "--resume",
            "--checkpoint",
            "next.wave",
        ])
        .expect("wave session resume parse");
        assert!(matches!(
            resumed.command,
            Some(WorkbenchCommand::Hna(HnaCommand::WaveSession {
                ref source, resume: true, seed: false, ref input, ref checkpoint
            })) if source == &PathBuf::from("saved.wave")
                && input == &PathBuf::from("-")
                && checkpoint == &PathBuf::from("next.wave")
        ));
        let seeded = parse_cli([
            "holonics", "hna", "wave-session", "seed.json", "--seed", "--checkpoint", "saved.wave",
        ]).expect("seeded wave session parse");
        assert!(matches!(seeded.command, Some(WorkbenchCommand::Hna(HnaCommand::WaveSession { seed: true, resume: false, .. }))));
        assert!(parse_cli([
            "holonics", "hna", "wave-session", "seed.json", "--seed", "--resume", "--checkpoint", "saved.wave",
        ]).is_err());
    }
    #[test]
    fn coupled_wave_session_preserves_configuration_and_resume_authority(){
        let fresh=parse_cli(["holonics","hna","coupled-wave-session","model","--member","2","--receiver","unit-real-sum","--checkpoint","saved.session"]).unwrap();
        assert!(matches!(fresh.command,Some(WorkbenchCommand::Hna(HnaCommand::CoupledWaveSession{member:Some(2),receiver:Some(ref receiver),resume:false,..})) if receiver=="unit-real-sum"));
        assert!(parse_cli(["holonics","hna","coupled-wave-session","saved.session","--resume","--member","2","--checkpoint","next.session"]).is_err());
        assert!(parse_cli(["holonics","hna","coupled-wave-session","model","--receiver","unknown","--checkpoint","saved.session"]).is_err());
    }

}
