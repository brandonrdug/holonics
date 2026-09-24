use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "domain", content = "command", rename_all = "kebab-case")]
pub enum WorkbenchCommand {
    Hna(HnaCommand),
    Diagnostic(DiagnosticCommand),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case", deny_unknown_fields)]
pub enum HnaCommand {
    Run {
        request: PathBuf,
    },
    Inspect {
        rest: PathBuf,
    },
    Infer {
        model: PathBuf,
        text: String,
    },
    Train {
        model: PathBuf,
        sequence: PathBuf,
        learning_shift: u32,
        series_terms: u32,
    },
    Session {
        source: PathBuf,
        resume: bool,
        base_override: Option<PathBuf>,
        #[serde(default)]
        input_material: Vec<PathBuf>,
        class: Option<usize>,
        input: PathBuf,
        checkpoint: PathBuf,
        learning_shift: u32,
        series_terms: u32,
    },
    NativeSession {
        source: PathBuf,
        resume: bool,
        input: PathBuf,
        checkpoint: PathBuf,
    },
    MathematicalSession {
        input: PathBuf,
    },
    WaveSession {
        source: PathBuf,
        resume: bool,
        #[serde(default)]
        seed: bool,
        input: PathBuf,
        checkpoint: PathBuf,
    },
    CoupledWaveSession {
        source:PathBuf,resume:bool,input:PathBuf,checkpoint:PathBuf,
        #[serde(default)] member:Option<usize>,
        #[serde(default)] receiver:Option<String>,
    },
    FieldSession {
        source: PathBuf,
        resume: bool,
        input: PathBuf,
        checkpoint: PathBuf,
    },
    WaveControl {
        #[serde(alias = "spec")]
        source: PathBuf,
        #[serde(default)]
        resume: bool,
        cycles: Option<usize>,
        checkpoint: Option<PathBuf>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum DiagnosticCommand {
    Status,
    Capabilities,
    Soulkiller(SoulkillerCommand),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum SoulkillerCommand {
    Inspect { path: PathBuf },
    Config { path: PathBuf },
    Index { path: PathBuf },
    Onnx { path: PathBuf },
}

