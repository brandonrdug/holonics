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

