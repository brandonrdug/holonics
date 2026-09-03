use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "domain", content = "command", rename_all = "kebab-case")]
pub enum WorkbenchCommand {
    Workspace(WorkspaceCommand),
    Diagnostic(DiagnosticCommand),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum DiagnosticCommand {
    Demo,
    Status,
    Capabilities,
    Athena(AthenaCommand),
    Eros(ErosCommand),
    Soulkiller(SoulkillerCommand),
    Engine(EngineCommand),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum WorkspaceCommand {
    Create {
        root: PathBuf,
        label: String,
    },
    Inspect {
        root: PathBuf,
    },
    LiftGemmaReceipt {
        root: PathBuf,
        receipt: PathBuf,
        receiver: u64,
    },
    ImportSnapshot {
        root: PathBuf,
        snapshot: PathBuf,
    },
    DefineExperiment {
        root: PathBuf,
        name: String,
        ingress: usize,
        receiver: Option<u64>,
    },
    Conduct {
        root: PathBuf,
        experiment: String,
    },
    Continue {
        root: PathBuf,
        successor: usize,
    },
    StageReturn {
        root: PathBuf,
        occurrence: u64,
        admitted: bool,
        diagnostic: String,
    },
    Commit {
        root: PathBuf,
    },
    Decline {
        root: PathBuf,
    },
    Evaluate {
        root: PathBuf,
        experiment: String,
    },
    Export {
        root: PathBuf,
        codec: ExportCodecArgument,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum AthenaCommand {
    DemoOpen {
        session: String,
    },
    Open {
        session: String,
        snapshot: PathBuf,
    },
    Inspect {
        session: String,
    },
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
        admitted: bool,
        diagnostic: String,
    },
    Decline {
        session: String,
    },
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
        codec: ExportCodecArgument,
        path: PathBuf,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum ErosCommand {
    Mouth {
        directory: PathBuf,
        extension: String,
        radius: usize,
        scales: usize,
        octet_budget: usize,
    },
    Atlas {
        directory: PathBuf,
        extension: String,
        octet_budget: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum SoulkillerCommand {
    Inspect { path: PathBuf },
    Config { path: PathBuf },
    Index { path: PathBuf },
    Onnx { path: PathBuf },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case")]
pub enum EngineCommand {
    Package {
        path: PathBuf,
    },
    Export {
        package: PathBuf,
        codec: ExportCodecArgument,
        path: PathBuf,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExportCodecArgument {
    Onnx,
    Safetensors,
}
