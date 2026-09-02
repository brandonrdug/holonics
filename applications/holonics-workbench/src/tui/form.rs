use std::path::PathBuf;

use crate::{
    AthenaCommand, EngineCommand, ErosCommand, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand,
};

#[derive(Clone, Debug)]
pub(crate) enum FormKind {
    AthenaOpen,
    AthenaReturn { session: String },
    ErosAtlas,
    ErosMouth,
    SoulkillerInspect,
    EnginePackage,
    EngineExport,
}

#[derive(Clone, Debug)]
pub(crate) struct FormField {
    pub label: &'static str,
    pub value: String,
    pub hint: &'static str,
    pub fresh: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct CommandForm {
    pub title: String,
    pub kind: FormKind,
    pub fields: Vec<FormField>,
    pub selected: usize,
}

impl CommandForm {
    pub fn new(title: String, kind: FormKind, fields: Vec<FormField>) -> Self {
        Self {
            title,
            kind,
            fields,
            selected: 0,
        }
    }

    pub fn hints(&self) -> String {
        self.fields
            .iter()
            .map(|field| format!("{}: {}", field.label, field.hint))
            .collect::<Vec<_>>()
            .join(" · ")
    }

    pub fn render(&self) -> String {
        let mut lines = vec![self.title.clone(), String::new()];
        for (at, field) in self.fields.iter().enumerate() {
            lines.push(format!(
                "{} {:<22} {}",
                if at == self.selected { "▶" } else { " " },
                field.label,
                if field.value.is_empty() {
                    "_"
                } else {
                    &field.value
                }
            ));
            lines.push(format!("  {:<22} {}", "", field.hint));
        }
        lines.extend([
            String::new(),
            "Enter advances and submits the final field. Tab moves between fields. Esc cancels."
                .to_owned(),
        ]);
        lines.join("\n")
    }

    pub fn command(&self) -> Result<WorkbenchCommand, String> {
        let value = |at: usize| self.fields[at].value.trim().to_owned();
        let unsigned = |at: usize, name: &str| {
            value(at)
                .parse::<u64>()
                .map_err(|_| format!("{name} needs to be an unsigned integer"))
        };
        let usize_value = |at: usize, name: &str| {
            value(at)
                .parse::<usize>()
                .map_err(|_| format!("{name} needs to be a nonnegative integer"))
        };
        match &self.kind {
            FormKind::AthenaOpen => {
                if value(0).is_empty() || value(1).is_empty() {
                    return Err("Session and snapshot path are required".to_owned());
                }
                Ok(WorkbenchCommand::Athena(AthenaCommand::Open {
                    session: value(0),
                    snapshot: PathBuf::from(value(1)),
                }))
            }
            FormKind::AthenaReturn { session } => {
                Ok(WorkbenchCommand::Athena(AthenaCommand::Return {
                    session: session.clone(),
                    occurrence: unsigned(0, "Returned occurrence")?,
                    boundary: unsigned(1, "World boundary")?,
                    real: value(2),
                    imaginary: value(3),
                    storage: value(4),
                }))
            }
            FormKind::ErosAtlas => Ok(WorkbenchCommand::Eros(ErosCommand::Atlas {
                directory: PathBuf::from(value(0)),
                extension: value(1),
                octet_budget: usize_value(2, "Octet budget")?,
            })),
            FormKind::ErosMouth => Ok(WorkbenchCommand::Eros(ErosCommand::Mouth {
                directory: PathBuf::from(value(0)),
                extension: value(1),
                radius: usize_value(2, "Radius")?,
                scales: usize_value(3, "Scales")?,
                octet_budget: usize_value(4, "Octet budget")?,
            })),
            FormKind::SoulkillerInspect => {
                if value(0).is_empty() {
                    return Err("Chart path is required".to_owned());
                }
                Ok(WorkbenchCommand::Soulkiller(SoulkillerCommand::Inspect {
                    path: PathBuf::from(value(0)),
                }))
            }
            FormKind::EnginePackage => {
                if value(0).is_empty() {
                    return Err("Package path is required".to_owned());
                }
                Ok(WorkbenchCommand::Engine(EngineCommand::Package {
                    path: PathBuf::from(value(0)),
                }))
            }
            FormKind::EngineExport => {
                if value(0).is_empty() || value(2).is_empty() {
                    return Err("Package and output paths are required".to_owned());
                }
                let codec = match value(1).to_lowercase().as_str() {
                    "onnx" => ExportCodecArgument::Onnx,
                    "safetensors" => ExportCodecArgument::Safetensors,
                    _ => return Err("Codec needs to be onnx or safetensors".to_owned()),
                };
                Ok(WorkbenchCommand::Engine(EngineCommand::Export {
                    package: PathBuf::from(value(0)),
                    codec,
                    path: PathBuf::from(value(2)),
                }))
            }
        }
    }
}

pub(crate) fn field(
    label: &'static str,
    value: impl Into<String>,
    hint: &'static str,
) -> FormField {
    FormField {
        label,
        value: value.into(),
        hint,
        fresh: false,
    }
}
