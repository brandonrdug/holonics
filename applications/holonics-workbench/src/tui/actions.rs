use std::path::PathBuf;

use crate::{
    AthenaCommand, ExportCodecArgument, WorkbenchCommand, WorkbenchRuntime, WorkbenchSessionView,
};

use super::app::{Action, ActionSpec, WorkbenchMode};
use super::form::{field, CommandForm, FormField, FormKind};

pub(crate) fn for_mode(
    mode: WorkbenchMode,
    runtime: &WorkbenchRuntime,
    session: Option<&WorkbenchSessionView>,
) -> Vec<ActionSpec> {
    match mode {
        WorkbenchMode::Athena => athena(runtime, session),
        WorkbenchMode::Eros => eros(),
        WorkbenchMode::Soulkiller => soulkiller(),
        WorkbenchMode::Engine => engine(),
    }
}

fn athena(runtime: &WorkbenchRuntime, session: Option<&WorkbenchSessionView>) -> Vec<ActionSpec> {
    let Some(session) = session else {
        return vec![
            command_action(
                "NEXT",
                "Run bounded alpha cycle",
                "Open source-neutral morphology, conduct generation 0, commit one bounded return, and conduct generation 1.",
                WorkbenchCommand::Demo,
            ),
            form_action(
                "MOUNT",
                "Open rested snapshot",
                FormKind::AthenaOpen,
                vec![
                    field("session", "remounted", "local session handle"),
                    field("snapshot path", "", "native circulation snapshot"),
                ],
            ),
        ];
    };
    let name = session.name.clone();
    let mut actions = vec![command_action(
        "INSPECT",
        "Inspect morphology",
        "Return generation, anatomy, receivers, ingress sections, and open obligations.",
        WorkbenchCommand::Athena(AthenaCommand::Inspect {
            session: name.clone(),
        }),
    )];
    if session.has_boundary {
        for successor in &session.actual_successors {
            actions.push(command_action(
                "NEXT",
                format!("Continue successor {}", successor.index + 1),
                format!(
                    "{} / {} / occurrence {} / receiver {}",
                    successor.spool, successor.thread, successor.occurrence, successor.receiver
                ),
                WorkbenchCommand::Athena(AthenaCommand::Continue {
                    session: name.clone(),
                    successor: successor.index,
                }),
            ));
        }
        let suggested = runtime.recommended_demo_return_command(&name).ok();
        let (occurrence, boundary, real, imaginary, storage) = match suggested.as_ref() {
            Some(WorkbenchCommand::Athena(AthenaCommand::Return {
                occurrence,
                boundary,
                real,
                imaginary,
                storage,
                ..
            })) => (
                occurrence.to_string(),
                boundary.to_string(),
                real.clone(),
                imaginary.clone(),
                storage.clone(),
            ),
            _ => (
                String::new(),
                String::new(),
                "0".to_owned(),
                "0".to_owned(),
                "0".to_owned(),
            ),
        };
        actions.push(form_action(
            "RETURN",
            "Enter exact world return",
            FormKind::AthenaReturn {
                session: name.clone(),
            },
            vec![
                field("returned occurrence", occurrence, "genuinely later event"),
                field("world boundary", boundary, "exterior boundary address"),
                field("current real", real, "integer or exact fraction"),
                field("current imaginary", imaginary, "integer or exact fraction"),
                field("storage", storage, "integer or exact fraction"),
            ],
        ));
        if let Some(command) = suggested {
            actions.push(command_action(
                "RETURN",
                "Commit bounded demo return",
                "Use only the bounded demo aperture and explicit exact demo current.",
                command,
            ));
        }
        actions.push(command_action(
            "RETURN",
            "Decline boundary",
            "Consume the current boundary without changing morphology.",
            WorkbenchCommand::Athena(AthenaCommand::Decline {
                session: name.clone(),
            }),
        ));
    } else {
        for (ingress_index, ingress) in session.ingress.iter().enumerate() {
            for receiver in &session.receivers {
                actions.push(command_action(
                    "NEXT",
                    format!(
                        "Conduct ingress {} → receiver {}",
                        ingress_index + 1,
                        receiver
                    ),
                    format!(
                        "{} / {} / occurrence {}",
                        ingress.spool, ingress.thread, ingress.occurrence
                    ),
                    WorkbenchCommand::Athena(AthenaCommand::Conduct {
                        session: name.clone(),
                        spool: ingress.spool.clone(),
                        thread: ingress.thread.clone(),
                        occurrence: ingress.occurrence,
                        receiver: *receiver,
                    }),
                ));
            }
        }
    }
    actions.push(command_action(
        "PROBE",
        "Closed unit-law diffusion probe",
        "One source-free exact step over unit capacity/conductance. Session state remains unchanged.",
        WorkbenchCommand::Athena(AthenaCommand::DiffuseDemo {
            session: name.clone(),
            occurrence: 10_000u64.saturating_add(session.generation),
            interval: "1".to_owned(),
        }),
    ));
    if let Ok(path) = runtime.suggested_artifact_path(&name, "snapshot.json") {
        actions.push(command_action(
            "PERSIST",
            "Save snapshot",
            format!("Write without overwrite: {}", path.display()),
            WorkbenchCommand::Athena(AthenaCommand::Snapshot {
                session: name.clone(),
                path,
            }),
        ));
    }
    for (label, codec, suffix) in [
        ("Export ONNX", ExportCodecArgument::Onnx, "onnx"),
        (
            "Export Safetensors",
            ExportCodecArgument::Safetensors,
            "safetensors",
        ),
    ] {
        if let Ok(path) = runtime.suggested_artifact_path(&name, suffix) {
            actions.push(command_action(
                "PERSIST",
                label,
                format!("Write without overwrite: {}", path.display()),
                WorkbenchCommand::Athena(AthenaCommand::Export {
                    session: name.clone(),
                    codec,
                    path,
                }),
            ));
        }
    }
    actions
}

fn eros() -> Vec<ActionSpec> {
    let current = std::env::current_dir()
        .unwrap_or_else(|_| PathBuf::from("."))
        .display()
        .to_string();
    vec![
        form_action(
            "MATERIAL",
            "Build incidence atlas",
            FormKind::ErosAtlas,
            vec![
                field(
                    "source root",
                    current.clone(),
                    "directory of complete files",
                ),
                field("extension", "auto", "auto, rs, lean, or md"),
                field("octet budget", "3000000", "complete-file aperture"),
            ],
        ),
        form_action(
            "MATERIAL",
            "Open exposure mouth",
            FormKind::ErosMouth,
            vec![
                field("source root", current, "directory of complete files"),
                field("extension", "auto", "auto, rs, lean, or md"),
                field("radius", "3", "candidate neighborhood"),
                field("scales", "3", "maximum recovery rungs"),
                field("octet budget", "3000000", "complete-file aperture"),
            ],
        ),
    ]
}

fn soulkiller() -> Vec<ActionSpec> {
    vec![form_action(
        "FOREIGN CHART",
        "Inspect model chart",
        FormKind::SoulkillerInspect,
        vec![field(
            "chart path",
            "",
            "config.json, *.safetensors.index.json, or *.onnx",
        )],
    )]
}

fn engine() -> Vec<ActionSpec> {
    vec![
        command_action(
            "APPARATUS",
            "Inspect hardware",
            "Return CPU parallelism and the live CUDA apparatus chart.",
            WorkbenchCommand::Status,
        ),
        command_action(
            "APPARATUS",
            "Inspect capabilities",
            "Return implemented Workbench surfaces and exact open fibres.",
            WorkbenchCommand::Capabilities,
        ),
        form_action(
            "MORPHOLOGY",
            "Inspect package",
            FormKind::EnginePackage,
            vec![field(
                "package path",
                "",
                "native package or circulation snapshot",
            )],
        ),
        form_action(
            "MORPHOLOGY",
            "Export package",
            FormKind::EngineExport,
            vec![
                field("package path", "", "native package or circulation snapshot"),
                field("codec", "onnx", "onnx or safetensors"),
                field("output path", "", "explicit non-directory destination"),
            ],
        ),
    ]
}

fn command_action(
    group: &'static str,
    label: impl Into<String>,
    description: impl Into<String>,
    command: WorkbenchCommand,
) -> ActionSpec {
    ActionSpec {
        group,
        label: label.into(),
        description: description.into(),
        action: Action::Command(command),
    }
}

fn form_action(
    group: &'static str,
    label: impl Into<String>,
    kind: FormKind,
    fields: Vec<FormField>,
) -> ActionSpec {
    let label = label.into();
    let form = CommandForm::new(label.clone(), kind, fields);
    ActionSpec {
        group,
        description: form.hints(),
        action: Action::Form(form),
        label,
    }
}
