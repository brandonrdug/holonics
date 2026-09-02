use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Receiver, TryRecvError};

use crossterm::event::{KeyCode, KeyEvent, KeyEventKind};

use crate::discovery::{
    home_directory, list_directory, workspace_root, WorkbenchResource, WorkbenchResourceKind,
};
use crate::{
    AthenaCommand, EngineCommand, ErosCommand, ExportCodecArgument, SoulkillerCommand,
    WorkbenchCommand, WorkbenchEvent, WorkbenchRuntime, WorkbenchSessionView,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActivePane {
    Resources,
    Actions,
    Events,
    Inspector,
}

#[derive(Clone, Debug)]
pub enum ResourceItem {
    Quickstart,
    Session(WorkbenchSessionView),
    CurrentDirectory(PathBuf),
    Entry(WorkbenchResource),
}

impl ResourceItem {
    pub fn label(&self) -> String {
        match self {
            Self::Quickstart => "◆ Guided start".to_owned(),
            Self::Session(session) => format!(
                "● {} · generation {}{}",
                session.name,
                session.generation,
                if session.has_boundary {
                    " · live boundary"
                } else {
                    ""
                }
            ),
            Self::CurrentDirectory(path) => format!("▣ {}", path.display()),
            Self::Entry(resource) => {
                let marker = match resource.kind {
                    WorkbenchResourceKind::Directory => "▸",
                    WorkbenchResourceKind::ModelConfiguration => "C",
                    WorkbenchResourceKind::ShardedWeightIndex => "S",
                    WorkbenchResourceKind::Onnx => "O",
                    WorkbenchResourceKind::CirculationSnapshot => "A",
                    WorkbenchResourceKind::MorphologyPackage => "P",
                };
                format!("{marker} {}", resource.label)
            }
        }
    }

    pub fn detail(&self) -> String {
        match self {
            Self::Quickstart => "A complete bounded Athena lifecycle with no required parameters. It opens source-neutral demo morphology, derives the first valid ingress and receiver, conducts generation 0, commits an explicit bounded return, then conducts generation 1.".to_owned(),
            Self::Session(session) => format!(
                "Session: {}\nGeneration: {}\nOrigin: {}\nIngress choices: {}\nReceivers: {}\nCurrent boundary: {}\nActual successors: {}",
                session.name,
                session.generation,
                if session.bounded_demo { "bounded demo" } else { "remounted morphology" },
                session.ingress.len(),
                session.receivers.len(),
                if session.has_boundary { "yes" } else { "no" },
                session.actual_successors.len()
            ),
            Self::CurrentDirectory(path) => format!(
                "Current resource directory\n{}\n\nChoose Eros operations from Actions. Enter a directory below without typing its path.",
                path.display()
            ),
            Self::Entry(resource) => format!(
                "Kind: {:?}\nPath: {}\n\nActions are derived from this resource kind.",
                resource.kind,
                resource.path.display()
            ),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ActionSpec {
    pub label: String,
    pub description: String,
    action: Action,
}

#[derive(Clone, Debug)]
enum Action {
    Command(WorkbenchCommand),
    Navigate(PathBuf),
    ReturnForm {
        session: String,
        occurrence: String,
        boundary: String,
        real: String,
        imaginary: String,
        storage: String,
    },
}

#[derive(Debug)]
struct FormField {
    label: &'static str,
    value: String,
    fresh: bool,
}

#[derive(Debug)]
struct ReturnForm {
    session: String,
    fields: Vec<FormField>,
    selected: usize,
}

#[derive(Debug)]
pub struct WorkbenchTui {
    runtime: WorkbenchRuntime,
    events: Vec<WorkbenchEvent>,
    workspace: PathBuf,
    directory: PathBuf,
    resources: Vec<ResourceItem>,
    actions: Vec<ActionSpec>,
    active: ActivePane,
    selected_resource: usize,
    selected_action: usize,
    selected_event: Option<usize>,
    should_quit: bool,
    status: String,
    pending: Option<Receiver<(WorkbenchRuntime, Vec<WorkbenchEvent>)>>,
    return_form: Option<ReturnForm>,
}

impl Default for WorkbenchTui {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkbenchTui {
    pub fn new() -> Self {
        let directory = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        Self::at(directory)
    }

    pub fn at(directory: PathBuf) -> Self {
        let workspace = workspace_root(&directory);
        let mut app = Self {
            runtime: WorkbenchRuntime::new(),
            events: Vec::new(),
            workspace,
            directory,
            resources: Vec::new(),
            actions: Vec::new(),
            active: ActivePane::Resources,
            selected_resource: 0,
            selected_action: 0,
            selected_event: None,
            should_quit: false,
            status: "Select a resource, then choose one valid action".to_owned(),
            pending: None,
            return_form: None,
        };
        app.refresh_resources();
        app
    }

    pub fn events(&self) -> &[WorkbenchEvent] {
        &self.events
    }

    pub fn sessions(&self) -> Vec<&str> {
        self.runtime.session_names()
    }

    pub fn resources(&self) -> &[ResourceItem] {
        &self.resources
    }

    pub fn actions(&self) -> &[ActionSpec] {
        &self.actions
    }

    pub fn directory(&self) -> &Path {
        &self.directory
    }

    pub fn active(&self) -> ActivePane {
        self.active
    }

    pub fn selected_resource(&self) -> usize {
        self.selected_resource
    }

    pub fn selected_action(&self) -> usize {
        self.selected_action
    }

    pub fn selected_event(&self) -> Option<usize> {
        self.selected_event
    }

    pub fn selected_payload(&self) -> Option<String> {
        self.selected_event
            .and_then(|at| self.events.get(at))
            .and_then(|event| event.payload.as_ref())
            .and_then(|payload| serde_json::to_string_pretty(payload).ok())
    }

    pub fn selected_detail(&self) -> String {
        if let Some(form) = &self.return_form {
            let fields = form
                .fields
                .iter()
                .enumerate()
                .map(|(at, field)| {
                    format!(
                        "{} {:<20} {}",
                        if at == form.selected { "▶" } else { " " },
                        field.label,
                        field.value
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            return format!(
                "Returned interaction for {}\n\n{}\n\nExact fractions are accepted. Type to replace a suggested value. Enter advances/submits; Esc cancels.",
                form.session, fields
            );
        }
        if matches!(self.active, ActivePane::Events | ActivePane::Inspector) {
            if let Some(payload) = self.selected_payload() {
                return payload;
            }
        }
        if self.active == ActivePane::Actions {
            if let Some(action) = self.actions.get(self.selected_action) {
                return format!("{}\n\n{}", action.label, action.description);
            }
        }
        self.resources
            .get(self.selected_resource)
            .map(ResourceItem::detail)
            .unwrap_or_else(|| "No selectable resource.".to_owned())
    }

    pub fn should_quit(&self) -> bool {
        self.should_quit
    }

    pub fn busy(&self) -> bool {
        self.pending.is_some()
    }

    pub fn status(&self) -> &str {
        &self.status
    }

    pub fn execute_command(&mut self, command: WorkbenchCommand) -> Vec<WorkbenchEvent> {
        if self.busy() {
            return Vec::new();
        }
        let returned = self.runtime.execute(command);
        self.absorb_returned(&returned);
        returned
    }

    pub fn begin_command(&mut self, command: WorkbenchCommand) {
        if self.busy() {
            self.status = "The current operation must return before another can begin".to_owned();
            return;
        }
        let mut runtime = std::mem::take(&mut self.runtime);
        let (sender, receiver) = mpsc::channel();
        std::thread::spawn(move || {
            let returned = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                runtime.execute(command)
            }))
            .unwrap_or_else(|_| {
                vec![runtime.obstruction_with_code(
                    "workbench/operation",
                    "operation-panic",
                    "the operation panicked; the owned runtime was recovered without beginning another mutation",
                )]
            });
            let _ = sender.send((runtime, returned));
        });
        self.pending = Some(receiver);
        self.status =
            "Operation is running; navigation and inspection remain responsive".to_owned();
    }

    pub fn poll_operation(&mut self) {
        let Some(receiver) = self.pending.as_ref() else {
            return;
        };
        match receiver.try_recv() {
            Ok((runtime, returned)) => {
                self.runtime = runtime;
                self.pending = None;
                self.absorb_returned(&returned);
            }
            Err(TryRecvError::Empty) => {}
            Err(TryRecvError::Disconnected) => {
                self.pending = None;
                let event = self.runtime.obstruction(
                    "workbench/operation",
                    "the operation worker departed without returning its runtime owner",
                );
                self.events.push(event);
                self.selected_event = self.events.len().checked_sub(1);
                self.status = "Operation worker departed without a return".to_owned();
                self.refresh_resources();
            }
        }
    }

    pub fn execute_selected_action(&mut self) -> Vec<WorkbenchEvent> {
        let Some(action) = self.actions.get(self.selected_action).cloned() else {
            return Vec::new();
        };
        match action.action {
            Action::Navigate(path) => {
                self.navigate(path);
                Vec::new()
            }
            Action::Command(command) => self.execute_command(command),
            Action::ReturnForm { .. } => {
                self.open_return_form(action.action);
                Vec::new()
            }
        }
    }

    pub fn begin_selected_action(&mut self) {
        let Some(action) = self.actions.get(self.selected_action).cloned() else {
            return;
        };
        match action.action {
            Action::Navigate(path) => self.navigate(path),
            Action::Command(command) => self.begin_command(command),
            form @ Action::ReturnForm { .. } => self.open_return_form(form),
        }
    }

    pub fn handle_key(&mut self, key: KeyEvent) {
        if key.kind != KeyEventKind::Press {
            return;
        }
        if self.return_form.is_some() {
            self.handle_form_key(key);
            return;
        }
        if self.busy()
            && matches!(
                key.code,
                KeyCode::Char('q' | 'w' | 'h' | 'r' | 'd') | KeyCode::Backspace | KeyCode::Enter
            )
        {
            self.status =
                "Operation is running; inspect its prior events while it returns".to_owned();
            return;
        }
        match key.code {
            KeyCode::Char('q') => self.should_quit = true,
            KeyCode::Char('w') => self.navigate(self.workspace.clone()),
            KeyCode::Char('h') => {
                if let Some(home) = home_directory() {
                    self.navigate(home);
                }
            }
            KeyCode::Char('r') => self.refresh_resources(),
            KeyCode::Char('d') => {
                self.begin_command(WorkbenchCommand::Demo);
            }
            KeyCode::Backspace => {
                if let Some(parent) = self.directory.parent() {
                    self.navigate(parent.to_path_buf());
                }
            }
            KeyCode::Tab | KeyCode::Right => self.next_pane(),
            KeyCode::BackTab | KeyCode::Left => self.previous_pane(),
            KeyCode::Up => self.move_selection(-1),
            KeyCode::Down => self.move_selection(1),
            KeyCode::Enter => self.enter(),
            _ => {}
        }
    }

    fn enter(&mut self) {
        match self.active {
            ActivePane::Resources => {
                if let Some(ResourceItem::Entry(WorkbenchResource {
                    kind: WorkbenchResourceKind::Directory,
                    path,
                    ..
                })) = self.resources.get(self.selected_resource)
                {
                    self.navigate(path.clone());
                } else {
                    self.active = ActivePane::Actions;
                }
            }
            ActivePane::Actions => {
                self.begin_selected_action();
            }
            ActivePane::Events => self.active = ActivePane::Inspector,
            ActivePane::Inspector => self.active = ActivePane::Resources,
        }
    }

    fn next_pane(&mut self) {
        self.active = match self.active {
            ActivePane::Resources => ActivePane::Actions,
            ActivePane::Actions => ActivePane::Events,
            ActivePane::Events => ActivePane::Inspector,
            ActivePane::Inspector => ActivePane::Resources,
        };
    }

    fn previous_pane(&mut self) {
        self.active = match self.active {
            ActivePane::Resources => ActivePane::Inspector,
            ActivePane::Actions => ActivePane::Resources,
            ActivePane::Events => ActivePane::Actions,
            ActivePane::Inspector => ActivePane::Events,
        };
    }

    fn move_selection(&mut self, direction: isize) {
        match self.active {
            ActivePane::Resources => {
                self.selected_resource =
                    shifted(self.selected_resource, direction, self.resources.len());
                self.selected_action = 0;
                self.refresh_actions();
            }
            ActivePane::Actions => {
                self.selected_action = shifted(self.selected_action, direction, self.actions.len());
            }
            ActivePane::Events | ActivePane::Inspector => {
                if !self.events.is_empty() {
                    let current = self.selected_event.unwrap_or(self.events.len() - 1);
                    self.selected_event = Some(shifted(current, direction, self.events.len()));
                }
            }
        }
    }

    fn navigate(&mut self, path: PathBuf) {
        if !path.is_dir() {
            self.status = format!("{} is not a directory", path.display());
            return;
        }
        self.directory = path;
        self.selected_resource = 0;
        self.selected_action = 0;
        self.active = ActivePane::Resources;
        self.refresh_resources();
    }

    fn refresh_resources(&mut self) {
        let mut resources = vec![ResourceItem::Quickstart];
        resources.extend(
            self.runtime
                .session_views()
                .into_iter()
                .map(ResourceItem::Session),
        );
        resources.push(ResourceItem::CurrentDirectory(self.directory.clone()));
        match list_directory(&self.directory) {
            Ok(entries) => resources.extend(entries.into_iter().map(ResourceItem::Entry)),
            Err(error) => {
                let event = self
                    .runtime
                    .obstruction("workbench/resources", error.to_string());
                self.events.push(event);
                self.selected_event = self.events.len().checked_sub(1);
                self.status = error.to_string();
            }
        }
        self.resources = resources;
        self.selected_resource = self
            .selected_resource
            .min(self.resources.len().saturating_sub(1));
        self.refresh_actions();
    }

    fn absorb_returned(&mut self, returned: &[WorkbenchEvent]) {
        self.events.extend(returned.iter().cloned());
        self.selected_event = self.events.len().checked_sub(1);
        self.status = returned
            .last()
            .map(|event| event.summary.clone())
            .unwrap_or_else(|| "operation returned no event".to_owned());
        self.refresh_resources();
    }

    fn refresh_actions(&mut self) {
        self.actions = self
            .resources
            .get(self.selected_resource)
            .cloned()
            .map(|resource| self.actions_for(resource))
            .unwrap_or_default();
        self.selected_action = self
            .selected_action
            .min(self.actions.len().saturating_sub(1));
    }

    fn actions_for(&self, resource: ResourceItem) -> Vec<ActionSpec> {
        match resource {
            ResourceItem::Quickstart => vec![
                command_action(
                    "Run complete Athena demo",
                    "No parameters. Open, derive valid ingress and receiver, conduct, commit a bounded returned interaction, and conduct the changed generation.",
                    WorkbenchCommand::Demo,
                ),
                command_action(
                    "Inspect hardware",
                    "Read the live CPU and CUDA apparatus chart.",
                    WorkbenchCommand::Status,
                ),
                command_action(
                    "Discover workspace resources",
                    "Find supported model charts, snapshots, packages, and ONNX files without typing paths.",
                    WorkbenchCommand::Discover {
                        root: Some(self.workspace.clone()),
                    },
                ),
            ],
            ResourceItem::Session(session) => self.session_actions(&session),
            ResourceItem::CurrentDirectory(path) => directory_actions(path, false),
            ResourceItem::Entry(resource) => match resource.kind {
                WorkbenchResourceKind::Directory => directory_actions(resource.path, true),
                WorkbenchResourceKind::ModelConfiguration
                | WorkbenchResourceKind::ShardedWeightIndex
                | WorkbenchResourceKind::Onnx => vec![command_action(
                    "Inspect with Soulkiller",
                    "Classify and retain the selected foreign chart without executing the model.",
                    WorkbenchCommand::Soulkiller(SoulkillerCommand::Inspect {
                        path: resource.path,
                    }),
                )],
                WorkbenchResourceKind::CirculationSnapshot => {
                    let session = self.runtime.next_session_name("remounted");
                    let onnx = adjacent_output(&resource.path, "onnx");
                    let safetensors = adjacent_output(&resource.path, "safetensors");
                    vec![
                        command_action(
                            "Open as Athena session",
                            "Remount the selected snapshot under an automatically available session name.",
                            WorkbenchCommand::Athena(AthenaCommand::Open {
                                session,
                                snapshot: resource.path.clone(),
                            }),
                        ),
                        command_action(
                            "Inspect package anatomy",
                            "Read the package carried by the selected snapshot.",
                            WorkbenchCommand::Engine(EngineCommand::Package {
                                path: resource.path.clone(),
                            }),
                        ),
                        command_action(
                            "Export adjacent ONNX",
                            &format!("Write {}", onnx.display()),
                            WorkbenchCommand::Engine(EngineCommand::Export {
                                package: resource.path.clone(),
                                codec: ExportCodecArgument::Onnx,
                                path: onnx,
                            }),
                        ),
                        command_action(
                            "Export adjacent Safetensors",
                            &format!("Write {}", safetensors.display()),
                            WorkbenchCommand::Engine(EngineCommand::Export {
                                package: resource.path.clone(),
                                codec: ExportCodecArgument::Safetensors,
                                path: safetensors,
                            }),
                        ),
                    ]
                }
                WorkbenchResourceKind::MorphologyPackage => {
                    let onnx = adjacent_output(&resource.path, "onnx");
                    let safetensors = adjacent_output(&resource.path, "safetensors");
                    vec![
                        command_action(
                            "Inspect package anatomy",
                            "Read lineage, anatomy, receiver, and reconstruction testimony.",
                            WorkbenchCommand::Engine(EngineCommand::Package {
                                path: resource.path.clone(),
                            }),
                        ),
                        command_action(
                            "Export adjacent ONNX",
                            &format!("Write {}", onnx.display()),
                            WorkbenchCommand::Engine(EngineCommand::Export {
                                package: resource.path.clone(),
                                codec: ExportCodecArgument::Onnx,
                                path: onnx,
                            }),
                        ),
                        command_action(
                            "Export adjacent Safetensors",
                            &format!("Write {}", safetensors.display()),
                            WorkbenchCommand::Engine(EngineCommand::Export {
                                package: resource.path,
                                codec: ExportCodecArgument::Safetensors,
                                path: safetensors,
                            }),
                        ),
                    ]
                }
            },
        }
    }

    fn session_actions(&self, session: &WorkbenchSessionView) -> Vec<ActionSpec> {
        let name = &session.name;
        let mut actions = vec![command_action(
            "Inspect morphology",
            "Show current generation, anatomy, receivers, ingress choices, and open obligations.",
            WorkbenchCommand::Athena(AthenaCommand::Inspect {
                session: name.clone(),
            }),
        )];
        if !session.has_boundary {
            for (ingress_index, ingress) in session.ingress.iter().enumerate() {
                for receiver in &session.receivers {
                    actions.push(command_action(
                        format!(
                            "Conduct ingress {} → receiver {}",
                            ingress_index + 1,
                            receiver
                        ),
                        format!(
                            "spool {}\nthread {}\noccurrence {}\nreceiver {}",
                            ingress.spool, ingress.thread, ingress.occurrence, receiver
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
        } else {
            for successor in &session.actual_successors {
                actions.push(command_action(
                    format!("Continue actual successor {}", successor.index + 1),
                    format!(
                        "spool {}\nthread {}\noccurrence {}\nreceiver {}",
                        successor.spool, successor.thread, successor.occurrence, successor.receiver
                    ),
                    WorkbenchCommand::Athena(AthenaCommand::Continue {
                        session: name.clone(),
                        successor: successor.index,
                    }),
                ));
            }
            if let Ok(command) = self.runtime.recommended_demo_return_command(name) {
                if let WorkbenchCommand::Athena(AthenaCommand::Return {
                    occurrence,
                    boundary,
                    real,
                    imaginary,
                    storage,
                    ..
                }) = &command
                {
                    actions.push(ActionSpec {
                        label: "Edit exact returned interaction".to_owned(),
                        description: "Open a typed form prefilled from the bounded return aperture; exact values remain visible and editable.".to_owned(),
                        action: Action::ReturnForm {
                            session: name.clone(),
                            occurrence: occurrence.to_string(),
                            boundary: boundary.to_string(),
                            real: real.clone(),
                            imaginary: imaginary.clone(),
                            storage: storage.clone(),
                        },
                    });
                }
                actions.push(command_action(
                    "Commit bounded demo return",
                    "Use the bounded demo's separated return aperture and an explicit exact current. This remains labeled demo material.",
                    command,
                ));
            } else {
                actions.push(ActionSpec {
                    label: "Enter exact returned interaction".to_owned(),
                    description: "The application cannot invent a world return for remounted morphology. Supply the exterior occurrence, boundary, exact current, and storage through a typed form.".to_owned(),
                    action: Action::ReturnForm {
                        session: name.clone(),
                        occurrence: String::new(),
                        boundary: String::new(),
                        real: "0".to_owned(),
                        imaginary: "0".to_owned(),
                        storage: "0".to_owned(),
                    },
                });
            }
            actions.push(command_action(
                "Decline current boundary",
                "Consume the boundary without changing morphology.",
                WorkbenchCommand::Athena(AthenaCommand::Decline {
                    session: name.clone(),
                }),
            ));
        }
        actions.push(command_action(
            "Run unit-law diffusion demo",
            "Apply declared unit capacity and conductance to the first native spool for interval 1.",
            WorkbenchCommand::Athena(AthenaCommand::DiffuseDemo {
                session: name.clone(),
                occurrence: 10_000u64.saturating_add(session.generation),
                interval: "1".to_owned(),
            }),
        ));
        if let Ok(path) = self.runtime.suggested_artifact_path(name, "snapshot.json") {
            actions.push(command_action(
                "Save snapshot",
                &format!(
                    "Write the next non-overwriting snapshot to {}",
                    path.display()
                ),
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
            if let Ok(path) = self.runtime.suggested_artifact_path(name, suffix) {
                actions.push(command_action(
                    label,
                    &format!(
                        "Write the next non-overwriting exact export to {}",
                        path.display()
                    ),
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

    fn open_return_form(&mut self, action: Action) {
        let Action::ReturnForm {
            session,
            occurrence,
            boundary,
            real,
            imaginary,
            storage,
        } = action
        else {
            return;
        };
        self.return_form = Some(ReturnForm {
            session,
            fields: vec![
                form_field("returned occurrence", occurrence),
                form_field("world boundary", boundary),
                form_field("current real", real),
                form_field("current imaginary", imaginary),
                form_field("storage", storage),
            ],
            selected: 0,
        });
        self.active = ActivePane::Inspector;
        self.status =
            "Edit exact return values; Enter advances and submits the final field".to_owned();
    }

    fn handle_form_key(&mut self, key: KeyEvent) {
        match key.code {
            KeyCode::Esc => {
                self.return_form = None;
                self.status = "Returned interaction form canceled".to_owned();
            }
            KeyCode::Tab | KeyCode::Down => {
                let form = self.return_form.as_mut().expect("form checked");
                form.selected = shifted(form.selected, 1, form.fields.len());
            }
            KeyCode::BackTab | KeyCode::Up => {
                let form = self.return_form.as_mut().expect("form checked");
                form.selected = shifted(form.selected, -1, form.fields.len());
            }
            KeyCode::Backspace => {
                let form = self.return_form.as_mut().expect("form checked");
                let field = &mut form.fields[form.selected];
                field.fresh = false;
                field.value.pop();
            }
            KeyCode::Char(character) => {
                let form = self.return_form.as_mut().expect("form checked");
                let field = &mut form.fields[form.selected];
                if field.fresh {
                    field.value.clear();
                    field.fresh = false;
                }
                field.value.push(character);
            }
            KeyCode::Enter => {
                let submit = self
                    .return_form
                    .as_ref()
                    .is_some_and(|form| form.selected + 1 == form.fields.len());
                if submit {
                    self.submit_return_form();
                } else {
                    let form = self.return_form.as_mut().expect("form checked");
                    form.selected = shifted(form.selected, 1, form.fields.len());
                }
            }
            _ => {}
        }
    }

    fn submit_return_form(&mut self) {
        let Some(form) = self.return_form.take() else {
            return;
        };
        let occurrence = form.fields[0].value.parse::<u64>();
        let boundary = form.fields[1].value.parse::<u64>();
        let (Ok(occurrence), Ok(boundary)) = (occurrence, boundary) else {
            let event = self.runtime.obstruction_with_code(
                "tui/return-form",
                "invalid-form",
                "returned occurrence and world boundary must be unsigned integers",
            );
            self.events.push(event);
            self.selected_event = self.events.len().checked_sub(1);
            self.status = "Return form contains an invalid occurrence or boundary".to_owned();
            return;
        };
        self.begin_command(WorkbenchCommand::Athena(AthenaCommand::Return {
            session: form.session,
            occurrence,
            boundary,
            real: form.fields[2].value.clone(),
            imaginary: form.fields[3].value.clone(),
            storage: form.fields[4].value.clone(),
        }));
    }
}

fn form_field(label: &'static str, value: String) -> FormField {
    FormField {
        label,
        value,
        fresh: true,
    }
}

fn directory_actions(path: PathBuf, include_open: bool) -> Vec<ActionSpec> {
    let mut actions = Vec::new();
    if include_open {
        actions.push(ActionSpec {
            label: "Open folder".to_owned(),
            description: "Browse this folder without typing its path.".to_owned(),
            action: Action::Navigate(path.clone()),
        });
    }
    actions.extend([
        command_action(
            "Build Eros atlas",
            "Automatically choose the dominant Rust, Lean, or Markdown material extension.",
            WorkbenchCommand::Eros(ErosCommand::Atlas {
                directory: path.clone(),
                extension: "auto".to_owned(),
                octet_budget: 3_000_000,
            }),
        ),
        command_action(
            "Open Eros material mouth",
            "Automatically choose material type and return three bounded recovery scales.",
            WorkbenchCommand::Eros(ErosCommand::Mouth {
                directory: path.clone(),
                extension: "auto".to_owned(),
                radius: 3,
                scales: 3,
                octet_budget: 3_000_000,
            }),
        ),
        command_action(
            "Discover supported resources here",
            "Return model charts, snapshots, packages, and ONNX files under this folder.",
            WorkbenchCommand::Discover { root: Some(path) },
        ),
    ]);
    actions
}

fn command_action(
    label: impl Into<String>,
    description: impl Into<String>,
    command: WorkbenchCommand,
) -> ActionSpec {
    ActionSpec {
        label: label.into(),
        description: description.into(),
        action: Action::Command(command),
    }
}

fn adjacent_output(source: &Path, extension: &str) -> PathBuf {
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("morphology");
    let directory = source.parent().unwrap_or_else(|| Path::new("."));
    let first = directory.join(format!("{stem}.export.{extension}"));
    if !first.exists() {
        return first;
    }
    (2u64..)
        .map(|ordinal| directory.join(format!("{stem}.export-{ordinal}.{extension}")))
        .find(|path| !path.exists())
        .expect("the filesystem cannot exhaust u64 export names")
}

fn shifted(current: usize, direction: isize, extent: usize) -> usize {
    if extent == 0 {
        return 0;
    }
    if direction.is_negative() {
        current.saturating_sub(direction.unsigned_abs())
    } else {
        current
            .saturating_add(direction as usize)
            .min(extent.saturating_sub(1))
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::tempdir;

    use super::*;

    #[test]
    fn guided_demo_and_direct_runtime_return_the_same_events() {
        let direct = WorkbenchRuntime::new().execute(WorkbenchCommand::Demo);
        let temporary = tempdir().expect("temporary");
        let mut tui = WorkbenchTui::at(temporary.path().to_path_buf());
        let returned = tui.execute_command(WorkbenchCommand::Demo);
        assert_eq!(returned, direct);
        assert_eq!(tui.sessions(), vec!["alpha"]);
        assert!(returned.len() >= 5);
    }

    #[test]
    fn browser_and_context_actions_require_no_path_typing_or_placeholders() {
        let temporary = tempdir().expect("temporary");
        fs::create_dir(temporary.path().join("models")).expect("models");
        fs::write(temporary.path().join("config.json"), b"{}").expect("config");
        let mut tui = WorkbenchTui::at(temporary.path().to_path_buf());
        assert!(tui
            .resources()
            .iter()
            .any(|resource| resource.label().contains("config.json")));
        assert!(tui
            .actions()
            .iter()
            .all(|action| !action.label.contains('<') && !action.description.contains('<')));
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('d'),
            crossterm::event::KeyModifiers::NONE,
        ));
        for _ in 0..2_000 {
            tui.poll_operation();
            if !tui.busy() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        assert!(!tui.busy());
        assert_eq!(tui.sessions(), vec!["alpha"]);
    }

    #[test]
    fn live_boundary_exposes_each_actual_successor_and_an_editable_exact_return_form() {
        let temporary = tempdir().expect("temporary");
        let mut tui = WorkbenchTui::at(temporary.path().to_path_buf());
        tui.execute_command(WorkbenchCommand::Demo);
        tui.selected_resource = 1;
        tui.refresh_actions();
        assert_eq!(
            tui.actions()
                .iter()
                .filter(|action| action.label.starts_with("Continue actual successor"))
                .count(),
            2
        );
        tui.selected_action = tui
            .actions()
            .iter()
            .position(|action| action.label == "Edit exact returned interaction")
            .expect("return form action");
        tui.execute_selected_action();
        let detail = tui.selected_detail();
        assert!(detail.contains("returned occurrence"));
        assert!(detail.contains("current imaginary"));
        tui.handle_key(KeyEvent::new(
            KeyCode::Esc,
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui.return_form.is_none());
    }
}
