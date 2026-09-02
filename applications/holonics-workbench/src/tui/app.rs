use std::sync::mpsc::{self, Receiver, TryRecvError};

use crossterm::event::{KeyCode, KeyEvent, KeyEventKind};

use crate::presentation;
use crate::{WorkbenchCommand, WorkbenchEvent, WorkbenchRuntime, WorkbenchSessionView};

use super::form::CommandForm;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorkbenchMode {
    Athena,
    Eros,
    Soulkiller,
    Engine,
}

impl WorkbenchMode {
    pub const ALL: [Self; 4] = [Self::Athena, Self::Eros, Self::Soulkiller, Self::Engine];

    pub fn label(self) -> &'static str {
        match self {
            Self::Athena => "ATHENA",
            Self::Eros => "EROS",
            Self::Soulkiller => "SOULKILLER",
            Self::Engine => "ENGINE",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActivePane {
    Actions,
    Detail,
    Events,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DetailTab {
    Summary,
    Structure,
    Exact,
}

impl DetailTab {
    pub const ALL: [Self; 3] = [Self::Summary, Self::Structure, Self::Exact];

    pub fn label(self) -> &'static str {
        match self {
            Self::Summary => "Summary",
            Self::Structure => "Structure",
            Self::Exact => "Exact",
        }
    }
}

#[derive(Clone, Debug)]
pub struct ActionSpec {
    pub group: &'static str,
    pub label: String,
    pub description: String,
    pub(crate) action: Action,
}

#[derive(Clone, Debug)]
pub(crate) enum Action {
    Command(WorkbenchCommand),
    Form(CommandForm),
}

#[derive(Debug)]
pub struct WorkbenchTui {
    runtime: WorkbenchRuntime,
    events: Vec<WorkbenchEvent>,
    mode: WorkbenchMode,
    active: ActivePane,
    selected_session: usize,
    actions: Vec<ActionSpec>,
    selected_action: usize,
    selected_event: Option<usize>,
    detail_tab: DetailTab,
    detail_scrolls: [u16; 3],
    detail_max_scrolls: [u16; 3],
    help_scroll: u16,
    help_max_scroll: u16,
    should_quit: bool,
    show_help: bool,
    status: String,
    pending_label: Option<String>,
    pending: Option<Receiver<(WorkbenchRuntime, Vec<WorkbenchEvent>)>>,
    form: Option<CommandForm>,
}

impl Default for WorkbenchTui {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkbenchTui {
    pub fn new() -> Self {
        let mut app = Self {
            runtime: WorkbenchRuntime::new(),
            events: Vec::new(),
            mode: WorkbenchMode::Athena,
            active: ActivePane::Actions,
            selected_session: 0,
            actions: Vec::new(),
            selected_action: 0,
            selected_event: None,
            detail_tab: DetailTab::Summary,
            detail_scrolls: [0; 3],
            detail_max_scrolls: [0; 3],
            help_scroll: 0,
            help_max_scroll: 0,
            should_quit: false,
            show_help: false,
            status: "Run the bounded alpha cycle or open a rested snapshot".to_owned(),
            pending_label: None,
            pending: None,
            form: None,
        };
        app.refresh_actions();
        app
    }

    pub fn events(&self) -> &[WorkbenchEvent] {
        &self.events
    }

    pub fn sessions(&self) -> Vec<&str> {
        self.runtime.session_names()
    }

    pub fn session_views(&self) -> Vec<WorkbenchSessionView> {
        self.runtime.session_views()
    }

    pub fn current_session(&self) -> Option<WorkbenchSessionView> {
        self.runtime
            .session_views()
            .get(self.selected_session)
            .cloned()
    }

    pub fn mode(&self) -> WorkbenchMode {
        self.mode
    }

    pub fn active(&self) -> ActivePane {
        self.active
    }

    pub fn actions(&self) -> &[ActionSpec] {
        &self.actions
    }

    pub fn selected_action(&self) -> usize {
        self.selected_action
    }

    pub fn selected_action_description(&self) -> &str {
        self.actions
            .get(self.selected_action)
            .map(|action| action.description.as_str())
            .unwrap_or("No action is available in the current state.")
    }

    pub fn selected_event(&self) -> Option<usize> {
        self.selected_event
    }

    pub fn detail_tab(&self) -> DetailTab {
        self.detail_tab
    }

    pub fn detail_scroll(&self) -> u16 {
        if self.show_help {
            self.help_scroll
        } else {
            self.detail_scrolls[detail_tab_index(self.detail_tab)]
        }
    }

    pub fn set_detail_max_scroll(&mut self, maximum: u16) {
        if self.show_help {
            self.help_max_scroll = maximum;
            self.help_scroll = self.help_scroll.min(maximum);
        } else {
            let at = detail_tab_index(self.detail_tab);
            self.detail_max_scrolls[at] = maximum;
            self.detail_scrolls[at] = self.detail_scrolls[at].min(maximum);
        }
    }

    pub fn selected_detail(&self) -> String {
        if self.show_help {
            return help_text().to_owned();
        }
        if let Some(form) = &self.form {
            return form.render();
        }
        if let Some(event) = self.current_event() {
            return match self.detail_tab {
                DetailTab::Summary => presentation::summary(event),
                DetailTab::Structure => presentation::structure(event),
                DetailTab::Exact => presentation::exact(event),
            };
        }
        self.current_state_text()
    }

    pub fn detail_line_count(&self) -> usize {
        self.selected_detail().lines().count().max(1)
    }

    pub fn detail_title(&self) -> String {
        if self.show_help {
            return "Help".to_owned();
        }
        if let Some(form) = &self.form {
            return form.title.clone();
        }
        self.current_event()
            .map(|event| format!("{} · #{}", event.subject, event.sequence))
            .unwrap_or_else(|| "Current state".to_owned())
    }

    pub fn lifecycle_line(&self) -> String {
        let Some(session) = self.current_session() else {
            return "MOUNT ○  →  CONDUCT ○  →  EMIT ○  →  WORLD RETURN ○  →  COMMIT ○".to_owned();
        };
        if session.has_boundary {
            format!(
                "MOUNT ●  →  CONDUCT ●  →  EMIT ●  →  WORLD RETURN ◉  →  COMMIT g{}",
                session.generation
            )
        } else {
            format!(
                "MOUNT ●  →  CONDUCT ◉  →  EMIT ○  →  WORLD RETURN ○  →  COMMIT g{}",
                session.generation
            )
        }
    }

    pub fn session_status_line(&self) -> String {
        match self.current_session() {
            Some(session) => format!(
                "{} · generation {} · boundary {} · successors {} · {}",
                session.name,
                session.generation,
                if session.has_boundary {
                    "LIVE"
                } else {
                    "RESTED"
                },
                session.actual_successors.len(),
                if self.busy() { "WORKING" } else { "IDLE" }
            ),
            None => format!(
                "no mounted Athena session · {}",
                if self.busy() { "WORKING" } else { "IDLE" }
            ),
        }
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

    pub fn pending_label(&self) -> Option<&str> {
        self.pending_label.as_deref()
    }

    pub fn execute_command(&mut self, command: WorkbenchCommand) -> Vec<WorkbenchEvent> {
        if self.busy() {
            return Vec::new();
        }
        let returned = self.runtime.execute(command);
        self.absorb_returned(&returned);
        returned
    }

    pub fn begin_command(&mut self, label: String, command: WorkbenchCommand) {
        if self.busy() {
            self.status = "The current operation still owns the runtime".to_owned();
            return;
        }
        let mut runtime = std::mem::take(&mut self.runtime);
        let (sender, receiver) = mpsc::channel();
        std::thread::spawn(move || {
            let returned =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| runtime.execute(command)))
                    .unwrap_or_else(|_| {
                        vec![runtime.obstruction_with_code(
                    "workbench/operation",
                    "operation-panic",
                    "the operation panicked; the runtime owner returned without another mutation",
                )]
                    });
            let _ = sender.send((runtime, returned));
        });
        self.pending = Some(receiver);
        self.pending_label = Some(label.clone());
        self.status = format!("{label} is running; prior receipts remain inspectable");
    }

    pub fn poll_operation(&mut self) {
        let Some(receiver) = self.pending.as_ref() else {
            return;
        };
        match receiver.try_recv() {
            Ok((runtime, returned)) => {
                self.runtime = runtime;
                self.pending = None;
                self.pending_label = None;
                self.absorb_returned(&returned);
            }
            Err(TryRecvError::Empty) => {}
            Err(TryRecvError::Disconnected) => {
                self.pending = None;
                self.pending_label = None;
                let event = self.runtime.obstruction_with_code(
                    "workbench/operation",
                    "operation-owner-lost",
                    "the operation worker departed before returning the runtime owner",
                );
                self.events.push(event);
                self.selected_event = self.events.len().checked_sub(1);
                self.status = "Operation owner was not returned".to_owned();
                self.refresh_actions();
            }
        }
    }

    pub fn execute_selected_action(&mut self) -> Vec<WorkbenchEvent> {
        let Some(action) = self.actions.get(self.selected_action).cloned() else {
            return Vec::new();
        };
        match action.action {
            Action::Command(command) => self.execute_command(command),
            Action::Form(form) => {
                self.open_form(form);
                Vec::new()
            }
        }
    }

    pub fn handle_key(&mut self, key: KeyEvent) {
        if key.kind != KeyEventKind::Press {
            return;
        }
        if self.form.is_some() {
            self.handle_form_key(key);
            return;
        }
        if self.show_help {
            match key.code {
                KeyCode::Char('?') | KeyCode::Esc => self.show_help = false,
                KeyCode::Up => self.scroll_detail(-1),
                KeyCode::Down => self.scroll_detail(1),
                KeyCode::PageUp => self.scroll_detail(-10),
                KeyCode::PageDown => self.scroll_detail(10),
                KeyCode::Home => self.move_to_boundary(false),
                KeyCode::End => self.move_to_boundary(true),
                _ => {}
            }
            return;
        }
        if self.busy() && matches!(key.code, KeyCode::Char('q') | KeyCode::Enter) {
            self.status =
                "The current operation must return before exit or another mutation".to_owned();
            return;
        }
        match key.code {
            KeyCode::Char('q') => self.should_quit = true,
            KeyCode::Char('?') => {
                self.show_help = true;
                self.help_scroll = 0;
            }
            KeyCode::Char('1') => self.set_mode(WorkbenchMode::Athena),
            KeyCode::Char('2') => self.set_mode(WorkbenchMode::Eros),
            KeyCode::Char('3') => self.set_mode(WorkbenchMode::Soulkiller),
            KeyCode::Char('4') => self.set_mode(WorkbenchMode::Engine),
            KeyCode::Char('[') => self.shift_session(-1),
            KeyCode::Char(']') => self.shift_session(1),
            KeyCode::Char('s') if self.active == ActivePane::Detail => {
                self.set_detail_tab(DetailTab::Summary)
            }
            KeyCode::Char('v') if self.active == ActivePane::Detail => {
                self.set_detail_tab(DetailTab::Structure)
            }
            KeyCode::Char('x') if self.active == ActivePane::Detail => {
                self.set_detail_tab(DetailTab::Exact)
            }
            KeyCode::Tab => self.next_pane(),
            KeyCode::BackTab => self.previous_pane(),
            KeyCode::Left if self.active == ActivePane::Detail => self.previous_detail_tab(),
            KeyCode::Right if self.active == ActivePane::Detail => self.next_detail_tab(),
            KeyCode::Up => self.move_selection(-1),
            KeyCode::Down => self.move_selection(1),
            KeyCode::PageUp => self.move_selection(-10),
            KeyCode::PageDown => self.move_selection(10),
            KeyCode::Home => self.move_to_boundary(false),
            KeyCode::End => self.move_to_boundary(true),
            KeyCode::Enter if self.active == ActivePane::Actions => self.begin_selected_action(),
            KeyCode::Enter if self.active == ActivePane::Events => {
                self.active = ActivePane::Detail;
                self.reset_detail_scrolls();
            }
            _ => {}
        }
    }

    fn begin_selected_action(&mut self) {
        let Some(action) = self.actions.get(self.selected_action).cloned() else {
            return;
        };
        match action.action {
            Action::Command(command) => self.begin_command(action.label, command),
            Action::Form(form) => self.open_form(form),
        }
    }

    fn set_mode(&mut self, mode: WorkbenchMode) {
        self.mode = mode;
        self.active = ActivePane::Actions;
        self.selected_action = 0;
        self.reset_detail_scrolls();
        self.refresh_actions();
        self.status = format!("{} operation surface", mode.label());
    }

    fn shift_session(&mut self, direction: isize) {
        let extent = self.runtime.session_views().len();
        self.selected_session = shifted(self.selected_session, direction, extent);
        self.refresh_actions();
        self.reset_detail_scrolls();
    }

    fn next_pane(&mut self) {
        self.active = match self.active {
            ActivePane::Actions => ActivePane::Detail,
            ActivePane::Detail => ActivePane::Events,
            ActivePane::Events => ActivePane::Actions,
        };
    }

    fn previous_pane(&mut self) {
        self.active = match self.active {
            ActivePane::Actions => ActivePane::Events,
            ActivePane::Detail => ActivePane::Actions,
            ActivePane::Events => ActivePane::Detail,
        };
    }

    fn move_selection(&mut self, direction: isize) {
        match self.active {
            ActivePane::Actions => {
                self.selected_action = shifted(self.selected_action, direction, self.actions.len());
            }
            ActivePane::Detail => self.scroll_detail(direction),
            ActivePane::Events => {
                if !self.events.is_empty() {
                    let current = self.selected_event.unwrap_or(self.events.len() - 1);
                    self.selected_event = Some(shifted(current, direction, self.events.len()));
                    self.reset_detail_scrolls();
                }
            }
        }
    }

    fn move_to_boundary(&mut self, end: bool) {
        match self.active {
            ActivePane::Actions => {
                self.selected_action = if end {
                    self.actions.len().saturating_sub(1)
                } else {
                    0
                };
            }
            ActivePane::Detail => {
                let maximum = if self.show_help {
                    self.help_max_scroll
                } else {
                    self.detail_max_scrolls[detail_tab_index(self.detail_tab)]
                };
                self.set_current_detail_scroll(if end { maximum } else { 0 });
            }
            ActivePane::Events => {
                self.selected_event = if self.events.is_empty() {
                    None
                } else if end {
                    Some(self.events.len() - 1)
                } else {
                    Some(0)
                };
                self.reset_detail_scrolls();
            }
        }
    }

    fn scroll_detail(&mut self, direction: isize) {
        let maximum = if self.show_help {
            self.help_max_scroll
        } else {
            self.detail_max_scrolls[detail_tab_index(self.detail_tab)]
        };
        let next = shifted(
            usize::from(self.detail_scroll()),
            direction,
            usize::from(maximum).saturating_add(1),
        );
        self.set_current_detail_scroll(u16::try_from(next).unwrap_or(maximum));
    }

    fn set_detail_tab(&mut self, tab: DetailTab) {
        self.detail_tab = tab;
    }

    fn set_current_detail_scroll(&mut self, value: u16) {
        if self.show_help {
            self.help_scroll = value.min(self.help_max_scroll);
        } else {
            let at = detail_tab_index(self.detail_tab);
            self.detail_scrolls[at] = value.min(self.detail_max_scrolls[at]);
        }
    }

    fn reset_detail_scrolls(&mut self) {
        self.detail_scrolls = [0; 3];
        self.detail_max_scrolls = [0; 3];
    }

    fn next_detail_tab(&mut self) {
        let at = DetailTab::ALL
            .iter()
            .position(|tab| *tab == self.detail_tab)
            .unwrap_or(0);
        self.set_detail_tab(DetailTab::ALL[(at + 1).min(DetailTab::ALL.len() - 1)]);
    }

    fn previous_detail_tab(&mut self) {
        let at = DetailTab::ALL
            .iter()
            .position(|tab| *tab == self.detail_tab)
            .unwrap_or(0);
        self.set_detail_tab(DetailTab::ALL[at.saturating_sub(1)]);
    }

    fn absorb_returned(&mut self, returned: &[WorkbenchEvent]) {
        self.events.extend(returned.iter().cloned());
        self.selected_event = self.events.len().checked_sub(1);
        self.detail_tab = DetailTab::Summary;
        self.reset_detail_scrolls();
        self.status = returned
            .last()
            .map(|event| event.summary.clone())
            .unwrap_or_else(|| "Operation returned no event".to_owned());
        self.selected_session = self
            .selected_session
            .min(self.runtime.session_views().len().saturating_sub(1));
        self.refresh_actions();
    }

    fn refresh_actions(&mut self) {
        let session = self.current_session();
        self.actions = super::actions::for_mode(self.mode, &self.runtime, session.as_ref());
        self.selected_action = self
            .selected_action
            .min(self.actions.len().saturating_sub(1));
    }

    fn open_form(&mut self, mut form: CommandForm) {
        for field in &mut form.fields {
            field.fresh = !field.value.is_empty();
        }
        self.form = Some(form);
        self.active = ActivePane::Detail;
        self.reset_detail_scrolls();
        self.status =
            "Edit fields; Enter advances and submits the last field; Esc cancels".to_owned();
    }

    fn handle_form_key(&mut self, key: KeyEvent) {
        match key.code {
            KeyCode::Esc => {
                self.form = None;
                self.status = "Form canceled without executing an operation".to_owned();
            }
            KeyCode::Tab | KeyCode::Down => self.shift_form_field(1),
            KeyCode::BackTab | KeyCode::Up => self.shift_form_field(-1),
            KeyCode::Backspace => {
                let form = self.form.as_mut().expect("form checked");
                let field = &mut form.fields[form.selected];
                field.fresh = false;
                field.value.pop();
            }
            KeyCode::Char(character) => {
                let form = self.form.as_mut().expect("form checked");
                let field = &mut form.fields[form.selected];
                if field.fresh {
                    field.value.clear();
                    field.fresh = false;
                }
                field.value.push(character);
            }
            KeyCode::Enter => {
                let submit = self
                    .form
                    .as_ref()
                    .is_some_and(|form| form.selected + 1 == form.fields.len());
                if submit {
                    self.submit_form();
                } else {
                    self.shift_form_field(1);
                }
            }
            _ => {}
        }
    }

    fn shift_form_field(&mut self, direction: isize) {
        let form = self.form.as_mut().expect("form checked");
        form.selected = shifted(form.selected, direction, form.fields.len());
    }

    fn submit_form(&mut self) {
        let Some(form) = self.form.take() else {
            return;
        };
        match form.command() {
            Ok(command) => self.begin_command(form.title, command),
            Err(summary) => {
                let event =
                    self.runtime
                        .obstruction_with_code("tui/form", "invalid-form", summary.clone());
                self.events.push(event);
                self.selected_event = self.events.len().checked_sub(1);
                self.status = summary;
            }
        }
    }

    fn current_event(&self) -> Option<&WorkbenchEvent> {
        self.selected_event.and_then(|at| self.events.get(at))
    }

    fn current_state_text(&self) -> String {
        match (self.mode, self.current_session()) {
            (WorkbenchMode::Athena, Some(session)) => format!(
                "ATHENA SESSION\n{}\n\nGeneration            {}\nBoundary              {}\nIngress sections       {}\nReceivers              {}\nActual successors      {}\nOrigin                 {}\n\nChoose a valid action on the right. Returned receipts appear here as typed summaries; raw JSON is confined to the Exact view.",
                session.name,
                session.generation,
                if session.has_boundary { "LIVE" } else { "RESTED" },
                session.ingress.len(),
                session.receivers.len(),
                session.actual_successors.len(),
                if session.bounded_demo { "bounded demo" } else { "remounted morphology" }
            ),
            (WorkbenchMode::Athena, None) => "ATHENA\nNo mounted session. Run the bounded alpha cycle or open a rested snapshot.".to_owned(),
            (WorkbenchMode::Eros, _) => "EROS\nExpose a declared source root through an incidence atlas or codec-recovery mouth. Paths are operation parameters, not standing Workbench navigation.".to_owned(),
            (WorkbenchMode::Soulkiller, _) => "SOULKILLER\nInspect one explicitly selected foreign configuration, Safetensors index, or ONNX chart without executing the foreign realization.".to_owned(),
            (WorkbenchMode::Engine, _) => "HOLONIC ENGINE\nInspect apparatus and native package anatomy or request an exact export.".to_owned(),
        }
    }
}

fn help_text() -> &'static str {
    "WORKBENCH KEYS\n\n1 Athena   2 Eros   3 Soulkiller   4 Engine\n[ / ]      previous / next Athena session\nTab        next pane\nShift-Tab  previous pane\n↑ / ↓      select action/event or scroll receipt\nPage keys  move ten rows\nHome / End first / last row\n← / →      previous / next receipt view\ns           Summary view\nv           Structure view\nx           Exact payload view\nEnter       execute action or open selected event\n?           close this help\nq           quit when no operation owns the runtime\n\nRECEIPT VIEWS\nSummary explains the returned consequence. Structure shows domain relations and exact tables. Exact preserves the complete serialized payload and scrolls independently."
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

fn detail_tab_index(tab: DetailTab) -> usize {
    match tab {
        DetailTab::Summary => 0,
        DetailTab::Structure => 1,
        DetailTab::Exact => 2,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn guided_demo_and_direct_runtime_return_the_same_events() {
        let direct = WorkbenchRuntime::new().execute(WorkbenchCommand::Demo);
        let mut tui = WorkbenchTui::new();
        let returned = tui.execute_command(WorkbenchCommand::Demo);
        assert_eq!(returned, direct);
        assert_eq!(tui.sessions(), vec!["alpha"]);
        assert_eq!(returned.len(), 5);
    }

    #[test]
    fn session_surface_exposes_every_successor_and_no_filesystem_navigation() {
        let mut tui = WorkbenchTui::new();
        tui.execute_command(WorkbenchCommand::Demo);
        assert_eq!(
            tui.actions()
                .iter()
                .filter(|action| action.label.starts_with("Continue successor"))
                .count(),
            2
        );
        assert!(tui
            .actions()
            .iter()
            .all(|action| !action.label.contains("Discover") && !action.label.contains("folder")));
    }

    #[test]
    fn exact_detail_scroll_is_independent_of_event_selection() {
        let mut tui = WorkbenchTui::new();
        tui.execute_command(WorkbenchCommand::Demo);
        let event = tui.selected_event();
        tui.active = ActivePane::Detail;
        tui.set_detail_tab(DetailTab::Exact);
        tui.set_detail_max_scroll(100);
        tui.handle_key(KeyEvent::new(
            KeyCode::Down,
            crossterm::event::KeyModifiers::NONE,
        ));
        assert_eq!(tui.selected_event(), event);
        assert_eq!(tui.detail_scroll(), 1);
        tui.set_detail_tab(DetailTab::Summary);
        tui.set_detail_max_scroll(100);
        tui.handle_key(KeyEvent::new(
            KeyCode::PageDown,
            crossterm::event::KeyModifiers::NONE,
        ));
        assert_eq!(tui.detail_scroll(), 10);
        tui.set_detail_tab(DetailTab::Exact);
        assert_eq!(tui.detail_scroll(), 1);
    }

    #[test]
    fn mode_keys_change_the_actual_action_surface() {
        let mut tui = WorkbenchTui::new();
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('2'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert_eq!(tui.mode(), WorkbenchMode::Eros);
        assert!(tui
            .actions()
            .iter()
            .any(|action| action.label.contains("atlas")));
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('3'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui
            .actions()
            .iter()
            .any(|action| action.label == "Inspect model chart"));
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('4'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui
            .actions()
            .iter()
            .any(|action| action.label == "Inspect hardware"));
    }

    #[test]
    fn typed_form_refusal_returns_an_event_without_starting_an_operation() {
        let mut tui = WorkbenchTui::new();
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('3'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui.execute_selected_action().is_empty());
        tui.handle_key(KeyEvent::new(
            KeyCode::Enter,
            crossterm::event::KeyModifiers::NONE,
        ));
        let event = tui.events().last().expect("form obstruction");
        assert_eq!(event.code.as_deref(), Some("invalid-form"));
        assert!(!tui.busy());
    }
}
