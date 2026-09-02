use crossterm::event::{KeyCode, KeyEvent, KeyEventKind};

use crate::{parse_cli, EventLevel, WorkbenchEvent, WorkbenchRuntime};

pub const COMMAND_CATALOGUE: &[&str] = &[
    "status",
    "capabilities",
    "athena demo-open alpha",
    "athena inspect alpha",
    "athena conduct alpha <spool> <thread> <occurrence> <receiver>",
    "athena continue alpha 0",
    "athena return alpha <occurrence> <boundary> <real> <imaginary> <storage>",
    "athena decline alpha",
    "athena diffuse-demo alpha <occurrence> <interval>",
    "athena snapshot alpha <path>",
    "athena open alpha <snapshot>",
    "athena export alpha safetensors <path>",
    "eros mouth <directory>",
    "eros atlas <directory>",
    "soulkiller config <config.json>",
    "soulkiller index <model.safetensors.index.json>",
    "soulkiller onnx <model.onnx>",
    "engine package <package-or-snapshot>",
    "engine export <package-or-snapshot> onnx <path>",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActivePane {
    Catalogue,
    Events,
    Inspector,
}

#[derive(Debug)]
pub struct WorkbenchTui {
    runtime: WorkbenchRuntime,
    events: Vec<WorkbenchEvent>,
    input: String,
    editing: bool,
    active: ActivePane,
    selected_command: usize,
    selected_event: Option<usize>,
    should_quit: bool,
    status: String,
}

impl Default for WorkbenchTui {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkbenchTui {
    pub fn new() -> Self {
        Self {
            runtime: WorkbenchRuntime::new(),
            events: Vec::new(),
            input: String::new(),
            editing: false,
            active: ActivePane::Events,
            selected_command: 0,
            selected_event: None,
            should_quit: false,
            status: "Press : to enter a command; q exits".to_owned(),
        }
    }

    pub fn events(&self) -> &[WorkbenchEvent] {
        &self.events
    }

    pub fn sessions(&self) -> Vec<&str> {
        self.runtime.session_names()
    }

    pub fn input(&self) -> &str {
        &self.input
    }

    pub fn editing(&self) -> bool {
        self.editing
    }

    pub fn active(&self) -> ActivePane {
        self.active
    }

    pub fn selected_command(&self) -> usize {
        self.selected_command
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

    pub fn should_quit(&self) -> bool {
        self.should_quit
    }

    pub fn status(&self) -> &str {
        &self.status
    }

    pub fn submit_line(&mut self, line: &str) -> Vec<WorkbenchEvent> {
        let Some(words) = shlex::split(line) else {
            return self.push_parse_obstruction("unclosed command quotation");
        };
        if words.is_empty() {
            return Vec::new();
        }
        let mut arguments = vec!["holonics".to_owned()];
        arguments.extend(words);
        let invocation = match parse_cli(arguments) {
            Ok(invocation) => invocation,
            Err(error) => return self.push_parse_obstruction(error.render().to_string()),
        };
        let Some(command) = invocation.command else {
            return self.push_parse_obstruction("nested TUI invocation is not a runtime command");
        };
        let returned = self.runtime.execute(command);
        self.events.extend(returned.iter().cloned());
        self.selected_event = self.events.len().checked_sub(1);
        self.status = returned
            .last()
            .map(|event| event.summary.clone())
            .unwrap_or_else(|| "command returned no event".to_owned());
        returned
    }

    pub fn handle_key(&mut self, key: KeyEvent) {
        if key.kind != KeyEventKind::Press {
            return;
        }
        if self.editing {
            match key.code {
                KeyCode::Esc => {
                    self.editing = false;
                    self.status = "command input closed".to_owned();
                }
                KeyCode::Enter => {
                    let line = std::mem::take(&mut self.input);
                    self.editing = false;
                    self.submit_line(&line);
                }
                KeyCode::Backspace => {
                    self.input.pop();
                }
                KeyCode::Char(character) => self.input.push(character),
                _ => {}
            }
            return;
        }
        match key.code {
            KeyCode::Char('q') => self.should_quit = true,
            KeyCode::Char(':') => {
                self.editing = true;
                self.input.clear();
                self.status = "enter Workbench command".to_owned();
            }
            KeyCode::Tab => {
                self.active = match self.active {
                    ActivePane::Catalogue => ActivePane::Events,
                    ActivePane::Events => ActivePane::Inspector,
                    ActivePane::Inspector => ActivePane::Catalogue,
                }
            }
            KeyCode::Up => self.move_selection(-1),
            KeyCode::Down => self.move_selection(1),
            KeyCode::Enter if self.active == ActivePane::Catalogue => {
                self.input = COMMAND_CATALOGUE[self.selected_command].to_owned();
                self.editing = true;
            }
            _ => {}
        }
    }

    fn move_selection(&mut self, direction: isize) {
        match self.active {
            ActivePane::Catalogue => {
                self.selected_command =
                    shifted(self.selected_command, direction, COMMAND_CATALOGUE.len());
            }
            ActivePane::Events | ActivePane::Inspector => {
                if !self.events.is_empty() {
                    let current = self.selected_event.unwrap_or(self.events.len() - 1);
                    self.selected_event = Some(shifted(current, direction, self.events.len()));
                }
            }
        }
    }

    fn push_parse_obstruction(&mut self, summary: impl Into<String>) -> Vec<WorkbenchEvent> {
        let event = WorkbenchEvent::new(
            self.events.len() as u64,
            EventLevel::Obstruction,
            "tui/command",
            summary,
            None,
        );
        self.status = event.summary.clone();
        self.events.push(event.clone());
        self.selected_event = Some(self.events.len() - 1);
        vec![event]
    }
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
    use super::*;
    use crate::{WorkbenchCommand, WorkbenchRuntime};

    #[test]
    fn tui_and_direct_runtime_return_the_same_command_events() {
        let direct = {
            let mut runtime = WorkbenchRuntime::new();
            runtime.execute(WorkbenchCommand::Status)
        };
        let mut tui = WorkbenchTui::new();
        assert_eq!(tui.submit_line("status"), direct);
        assert_eq!(tui.events(), direct);
    }

    #[test]
    fn key_update_opens_palette_executes_and_quits_only_outside_editing() {
        let mut tui = WorkbenchTui::new();
        tui.handle_key(KeyEvent::new(
            KeyCode::Char(':'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui.editing());
        for character in "capabilities".chars() {
            tui.handle_key(KeyEvent::new(
                KeyCode::Char(character),
                crossterm::event::KeyModifiers::NONE,
            ));
        }
        tui.handle_key(KeyEvent::new(
            KeyCode::Enter,
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(!tui.editing());
        assert_eq!(tui.events().len(), 1);
        tui.handle_key(KeyEvent::new(
            KeyCode::Char('q'),
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(tui.should_quit());
    }
}
