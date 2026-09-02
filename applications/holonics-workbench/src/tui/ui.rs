use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Block, List, ListItem, ListState, Paragraph, Wrap};
use ratatui::Frame;

use crate::tui::{ActivePane, WorkbenchTui};
use crate::EventLevel;

pub fn render(frame: &mut Frame<'_>, app: &WorkbenchTui) {
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(2),
            Constraint::Min(10),
            Constraint::Length(7),
            Constraint::Length(2),
        ])
        .split(frame.area());

    render_header(frame, app, rows[0]);
    if frame.area().width >= 100 {
        let columns = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([
                Constraint::Percentage(34),
                Constraint::Percentage(32),
                Constraint::Percentage(34),
            ])
            .split(rows[1]);
        render_resources(frame, app, columns[0]);
        render_actions(frame, app, columns[1]);
        render_detail(frame, app, columns[2]);
    } else {
        let body = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(6), Constraint::Length(6)])
            .split(rows[1]);
        let columns = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
            .split(body[0]);
        render_resources(frame, app, columns[0]);
        render_actions(frame, app, columns[1]);
        render_detail(frame, app, body[1]);
    }
    render_events(frame, app, rows[2]);
    render_footer(frame, app, rows[3]);
}

fn render_header(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let sessions = if app.sessions().is_empty() {
        "no live session".to_owned()
    } else {
        format!("sessions {}", app.sessions().join(", "))
    };
    frame.render_widget(
        Paragraph::new(vec![
            Line::from(vec![
                "HOLONICS WORKBENCH".bold().fg(Color::Cyan),
                "  select → act → inspect".dark_gray(),
            ]),
            Line::from(format!("{}  ·  {sessions}", app.directory().display())).dark_gray(),
        ]),
        area,
    );
}

fn render_resources(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let items = app
        .resources()
        .iter()
        .enumerate()
        .map(|(at, resource)| {
            ListItem::new(resource.label()).style(selected_style(
                at == app.selected_resource() && app.active() == ActivePane::Resources,
            ))
        })
        .collect::<Vec<_>>();
    let mut state = ListState::default().with_selected(Some(app.selected_resource()));
    frame.render_stateful_widget(
        List::new(items).block(pane_block(
            " Resources ",
            app.active() == ActivePane::Resources,
        )),
        area,
        &mut state,
    );
}

fn render_actions(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let items = app
        .actions()
        .iter()
        .enumerate()
        .map(|(at, action)| {
            ListItem::new(vec![
                Line::from(action.label.clone()).bold(),
                Line::from(action.description.clone()).dark_gray(),
            ])
            .style(selected_style(
                at == app.selected_action() && app.active() == ActivePane::Actions,
            ))
        })
        .collect::<Vec<_>>();
    let mut state = ListState::default().with_selected(Some(app.selected_action()));
    frame.render_stateful_widget(
        List::new(items).block(pane_block(
            " Valid actions ",
            app.active() == ActivePane::Actions,
        )),
        area,
        &mut state,
    );
}

fn render_detail(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    frame.render_widget(
        Paragraph::new(app.selected_detail())
            .block(pane_block(
                " Exact detail ",
                app.active() == ActivePane::Inspector,
            ))
            .wrap(Wrap { trim: false }),
        area,
    );
}

fn render_events(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let items = app
        .events()
        .iter()
        .enumerate()
        .map(|(at, event)| {
            let (marker, color) = match event.level {
                EventLevel::Information => ("·", Color::Blue),
                EventLevel::Consequence => ("→", Color::Green),
                EventLevel::Obstruction => ("!", Color::Red),
            };
            let selected = app.selected_event() == Some(at)
                && matches!(app.active(), ActivePane::Events | ActivePane::Inspector);
            ListItem::new(Line::from(vec![
                format!("{marker} ").fg(color),
                format!("#{} ", event.sequence).dark_gray(),
                event.subject.clone().bold(),
                event
                    .code
                    .as_ref()
                    .map(|code| format!(" [{code}]").red())
                    .unwrap_or_else(|| "".into()),
                format!("  {}", event.summary).into(),
            ]))
            .style(selected_style(selected))
        })
        .collect::<Vec<_>>();
    let mut state = ListState::default().with_selected(app.selected_event());
    frame.render_stateful_widget(
        List::new(items).block(pane_block(
            " Returned events ",
            app.active() == ActivePane::Events,
        )),
        area,
        &mut state,
    );
}

fn render_footer(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let status = if app.busy() {
        format!("WORKING  {}", app.status())
    } else {
        app.status().to_owned()
    };
    frame.render_widget(
        Paragraph::new(vec![
            Line::from(
                "↑↓ choose  Enter open/run  Tab pane  ⌫ parent  w root  h home  d demo  q quit",
            )
            .dark_gray(),
            Line::from(status).fg(if app.busy() {
                Color::Yellow
            } else {
                Color::Gray
            }),
        ]),
        area,
    );
}

fn pane_block(title: &'static str, active: bool) -> Block<'static> {
    Block::bordered().title(if active {
        Line::from(title).fg(Color::Cyan).bold()
    } else {
        Line::from(title).fg(Color::Gray)
    })
}

fn selected_style(selected: bool) -> Style {
    if selected {
        Style::default()
            .fg(Color::Black)
            .bg(Color::Cyan)
            .add_modifier(Modifier::BOLD)
    } else {
        Style::default()
    }
}

#[cfg(test)]
mod tests {
    use ratatui::backend::TestBackend;
    use ratatui::Terminal;
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn guided_view_renders_at_eighty_columns_and_wide_without_command_placeholders() {
        let temporary = tempdir().expect("temporary");
        let mut app = WorkbenchTui::at(temporary.path().to_path_buf());
        app.execute_command(crate::WorkbenchCommand::Demo);
        for (width, height) in [(80, 24), (120, 36)] {
            let backend = TestBackend::new(width, height);
            let mut terminal = Terminal::new(backend).expect("terminal");
            terminal.draw(|frame| render(frame, &app)).expect("render");
            let rendered = terminal
                .backend()
                .buffer()
                .content()
                .iter()
                .map(|cell| cell.symbol())
                .collect::<String>();
            assert!(rendered.contains("HOLONICS WORKBENCH"));
            assert!(rendered.contains("Guided start"));
            assert!(rendered.contains("Valid actions"));
            assert!(!rendered.contains("<spool>"));
        }
    }
}
