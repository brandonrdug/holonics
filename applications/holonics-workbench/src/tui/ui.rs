use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Block, List, ListItem, Paragraph, Tabs, Wrap};
use ratatui::Frame;

use crate::tui::{ActivePane, WorkbenchTui, COMMAND_CATALOGUE};
use crate::EventLevel;

pub fn render(frame: &mut Frame<'_>, app: &WorkbenchTui) {
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(8),
            Constraint::Length(3),
            Constraint::Length(1),
        ])
        .split(frame.area());
    let tabs = Tabs::new(["Workbench", "Athena", "Eros", "Soulkiller", "Engine"])
        .block(Block::bordered().title(" Holonics "))
        .highlight_style(
            Style::default()
                .fg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        )
        .select(0);
    frame.render_widget(tabs, rows[0]);

    let columns = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage(28),
            Constraint::Percentage(38),
            Constraint::Percentage(34),
        ])
        .split(rows[1]);
    render_catalogue(frame, app, columns[0]);
    render_events(frame, app, columns[1]);
    render_inspector(frame, app, columns[2]);

    let title = if app.editing() {
        " Command · Enter execute · Esc cancel "
    } else {
        " Command · : edit · Tab pane · ↑↓ select · q quit "
    };
    let input = Paragraph::new(format!(":{}", app.input()))
        .block(Block::bordered().title(title))
        .style(if app.editing() {
            Style::default().fg(Color::Yellow)
        } else {
            Style::default().fg(Color::DarkGray)
        });
    frame.render_widget(input, rows[2]);
    frame.render_widget(
        Paragraph::new(format!(
            "{} · sessions [{}]",
            app.status(),
            app.sessions().join(", ")
        ))
        .style(Style::default().fg(Color::Gray)),
        rows[3],
    );
}

fn render_catalogue(frame: &mut Frame<'_>, app: &WorkbenchTui, area: ratatui::layout::Rect) {
    let items = COMMAND_CATALOGUE
        .iter()
        .enumerate()
        .map(|(at, command)| {
            let style = if at == app.selected_command() && app.active() == ActivePane::Catalogue {
                Style::default()
                    .fg(Color::Black)
                    .bg(Color::Cyan)
                    .add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            ListItem::new(*command).style(style)
        })
        .collect::<Vec<_>>();
    frame.render_widget(
        List::new(items).block(
            Block::bordered().title(if app.active() == ActivePane::Catalogue {
                " Commands ● "
            } else {
                " Commands "
            }),
        ),
        area,
    );
}

fn render_events(frame: &mut Frame<'_>, app: &WorkbenchTui, area: ratatui::layout::Rect) {
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
                format!(" — {}", event.summary).into(),
            ]))
            .style(if selected {
                Style::default().bg(Color::DarkGray)
            } else {
                Style::default()
            })
        })
        .collect::<Vec<_>>();
    frame.render_widget(
        List::new(items).block(
            Block::bordered().title(if app.active() == ActivePane::Events {
                " Causal events ● "
            } else {
                " Causal events "
            }),
        ),
        area,
    );
}

fn render_inspector(frame: &mut Frame<'_>, app: &WorkbenchTui, area: ratatui::layout::Rect) {
    let text = app.selected_payload().unwrap_or_else(|| {
        "Select an event carrying structured testimony.\n\nThe inspector is a cold receiver; it cannot route conduct.".to_owned()
    });
    frame.render_widget(
        Paragraph::new(text)
            .block(
                Block::bordered().title(if app.active() == ActivePane::Inspector {
                    " Inspector ● "
                } else {
                    " Inspector "
                }),
            )
            .wrap(Wrap { trim: false }),
        area,
    );
}

#[cfg(test)]
mod tests {
    use ratatui::backend::TestBackend;
    use ratatui::Terminal;

    use super::*;

    #[test]
    fn headless_view_renders_small_and_large_terminals() {
        let mut app = WorkbenchTui::new();
        app.submit_line("capabilities");
        for (width, height) in [(60, 16), (120, 36)] {
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
            assert!(rendered.contains("Holonics"));
            assert!(rendered.contains("capabilities"));
        }
    }
}
