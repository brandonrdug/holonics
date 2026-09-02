use ratatui::layout::{Constraint, Direction, Layout, Margin, Rect};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{
    Block, List, ListItem, ListState, Paragraph, Scrollbar, ScrollbarOrientation, ScrollbarState,
    Wrap,
};
use ratatui::Frame;

use crate::tui::{ActivePane, DetailTab, WorkbenchMode, WorkbenchTui};
use crate::EventLevel;

pub fn render(frame: &mut Frame<'_>, app: &mut WorkbenchTui) {
    let event_height = if frame.area().height < 30 { 5 } else { 8 };
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(10),
            Constraint::Length(event_height),
            Constraint::Length(2),
        ])
        .split(frame.area());
    render_header(frame, app, rows[0]);
    if frame.area().width >= 96 {
        let columns = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([Constraint::Percentage(68), Constraint::Percentage(32)])
            .split(rows[1]);
        render_detail(frame, app, columns[0]);
        render_actions(frame, app, columns[1]);
    } else {
        let body = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(8), Constraint::Length(6)])
            .split(rows[1]);
        render_detail(frame, app, body[0]);
        render_actions(frame, app, body[1]);
    }
    render_events(frame, app, rows[2]);
    render_footer(frame, app, rows[3]);
}

fn render_header(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let mode_spans = WorkbenchMode::ALL
        .iter()
        .enumerate()
        .flat_map(|(at, mode)| {
            let selected = *mode == app.mode();
            [
                Span::styled(
                    format!(" {} {} ", at + 1, mode.label()),
                    if selected {
                        Style::default()
                            .fg(Color::Black)
                            .bg(Color::Cyan)
                            .add_modifier(Modifier::BOLD)
                    } else {
                        Style::default().fg(Color::Gray)
                    },
                ),
                Span::raw(" "),
            ]
        })
        .collect::<Vec<_>>();
    frame.render_widget(
        Paragraph::new(vec![
            Line::from(mode_spans),
            Line::from(app.session_status_line()).bold(),
            Line::from(app.lifecycle_line()).fg(Color::DarkGray),
        ]),
        area,
    );
}

fn render_detail(frame: &mut Frame<'_>, app: &mut WorkbenchTui, area: Rect) {
    let title = detail_title(app);
    let text = app.selected_detail();
    let block = pane_block(title, app.active() == ActivePane::Detail);
    let paragraph = Paragraph::new(text).block(block).wrap(Wrap { trim: false });
    let viewport = usize::from(area.height.saturating_sub(2)).max(1);
    let visual_lines = paragraph.line_count(area.width.saturating_sub(2).max(1));
    let maximum = visual_lines.saturating_sub(viewport);
    app.set_detail_max_scroll(u16::try_from(maximum).unwrap_or(u16::MAX));
    let scroll = app.detail_scroll();
    frame.render_widget(paragraph.scroll((scroll, 0)), area);
    if maximum > 0 {
        let mut state = ScrollbarState::new(maximum.saturating_add(1))
            .position(usize::from(app.detail_scroll()));
        frame.render_stateful_widget(
            Scrollbar::new(ScrollbarOrientation::VerticalRight)
                .begin_symbol(Some("↑"))
                .end_symbol(Some("↓")),
            area.inner(Margin {
                vertical: 1,
                horizontal: 0,
            }),
            &mut state,
        );
    }
}

fn render_actions(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let areas = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Min(5), Constraint::Length(5)])
        .split(area);
    let mut previous_group = None;
    let items = app
        .actions()
        .iter()
        .enumerate()
        .map(|(at, action)| {
            let group = if previous_group == Some(action.group) {
                ""
            } else {
                previous_group = Some(action.group);
                action.group
            };
            ListItem::new(Line::from(vec![
                format!("{group:<9}").dark_gray(),
                action.label.clone().into(),
            ]))
            .style(selected_style(
                at == app.selected_action() && app.active() == ActivePane::Actions,
            ))
        })
        .collect::<Vec<_>>();
    let mut state = ListState::default().with_selected(Some(app.selected_action()));
    frame.render_stateful_widget(
        List::new(items).block(pane_block(
            Line::from(" Next and available actions "),
            app.active() == ActivePane::Actions,
        )),
        areas[0],
        &mut state,
    );
    frame.render_widget(
        Paragraph::new(app.selected_action_description())
            .block(Block::bordered().title(" Selected action "))
            .wrap(Wrap { trim: true })
            .style(Style::default().fg(Color::Gray)),
        areas[1],
    );
}

fn render_events(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let items = app
        .events()
        .iter()
        .enumerate()
        .map(|(at, event)| {
            let (marker, label, color) = match event.level {
                EventLevel::Information => ("·", "INFO", Color::Blue),
                EventLevel::Consequence => ("→", "RETURN", Color::Green),
                EventLevel::Obstruction => ("!", "STOP", Color::Red),
            };
            let selected = app.selected_event() == Some(at) && app.active() == ActivePane::Events;
            ListItem::new(Line::from(vec![
                format!("{marker} ").fg(color),
                format!("{label:<7}").fg(color),
                format!("#{:<3}", event.sequence).dark_gray(),
                format!("{:<28}", event.subject).bold(),
                event.summary.clone().into(),
            ]))
            .style(selected_style(selected))
        })
        .collect::<Vec<_>>();
    let mut state = ListState::default().with_selected(app.selected_event());
    frame.render_stateful_widget(
        List::new(items).block(pane_block(
            Line::from(" Causal return timeline "),
            app.active() == ActivePane::Events,
        )),
        area,
        &mut state,
    );
}

fn render_footer(frame: &mut Frame<'_>, app: &WorkbenchTui, area: Rect) {
    let status = match app.pending_label() {
        Some(label) => format!("WORKING  {label}"),
        None => app.status().to_owned(),
    };
    let keys = if area.width < 100 {
        "1–4 mode  Tab pane  ↑↓/Pg scroll  ←→ view  Enter act  ? help  q quit"
    } else {
        "1–4 mode  [ ] session  Tab pane  ↑↓/Pg scroll  ←→ view  Enter act  ? help  q quit"
    };
    frame.render_widget(
        Paragraph::new(vec![
            Line::from(keys).dark_gray(),
            Line::from(status).fg(if app.busy() {
                Color::Yellow
            } else {
                Color::Gray
            }),
        ]),
        area,
    );
}

fn detail_title(app: &WorkbenchTui) -> Line<'static> {
    let mut spans = vec![Span::styled(
        format!(" {}  ", app.detail_title()),
        Style::default().add_modifier(Modifier::BOLD),
    )];
    for tab in DetailTab::ALL {
        spans.push(Span::styled(
            format!(" {} ", tab.label()),
            if tab == app.detail_tab() {
                Style::default()
                    .fg(Color::Black)
                    .bg(Color::Cyan)
                    .add_modifier(Modifier::BOLD)
            } else {
                Style::default().fg(Color::DarkGray)
            },
        ));
        spans.push(Span::raw(" "));
    }
    Line::from(spans)
}

fn pane_block(title: Line<'static>, active: bool) -> Block<'static> {
    Block::bordered().title(if active {
        title.fg(Color::Cyan)
    } else {
        title.fg(Color::Gray)
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

    use super::*;

    #[test]
    fn session_first_view_renders_narrow_and_wide_without_file_browser_or_raw_json_default() {
        let mut app = WorkbenchTui::new();
        app.execute_command(crate::WorkbenchCommand::Demo);
        for (width, height) in [(80, 28), (120, 36), (180, 48)] {
            let backend = TestBackend::new(width, height);
            let mut terminal = Terminal::new(backend).expect("terminal");
            terminal
                .draw(|frame| render(frame, &mut app))
                .expect("render");
            let rendered = terminal
                .backend()
                .buffer()
                .content()
                .iter()
                .map(|cell| cell.symbol())
                .collect::<String>();
            assert!(rendered.contains("ATHENA"));
            assert!(rendered.contains("WORLD RETURN"));
            assert!(rendered.contains("Next and available actions"));
            assert!(!rendered.contains("Resources"));
            assert!(!rendered.contains("branch_to_occurrence"));
        }
        app.handle_key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Tab,
            crossterm::event::KeyModifiers::NONE,
        ));
        app.handle_key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Char('x'),
            crossterm::event::KeyModifiers::NONE,
        ));
        let backend = TestBackend::new(80, 28);
        let mut terminal = Terminal::new(backend).expect("terminal");
        terminal
            .draw(|frame| render(frame, &mut app))
            .expect("render exact");
        let rendered = terminal
            .backend()
            .buffer()
            .content()
            .iter()
            .map(|cell| cell.symbol())
            .collect::<String>();
        assert!(rendered.contains('↑'));
        assert!(rendered.contains('↓'));
        app.handle_key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::End,
            crossterm::event::KeyModifiers::NONE,
        ));
        let end = app.detail_scroll();
        assert!(end > 0);
        app.handle_key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::PageUp,
            crossterm::event::KeyModifiers::NONE,
        ));
        assert!(app.detail_scroll() < end);
    }
}
