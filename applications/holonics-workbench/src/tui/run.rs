use std::time::Duration;

use crossterm::event::{self, Event};

use crate::tui::{render, WorkbenchTui};

pub fn run_tui() -> std::io::Result<()> {
    ratatui::run(|terminal| {
        let mut app = WorkbenchTui::new();
        while !app.should_quit() {
            app.poll_operation();
            terminal.draw(|frame| render(frame, &app))?;
            if event::poll(Duration::from_millis(100))? {
                if let Event::Key(key) = event::read()? {
                    app.handle_key(key);
                }
            }
        }
        Ok(())
    })
}
