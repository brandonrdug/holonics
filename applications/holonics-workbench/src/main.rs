use clap::Parser;
use holonics_workbench::{
    render_human, render_json_lines, run_tui, Cli, EventLevel, WorkbenchRuntime,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("holonics: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let invocation = Cli::parse().invocation();
    if invocation.tui {
        run_tui()?;
    } else if let Some(command) = invocation.command {
        let mut runtime = WorkbenchRuntime::new();
        let events = runtime.execute(command);
        let rendered = if invocation.json {
            render_json_lines(&events).expect("event JSON")
        } else {
            render_human(&events)
        };
        println!("{rendered}");
        if events
            .iter()
            .any(|event| event.level == EventLevel::Obstruction)
        {
            std::process::exit(1);
        }
    }
    Ok(())
}
