use clap::Parser;
use holonics_workbench::Cli;

fn main() {
    let invocation = Cli::parse().invocation();
    if invocation.tui {
        println!("Holonics Workbench TUI is being constructed under WB3.");
    } else if let Some(command) = invocation.command {
        println!(
            "{}",
            serde_json::to_string_pretty(&command).expect("command wire")
        );
    }
}
