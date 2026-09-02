use std::ffi::OsString;
use std::fs;
use std::io::{self, IsTerminal, Read};

use clap::{error::ErrorKind, Parser};
use holonics_workbench::{
    render_human, render_json, render_json_lines, run_tui, Cli, EventLevel, OutputFormat,
    WorkbenchEvent, WorkbenchRequest, WorkbenchResponse, WorkbenchRuntime,
};

fn main() {
    std::process::exit(run(std::env::args_os().collect()));
}

fn run(arguments: Vec<OsString>) -> i32 {
    let requested_format = requested_format(&arguments);
    let invocation = match Cli::try_parse_from(&arguments) {
        Ok(cli) => cli.invocation(),
        Err(error)
            if matches!(
                error.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) =>
        {
            print!("{error}");
            return 0;
        }
        Err(error) => {
            return emit_input_obstruction(requested_format, error.to_string());
        }
    };

    if invocation.tui {
        if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
            return emit_input_obstruction(
                invocation.format,
                "no command was supplied and the Workbench TUI requires an interactive terminal"
                    .to_owned(),
            );
        }
        return match run_tui() {
            Ok(()) => 0,
            Err(error) => {
                eprintln!("holonics: {error}");
                1
            }
        };
    }

    let command = if let Some(command) = invocation.command {
        command
    } else if let Some(input) = invocation.request_input {
        match read_request(&input) {
            Ok(request) => request.command,
            Err(error) => return emit_input_obstruction(invocation.format, error),
        }
    } else {
        return emit_input_obstruction(
            invocation.format,
            "no command or structured request was supplied".to_owned(),
        );
    };

    let events = WorkbenchRuntime::new().execute(command.clone());
    let response = WorkbenchResponse::new(command, events);
    if let Err(error) = emit_response(invocation.format, &response) {
        eprintln!("holonics: {error}");
        return 1;
    }
    if response.obstructed() {
        1
    } else {
        0
    }
}

fn read_request(input: &str) -> Result<WorkbenchRequest, String> {
    let bytes = if input == "-" {
        let mut bytes = Vec::new();
        io::stdin().read_to_end(&mut bytes).map_err(|error| {
            format!("cannot read Workbench request from standard input: {error}")
        })?;
        bytes
    } else {
        fs::read(input)
            .map_err(|error| format!("cannot read Workbench request {input:?}: {error}"))?
    };
    WorkbenchRequest::read(&bytes)
}

fn emit_input_obstruction(format: OutputFormat, summary: String) -> i32 {
    let response = WorkbenchResponse::input_obstruction(vec![WorkbenchEvent::new(
        0,
        EventLevel::Obstruction,
        "workbench/input",
        summary,
        None,
    )
    .with_code("invalid-input")]);
    if let Err(error) = emit_response(format, &response) {
        eprintln!("holonics: {error}");
    }
    2
}

fn emit_response(format: OutputFormat, response: &WorkbenchResponse) -> Result<(), String> {
    let rendered = match format {
        OutputFormat::Human => render_human(&response.events),
        OutputFormat::Json => render_json(response).map_err(|error| error.to_string())?,
        OutputFormat::Jsonl => {
            render_json_lines(&response.events).map_err(|error| error.to_string())?
        }
    };
    println!("{rendered}");
    Ok(())
}

fn requested_format(arguments: &[OsString]) -> OutputFormat {
    let arguments = arguments
        .iter()
        .map(|argument| argument.to_string_lossy())
        .collect::<Vec<_>>();
    for (at, argument) in arguments.iter().enumerate() {
        let value = if argument == "--format" {
            arguments.get(at + 1).map(|value| value.as_ref())
        } else {
            argument.strip_prefix("--format=")
        };
        match value {
            Some("json") => return OutputFormat::Json,
            Some("jsonl") => return OutputFormat::Jsonl,
            _ => {}
        }
    }
    OutputFormat::Human
}
