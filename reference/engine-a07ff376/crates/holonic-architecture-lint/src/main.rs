use std::{env, path::PathBuf, process::ExitCode};

use holonic_architecture_lint::{check_repository, emit_baseline};

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("holonic architecture lint failed: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let mut emit = false;
    let mut root = None::<PathBuf>;
    for argument in env::args().skip(1) {
        if argument == "--emit-baseline" {
            emit = true;
        } else if root.replace(PathBuf::from(&argument)).is_some() {
            return Err("expected at most one repository root".to_owned());
        }
    }
    let root = match root {
        Some(root) => root,
        None => env::current_dir().map_err(|error| format!("cannot resolve cwd: {error}"))?,
    };
    if emit {
        print!("{}", emit_baseline(&root)?);
        return Ok(ExitCode::SUCCESS);
    }
    let report = check_repository(&root)?;
    if report.is_clean() {
        println!(
            "holonic architecture clean: {} files, {} inherited occurrences, {} retired",
            report.protected_files, report.inherited_occurrences, report.retired_occurrences
        );
        return Ok(ExitCode::SUCCESS);
    }
    eprintln!(
        "holonic architecture rejected {} new ownership/materialization occurrences:",
        report.violations.len()
    );
    for violation in report.violations {
        eprintln!(
            "  {}: {} observed {}, allowed {}",
            violation.path, violation.construct, violation.observed, violation.allowed
        );
    }
    Ok(ExitCode::FAILURE)
}
