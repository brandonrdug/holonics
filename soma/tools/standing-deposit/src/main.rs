//! `standing-deposit deposit --root R --plan P --standing S`
//! `standing-deposit verify  --root R --standing S [--report F]`
//!
//! Exit status is the verdict and nothing else: nonzero on CONTENT drift or an ABSENT deposit,
//! zero on CLOSURE drift. Anything that collapses those two has not ported the distinction.

use std::path::PathBuf;
use std::process::ExitCode;

use soma_standing_deposit::manifest::MANIFEST_NAME;
use soma_standing_deposit::plan::Plan;
use soma_standing_deposit::registry::{deposit, verify};

const USAGE: &str = "\
usage:
  standing-deposit deposit --root DIR --plan FILE --standing DIR
  standing-deposit verify  --root DIR --standing DIR [--report FILE]

  deposit  folds each founding's closure, copies its declared returns into the standing,
           and writes standing/MANIFEST.txt binding every return to two hashes.
  verify   REFUSES on content drift or an absent deposit; REPORTS closure drift.";

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(message) => {
            eprintln!("standing-deposit: {message}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let mut args = std::env::args().skip(1);
    let Some(command) = args.next() else {
        println!("{USAGE}");
        return Ok(ExitCode::from(2));
    };
    if command == "--help" || command == "-h" {
        println!("{USAGE}");
        return Ok(ExitCode::SUCCESS);
    }

    let mut root: Option<PathBuf> = None;
    let mut plan_path: Option<PathBuf> = None;
    let mut standing: Option<PathBuf> = None;
    let mut report: Option<PathBuf> = None;
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("`{flag}` carries no operand\n{USAGE}"))?;
        match flag.as_str() {
            "--root" => root = Some(PathBuf::from(value)),
            "--plan" => plan_path = Some(PathBuf::from(value)),
            "--standing" => standing = Some(PathBuf::from(value)),
            "--report" => report = Some(PathBuf::from(value)),
            other => return Err(format!("unknown flag `{other}`\n{USAGE}")),
        }
    }
    let root = root.ok_or_else(|| format!("--root is required\n{USAGE}"))?;
    let standing = standing.ok_or_else(|| format!("--standing is required\n{USAGE}"))?;

    match command.as_str() {
        "deposit" => {
            let plan_path = plan_path.ok_or_else(|| format!("--plan is required\n{USAGE}"))?;
            let plan = Plan::read(&plan_path).map_err(|refusal| refusal.to_string())?;
            let manifest =
                deposit(&root, &plan, &standing).map_err(|refusal| refusal.to_string())?;
            let octets = manifest
                .headers
                .get("deposited_octets")
                .map(String::as_str)
                .unwrap_or("0");
            let derived = manifest
                .headers
                .get("derived_returns_not_deposited")
                .map(String::as_str)
                .unwrap_or("0");
            println!(
                "deposited {} founded returns over {} foundings, {octets} octets; \
                 {derived} derived returns left to be reproduced",
                manifest.deposits.len(),
                manifest.foundings.len()
            );
            println!("manifest {}", standing.join(MANIFEST_NAME).display());
            Ok(ExitCode::SUCCESS)
        }
        "verify" => {
            let verdict = verify(&root, &standing).map_err(|refusal| refusal.to_string())?;
            let rendered = verdict.render();
            if let Some(report) = &report {
                if let Some(parent) = report.parent() {
                    let _ = std::fs::create_dir_all(parent);
                }
                std::fs::write(report, &rendered)
                    .map_err(|error| format!("{}: {error}", report.display()))?;
            }
            print!("{rendered}");
            if verdict.refuses() {
                eprintln!(
                    "standing-deposit: REFUSED — {} deposited returns no longer match their \
                     recorded content and {} are absent",
                    verdict.content_drift, verdict.absent
                );
                return Ok(ExitCode::from(1));
            }
            eprintln!(
                "standing-deposit: HELD — {} deposits hold; {} closures current, {} superseded, \
                 {} unrecomputable",
                verdict.checked,
                verdict.closure_held,
                verdict.closure_drift,
                verdict.closure_unrecomputable
            );
            Ok(ExitCode::SUCCESS)
        }
        other => Err(format!("unknown command `{other}`\n{USAGE}")),
    }
}
