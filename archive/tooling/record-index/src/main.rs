use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use soma_record_index::{
    check_generated, discover_laboratory_root, generate, write_generated, IndexError,
};

const USAGE: &str = "usage: soma-record-index <generate|check> [--root LABORATORY] --out DIRECTORY";

#[derive(Clone, Copy)]
enum Command {
    Generate,
    Check,
}

struct Args {
    command: Command,
    root: Option<PathBuf>,
    out: PathBuf,
}

fn parse_args() -> Result<Option<Args>, IndexError> {
    let mut args = env::args_os().skip(1);
    let Some(command) = args.next() else {
        return Err(IndexError::usage(USAGE));
    };
    if command == "--help" || command == "-h" {
        return Ok(None);
    }
    let command = match command.to_str() {
        Some("generate") => Command::Generate,
        Some("check") => Command::Check,
        _ => return Err(IndexError::usage(USAGE)),
    };

    let mut root = None;
    let mut out = None;
    while let Some(flag) = args.next() {
        match flag.to_str() {
            Some("--root") => {
                let value = args
                    .next()
                    .ok_or_else(|| IndexError::usage("--root requires a path"))?;
                if root.replace(PathBuf::from(value)).is_some() {
                    return Err(IndexError::usage("--root may be supplied only once"));
                }
            }
            Some("--out") => {
                let value = args
                    .next()
                    .ok_or_else(|| IndexError::usage("--out requires a path"))?;
                if out.replace(PathBuf::from(value)).is_some() {
                    return Err(IndexError::usage("--out may be supplied only once"));
                }
            }
            Some("--help") | Some("-h") => return Ok(None),
            _ => return Err(IndexError::usage(USAGE)),
        }
    }

    let out = out.ok_or_else(|| IndexError::usage("--out is required"))?;
    Ok(Some(Args { command, root, out }))
}

fn run() -> Result<(), IndexError> {
    let Some(args) = parse_args()? else {
        println!("{USAGE}");
        return Ok(());
    };
    let root = match args.root {
        Some(root) => root,
        None => discover_laboratory_root(&env::current_dir().map_err(|source| {
            IndexError::io("read current directory", PathBuf::from("."), source)
        })?)?,
    };
    let generated = generate(&root)?;
    match args.command {
        Command::Generate => write_generated(&root, &args.out, &generated)?,
        Command::Check => check_generated(&root, &args.out, &generated)?,
    }
    println!(
        "{} {} files ({} formula claims, {} research documents, {} observation records, {} letters, {} crates, {} public declarations, {} ABI identifiers)",
        match args.command {
            Command::Generate => "generated",
            Command::Check => "checked",
        },
        generated.files().len(),
        generated.counts().formula_claims,
        generated.counts().research_documents,
        generated.counts().observation_records,
        generated.counts().correspondence,
        generated.counts().crates,
        generated.counts().public_symbols,
        generated.counts().abi_identifiers,
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("soma-record-index: {error}");
            ExitCode::FAILURE
        }
    }
}
