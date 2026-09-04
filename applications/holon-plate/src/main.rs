//! `holon-plate deposit --from SCHEMA:FILE --to PLATE.holon`
//! `holon-plate resume  --plate PLATE.holon [--deed FILE] [--to PLATE.holon] [--form FILE]`
//! `holon-plate inspect --plate PLATE.holon`
//!
//! Exit status is the verdict: `0` held, `1` refused, `2` the invocation was wrong.
//!
//! The wording in this file is load-bearing. `deposit` says a FORM was deposited and says plainly
//! that the currents were not; `resume` says a FRESH current was lit and says plainly that the
//! depositing current is gone. There is no `restore` verb and no `thaw` verb, because there is no
//! such operation.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use holon_plate::plate::SchemaTag;
use holon_plate::registry::{deposit, held_schemas, inspect, redeposit, resume};
use holon_plate::schema::present_and_require_change;
use holon_plate::{Census, PLATE_SUFFIX};

const USAGE: &str = "\
usage:
  holon-plate deposit --from SCHEMA:FILE --to PLATE.holon
  holon-plate resume  --plate PLATE.holon [--deed FILE] [--to PLATE.holon] [--form FILE]
  holon-plate inspect --plate PLATE.holon

  deposit  mounts FILE as SCHEMA through the real machine, re-takes the form from the
           mounted body, requires the two to be byte-identical, and seals a plate around
           the FORM with two digests and a declared census.
  resume   verifies a plate and RE-LIGHTS A FRESH CURRENT off the stored form. It does not
           restore the current that deposited the plate; that current is gone.
           --deed presents one further deed to the re-lit body and refuses if the body
                  does not change.
           --to   re-deposits the body afterwards.
           --form writes the body's contemporary form octets out.
  inspect  verifies a plate and reports it WITHOUT lighting a body.

  SCHEMA is a four-octet tag this reader holds. `holon-plate --help` lists them.";

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(Fault::Refused(message)) => {
            eprintln!("{message}");
            ExitCode::from(1)
        }
        Err(Fault::Invocation(message)) => {
            eprintln!("holon-plate: {message}");
            ExitCode::from(2)
        }
    }
}

enum Fault {
    Refused(String),
    Invocation(String),
}

fn invocation(message: impl Into<String>) -> Fault {
    Fault::Invocation(message.into())
}

fn run() -> Result<ExitCode, Fault> {
    let mut args = std::env::args().skip(1);
    let Some(command) = args.next() else {
        println!("{USAGE}\n\n{}", held_report());
        return Ok(ExitCode::from(2));
    };
    if command == "--help" || command == "-h" {
        println!("{USAGE}\n\n{}", held_report());
        return Ok(ExitCode::SUCCESS);
    }

    let mut from: Option<String> = None;
    let mut plate_path: Option<PathBuf> = None;
    let mut to: Option<PathBuf> = None;
    let mut deed_path: Option<PathBuf> = None;
    let mut form_path: Option<PathBuf> = None;
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| invocation(format!("`{flag}` carries no operand\n{USAGE}")))?;
        match flag.as_str() {
            "--from" => from = Some(value),
            "--plate" => plate_path = Some(PathBuf::from(value)),
            "--to" => to = Some(PathBuf::from(value)),
            "--deed" => deed_path = Some(PathBuf::from(value)),
            "--form" => form_path = Some(PathBuf::from(value)),
            other => return Err(invocation(format!("unknown flag `{other}`\n{USAGE}"))),
        }
    }

    match command.as_str() {
        "deposit" => {
            let from = from.ok_or_else(|| invocation(format!("--from is required\n{USAGE}")))?;
            let to = to.ok_or_else(|| invocation(format!("--to is required\n{USAGE}")))?;
            let (tag, source) = split_from(&from)?;
            let form = read(&source)?;
            let deposited =
                deposit(tag, &form).map_err(|refusal| Fault::Refused(refusal.to_string()))?;
            write(&to, &deposited.plate)?;
            println!("DEPOSITED  {}", to.display());
            println!(
                "  schema        {}/{}",
                deposited.tag, deposited.schema_version
            );
            println!(
                "  form          {} octets   form_sha256  {}",
                deposited.form_octets, deposited.form_sha256
            );
            println!(
                "  plate         {} octets   plate_sha256 {}",
                deposited.plate.len(),
                deposited.plate_sha256
            );
            println!("  census        {}", deposited.census.render());
            println!(
                "\n  A FORM was deposited. The currents that ran to bring the body to this form\n  \
                 were NOT deposited -- they died as they flowed and are not in this file."
            );
            warn_suffix(&to);
            Ok(ExitCode::SUCCESS)
        }
        "resume" => {
            let plate_path =
                plate_path.ok_or_else(|| invocation(format!("--plate is required\n{USAGE}")))?;
            let octets = read(&plate_path)?;
            let mut relit =
                resume(&octets).map_err(|refusal| Fault::Refused(refusal.to_string()))?;
            println!("RE-LIT  {}", plate_path.display());
            println!("  schema        {}/{}", relit.tag, relit.schema_version);
            println!(
                "  form          {} octets   form_sha256  {}",
                relit.form_octets, relit.form_sha256
            );
            println!("  census        {}", relit.relit.render());
            println!("  census frames declared and re-lit agree on every field");
            println!(
                "\n  A FRESH current was lit off the stored form. This is NOT the current that\n  \
                 deposited the plate; that current no longer exists and nothing returns it."
            );

            if let Some(deed_path) = &deed_path {
                let deed = read(deed_path)?;
                let (before, after) = present_and_require_change(relit.body.as_mut(), &deed)
                    .map_err(|refusal| Fault::Refused(refusal.to_string()))?;
                println!(
                    "\n  deed          {} ({} octets)",
                    deed_path.display(),
                    deed.len()
                );
                println!("  the re-lit body accepted it and CHANGED:");
                for line in census_delta(&before, &after) {
                    println!("    {line}");
                }
            }

            if let Some(form_path) = &form_path {
                let form = relit
                    .body
                    .form()
                    .map_err(|detail| Fault::Refused(format!("REFUSED: {detail}")))?;
                write(form_path, &form)?;
                println!(
                    "\n  form written  {} ({} octets)",
                    form_path.display(),
                    form.len()
                );
            }

            if let Some(to) = &to {
                let redeposited = redeposit(relit.tag, relit.body.as_ref())
                    .map_err(|refusal| Fault::Refused(refusal.to_string()))?;
                write(to, &redeposited.plate)?;
                let identical = redeposited.plate == octets;
                println!("\n  RE-DEPOSITED  {}", to.display());
                println!(
                    "  plate         {} octets   plate_sha256 {}",
                    redeposited.plate.len(),
                    redeposited.plate_sha256
                );
                println!("  census        {}", redeposited.census.render());
                println!(
                    "  byte-identical to the plate it resumed: {}",
                    if identical {
                        "yes"
                    } else {
                        "no -- a deed moved the body, which is the point of presenting one"
                    }
                );
                warn_suffix(to);
            }
            Ok(ExitCode::SUCCESS)
        }
        "inspect" => {
            let plate_path =
                plate_path.ok_or_else(|| invocation(format!("--plate is required\n{USAGE}")))?;
            let octets = read(&plate_path)?;
            let report = inspect(&octets).map_err(|refusal| Fault::Refused(refusal.to_string()))?;
            println!("PLATE  {}", plate_path.display());
            println!("  schema        {}/{}", report.tag, report.schema_version);
            match report.shape {
                Some(shape) => println!("  shape         {shape}"),
                None => println!(
                    "  shape         NOT HELD by this reader -- `resume` would refuse this plate.\n\
                     \x20               held: {}",
                    held_schemas()
                        .iter()
                        .map(|schema| format!("{}/{}", schema.tag(), schema.version()))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            }
            println!(
                "  layout        head 32 + census {} + form {} + seal 64 = {} octets",
                report.census_octets, report.form_octets, report.plate_octets
            );
            println!("  form_sha256   {}", report.form_sha256);
            println!("  plate_sha256  {}", report.plate_sha256);
            println!("  census        {}", report.census.render());
            println!(
                "\n  Both digests hold. NO BODY WAS LIT: this reports what the plate declares,\n  \
                 not that a body comes out of it. Only `resume` mounts the form."
            );
            Ok(ExitCode::SUCCESS)
        }
        other => Err(invocation(format!("unknown command `{other}`\n{USAGE}"))),
    }
}

fn split_from(from: &str) -> Result<(SchemaTag, PathBuf), Fault> {
    let (tag, path) = from.split_once(':').ok_or_else(|| {
        invocation(format!(
            "--from must be SCHEMA:FILE, e.g. --from HTEC:body.form\n{USAGE}"
        ))
    })?;
    let tag = SchemaTag::parse(tag).ok_or_else(|| {
        invocation(format!(
            "`{tag}` is not a schema tag; a tag is four octets of [A-Z0-9]\n\n{}",
            held_report()
        ))
    })?;
    Ok((tag, PathBuf::from(path)))
}

fn census_delta(before: &Census, after: &Census) -> Vec<String> {
    let mut lines = Vec::new();
    for (field, was) in before.rows() {
        let now = after.value(field).unwrap_or(*was);
        if now == *was {
            lines.push(format!("{field}  {was}  (unmoved)"));
        } else {
            lines.push(format!("{field}  {was} -> {now}"));
        }
    }
    lines
}

fn held_report() -> String {
    let mut out = String::from("schemas this reader holds:\n");
    for schema in held_schemas() {
        out.push_str(&format!(
            "  {}/{}  {}\n    deed: {}\n",
            schema.tag(),
            schema.version(),
            schema.shape(),
            schema.deed_shape().replace('\n', "\n    ")
        ));
    }
    out.push_str(
        "\nA plate naming anything else is REFUSED, never guessed at.\n\n\
         A plate deposits a FORM. It does not deposit currents, it is not comprehension,\n\
         and freezing is not understanding. It applies no compression: the form octets go\n\
         to disk exactly as the form codec emitted them.",
    );
    out
}

fn warn_suffix(path: &Path) {
    if path.extension().and_then(|suffix| suffix.to_str()) != Some(PLATE_SUFFIX) {
        eprintln!(
            "holon-plate: note -- {} does not carry the agreed `.{PLATE_SUFFIX}` suffix",
            path.display()
        );
    }
}

fn read(path: &Path) -> Result<Vec<u8>, Fault> {
    std::fs::read(path)
        .map_err(|error| invocation(format!("cannot read {}: {error}", path.display())))
}

fn write(path: &Path, octets: &[u8]) -> Result<(), Fault> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).map_err(|error| {
                invocation(format!("cannot found {}: {error}", parent.display()))
            })?;
        }
    }
    std::fs::write(path, octets)
        .map_err(|error| invocation(format!("cannot write {}: {error}", path.display())))
}
