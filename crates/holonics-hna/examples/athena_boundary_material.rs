//! Inspect persisted E_in/R_text normal laws, or measure one supplied observed return.
//! Optional comparison mode previews the same source on both sides of the material update,
//! retaining the continuing current and writing each stage separately for failure diagnosis.
use holonics_hna::native::{FieldSectionRequest, IncidentFieldSolver, NativeFieldSavedSession};
use serde::Deserialize;
use serde_json::Value;
use std::{env, fs::OpenOptions, io::BufWriter, path::Path, time::Instant};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Comparison {
    request: FieldSectionRequest,
    #[serde(default)]
    observed: Option<String>,
    #[serde(default)]
    step_bits: u32,
    #[serde(default)]
    solver: Option<Solver>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Solver {
    method: IncidentFieldSolver,
    steps: usize,
}

fn write(path: &Path, value: &Value) -> Result<(), Box<dyn std::error::Error>> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    serde_json::to_writer(BufWriter::new(options.open(path)?), value)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let checkpoint = args.next().ok_or("expected checkpoint and output paths")?;
    let output = args.next().ok_or("expected output path")?;
    let comparison = args.next();
    if args.next().is_some() {
        return Err("usage: athena_boundary_material CHECKPOINT OUTPUT [COMPARISON.json]".into());
    }
    if let Some(path) = comparison {
        let mut comparison: Comparison = serde_json::from_slice(&std::fs::read(path)?)?;
        // A material comparison keeps the same continuing current before and after the update.
        // The public observation consumes its actual producing handle once.
        comparison.request.commit = false;
        comparison.request.retain_comparison = true;
        let output = Path::new(&output);
        std::fs::create_dir(output)?;
        let started = Instant::now();
        let saved = NativeFieldSavedSession::open(checkpoint)?;
        println!("saved model read in {} ms", started.elapsed().as_millis());
        saved.with_session(|session, stream| {
            println!("resident model remounted in {} ms", started.elapsed().as_millis());
            if let Some(solver) = &comparison.solver {
                session.configure_incident_solver(solver.method, solver.steps)?;
            }
            let mut source_texts = comparison.request.context.clone();
            source_texts.push(comparison.request.text.clone());
            if let Some(partial) = &comparison.request.partial {
                source_texts.extend(partial.iter().flatten().cloned());
            }
            session.admit_incident_source_texts(&source_texts)?;
            let save = |name: &str, value: Value| {
                write(&output.join(name), &value).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })
            };
            save(
                "material-before.json",
                session.inspect_incident_boundary_material()?,
            )?;
            let before = session.request(&comparison.request)?;
            let id = before["comparison"].as_u64().expect("retained comparison");
            save("generation-before.json", before)?;
            save(
                "receivers-before.json",
                session.inspect_incident_comparison(id)?,
            )?;
            println!("producing field and receiver recorded");
            let Some(observed) = &comparison.observed else {
                session.release(id)?;
                session.checkpoint(&output.join("after.session"), stream.state())?;
                return Ok(());
            };
            let observed_return = match session.observe(id, observed, comparison.step_bits) {
                Ok(value) => value,
                Err(error) => {
                    save("refusal.json", serde_json::json!({
                        "comparison": id, "error": error.to_string(),
                        "scope": "failed staged return; producing comparison retained for retry",
                    }))?;
                    save("material-on-refusal.json", session.inspect_incident_boundary_material()?)?;
                    session.checkpoint(&output.join("pending.session"), stream.state())?;
                    return Err(error);
                }
            };
            save("observation.json", observed_return)?;
            save(
                "material-after.json",
                session.inspect_incident_boundary_material()?,
            )?;
            session.checkpoint(&output.join("after.session"), stream.state())?;
            println!("observed material return recorded");
            let after = session.request(&comparison.request)?;
            let after_id = after["comparison"].as_u64().expect("retained comparison");
            save("generation-after.json", after)?;
            save(
                "receivers-after.json",
                session.inspect_incident_comparison(after_id)?,
            )?;
            session.release(after_id)?;
            println!("same-current material comparison recorded");
            Ok(())
        })?;
        return Ok(());
    }
    let value = NativeFieldSavedSession::open(checkpoint)?
        .with_session(|session, _| session.inspect_incident_boundary_material())?;
    write(Path::new(&output), &value)?;
    Ok(())
}
