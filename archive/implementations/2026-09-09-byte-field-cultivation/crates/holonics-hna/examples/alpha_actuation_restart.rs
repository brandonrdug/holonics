//! Exterior restart comparison for the native material-actuation path.
//! Mounts a saved field, applies ordinary input and native generation, and saves the actual
//! post-generation state. It supplies no learner, expected response or source-data replay.
use holonics_hna::alpha::{checkpoint::SavedTextField, text_codec::TextSymbol};
use serde_json::json;
use std::{error::Error, path::PathBuf, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 6 || !matches!(args[0].as_str(), "split" | "resume") {
        return Err("alpha_actuation_restart split|resume INPUT PROMPT SPLIT_CHECKPOINT FINAL_CHECKPOINT REPORT".into());
    }
    let split = args[0] == "split";
    let saved = SavedTextField::read(&args[1])?;
    let prompt = if split {
        Some(std::fs::read_to_string(&args[2])?)
    } else {
        None
    };
    let split_path = PathBuf::from(&args[3]);
    let final_path = PathBuf::from(&args[4]);
    let started = Instant::now();
    let mut report = json!({"schema":"holonics.material-actuation-restart.v1", "mode":args[0]});
    saved.with_session(|session, stream, anchors, _application| {
        // This study does not consume partially delivered application output.
        if stream.state() != &holonics_hna::HnaStreamState::default() {
            return Err(
                holonics_hna::alpha::material::AlphaMaterialError::Apparatus(
                    "restart comparison requires an idle delivery stream".into(),
                ),
            );
        }
        report["mounted_occurrences"] = json!(session.field().occurrence_count());
        let anchors = anchors.iter().collect::<Vec<_>>();
        if let Some(prompt) = prompt.as_ref() {
            session.begin_part(None)?;
            for symbol in prompt
                .bytes()
                .map(TextSymbol::Octet)
                .chain([TextSymbol::EndPart])
            {
                session.receive(symbol)?;
            }
            report["prefix"] = json!(session.generate(3));
            session.checkpoint(&split_path, &anchors, b"material-actuation-restart-v1")?;
            report["split_occurrences"] = json!(session.field().occurrence_count());
        }
        report["continuation"] = json!(session.generate(125));
        session.checkpoint(&final_path, &anchors, b"material-actuation-restart-v1")?;
        report["final_occurrences"] = json!(session.field().occurrence_count());
        report["return_storage"] = json!(session.field().operative_return_storage());
        report["checkpoint"] = json!(final_path);
        Ok(())
    })?;
    report["mounted_work_seconds"] = json!(started.elapsed().as_secs_f64());
    holonics_hna::publish_new(&args[5], |file| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
        }
        serde_json::to_writer_pretty(file, &report).map_err(std::io::Error::other)
    })?;
    println!(
        "{}",
        json!({"report":args[5],"final_occurrences":report["final_occurrences"]})
    );
    Ok(())
}
