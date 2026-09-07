//! Construction probe over actual exposure using the public text session and native source
//! receiver. No learner or response generator is defined here; this does not publish a model.
use holonic_engine::{
    native_ecology::constitutive_fibre::NativeCurrentHistorySourceReceiver,
    resident_section::ResidentSectionRest,
};
use holonics_hna::{
    alpha::{
        exposure::{ExposurePartition, ExposureReader},
        material::AlphaMaterialError,
        text_codec::{with_text_field, TextSymbol},
        text_session::TextFieldSession,
    },
    publish_new,
};
use serde_json::{json, Value};
use std::{collections::BTreeMap, io::Write, path::PathBuf, time::Instant};

fn error(e: impl std::fmt::Display) -> AlphaMaterialError {
    AlphaMaterialError::Exposure(e.to_string())
}
fn section(s: ResidentSectionRest) -> Value {
    json!({"rows":s.rows,"width":s.width,"grain":s.grain.0,
    "bound_octaves":s.bound_octaves,"intervals":s.intervals})
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = PathBuf::from(
        args.next()
            .ok_or("usage: alpha_current_source EXPOSURE --families N --report NEW.json")?,
    );
    let mut families = None;
    let mut output = None;
    while let Some(option) = args.next() {
        let value = args.next().ok_or("missing option value")?;
        match option.as_str() {
            "--families" => families = Some(value.parse::<usize>()?),
            "--report" => output = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown option {option}").into()),
        }
    }
    let families = families
        .filter(|n| *n > 0)
        .ok_or("positive --families required")?;
    let output = output.ok_or("--report required")?;
    if output.exists() {
        return Err("report destination already exists".into());
    }
    let mut reader = ExposureReader::open(&path)?;
    let mut report = json!({"schema":"holonics.complete-current-source-study.v1","exposure":path,
        "families_requested":families,"fractional_bits":72,"model_persisted":false,
        "language_quality_established":false,"productive_material_source":"coupled-outgoing"});
    let result = with_text_field(72, |field| {
        let mut receiver = NativeCurrentHistorySourceReceiver::on_empty(field)?;
        let mut session = TextFieldSession::on(field)?;
        let mut anchors = BTreeMap::new();
        let mut records = Vec::new();
        let mut sources = Vec::new();
        let mut last_progress = Instant::now();
        let start = Instant::now();
        let constructed = (|| -> Result<(), AlphaMaterialError> {
            while records.len() < families {
                let Some(frame) = reader.peek().map_err(error)? else {
                    break;
                };
                let sequence = frame.sequence;
                if frame.partition != ExposurePartition::Development {
                    reader.acknowledge(sequence).map_err(error)?;
                    continue;
                }
                let (parent, parent_open) = match frame.shared_prior_parent() {
                    Ok(p) => (p, None),
                    Err(e) => (None, Some(e.to_string())),
                };
                let available = parent.as_ref().and_then(|p| anchors.get(p));
                let parent_open = parent_open.or_else(|| {
                    (parent.is_some() && available.is_none())
                        .then(|| "prior parent is not mounted".into())
                });
                let before = session.field().occurrence_count();
                let mut parts = Vec::new();
                for (index, part) in frame.development_parts().map_err(error)?.iter().enumerate() {
                    let Some(text) = &part.text else {
                        continue;
                    };
                    if !matches!(
                        part.kind.as_str(),
                        "human-text" | "human-command" | "agent-text"
                    ) {
                        continue;
                    }
                    session.begin_part(if index == 0 { available } else { None })?;
                    let from = session.field().occurrence_count();
                    for symbol in text
                        .bytes()
                        .map(TextSymbol::Octet)
                        .chain([TextSymbol::EndPart])
                    {
                        session.receive(symbol)?;
                        sources.push(receiver.receive_completed(session.field())?);
                        if last_progress.elapsed().as_secs() >= 10 {
                            eprintln!(
                                "{}",
                                json!({"phase":"native-current-source-construction","native_occurrences":session.field().occurrence_count()})
                            );
                            last_progress = Instant::now();
                        }
                    }
                    parts.push(json!({"ordinal":part.ordinal,"pointer":part.pointer,"native_from":from,"native_until":session.field().occurrence_count()}));
                }
                records.push(json!({"family":frame.family,"sequence":sequence,"parent":parent,"parent_open":parent_open,
                "native_from":before,"native_until":session.field().occurrence_count(),"parts":parts}));
                if session.field().occurrence_count() > before {
                    anchors.insert(frame.family.clone(), session.retain_part_source()?);
                }
                reader.acknowledge(sequence).map_err(error)?;
            }
            Ok(())
        })();
        report["construction_wall_seconds"] = json!(start.elapsed().as_secs_f64());
        report["census_before_diagnostics"] = json!(session.field().census());
        report["native_occurrences"] = json!(session.field().occurrence_count());
        report["development_records"] = json!(records);
        report["exposure_cursor"] = json!(reader.cursor());
        report["boundary_error"] = json!(constructed.as_ref().err().map(ToString::to_string));
        report["pending_native_lineage"] = json!(session.field().pending_lineage());
        report["pending_symbol"] = json!(session.pending_symbol());
        report["lineage"] = json!((0..session.field().occurrence_count())
            .map(|i| session.field().lineage(i))
            .collect::<Vec<_>>());
        report["source_geometry"] = json!(sources
            .iter()
            .map(|s| Ok(
                json!({"occurrence":s.occurrence(),"source":section(receiver.inspect_wire(s)?)})
            ))
            .collect::<Result<Vec<Value>, AlphaMaterialError>>()?);
        report["history_geometry_state"] = section(receiver.inspect_state()?);
        report["covariance"] = if session.field().pending_lineage().is_none() {
            session
                .field()
                .inspect_junction_covariance()?
                .map(section)
                .unwrap_or(Value::Null)
        } else {
            Value::Null
        };
        constructed
    });
    report["construction_error"] = json!(result.as_ref().err().map(ToString::to_string));
    publish_new(&output, |file| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
        }
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer_pretty(&mut writer, &report).map_err(std::io::Error::other)?;
        writer.flush()
    })?;
    println!(
        "{}",
        json!({"report":output,"native_occurrences":report["native_occurrences"],"construction_error":report["construction_error"],"model_persisted":false})
    );
    result?;
    Ok(())
}
