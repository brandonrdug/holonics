//! First public text-codec composition over the resident native field. This driver mounts actual
//! exposure and reads actual native emission; it contains no learner, target answer or fallback.
use holonic_engine::native_ecology::constitutive_fibre::NativeFieldSourceAnchor;
use holonics_hna::{
    alpha::{
        exposure::{ExposureFamily, ExposurePartition, ExposureReader},
        material::AlphaMaterialError,
        text_codec::{with_text_field, TextSymbol},
        text_session::TextFieldSession,
    },
    publish_new,
};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    io::{self, Write},
    path::PathBuf,
    time::Instant,
};

fn section(rest: holonic_engine::resident_section::ResidentSectionRest) -> Value {
    json!({"rows":rest.rows,"width":rest.width,"grain":rest.grain.0,
        "bound_octaves":rest.bound_octaves,"intervals":rest.intervals})
}

fn exposure_error(error: impl std::fmt::Display) -> AlphaMaterialError {
    AlphaMaterialError::Exposure(error.to_string())
}

fn cultivate(
    reader: &mut ExposureReader,
    session: &mut TextFieldSession<'_, '_>,
    families: usize,
    records: &mut Vec<Value>,
) -> Result<(), AlphaMaterialError> {
    let mut anchors: BTreeMap<ExposureFamily, (NativeFieldSourceAnchor, usize)> = BTreeMap::new();
    let mut completed = 0;
    let mut last_progress = Instant::now();
    while completed < families {
        let Some(frame) = reader.peek().map_err(exposure_error)? else {
            break;
        };
        let sequence = frame.sequence;
        if frame.partition != ExposurePartition::Development {
            reader.acknowledge(sequence).map_err(exposure_error)?;
            continue;
        }
        if anchors.contains_key(&frame.family) {
            return Err(exposure_error("repeated developmental family"));
        }
        let (parent, parent_open) = match frame.shared_prior_parent() {
            Ok(parent) => (parent, None),
            Err(error) => (None, Some(error.to_string())),
        };
        let mounted_parent = parent.as_ref().and_then(|family| anchors.get(family));
        let parent_open = parent_open.or_else(|| {
            (parent.is_some() && mounted_parent.is_none()).then(|| {
                "source-supported prior parent has not entered this native exposure".into()
            })
        });
        let parts = frame.development_parts().map_err(exposure_error)?;
        let native_from = session.field().occurrence_count();
        let mut part_receipts = Vec::new();
        for (part_index, part) in parts.iter().enumerate() {
            let Some(text) = &part.text else {
                continue;
            };
            if !matches!(
                part.kind.as_str(),
                "human-text" | "human-command" | "agent-text"
            ) {
                continue;
            }
            let parent_anchor = if part_index == 0 {
                mounted_parent.map(|v| &v.0)
            } else {
                None
            };
            session.begin_part(parent_anchor)?;
            let part_from = session.field().occurrence_count();
            let mut failure = None;
            for (symbol_index, symbol) in text
                .bytes()
                .map(TextSymbol::Octet)
                .chain([TextSymbol::EndPart])
                .enumerate()
            {
                if let Err(error) = session.receive(symbol) {
                    failure = Some(
                        json!({"symbol_index":symbol_index,"symbol":symbol,"error":error.to_string()}),
                    );
                    break;
                }
                if last_progress.elapsed().as_secs() >= 10 {
                    eprintln!(
                        "{}",
                        json!({"phase":"development","families_completed":completed,
                        "native_occurrences":session.field().occurrence_count()})
                    );
                    last_progress = Instant::now();
                }
            }
            part_receipts.push(json!({"ordinal":part.ordinal,"pointer":part.pointer,"kind":part.kind,
                "source_octets":text.len(),"native_from":part_from,"native_until":session.field().occurrence_count(),
                "parent_source_occurrence":parent_anchor.and(mounted_parent.map(|v| v.1)),"failure":failure}));
            if failure.is_some() {
                break;
            }
        }
        let failed = session.pending_symbol().is_some();
        records.push(json!({"sequence":sequence,"family":frame.family,"views":frame.views.iter().map(|v|
            json!({"event":v.event,"source":v.source,"record":v.record,"links":v.links})).collect::<Vec<_>>(),
            "parent":parent,"parent_open":parent_open,"native_from":native_from,
            "native_until":session.field().occurrence_count(),"parts":part_receipts,"complete":!failed}));
        if failed {
            return Err(exposure_error(
                "native material reception remains pending; source coordinate is in the record",
            ));
        }
        if session.field().occurrence_count() > native_from {
            anchors.insert(
                frame.family.clone(),
                (
                    session.retain_part_source()?,
                    session.field().occurrence_count() - 1,
                ),
            );
        }
        reader.acknowledge(sequence).map_err(exposure_error)?;
        completed += 1;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let exposure = PathBuf::from(args.next().ok_or("usage: alpha_text EXPOSURE --families N --fractional-bits G --prompt FILE --emit-symbols N --report NEW.json")?);
    let (mut families, mut grain, mut prompt_path, mut limit, mut report_path) =
        (None, None, None, None, None);
    let mut inspect_all_currents = false;
    while let Some(option) = args.next() {
        let value = args.next().ok_or("missing option value")?;
        match option.as_str() {
            "--families" => families = Some(value.parse::<usize>()?),
            "--fractional-bits" => grain = Some(value.parse::<u32>()?),
            "--prompt" => prompt_path = Some(PathBuf::from(value)),
            "--emit-symbols" => limit = Some(value.parse::<usize>()?),
            "--report" => report_path = Some(PathBuf::from(value)),
            "--inspect-all-currents" => inspect_all_currents = value.parse::<bool>()?,
            _ => return Err(format!("unknown option {option}").into()),
        }
    }
    let families = families
        .filter(|n| *n > 0)
        .ok_or("positive --families required")?;
    let grain = grain.ok_or("--fractional-bits required")?;
    let limit = limit.ok_or("--emit-symbols required; interruption does not mean completion")?;
    let prompt_path = prompt_path.ok_or("--prompt required")?;
    let report_path = report_path.ok_or("--report required")?;
    let prompt = std::fs::read_to_string(&prompt_path)?;
    let mut reader = ExposureReader::open(&exposure)?;
    let mut report = json!({"schema":"holonics.alpha-text-study.v1","exposure":exposure,"families_aperture":families,
        "fractional_bits":grain,"prompt_path":prompt_path,"prompt":prompt,"symbol_work_limit":limit,
        "model_persisted":false,"language_quality_established":false});
    report["all_currents_requested"] = json!(inspect_all_currents);
    let native_result = with_text_field(grain, |field| {
        let mut session = TextFieldSession::on(field)?;
        report["junction_solver"] = json!(session.field().junction_solver());
        report["has_material_transport"] = json!(session.field().has_material_transport());
        let mut records = Vec::new();
        let start = Instant::now();
        let developed = cultivate(&mut reader, &mut session, families, &mut records);
        report["material_wall_seconds"] = json!(start.elapsed().as_secs_f64());
        report["development_records"] = json!(records);
        report["development_native_until"] = json!(session.field().occurrence_count());
        report["development_census"] = json!(session.field().census());
        report["development_error"] = json!(developed.as_ref().err().map(ToString::to_string));
        if developed.is_ok() {
            let start = Instant::now();
            session.begin_part(None)?;
            let prompt_from = session.field().occurrence_count();
            let mut prompt_error = None;
            for symbol in prompt
                .bytes()
                .map(TextSymbol::Octet)
                .chain([TextSymbol::EndPart])
            {
                if let Err(error) = session.receive(symbol) {
                    prompt_error = Some(error.to_string());
                    break;
                }
            }
            report["prompt_native_from"] = json!(prompt_from);
            report["prompt_native_until"] = json!(session.field().occurrence_count());
            report["prompt_error"] = json!(prompt_error);
            if prompt_error.is_none() {
                let generated = session.generate(limit);
                report["utf8"] = json!(std::str::from_utf8(&generated.emitted_octets).ok());
                report["utf8_error"] = json!(std::str::from_utf8(&generated.emitted_octets)
                    .err()
                    .map(|e| e.to_string()));
                report["generation"] = json!(generated);
            }
            report["prompt_and_emission_wall_seconds"] = json!(start.elapsed().as_secs_f64());
        }
        let field = session.field();
        report["final_native_census_before_diagnostics"] = json!(field.census());
        let start = Instant::now();
        let final_occurrence = field.occurrence_count().checked_sub(1);
        report["body"] = json!({"occurrences":field.occurrence_count(),
            "lineage":(0..field.occurrence_count()).map(|i| field.lineage(i)).collect::<Vec<_>>(),
            "pending_lineage":field.pending_lineage(),"pending_symbol":session.pending_symbol(),
            "held":section(field.inspect_held()?),"relation":section(field.inspect_relation()?),
            "junction_covariance":field.inspect_junction_covariance()?.map(section),
            "final_junction":final_occurrence.map(|i| field.inspect_junction(i)).transpose()?.flatten().map(section),
            "material_transport":field.inspect_material_transport_state()?,
            "internal_current_enclosures":if inspect_all_currents { field.inspect_internal_current_enclosures()? } else { None }});
        // Only cold diagnostics copy numerical emission carriers. Product steps above read the
        // four differential masks and retain all junction reports on the device.
        let emitted_at = report["generation"]["readings"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|reading| reading["native"]["occurrence"].as_u64())
            .map(|at| at as usize)
            .collect::<Vec<_>>();
        let mut emission_currents = Vec::new();
        for at in emitted_at {
            emission_currents.push(
                json!({"occurrence":at,"junction":field.inspect_junction(at)?.map(section),
                    "transport":field.inspect_material_transport_wire(at)?.map(section)}),
            );
        }
        report["emission_current_history"] = json!(emission_currents);
        if inspect_all_currents {
            let mut history = Vec::new();
            for at in 0..field.occurrence_count() {
                history.push(
                    json!({"occurrence":at,"junction":field.inspect_junction(at)?.map(section),
                    "transport":field.inspect_material_transport_wire(at)?.map(section)}),
                );
            }
            report["junction_history"] = json!(history);
        }
        report["diagnostics_wall_seconds"] = json!(start.elapsed().as_secs_f64());
        Ok(())
    });
    report["native_error"] = json!(native_result.as_ref().err().map(ToString::to_string));
    report["exposure_cursor"] = json!(reader.cursor());
    publish_new(&report_path, |file| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
        }
        let mut writer = io::BufWriter::new(file);
        serde_json::to_writer_pretty(&mut writer, &report).map_err(io::Error::other)?;
        writer.flush()
    })?;
    println!(
        "{}",
        json!({"report":report_path,"native_occurrences":report["body"]["occurrences"],
        "development_native_until":report["development_native_until"],
        "emitted_octets":report["generation"]["emitted_octets"].as_array().map(Vec::len),
        "disposition":report["generation"]["disposition"],"native_error":report["native_error"],
        "development_error":report["development_error"],"model_persisted":false})
    );
    native_result?;
    for key in ["development_error", "prompt_error"] {
        if let Some(error) = report[key].as_str() {
            return Err(error.to_owned().into());
        }
    }
    if report["generation"]["disposition"]["kind"] == "native-refusal" {
        return Err(report["generation"]["disposition"]["reason"]
            .as_str()
            .unwrap_or("native text return refused")
            .to_owned()
            .into());
    }
    Ok(())
}
