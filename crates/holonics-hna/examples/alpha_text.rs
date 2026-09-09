//! First public text-codec composition over the resident native field. This driver mounts actual
//! exposure and reads actual native emission; it contains no learner, target answer or fallback.
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeFieldSourceAnchor, NativeMaterialTransportSource, NativeContactRealization, NativeMaterialTarget, NativeMaterialPullbackMetric,
};
use holonics_hna::{
    alpha::{
        checkpoint::SavedTextField,
        exposure::{ExposureCursor, ExposureFamily, ExposurePartition, ExposureReader},
        material::AlphaMaterialError,
        text_codec::{with_text_field_chart, TextSymbol, TextDirection},
        text_session::{TextCurrentReceiver, TextFieldSession},
    },
    publish_new,
};
use serde::{Deserialize, Serialize};
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

type AnchorMap = BTreeMap<ExposureFamily, (NativeFieldSourceAnchor, usize)>;
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct AnchorPosition {
    family: ExposureFamily,
    occurrence: usize,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CultivationCheckpoint {
    schema: String,
    exposure: String,
    cursor: ExposureCursor,
    native_until: usize,
    records: Vec<Value>,
    anchors: Vec<AnchorPosition>,
    #[serde(default)]
    contact_response: bool,
    #[serde(default)]
    contact_realization: NativeContactRealization,
    #[serde(default)]
    contact_metric: NativeMaterialPullbackMetric,
}

fn cultivate(
    reader: &mut ExposureReader,
    session: &mut TextFieldSession<'_, '_>,
    families: usize,
    records: &mut Vec<Value>,
    anchors: &mut AnchorMap,
    contact_response: bool,
    contact_realization: NativeContactRealization,
    contact_metric: NativeMaterialPullbackMetric,
) -> Result<(), AlphaMaterialError> {
    let mut partial = records.last().filter(|r| r["complete"] == false).cloned();
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
        let resumed = partial.take();
        if resumed
            .as_ref()
            .is_some_and(|r| r["sequence"] != sequence || r["family"] != json!(frame.family))
        {
            return Err(exposure_error(
                "saved partial frame disagrees with exposure cursor",
            ));
        }
        let native_from = resumed
            .as_ref()
            .and_then(|r| r["native_from"].as_u64())
            .map_or(session.field().occurrence_count(), |v| v as usize);
        let mut part_receipts = resumed
            .as_ref()
            .and_then(|r| r["parts"].as_array())
            .cloned()
            .unwrap_or_default();
        let partial_part = if resumed.is_some() {
            part_receipts.pop()
        } else {
            None
        };
        let partial_ordinal = partial_part.as_ref().and_then(|p| p["ordinal"].as_u64());
        // The first part admitted by this text chart inherits the actual available parent,
        // including when an image or other unmounted material precedes it in the source.
        for (part_index, part) in parts
            .iter()
            .filter(|part| {
                part.text.is_some()
                    && matches!(
                        part.kind.as_str(),
                        "human-text" | "human-command" | "agent-text"
                    )
            })
            .enumerate()
        {
            let Some(text) = &part.text else {
                continue;
            };
            if partial_ordinal.is_some_and(|ordinal| part.ordinal < ordinal) {
                continue;
            }
            let parent_anchor = if part_index == 0 {
                mounted_parent.map(|v| &v.0)
            } else {
                None
            };
            let resume_part = partial_part
                .as_ref()
                .filter(|p| p["ordinal"] == part.ordinal);
            let mut skip = 0usize;
            let part_from = if let Some(saved) = resume_part {
                if saved["pointer"] != part.pointer
                    || saved["native_until"].as_u64()
                        != Some(session.field().occurrence_count() as u64)
                {
                    return Err(exposure_error(
                        "partial inscription/current boundary mismatch",
                    ));
                }
                skip = saved["failure"]["symbol_index"]
                    .as_u64()
                    .ok_or_else(|| exposure_error("missing pending symbol coordinate"))?
                    as usize;
                saved["native_from"]
                    .as_u64()
                    .ok_or_else(|| exposure_error("missing partial native start"))?
                    as usize
            } else {
                session.begin_part(parent_anchor)?;
                session.field().occurrence_count()
            };
            let direction=if part.kind=="agent-text"{TextDirection::Outgoing}else{TextDirection::Incoming};
            let mut failure = None;
            for (symbol_index, symbol) in text
                .bytes()
                .map(TextSymbol::Octet)
                .chain([TextSymbol::EndPart])
                .enumerate()
            {
                if symbol_index < skip {
                    continue;
                }
                let retry_contact = resume_part.is_some_and(|p|p["failure"]["phase"]=="contact-response") && symbol_index==skip;
                let result = if retry_contact {
                    if session.pending_symbol().is_some() || !contact_response {
                        return Err(exposure_error("pending contact response disagrees with session or configured law"));
                    }
                    Ok(())
                } else if resume_part.is_some() && symbol_index == skip {
                    if session.pending_symbol() != Some(symbol) || (session.duplex() && session.pending_direction()!=Some(direction)) {
                        return Err(exposure_error(
                            "saved pending symbol disagrees with source material",
                        ));
                    }
                    session.retry_pending()
                } else {
                    session.receive_on(symbol,direction)
                };
                if let Err(error) = result {
                    failure = Some(
                        json!({"phase":"reception","symbol_index":symbol_index,"symbol":symbol,"error":error.to_string()}),
                    );
                    break;
                }
                if contact_response {
                    let group=match session.field().material_target(){Some(NativeMaterialTarget::TensorProduct{..})=>session.field().material_target_dimension().unwrap(),_=>2};
                    if let Err(error)=session.respond_to_latest_material_with_realization(group,
                        contact_metric,
                        contact_realization) {
                        failure=Some(json!({"phase":"contact-response","symbol_index":symbol_index,
                            "symbol":symbol,"error":error.to_string()}));
                        break;
                    }
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
            // A resumed part keeps the source that actually began it. Correcting the future
            // framing must not rewrite an already committed or previously staged inscription.
            let actual_parent = if session.field().occurrence_count() > part_from {
                session
                    .field()
                    .lineage(part_from)
                    .and_then(|l| l.received_from)
            } else if let Some(saved) = resume_part {
                saved["parent_source_occurrence"]
                    .as_u64()
                    .map(|at| at as usize)
            } else {
                parent_anchor.and(mounted_parent.map(|v| v.1))
            };
            part_receipts.push(json!({"ordinal":part.ordinal,"pointer":part.pointer,"kind":part.kind,
                "source_octets":text.len(),"native_from":part_from,"native_until":session.field().occurrence_count(),
                "parent_source_occurrence":actual_parent,"failure":failure}));
            if failure.is_some() {
                break;
            }
        }
        let failed = session.pending_symbol().is_some() || part_receipts.iter().any(|p|!p["failure"].is_null());
        if resumed.is_some() {
            records.pop();
        }
        records.push(json!({"sequence":sequence,"family":frame.family,"views":frame.views.iter().map(|v|
            json!({"event":v.event,"source":v.source,"record":v.record,"links":v.links})).collect::<Vec<_>>(),
            "parent":parent,"parent_open":parent_open,"native_from":native_from,
            "native_until":session.field().occurrence_count(),"parts":part_receipts,"complete":!failed}));
        if failed {
            return Err(exposure_error(
                "native reception or its contact response remains pending; source coordinate is in the record",
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
        if session.field().has_history_archive() {
            session.archive_history()?;
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "alpha_text/tests.rs"]
mod tests;

fn run_session(
    session: &mut TextFieldSession<'_, '_>,
    reader: &mut Option<ExposureReader>,
    cursor: &mut ExposureCursor,
    exposure: &str,
    families: usize,
    records: &mut Vec<Value>,
    anchors: &mut AnchorMap,
    prompt: Option<&str>,
    limit: usize,
    text_receiver: TextCurrentReceiver,
    inspect_all_currents: bool,
    operative: bool,
    contact_response: bool,
    contact_realization: NativeContactRealization,
    contact_metric: NativeMaterialPullbackMetric,
    checkpoint: Option<&PathBuf>,
    report: &mut Value,
) -> Result<(), AlphaMaterialError> {
    if operative {
        session.enable_operative_contacts()?;
    }
    report["operative_contacts"] = json!(session.field().has_operative_contacts());
    report["junction_solver"] = json!(session.field().junction_solver());
    report["has_material_transport"] = json!(session.field().has_material_transport());
    report["material_source"] = json!(session.field().material_transport_source());
    report["material_target"] = json!(session.field().material_target());
    report["text_receiver"] = json!(text_receiver);
    report["duplex"] = json!(session.duplex());
    report["contact_response_during_development"] = json!(contact_response);
    report["contact_realization"] = json!(contact_realization);
    report["contact_metric"] = json!(contact_metric);
    let start = Instant::now();
    let developed = if let Some(reader) = reader.as_mut() {
        cultivate(reader, session, families, records, anchors, contact_response, contact_realization, contact_metric)
    } else {
        Ok(())
    };
    if let Some(reader) = reader.as_ref() {
        *cursor = reader.cursor();
    }
    report["material_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    report["development_records"] = json!(&*records);
    report["development_native_until"] = json!(session.field().occurrence_count());
    report["development_operative_returns"] = json!(session.field().operative_return_count());
    report["development_census"] = json!(session.field().census());
    report["history_placement"] = json!(session.field().history_placement());
    report["development_section_readouts_outside_history_placement"] = json!(
        session.field().census().section_read_outs
            - session
                .field()
                .history_placement()
                .archive_section_read_outs
    );
    report["development_error"] = json!(developed.as_ref().err().map(ToString::to_string));
    if let Some(path) = checkpoint {
        let app = CultivationCheckpoint {
            schema: "holonics.text-cultivation-checkpoint.v1".into(),
            exposure: exposure.to_owned(),
            cursor: cursor.clone(),
            native_until: session.field().occurrence_count(),
            contact_response,
            contact_realization,
            contact_metric,
            records: records.clone(),
            anchors: anchors
                .iter()
                .map(|(family, (_, occurrence))| AnchorPosition {
                    family: family.clone(),
                    occurrence: *occurrence,
                })
                .collect(),
        };
        let encoded = serde_json::to_vec(&app).map_err(exposure_error)?;
        let sources = anchors
            .values()
            .map(|(anchor, _)| anchor)
            .collect::<Vec<_>>();
        let start = Instant::now();
        match session.checkpoint(path, &sources, &encoded) {
            Ok(_) => {
                report["model_persisted"] = json!(true);
                report["checkpoint"] = json!(path);
                report["checkpoint_native_occurrences"] = json!(session.field().occurrence_count());
                report["checkpoint_boundary"] = json!(if session.pending_symbol().is_some() {
                    "pending-development-symbol"
                } else if developed.is_err() {
                    "pending-contact-response"
                } else {
                    "after-development-before-prompt"
                });
            }
            Err(error) => report["checkpoint_error"] = json!(error.to_string()),
        }
        report["checkpoint_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    }
    if developed.is_ok() && prompt.is_some() {
        let prompt = prompt.expect("checked prompt");
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
            let generated = session.generate_with_receiver(limit, text_receiver);
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
            "junction_covariance":if field.has_operative_contacts() {None} else {field.inspect_junction_covariance()?.map(section)},
            "operative_contacts":field.inspect_operative_contacts()?,
            "final_junction":final_occurrence.map(|i| field.inspect_junction(i)).transpose()?.flatten().map(section),
            "material_transport":if field.material_transport_source()==Some(NativeMaterialTransportSource::CompleteCurrent) {
                json!(field.inspect_complete_material_transport_state()?)
            } else if field.material_transport_source()==Some(NativeMaterialTransportSource::HomogeneousMoment) {
                json!(final_occurrence.map(|at|field.inspect_moment_material_transport(at)).transpose()?.flatten())
            } else if matches!(field.material_transport_source(),Some(NativeMaterialTransportSource::Contextual|NativeMaterialTransportSource::BilinearContextual|NativeMaterialTransportSource::OperativeContextual|NativeMaterialTransportSource::OperativeBoundary)) {
                json!(final_occurrence.map(|at|field.inspect_contextual_material_transport(at)).transpose()?.flatten())
            } else {json!(field.inspect_material_transport_state()?)},
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
    report["exposure_cursor"] = json!(cursor);
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let first=args.next().ok_or("usage: alpha_text EXPOSURE | --resume CHECKPOINT [--families N] [--fractional-bits G] [--prompt FILE --emit-symbols N] --report NEW.json [--checkpoint NEW.hna] [--history-archive NEW.history] [--material-source coupled-outgoing|complete-current|homogeneous-moment|contextual|bilinear-contextual|contextual-direct-sum|operative-contextual|operative-boundary|operative-linear] [--material-target direct-current|joint-packet] [--text-receiver material|constitutive] [--operative-junction true|false] [--contact-response true|false] [--duplex true|false] [--contact-metric current|relative-entropy|squared-probability]")?;
    let resume = if first == "--resume" {
        Some(PathBuf::from(
            args.next().ok_or("missing resume checkpoint")?,
        ))
    } else {
        None
    };
    let (mut families, mut grain, mut prompt_path, mut limit, mut report_path, mut checkpoint) =
        (None, None, None, None, None, None);
    let mut inspect_all_currents = false;
    let mut operative = false;
    let mut contact_response = None;
    let mut contact_realization = None;
    let mut contact_metric = None;
    let mut duplex = None;
    let mut history_archive = None;
    let mut material_source = None;
    let mut material_target = None;
    let mut text_receiver = TextCurrentReceiver::Material;
    while let Some(option) = args.next() {
        let value = args.next().ok_or("missing option value")?;
        match option.as_str() {
            "--families" => families = Some(value.parse::<usize>()?),
            "--fractional-bits" => grain = Some(value.parse::<u32>()?),
            "--prompt" => prompt_path = Some(PathBuf::from(value)),
            "--emit-symbols" => limit = Some(value.parse::<usize>()?),
            "--text-receiver" => {
                text_receiver = match value.as_str() {
                    "material" => TextCurrentReceiver::Material,
                    "constitutive" => TextCurrentReceiver::Constitutive,
                    _ => return Err("text receiver must be material or constitutive".into()),
                }
            }
            "--report" => report_path = Some(PathBuf::from(value)),
            "--checkpoint" => checkpoint = Some(PathBuf::from(value)),
            "--history-archive" => history_archive = Some(PathBuf::from(value)),
            "--material-source" => {
                material_source = Some(match value.as_str() {
                    "coupled-outgoing" => NativeMaterialTransportSource::CoupledOutgoing,
                    "complete-current" => NativeMaterialTransportSource::CompleteCurrent,
                    "homogeneous-moment" => NativeMaterialTransportSource::HomogeneousMoment,
                    "contextual" | "bilinear-contextual" => {
                        NativeMaterialTransportSource::BilinearContextual
                    }
                    "contextual-direct-sum" => NativeMaterialTransportSource::Contextual,
                    "operative-contextual" => NativeMaterialTransportSource::OperativeContextual,
                    "operative-boundary" => NativeMaterialTransportSource::OperativeBoundary,
                    "operative-linear" => NativeMaterialTransportSource::OperativeLinear,
                    _ => {
                        return Err(
                            "material source must be coupled-outgoing, complete-current, homogeneous-moment, contextual (alias bilinear-contextual), contextual-direct-sum, operative-contextual, operative-boundary, or operative-linear".into(),
                        );
                    }
                })
            }
            "--operative-junction" => operative = value.parse::<bool>()?,
            "--duplex" => duplex=Some(value.parse::<bool>()?),
            "--contact-response" => contact_response = Some(value.parse::<bool>()?),
            "--material-target" => material_target=Some(match value.as_str(){
                "direct-current"=>NativeMaterialTarget::DirectCurrent,
                "joint-packet"=>NativeMaterialTarget::TensorProduct{factor_width:2},
                _=>return Err("material target must be direct-current or joint-packet".into()),
            }),
            "--contact-metric" => contact_metric=Some(match value.as_str(){
                "current"=>NativeMaterialPullbackMetric::SquaredCurrent,
                "relative-entropy"=>NativeMaterialPullbackMetric::RelativeEntropy,
                "squared-probability"=>NativeMaterialPullbackMetric::SquaredProbability,
                _=>return Err("contact metric must be current, relative-entropy or squared-probability".into()),
            }),
            "--contact-realization" => contact_realization = Some(match value.as_str() {
                "enclosed-flow" => NativeContactRealization::EnclosedFlow,
                "dyadic-deposit" => NativeContactRealization::DyadicDeposit,
                _ => return Err("contact realization must be enclosed-flow or dyadic-deposit".into()),
            }),
            "--inspect-all-currents" => inspect_all_currents = value.parse::<bool>()?,
            _ => return Err(format!("unknown option {option}").into()),
        }
    }
    let families = families.unwrap_or(0);
    if resume.is_none() && families == 0 {
        return Err("fresh cultivation requires positive --families".into());
    }
    if prompt_path.is_none() && checkpoint.is_none() && (resume.is_none() || families > 0) {
        return Err("supply a prompt or a checkpoint destination".into());
    }
    let limit = if prompt_path.is_some() {
        limit.ok_or("--emit-symbols required for a prompt")?
    } else {
        0
    };
    let prompt = prompt_path
        .as_ref()
        .map(std::fs::read_to_string)
        .transpose()?;
    let report_path = report_path.ok_or("--report required")?;
    let mut report = json!({"schema":"holonics.alpha-text-study.v1","prompt_path":prompt_path,"prompt":prompt,
        "symbol_work_limit":limit,"model_persisted":false,"language_quality_established":false,
        "all_currents_requested":inspect_all_currents,"additional_families_requested":families});
    let native_result = if let Some(path) = resume {
        let saved = SavedTextField::read(&path)?;
        if duplex.is_some_and(|value|value!=saved.duplex()){return Err("resume cannot relabel the saved text boundary chart".into());}
        let mut app: CultivationCheckpoint = serde_json::from_slice(saved.application_state())?;
        if app.schema != "holonics.text-cultivation-checkpoint.v1"
            || app.native_until != saved.occurrences()
            || app.anchors.len() != saved.external_anchor_occurrences().len()
            || app
                .anchors
                .iter()
                .zip(saved.external_anchor_occurrences())
                .any(|(a, b)| Some(a.occurrence) != *b)
        {
            return Err("saved cultivation/capability boundary mismatch".into());
        }
        let mut recorded = BTreeMap::new();
        let mut prior_end = 0u64;
        for record in &app.records {
            let family: ExposureFamily = serde_json::from_value(record["family"].clone())?;
            let from = record["native_from"]
                .as_u64()
                .ok_or("missing native record start")?;
            let end = record["native_until"]
                .as_u64()
                .ok_or("missing native record end")?;
            if from != prior_end
                || end < from
                || recorded
                    .insert(family, (end, record["complete"] == true))
                    .is_some()
            {
                return Err("saved record population or chronology mismatch".into());
            }
            prior_end = end;
        }
        let mut families_seen = std::collections::BTreeSet::new();
        if prior_end != app.native_until as u64
            || app.anchors.iter().any(|a| {
                !families_seen.insert(a.family.clone())
                    || recorded.get(&a.family) != Some(&(a.occurrence as u64 + 1, true))
            })
        {
            return Err("saved parent/source record boundary mismatch".into());
        }
        let actual_grain = saved.fractional_bits()?;
        if material_source.is_some() && material_source != saved.material_transport_source() {
            return Err("resume cannot silently change the saved material source".into());
        }
        if material_target.is_some() && material_target!=saved.material_target(){return Err("resume cannot silently change the saved material target".into());}
        if grain.is_some_and(|g| g != actual_grain) {
            return Err("resume cannot silently change the saved numerical chart".into());
        }
        report["resumed_from"] = json!(path);
        report["resume_native_from"] = json!(saved.occurrences());
        report["exposure"] = json!(app.exposure);
        report["fractional_bits"] = json!(actual_grain);
        report["families_aperture"] = json!(app.records.len() + families);
        let operation = |session: &mut TextFieldSession<'_, '_>,
                         stream: &mut holonics_hna::HnaStream,
                         restored: Vec<NativeFieldSourceAnchor>,
                         _application: Vec<u8>| {
            if stream.state() != &holonics_hna::HnaStreamState::default() {
                return Err(exposure_error(
                    "batch driver cannot discard saved delivery state; use the saved-session API",
                ));
            }
            report["remount_native_deeds"] = json!(session.field().census().deed_launches);
            let mut anchors = app
                .anchors
                .into_iter()
                .zip(restored)
                .map(|(a, handle)| (a.family, (handle, a.occurrence)))
                .collect();
            // Inference-only resume never opens the original exposure source.
            let mut reader = if families > 0 {
                Some(ExposureReader::resume(app.cursor.clone()).map_err(exposure_error)?)
            } else {
                None
            };
            run_session(
                session,
                &mut reader,
                &mut app.cursor,
                &app.exposure,
                families,
                &mut app.records,
                &mut anchors,
                prompt.as_deref(),
                limit,
                text_receiver,
                inspect_all_currents,
                operative,
                contact_response.unwrap_or(app.contact_response),
                contact_realization.unwrap_or(app.contact_realization),
                contact_metric.unwrap_or(app.contact_metric),
                checkpoint.as_ref(),
                &mut report,
            )
        };
        match &history_archive {
            Some(path) => saved.with_session_archived(path, operation),
            None => saved.with_session(operation),
        }
    } else {
        let exposure = PathBuf::from(first);
        let grain = grain.ok_or("--fractional-bits required for fresh cultivation")?;
        let mut reader = Some(ExposureReader::open(&exposure)?);
        let mut cursor = reader.as_ref().unwrap().cursor();
        report["exposure"] = json!(exposure);
        report["fractional_bits"] = json!(grain);
        report["families_aperture"] = json!(families);
        let exposure = exposure.to_string_lossy().into_owned();
        with_text_field_chart(
            grain,
            material_source.unwrap_or(NativeMaterialTransportSource::OperativeContextual),
            material_target.unwrap_or(if material_source.is_some_and(|s|!matches!(s,NativeMaterialTransportSource::OperativeContextual|NativeMaterialTransportSource::OperativeBoundary|NativeMaterialTransportSource::OperativeLinear)){NativeMaterialTarget::DirectCurrent}else{NativeMaterialTarget::TensorProduct{factor_width:2}}),
            |field| {
                if let Some(path) = &history_archive {
                    field.enable_history_archive(path)?;
                }
                let mut session = TextFieldSession::on(field)?;
                if duplex.unwrap_or(false){session.enable_duplex()?;}
                let mut records = Vec::new();
                let mut anchors = AnchorMap::new();
                run_session(
                    &mut session,
                    &mut reader,
                    &mut cursor,
                    &exposure,
                    families,
                    &mut records,
                    &mut anchors,
                    prompt.as_deref(),
                    limit,
                    text_receiver,
                    inspect_all_currents,
                    operative,
                    contact_response.unwrap_or(false),
                    contact_realization.unwrap_or(NativeContactRealization::DyadicDeposit),
                    contact_metric.unwrap_or(NativeMaterialPullbackMetric::SquaredCurrent),
                    checkpoint.as_ref(),
                    &mut report,
                )
            },
        )
    };
    report["native_error"] = json!(native_result.as_ref().err().map(ToString::to_string));
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
        "development_error":report["development_error"],"model_persisted":report["model_persisted"],
        "checkpoint":report["checkpoint"],"checkpoint_error":report["checkpoint_error"]})
    );
    native_result?;
    for key in ["development_error", "prompt_error", "checkpoint_error"] {
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
