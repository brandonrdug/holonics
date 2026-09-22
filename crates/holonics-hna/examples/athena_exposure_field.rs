//! Walk the private conversation exposure into the constituted field session.
//!
//! One development frame supplies the held request positions; the declared aperture leaves the
//! response extent free; the recorded responding occurrence arrives later as an observed
//! comparison, never as gold. Source position and trained state are published together (AC3):
//! a frame is acknowledged only after its native use, and the cursor is attached to the same
//! atomic checkpoint file as the model.
//!
//! Public reports contain counts, declared refusal labels and timings. A caller may explicitly
//! request a new private diagnostic file for a native failure; that file can quote source
//! material and is created with owner-only permissions. Reports never include its contents.
use holonics_hna::{
    HnaStreamState,
    alpha::exposure::{
        ExposureError, ExposureFamily, ExposureOccurrence, ExposureReader, ExteriorReturnObserver,
    },
    native::{
        ExposureAperture, FieldSectionRequest, FieldSessionSpec, FieldSourceChart, FieldTextCodec,
        NativeFieldSavedSession, NativeFieldSession, with_field_session,
    },
};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

/// Every outcome this driver can report. A native refusal is counted, never quoted.
const LABELS: [&str; 15] = [
    "paired-and-applied",
    "outside-development",
    "not-human-authored",
    "no-visible-text",
    "request-over-aperture",
    "context-unavailable",
    "bridge-refused",
    "native-request-refused",
    "native-observation-refused",
    "unpaired-request-released",
    "response-under-aperture",
    "response-aperture-boundary",
    "response-role-refused",
    "response-target-refused",
    "response-unpaired",
];

struct Options {
    exposure: Option<PathBuf>,
    resume: Option<PathBuf>,
    checkpoint: PathBuf,
    spec: Option<PathBuf>,
    frames: u64,
    aperture: ExposureAperture,
    step_bits: u32,
    report: Option<PathBuf>,
    private_diagnostic: Option<PathBuf>,
    /// New JSONL file of exterior return readings (bits, octets, seconds; counts only).
    readings: Option<PathBuf>,
}

fn options() -> Result<Options, String> {
    let mut args = std::env::args().skip(1);
    let mut exposure = None;
    let mut resume = None;
    let mut checkpoint = None;
    let mut spec = None;
    let mut frames = None;
    let mut request_bytes = None;
    let mut response_symbols = None;
    let mut context_bytes = 0;
    let mut step_bits = 1;
    let mut report = None;
    let mut private_diagnostic = None;
    let mut readings = None;
    let value = |args: &mut dyn Iterator<Item = String>, name: &str| {
        args.next().ok_or_else(|| format!("missing {name}"))
    };
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--exposure" => exposure = Some(PathBuf::from(value(&mut args, "exposure wire")?)),
            "--resume" => resume = Some(PathBuf::from(value(&mut args, "saved session")?)),
            "--checkpoint" => checkpoint = Some(PathBuf::from(value(&mut args, "checkpoint")?)),
            "--spec" => spec = Some(PathBuf::from(value(&mut args, "field spec")?)),
            "--frames" => {
                frames = Some(
                    value(&mut args, "frame budget")?
                        .parse::<u64>()
                        .map_err(|e| e.to_string())?,
                )
            }
            "--request-bytes" => {
                request_bytes = Some(
                    value(&mut args, "request byte aperture")?
                        .parse::<usize>()
                        .map_err(|e| e.to_string())?,
                )
            }
            "--response-symbols" => {
                response_symbols = Some(
                    value(&mut args, "response symbol extent")?
                        .parse::<usize>()
                        .map_err(|e| e.to_string())?,
                )
            }
            "--context-bytes" => {
                context_bytes = value(&mut args, "context byte aperture")?
                    .parse::<usize>()
                    .map_err(|e| e.to_string())?
            }
            "--step-bits" => {
                step_bits = value(&mut args, "step bits")?
                    .parse::<u32>()
                    .map_err(|e| e.to_string())?
            }
            "--report" => report = Some(PathBuf::from(value(&mut args, "report path")?)),
            "--readings" => readings = Some(PathBuf::from(value(&mut args, "readings path")?)),
            "--private-diagnostic" => {
                private_diagnostic =
                    Some(PathBuf::from(value(&mut args, "private diagnostic path")?))
            }
            _ => return Err(format!("unknown option {arg}")),
        }
    }
    Ok(Options {
        exposure,
        resume,
        checkpoint: checkpoint.ok_or(
            "usage: athena_exposure_field (--exposure WIRE --spec SPEC | --resume SESSION) \
             --checkpoint OUT --frames N --request-bytes N --response-symbols N \
             [--context-bytes N] [--step-bits N] [--report PATH] [--readings PATH]",
        )?,
        spec,
        frames: frames.ok_or("a frame budget must be declared with --frames")?,
        aperture: ExposureAperture {
            request_bytes: request_bytes
                .ok_or("a request byte aperture must be declared with --request-bytes")?,
            response_symbols: response_symbols
                .ok_or("a free response extent must be declared with --response-symbols")?,
            context_bytes,
        },
        step_bits,
        report,
        private_diagnostic,
        readings,
    })
}

fn private_failure(options: &Options, error: &impl std::fmt::Display) -> std::io::Result<()> {
    let Some(path) = &options.private_diagnostic else {
        return Ok(());
    };
    let mut create = std::fs::OpenOptions::new();
    create.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        create.mode(0o600);
    }
    writeln!(create.open(path)?, "{error}")
}

/// The held request text and its recorded response share one section: the response prefix is
/// taken at exactly the declared free extent, at a character boundary, or the pair is refused.
fn target(
    spec: &FieldSessionSpec,
    response_symbols: usize,
    request: &str,
    response: &ExposureOccurrence,
) -> Result<String, &'static str> {
    let parts = response
        .development_parts()
        .map_err(|_| "outside-development")?;
    let mut text = String::new();
    for part in parts {
        text.push_str(part.text.as_deref().ok_or("no-visible-text")?);
    }
    if matches!(
        spec.source_chart,
        FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
    ) {
        if spec.codec != FieldTextCodec::UnicodeScalars {
            return Err("incident-codec-mismatch");
        }
        if text.chars().count() > response_symbols {
            return Err("response-over-aperture");
        }
        return Ok(text);
    }
    let response = match spec.codec {
        FieldTextCodec::Utf8Nibbles => {
            if response_symbols % 2 != 0 {
                return Err("response-aperture-boundary");
            }
            let bytes = response_symbols / 2;
            if text.len() < bytes {
                return Err("response-under-aperture");
            }
            if !text.is_char_boundary(bytes) {
                return Err("response-aperture-boundary");
            }
            text[..bytes].to_owned()
        }
        FieldTextCodec::UnicodeScalars => {
            let response: String = text.chars().take(response_symbols).collect();
            if response.chars().count() != response_symbols {
                return Err("response-under-aperture");
            }
            response
        }
        FieldTextCodec::WhitespaceWords => {
            let words: Vec<&str> = text.split_whitespace().take(response_symbols).collect();
            if words.len() != response_symbols {
                return Err("response-under-aperture");
            }
            words.join(" ")
        }
    };
    Ok(match spec.codec {
        FieldTextCodec::WhitespaceWords if request.is_empty() => response,
        FieldTextCodec::WhitespaceWords => format!("{request} {response}"),
        _ => format!("{request}{response}"),
    })
}

#[derive(Clone)]
struct Pending {
    family: ExposureFamily,
    request_events: Vec<u64>,
    comparison: u64,
    request: String,
    response_symbols: usize,
}

struct Walk {
    counts: BTreeMap<&'static str, u64>,
    generation_us: Vec<u128>,
    update_us: Vec<u128>,
    frames: u64,
    acknowledged: u64,
    held_symbols: u64,
    released_on_open: usize,
    retained_on_open: usize,
    context_index_entries: u64,
    context_index_scan_octets: u64,
    context_lookup_frames: u64,
    context_lookup_octets: u64,
    /// Exterior observer of the generator chart's returns; never enters the session.
    observer: ExteriorReturnObserver,
    readings: Vec<Value>,
}

impl Walk {
    fn count(&mut self, label: &'static str) {
        *self.counts.entry(label).or_default() += 1;
    }
}

fn quantile(values: &mut Vec<u128>, fraction: f64) -> Option<u128> {
    if values.is_empty() {
        return None;
    }
    values.sort_unstable();
    let at = ((values.len() as f64 - 1.0) * fraction).round() as usize;
    Some(values[at])
}

fn walk(
    session: &mut NativeFieldSession<'_>,
    reader: &mut ExposureReader,
    options: &Options,
    state: &mut Walk,
) -> Result<(), Box<dyn std::error::Error>> {
    let spec = session.spec().clone();
    let manifest = reader.manifest().clone();
    let retained_ids = session.retained_shared_comparisons();
    state.released_on_open = 0;
    state.retained_on_open = retained_ids.len();
    let mut pending: Vec<Pending> = session
        .retained_exposure_pairings()
        .into_iter()
        .map(|(comparison, pairing)| Pending {
            family: pairing.family,
            request_events: pairing.request_events,
            comparison,
            request: pairing.request_text,
            response_symbols: pairing.response_symbols,
        })
        .collect();
    session.attach_exposure_cursor(reader.cursor());
    while state.frames < options.frames {
        let Some(frame) = reader.peek()? else { break };
        let frame = frame.clone();
        // Persist the producing cut before any bridge/native operation can refuse.  A first
        // request failure must remain resumable from this frame rather than losing its cursor.
        session.attach_exposure_cursor(reader.cursor());
        state.frames += 1;
        // A recorded partner can arrive after intervening occurrences. Keep the source frame
        // pending until its event coordinate and family identify the retained producing cut.
        let partner = match frame.recorded_comparison_request_targets() {
            Ok(Some((family, aliases))) => {
                if frame
                    .shared_author_class()
                    .map_or(true, |role| role != "agent-visible")
                {
                    state.count("response-role-refused");
                    break;
                }
                Some((family, aliases))
            }
            Ok(None) => None,
            Err(_) => {
                state.count("response-target-refused");
                break;
            }
        };
        if let Some((partner_family, partner_events)) = partner {
            if let Some(index) = pending.iter().position(|held| {
                held.family == partner_family
                    && held
                        .request_events
                        .iter()
                        .any(|event| partner_events.contains(event))
            }) {
                let held = pending[index].clone();
                let text = target(&spec, held.response_symbols, &held.request, &frame);
                match text {
                    Ok(text) => {
                        if matches!(
                            spec.source_chart,
                            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
                        ) {
                            // Class admission is an explicit development-source operation. A
                            // later comparison uses its frozen decoder or an explicit retro face.
                            session.admit_incident_development_occurrence(&frame)?;
                        }
                        let update_start = Instant::now();
                        let observed = if options.readings.is_some()
                            && state.observer.requests.contains_key(&held.comparison)
                        {
                            session
                                .read_return(
                                    held.comparison,
                                    &text,
                                    options.step_bits,
                                    &mut state.observer,
                                )
                                .map(|(value, reading)| {
                                    // Counts, bits, octets and seconds only; no source text.
                                    state.readings.push(json!({
                                        "frame": state.frames,
                                        "reading": reading,
                                    }));
                                    value
                                })
                        } else {
                            session.observe(held.comparison, &text, options.step_bits)
                        };
                        match observed {
                            Ok(_) => {
                                state.update_us.push(update_start.elapsed().as_micros());
                                state.count("paired-and-applied");
                                pending.remove(index);
                                reader.acknowledge(frame.sequence)?;
                                state.acknowledged += 1;
                                session.attach_exposure_cursor(reader.cursor());
                                continue;
                            }
                            Err(error) => {
                                if private_failure(options, &error).is_err() {
                                    eprintln!(
                                        "private diagnostic write failed; source remains retryable"
                                    );
                                }
                                state.count("native-observation-refused");
                                break;
                            }
                        }
                    }
                    Err(label) => {
                        state.count(label);
                        break;
                    }
                }
            }
            state.count("response-unpaired");
            if pending.iter().any(|held| held.family == partner_family) {
                // A retained producing family exists, but this response's event alias does not
                // identify it. Keep the response and the retained comparison retryable.
                break;
            }
            // This is a legitimate response for a request that was skipped or never retained in
            // this bounded walk. It cannot affect the field, so consume only this occurrence and
            // continue looking for later source frames.
            reader.acknowledge(frame.sequence)?;
            state.acknowledged += 1;
            session.attach_exposure_cursor(reader.cursor());
            continue;
        }
        // A held request position takes development-partition, human-authored material only.
        // Every other admission gate lives in the bridge; this counts what it refuses.
        // Build the source index only for an actually admissible request candidate. Response,
        // evaluation and role-refused frames remain explicit bridge outcomes without paying a
        // context lookup that cannot be consumed.
        let context_owned = match (
            frame.development_parts().is_ok(),
            frame
                .shared_author_class()
                .is_ok_and(|role| role == "human"),
        ) {
            (true, true) => reader.recorded_context(&frame, options.aperture.context_bytes),
            _ => Ok(Vec::new()),
        };
        let context_owned = match context_owned {
            Ok(context) => context,
            Err(ExposureError::Open(_)) => {
                state.count("context-unavailable");
                reader.acknowledge(frame.sequence)?;
                state.acknowledged += 1;
                session.attach_exposure_cursor(reader.cursor());
                continue;
            }
            Err(_) => {
                state.count("context-unavailable");
                break;
            }
        };
        let context = context_owned.iter().collect::<Vec<_>>();
        if matches!(
            spec.source_chart,
            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
        ) && frame.development_parts().is_ok()
        {
            let mut texts = Vec::new();
            for occurrence in context.iter().copied().chain(std::iter::once(&frame)) {
                for part in occurrence.development_parts()? {
                    if let Some(text) = &part.text {
                        texts.push(text.clone());
                    }
                }
            }
            session.admit_incident_source_texts(&texts)?;
        }
        let bridged = FieldSectionRequest::from_exposures(
            session.spec(),
            &options.aperture,
            &manifest,
            &frame,
            &context,
            matches!(
                spec.source_chart,
                FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
            ),
            true,
        );
        let request = match bridged {
            Ok(request) => request,
            Err(_) => {
                state.count(match frame.development_parts() {
                    Err(_) => "outside-development",
                    Ok(parts) if parts.iter().any(|p| p.text.is_none()) => "no-visible-text",
                    Ok(parts) => {
                        if frame
                            .shared_author_class()
                            .is_ok_and(|role| role != "human")
                        {
                            "not-human-authored"
                        } else if parts
                            .iter()
                            .filter_map(|p| p.text.as_ref())
                            .map(String::len)
                            .sum::<usize>()
                            > options.aperture.request_bytes
                        {
                            "request-over-aperture"
                        } else if frame.shared_prior_parent().is_err() {
                            "context-unavailable"
                        } else {
                            "bridge-refused"
                        }
                    }
                });
                reader.acknowledge(frame.sequence)?;
                state.acknowledged += 1;
                session.attach_exposure_cursor(reader.cursor());
                continue;
            }
        };
        let held = request
            .partial
            .as_ref()
            .map(|parts| parts.iter().filter(|p| p.is_some()).count())
            .unwrap_or_default();
        let text = frame
            .development_parts()?
            .iter()
            .filter_map(|p| p.text.clone())
            .collect::<String>();
        let start = Instant::now();
        let requested = if options.readings.is_some()
            && spec.source_chart == FieldSourceChart::GeneratorMachine
        {
            session.measured_request(&request, &mut state.observer)
        } else {
            session.request(&request)
        };
        match requested {
            Ok(value) => {
                state.generation_us.push(
                    value["generation_us"]
                        .as_u64()
                        .map_or(start.elapsed().as_micros(), u128::from),
                );
                state.held_symbols += held as u64;
                if let Some(comparison) = value["comparison"].as_u64() {
                    let request_events = frame
                        .views
                        .iter()
                        .map(|view| view.event)
                        .collect::<Vec<_>>();
                    if request_events.is_empty() {
                        return Err("request frame has no event view".into());
                    }
                    session.attach_exposure_pairing(
                        comparison,
                        frame.family.clone(),
                        request_events.clone(),
                        text.clone(),
                    )?;
                    pending.push(Pending {
                        family: frame.family.clone(),
                        request_events,
                        comparison,
                        request: text,
                        response_symbols: value["output_symbols"]
                            .as_u64()
                            .and_then(|extent| extent.checked_sub(held as u64))
                            .map_or(options.aperture.response_symbols, |value| value as usize),
                    });
                }
            }
            Err(error) => {
                if private_failure(options, &error).is_err() {
                    eprintln!("private diagnostic write failed; source remains retryable");
                }
                state.count("native-request-refused");
                break;
            }
        }
        // Complete native use of this frame's own material: the held positions were consumed.
        reader.acknowledge(frame.sequence)?;
        state.acknowledged += 1;
        session.attach_exposure_cursor(reader.cursor());
    }
    let context_stats = reader.context_stats();
    state.context_index_entries = context_stats.index_entries;
    state.context_index_scan_octets = context_stats.index_scan_octets;
    state.context_lookup_frames = context_stats.lookup_frames;
    state.context_lookup_octets = context_stats.lookup_octets;
    // Outstanding retained comparisons remain in the session rest and are retried by a later
    // process; dropping them would detach the source cursor from its producing cut.
    Ok(())
}

fn report(options: &Options, state: &mut Walk, wall: u128, anatomy: Value) -> Value {
    json!({
        "schema":"org.holonics.hna.exposure-field-driver.v1",
        "scope":"development exposure frames into one constituted field session; declared aperture, no message content",
        "frames_declared":options.frames,"frames_peeked":state.frames,"frames_acknowledged":state.acknowledged,
        "aperture":options.aperture,"step_bits":options.step_bits,
        "context_cache_budget_bytes":options.aperture.context_bytes,
        "context_source_lookup":{
            "index_entries":state.context_index_entries,
            "index_scan_octets":state.context_index_scan_octets,
            "lookup_frames":state.context_lookup_frames,
            "lookup_octets":state.context_lookup_octets,
            "index":"lazy metadata scan of the verified exposure wire; no native event history",
        },
        "held_request_symbols":state.held_symbols,
        "retained_released_at_open":state.released_on_open,
        "retained_pending_at_open":state.retained_on_open,
        "outcomes":LABELS.iter().map(|label|(*label,state.counts.get(label).copied().unwrap_or(0))).collect::<BTreeMap<_,_>>(),
        "generation_us":{"count":state.generation_us.len(),"median":quantile(&mut state.generation_us,0.5),"p95":quantile(&mut state.generation_us,0.95)},
        "update_us":{"count":state.update_us.len(),"median":quantile(&mut state.update_us,0.5),"p95":quantile(&mut state.update_us,0.95)},
        "wall_us":wall,
        "refusal_reasons":"declared driver labels; native refusal text is withheld because it can quote source material",
        "anatomy":anatomy,
        "return_readings":{
            "count":state.readings.len(),
            "source_cells":state.observer.source_cells_total,
            "source_bits":state.observer.source_bits_total,
            "exposure_symbols":state.observer.stream.symbols(),
            "exposure_order0_bits":state.observer.stream.order0_bits(),
            "exposure_order1_bits":state.observer.stream.order1_bits(),
            "committed_source_steps":state.observer.committed_source_steps,
            "scope":"exterior observer readings; one JSONL row per observed return in --readings",
        },
    })
}

fn publish_readings(options: &Options, state: &Walk) -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = &options.readings else {
        return Ok(());
    };
    let mut bytes = Vec::new();
    for reading in &state.readings {
        serde_json::to_writer(&mut bytes, reading)?;
        bytes.push(b'\n');
    }
    holonics_hna::publish_new(path, |out| out.write_all(&bytes))?;
    Ok(())
}

fn publish(options: &Options, value: &Value) -> Result<(), Box<dyn std::error::Error>> {
    let mut bytes = serde_json::to_vec(value)?;
    bytes.push(b'\n');
    println!("{}", String::from_utf8_lossy(&bytes).trim_end());
    if let Some(path) = &options.report {
        holonics_hna::publish_new(path, |out| out.write_all(&bytes))?;
    }
    Ok(())
}

fn spec_of(path: &Path) -> Result<FieldSessionSpec, Box<dyn std::error::Error>> {
    let spec: FieldSessionSpec = serde_json::from_reader(File::open(path)?)?;
    if !matches!(
        spec.source_chart,
        FieldSourceChart::SharedRegions
            | FieldSourceChart::GeometricRegions
            | FieldSourceChart::IncidentField
            | FieldSourceChart::GeneratorMachine
    ) {
        return Err(
            "this driver's held/free aperture requires the shared-regions source chart".into(),
        );
    }
    Ok(spec)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let options = options()?;
    let mut state = Walk {
        counts: BTreeMap::new(),
        generation_us: Vec::new(),
        update_us: Vec::new(),
        frames: 0,
        acknowledged: 0,
        held_symbols: 0,
        released_on_open: 0,
        retained_on_open: 0,
        context_index_entries: 0,
        context_index_scan_octets: 0,
        context_lookup_frames: 0,
        context_lookup_octets: 0,
        observer: ExteriorReturnObserver::default(),
        readings: Vec::new(),
    };
    let start = Instant::now();
    let anatomy = match (&options.resume, &options.exposure, &options.spec) {
        (Some(session), None, None) => {
            let saved = NativeFieldSavedSession::open(session)?;
            let cursor = saved
                .exposure_cursor()
                .cloned()
                .ok_or("the saved session carries no exposure cursor to resume")?;
            saved.with_session(|session, _| {
                let mut reader = ExposureReader::resume(cursor).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })?;
                walk(session, &mut reader, &options, &mut state).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })?;
                session.checkpoint(&options.checkpoint, &HnaStreamState::default())?;
                Ok(session.inspect())
            })?
        }
        (None, Some(wire), Some(path)) => {
            let spec = spec_of(path)?;
            let mut reader = ExposureReader::open(wire)?;
            with_field_session(&spec, |session| {
                walk(session, &mut reader, &options, &mut state).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })?;
                session.checkpoint(&options.checkpoint, &HnaStreamState::default())?;
                Ok(session.inspect())
            })?
        }
        _ => return Err("supply --exposure with --spec, or --resume alone".into()),
    };
    let value = report(&options, &mut state, start.elapsed().as_micros(), anatomy);
    publish_readings(&options, &state)?;
    publish(&options, &value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn response(text: &str) -> ExposureOccurrence {
        serde_json::from_value(json!({
            "schema": "holonics.conversation-exposure.v1",
            "kind": "occurrence-family",
            "sequence": 1,
            "position": {"first_source":1,"first_record":2,"first_event":2},
            "family": {"provider":"codex","record_group":"declared:reply"},
            "partition": "development",
            "partition_reasons": [],
            "conflicts": [],
            "views": [{
                "event":2,"source":1,"provider":"codex",
                "record":{"number":2,"byte_start":100,"byte_end":200},
                "timestamp":null,"normalized_timestamp":null,"native_id":"reply",
                "parent_id":null,"session_id":null,"branch_id":null,"workspace":null,
                "phase":null,"turn_id":null,"model":null,"author_class":"agent-visible",
                "record_kind":"message","flags":[],"provider_metadata":{},
                "previous_record":null,
                "visible_parts":[{"ordinal":0,"pointer":"/text","kind":"agent-text","text":text}],
                "nonvisible_part_references":[],"links":[]
            }]
        }))
        .unwrap()
    }

    #[test]
    fn response_target_uses_codec_symbol_units() {
        let unicode = FieldSessionSpec {
            symbols: vec!["é".into(), "x".into()],
            section_symbols: 8,
            context_symbols: 0,
            region_offsets: vec![0],
            source_chart: FieldSourceChart::SharedRegions,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 1,
        };
        assert_eq!(target(&unicode, 1, "q", &response("éx")).unwrap(), "qé");

        let words = FieldSessionSpec {
            codec: FieldTextCodec::WhitespaceWords,
            ..unicode.clone()
        };
        assert_eq!(
            target(&words, 2, "q", &response("one two three")).unwrap(),
            "q one two"
        );

        let nibbles = FieldSessionSpec {
            codec: FieldTextCodec::Utf8Nibbles,
            ..unicode
        };
        assert_eq!(target(&nibbles, 4, "q", &response("ABCD")).unwrap(), "qAB");
    }

    fn fixture_frame(sequence: u64, name: &str, role: &str, text: &str) -> Value {
        let mut frame = serde_json::to_value(response(text)).unwrap();
        frame["schema"] = json!(holonics_hna::alpha::exposure::EXPOSURE_SCHEMA);
        frame["sequence"] = json!(sequence);
        frame["family"]["record_group"] = json!(format!("declared:{name}"));
        let event = sequence * 10 + 1;
        frame["position"] = json!({"first_source":1,"first_record":event,"first_event":event});
        let v = &mut frame["views"][0];
        v["event"] = json!(event);
        v["record"] = json!({"number":event,"byte_start":event*100,"byte_end":event*100+50});
        v["native_id"] = json!(name);
        v["normalized_timestamp"] = json!(format!("2026-09-03T{sequence:02}:00:00.000000+00:00"));
        v["author_class"] = json!(role);
        v["visible_parts"][0]["kind"] = json!(if role == "human" {
            "human-text"
        } else {
            "agent-text"
        });
        frame
    }

    fn comparison(frame: &mut Value, alias: u64) {
        frame["views"][0]["links"] = json!([{
            "kind":"comparison-request", "evidence":"declared fixture source", "availability":"prior",
            "target_event":alias,"target":{"event":alias,"source":1,"provider":"codex",
                "record_group":"declared:request", "timestamp":null,"normalized_timestamp":"2026-09-03T00:00:00.000000+00:00"}
        }]);
    }

    fn stream(path: &Path, frames: &[Value]) {
        let manifest = json!({"schema":holonics_hna::alpha::exposure::EXPOSURE_SCHEMA,"kind":"manifest",
            "temporal_cut":"2026-09-04T00:00:00Z","temporal_cut_normalized":"2026-09-04T00:00:00.000000+00:00",
            "private_sources":[{"source":1,"provider":"codex","private_path":"fixture.jsonl",
                "captured_octets":10000,"records":100}],"visible_parts":{},"boundary":{}});
        let mut bytes = serde_json::to_vec(&manifest).unwrap();
        bytes.push(b'\n');
        for frame in frames {
            bytes.extend(serde_json::to_vec(frame).unwrap());
            bytes.push(b'\n');
        }
        std::fs::write(path, bytes).unwrap();
    }

    fn fixture_spec() -> FieldSessionSpec {
        FieldSessionSpec {
            symbols: vec!["a".into(), "b".into()],
            section_symbols: 8,
            context_symbols: 0,
            region_offsets: vec![0],
            source_chart: FieldSourceChart::SharedRegions,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        }
    }
    fn fixture_options(path: &Path, frames: u64) -> Options {
        Options {
            exposure: None,
            resume: None,
            checkpoint: path.to_owned(),
            spec: None,
            frames,
            aperture: ExposureAperture {
                request_bytes: 1,
                response_symbols: 1,
                context_bytes: 0,
            },
            step_bits: 1,
            report: None,
            private_diagnostic: None,
            readings: None,
        }
    }
    fn counters() -> Walk {
        Walk {
            counts: BTreeMap::new(),
            generation_us: vec![],
            update_us: vec![],
            frames: 0,
            acknowledged: 0,
            held_symbols: 0,
            released_on_open: 0,
            retained_on_open: 0,
            context_index_entries: 0,
            context_index_scan_octets: 0,
            context_lookup_frames: 0,
            context_lookup_octets: 0,
            observer: ExteriorReturnObserver::default(),
            readings: Vec::new(),
        }
    }
    fn app_error(error: Box<dyn std::error::Error>) -> holonics_hna::native::NativeSessionError {
        holonics_hna::native::NativeSessionError::Application(error.to_string())
    }

    #[test]
    fn context_aperture_is_explicit_and_reopened_lookup_uses_the_pinned_source() {
        let mut request: ExposureOccurrence =
            serde_json::from_value(fixture_frame(2, "child", "human", "a")).unwrap();
        let mut parent = fixture_frame(0, "request", "human", "b");
        comparison(&mut parent, 1);
        request.views[0].links =
            serde_json::from_value(parent["views"][0]["links"].clone()).unwrap();
        request.views[0].links[0].kind = "provider-parent".into();
        // The child's prior link targets this parent; the parent has no link to itself.
        parent["views"][0]["links"] = json!([]);
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("exposure.jsonl");
        let mut wire_parent = serde_json::to_value(&parent).unwrap();
        wire_parent["family"]["record_group"] = json!("declared:request");
        let mut wire_request = serde_json::to_value(&request).unwrap();
        wire_request["family"]["record_group"] = json!("declared:child");
        stream(
            &source,
            &[
                wire_parent,
                fixture_frame(1, "intervening", "human", "x"),
                wire_request,
            ],
        );
        let mut reader = ExposureReader::open(&source).unwrap();
        assert!(reader.recorded_context(&request, 0).unwrap().is_empty());
        reader.peek().unwrap();
        reader.acknowledge(0).unwrap();
        reader.peek().unwrap();
        reader.acknowledge(1).unwrap();
        let cursor = reader.cursor();
        let restored = reader.peek().unwrap().unwrap().clone();
        let context = reader.recorded_context(&restored, 4096).unwrap();
        assert_eq!(context.len(), 1);
        assert_eq!(context[0].family.record_group, "declared:request");
        drop(reader);
        let mut reopened = ExposureReader::resume(cursor).unwrap();
        let restored = reopened.peek().unwrap().unwrap().clone();
        let context = reopened.recorded_context(&restored, 4096).unwrap();
        assert_eq!(context.len(), 1);
        assert_eq!(reopened.context_stats().index_entries, 2);
    }

    #[test]
    #[ignore = "requires CUDA; actual delayed captured-event pairing, failed update and changed-aperture restart"]
    fn delayed_capture_alias_survives_restart_and_failed_update() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("exposure.jsonl");
        let checkpoint = dir.path().join("first.session");
        let retry = dir.path().join("retry.session");
        let mut request = fixture_frame(0, "request", "human", "a");
        let mut other = request["views"][0].clone();
        other["event"] = json!(2);
        other["record"] = json!({"number":2,"byte_start":200,"byte_end":250});
        request["views"].as_array_mut().unwrap().push(other);
        let mut answer = fixture_frame(2, "reply", "agent-visible", "b");
        comparison(&mut answer, 2);
        stream(
            &source,
            &[
                request,
                fixture_frame(1, "intervening", "agent-visible", "a"),
                answer,
            ],
        );
        with_field_session(&fixture_spec(), |session| {
            let mut reader = ExposureReader::open(&source).unwrap();
            let mut state = counters();
            walk(
                session,
                &mut reader,
                &fixture_options(&checkpoint, 2),
                &mut state,
            )
            .map_err(app_error)?;
            assert_eq!(state.acknowledged, 2);
            assert_eq!(
                session.retained_exposure_pairings()[0].1.request_events,
                vec![1, 2]
            );
            session.checkpoint(&checkpoint, &HnaStreamState::default())?;
            Ok(())
        })
        .unwrap();
        let saved = NativeFieldSavedSession::open(&checkpoint).unwrap();
        let cursor = saved.exposure_cursor().unwrap().clone();
        saved
            .with_session(|session, _| {
                let mut reader = ExposureReader::resume(cursor.clone()).unwrap();
                let mut options = fixture_options(&retry, 1);
                options.aperture.response_symbols = 2; // applies only to new requests
                options.step_bits = 121; // typed failure before the material commit
                // A diagnostic I/O failure must not discard the retryable source/model cut.
                options.private_diagnostic = Some(dir.path().to_owned());
                let mut state = counters();
                walk(session, &mut reader, &options, &mut state).map_err(app_error)?;
                assert_eq!(state.counts.get("native-observation-refused"), Some(&1));
                assert_eq!(reader.cursor(), cursor);
                assert_eq!(session.retained_shared_comparisons(), vec![0]);
                assert_eq!(session.inspect()["epoch"], 0);
                session.checkpoint(&retry, &HnaStreamState::default())?;
                Ok(())
            })
            .unwrap();
        let saved = NativeFieldSavedSession::open(&retry).unwrap();
        let cursor = saved.exposure_cursor().unwrap().clone();
        saved
            .with_session(|session, _| {
                let mut reader = ExposureReader::resume(cursor).unwrap();
                let mut options = fixture_options(&retry, 1);
                options.aperture.response_symbols = 2;
                let mut state = counters();
                walk(session, &mut reader, &options, &mut state).map_err(app_error)?;
                assert_eq!(state.counts.get("paired-and-applied"), Some(&1));
                assert_eq!(state.acknowledged, 1);
                assert!(session.retained_shared_comparisons().is_empty());
                assert_eq!(session.inspect()["epoch"], 1);
                assert!(reader.peek().unwrap().is_none());
                Ok(())
            })
            .unwrap();
    }

    #[test]
    #[ignore = "requires CUDA; a skipped request's response cannot stall later admitted material"]
    fn skipped_request_response_does_not_block_a_later_request() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("exposure.jsonl");
        let mut answer = fixture_frame(1, "reply", "agent-visible", "b");
        comparison(&mut answer, 1);
        stream(
            &source,
            &[
                fixture_frame(0, "request", "human", "aa"),
                answer,
                fixture_frame(2, "next", "human", "b"),
            ],
        );
        with_field_session(&fixture_spec(), |session| {
            let mut reader = ExposureReader::open(&source).unwrap();
            let mut state = counters();
            walk(
                session,
                &mut reader,
                &fixture_options(&source, 3),
                &mut state,
            )
            .map_err(app_error)?;
            assert_eq!(state.acknowledged, 3);
            assert_eq!(state.counts.get("request-over-aperture"), Some(&1));
            assert_eq!(state.counts.get("response-unpaired"), Some(&1));
            assert_eq!(
                session.retained_exposure_pairings()[0]
                    .1
                    .family
                    .record_group,
                "declared:next"
            );
            Ok(())
        })
        .unwrap();
    }
}
