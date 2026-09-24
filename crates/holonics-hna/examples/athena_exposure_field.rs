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

/// The driver's own record of a held request. On the generator chart the session keeps only
/// digests of it; the driver persists these (private sidecar beside its checkpoint) and the
/// session confirms them on resume.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
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
    /// Held requests at the end of the walk (the driver's own pairing state), and those read
    /// back from the resumed checkpoint's sidecar.
    held: Vec<Pending>,
    resumed: Vec<Pending>,
}

/// The driver's private pairing sidecar of a checkpoint: request text and events it owns.
fn pairing_sidecar(checkpoint: &Path) -> PathBuf {
    let mut path = checkpoint.as_os_str().to_owned();
    path.push(".pairings.json");
    PathBuf::from(path)
}

fn write_pairing_sidecar(
    checkpoint: &Path,
    held: &[Pending],
) -> Result<(), Box<dyn std::error::Error>> {
    let bytes = serde_json::to_vec(held)?;
    let mut create = std::fs::OpenOptions::new();
    create.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        create.mode(0o600);
    }
    create
        .open(pairing_sidecar(checkpoint))?
        .write_all(&bytes)?;
    Ok(())
}

fn read_pairing_sidecar(checkpoint: &Path) -> Result<Vec<Pending>, Box<dyn std::error::Error>> {
    match std::fs::read(pairing_sidecar(checkpoint)) {
        Ok(bytes) => Ok(serde_json::from_slice(&bytes)?),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(Vec::new()),
        Err(error) => Err(error.into()),
    }
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
    // Generator chart: the session holds digests only; confirm the driver's own records.
    for (comparison, family, response_symbols) in session.retained_generator_exposures() {
        let Some(held) = state
            .resumed
            .iter()
            .find(|held| held.comparison == comparison)
            .cloned()
        else {
            // No driver record can pair this comparison: release it rather than hold it forever.
            session.release(comparison)?;
            state.released_on_open += 1;
            state.count("unpaired-request-released");
            continue;
        };
        let confirmed = session.confirm_exposure_pairing(
            comparison,
            family,
            held.request_events.clone(),
            held.request.clone(),
        )?;
        if confirmed.response_symbols != response_symbols {
            return Err("confirmed generator pairing response extent".into());
        }
        pending.push(Pending {
            family: confirmed.family,
            request_events: confirmed.request_events,
            comparison,
            request: confirmed.request_text,
            response_symbols,
        });
    }
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
    state.held = pending;
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
        held: Vec::new(),
        resumed: Vec::new(),
    };
    let start = Instant::now();
    let anatomy = match (&options.resume, &options.exposure, &options.spec) {
        (Some(session), None, None) => {
            state.resumed = read_pairing_sidecar(session)?;
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
                write_pairing_sidecar(&options.checkpoint, &state.held).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })?;
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
                write_pairing_sidecar(&options.checkpoint, &state.held).map_err(|error| {
                    holonics_hna::native::NativeSessionError::Application(error.to_string())
                })?;
                Ok(session.inspect())
            })?
        }
        _ => return Err("supply --exposure with --spec, or --resume alone".into()),
    };
    let value = report(&options, &mut state, start.elapsed().as_micros(), anatomy);
    publish_readings(&options, &state)?;
    publish(&options, &value)
}
