//! Walk the private conversation exposure into the constituted field session.
//!
//! One development frame supplies the held request positions; the declared aperture leaves the
//! response extent free; the recorded responding occurrence arrives later as an observed
//! comparison, never as gold. Source position and trained state are published together (AC3):
//! a frame is acknowledged only after its native use, and the cursor is attached to the same
//! atomic checkpoint file as the model.
//!
//! This driver prints counts, declared refusal labels and timings only. It never prints, logs
//! or persists message text, and it never echoes a native refusal string, because a refusal can
//! quote source material. Refusal reasons are this driver's own fixed vocabulary.
use holonics_hna::{
    alpha::exposure::{ExposureFamily, ExposureOccurrence, ExposureReader},
    native::{
        with_field_session, ExposureAperture, FieldSectionRequest, FieldSessionSpec,
        FieldSourceChart, FieldTextCodec, NativeFieldSavedSession, NativeFieldSession,
    },
    HnaStreamState,
};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

/// Every outcome this driver can report. A native refusal is counted, never quoted.
const LABELS: [&str; 12] = [
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
            _ => return Err(format!("unknown option {arg}")),
        }
    }
    Ok(Options {
        exposure,
        resume,
        checkpoint: checkpoint.ok_or(
            "usage: athena_exposure_field (--exposure WIRE --spec SPEC | --resume SESSION) \
             --checkpoint OUT --frames N --request-bytes N --response-symbols N \
             [--context-bytes N] [--step-bits N] [--report PATH]",
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
    })
}

/// The held request text and its recorded response share one section: the response prefix is
/// taken at exactly the declared free extent, at a character boundary, or the pair is refused.
fn target(
    spec: &FieldSessionSpec,
    aperture: &ExposureAperture,
    request: &str,
    response: &ExposureOccurrence,
) -> Result<String, &'static str> {
    let per_byte = usize::from(spec.codec == FieldTextCodec::Utf8Nibbles) + 1;
    if aperture.response_symbols % per_byte != 0 {
        return Err("response-aperture-boundary");
    }
    let bytes = aperture.response_symbols / per_byte;
    let parts = response
        .development_parts()
        .map_err(|_| "outside-development")?;
    let mut text = String::new();
    for part in parts {
        text.push_str(part.text.as_deref().ok_or("no-visible-text")?);
    }
    if text.len() < bytes {
        return Err("response-under-aperture");
    }
    if !text.is_char_boundary(bytes) {
        return Err("response-aperture-boundary");
    }
    Ok(format!("{request}{}", &text[..bytes]))
}

struct Pending {
    family: ExposureFamily,
    comparison: u64,
    request: String,
}

struct Walk {
    counts: BTreeMap<&'static str, u64>,
    generation_us: Vec<u128>,
    update_us: Vec<u128>,
    frames: u64,
    acknowledged: u64,
    held_symbols: u64,
    released_on_open: usize,
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
    // A retained comparison outstanding at reopen cannot be attributed to a recorded partner by
    // this driver, so it is released and counted rather than applied to the wrong source.
    state.released_on_open = session.retained_shared_comparisons().len();
    for id in session.retained_shared_comparisons() {
        session.release(id)?;
    }
    let mut pending: Option<Pending> = None;
    while state.frames < options.frames {
        let Some(frame) = reader.peek()? else { break };
        let frame = frame.clone();
        state.frames += 1;
        // A recorded partner arrives as an observed comparison for the request just retained.
        if let Some(held) = pending.take() {
            let partner = frame.recorded_comparison_request().ok().flatten();
            let label = if partner.as_ref() != Some(&held.family) {
                Some("unpaired-request-released")
            } else if frame.shared_author_class().is_ok_and(|role| role != "agent-visible") {
                Some("unpaired-request-released")
            } else {
                match target(&spec, &options.aperture, &held.request, &frame) {
                    Ok(text) => {
                        let start = Instant::now();
                        match session.observe(held.comparison, &text, options.step_bits) {
                            Ok(_) => {
                                state.update_us.push(start.elapsed().as_micros());
                                state.count("paired-and-applied");
                                reader.acknowledge(frame.sequence)?;
                                state.acknowledged += 1;
                                session.attach_exposure_cursor(reader.cursor());
                                continue;
                            }
                            Err(_) => Some("native-observation-refused"),
                        }
                    }
                    Err(label) => Some(label),
                }
            };
            if let Some(label) = label {
                session.release(held.comparison)?;
                state.count(label);
            }
        }
        // A held request position takes development-partition, human-authored material only.
        // Every other admission gate lives in the bridge; this counts what it refuses.
        let bridged = FieldSectionRequest::from_exposures(
            &spec,
            &options.aperture,
            &manifest,
            &frame,
            &[],
            false,
            true,
        );
        let request = match bridged {
            Ok(request) => request,
            Err(_) => {
                state.count(match frame.development_parts() {
                    Err(_) => "outside-development",
                    Ok(parts) if parts.iter().any(|p| p.text.is_none()) => "no-visible-text",
                    Ok(parts) => {
                        if frame.shared_author_class().is_ok_and(|role| role != "human") {
                            "not-human-authored"
                        } else if parts.iter().filter_map(|p| p.text.as_ref()).map(String::len).sum::<usize>()
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
        match session.request(&request) {
            Ok(value) => {
                state.generation_us.push(
                    value["generation_us"]
                        .as_u64()
                        .map_or(start.elapsed().as_micros(), u128::from),
                );
                state.held_symbols += held as u64;
                pending = value["comparison"].as_u64().map(|comparison| Pending {
                    family: frame.family.clone(),
                    comparison,
                    request: text,
                });
            }
            Err(_) => state.count("native-request-refused"),
        }
        // Complete native use of this frame's own material: the held positions were consumed.
        reader.acknowledge(frame.sequence)?;
        state.acknowledged += 1;
        session.attach_exposure_cursor(reader.cursor());
    }
    // Never checkpoint with an outstanding retained comparison this driver alone can attribute.
    if let Some(held) = pending {
        session.release(held.comparison)?;
        state.count("unpaired-request-released");
    }
    Ok(())
}

fn report(options: &Options, state: &mut Walk, wall: u128, anatomy: Value) -> Value {
    json!({
        "schema":"org.holonics.hna.exposure-field-driver.v1",
        "scope":"development exposure frames into one constituted field session; declared aperture, no message content",
        "frames_declared":options.frames,"frames_peeked":state.frames,"frames_acknowledged":state.acknowledged,
        "aperture":options.aperture,"step_bits":options.step_bits,
        "held_request_symbols":state.held_symbols,
        "retained_released_at_open":state.released_on_open,
        "outcomes":LABELS.iter().map(|label|(*label,state.counts.get(label).copied().unwrap_or(0))).collect::<BTreeMap<_,_>>(),
        "generation_us":{"count":state.generation_us.len(),"median":quantile(&mut state.generation_us,0.5),"p95":quantile(&mut state.generation_us,0.95)},
        "update_us":{"count":state.update_us.len(),"median":quantile(&mut state.update_us,0.5),"p95":quantile(&mut state.update_us,0.95)},
        "wall_us":wall,
        "refusal_reasons":"declared driver labels; native refusal text is withheld because it can quote source material",
        "anatomy":anatomy,
    })
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
    if spec.source_chart != FieldSourceChart::SharedRegions {
        return Err("this driver's held/free aperture requires the shared-regions source chart".into());
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
    publish(&options, &value)
}
