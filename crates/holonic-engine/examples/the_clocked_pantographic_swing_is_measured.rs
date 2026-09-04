//! Measure one exact receiver body through CPU and CUDA apparatus charts.
//!
//! This is a narrow apparatus driver.  It does not define holonic time, select a carrier from
//! elapsed time, or add a semantic execution owner.  The engine already owns the exact CPU and
//! CUDA receiver laws.  This driver retains their common receiver face beside two integer clock
//! sections:
//!
//! * the invariant-TSC counter local to the observation thread, including the RDTSCP auxiliary
//!   address before and after the deed; and
//! * Linux `CLOCK_MONOTONIC_RAW`, kept as an exterior calibration chart.
//!
//! Every scale is an integer pair.  No floating-point duration or fitted cost law is produced.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use holonic_engine::{
    ApertureExecutionBackend, CarrierWork, ContinuousPresentation, CpuExecutionReceipt,
    CpuExecutor, CudaApertureExecutor, CudaApertureReceipt, DeclaredCarrierMetric, DisplayFrame,
    HomogeneousConic, PresentationBoundary, PresentedPrimitive, ProjectedConic, ProjectiveDepthLaw,
    ProjectiveLine2, ReceiverApertureTrace, ReceiverPrimitive, ReceiverPrimitiveId,
    TerminalMatrixSpec, trace_receivers_aperture_with_cpu,
};
use num_bigint::BigUint;
use relational_geometry::{Rat, ReceiverId, integer};
use serde::Serialize;
use sha2::{Digest, Sha256};

const SCHEMA: &str = "holonic-engine.clocked-pantographic-swing-measurement.v1";
const DEFAULT_WORKERS: &[usize] = &[1, 2, 4, 8, 12, 24];

#[derive(Clone, Debug)]
struct Config {
    cpu_only: bool,
    workers: Vec<usize>,
    repetitions: usize,
    warmups: usize,
    population: usize,
    width: u32,
    height: u32,
    output: PathBuf,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct ExactRatio {
    numerator: u128,
    denominator: u128,
}

#[derive(Clone, Copy, Debug)]
struct CounterEndpoint {
    tsc: u64,
    tsc_aux: u32,
    monotonic_raw_ns: u128,
}

#[derive(Clone, Debug, Serialize)]
struct ClockSection {
    tsc_clock_domain: &'static str,
    tsc_source: u64,
    tsc_target: u64,
    tsc_ticks: u64,
    tsc_aux_source: u32,
    tsc_aux_target: u32,
    observation_thread_migrated: bool,
    exterior_clock_domain: &'static str,
    monotonic_raw_source_ns: u128,
    monotonic_raw_target_ns: u128,
    monotonic_raw_elapsed_ns: u128,
    tsc_ticks_per_exterior_nanosecond: ExactRatio,
}

#[derive(Clone, Debug, Serialize)]
struct CpuExecutionRecord {
    schema: String,
    mode: String,
    tasks: String,
    worker_limit: String,
    workers_used: String,
    batches: String,
    joins: String,
}

#[derive(Clone, Debug, Serialize)]
struct CarrierWorkRecord {
    cpu_evaluations: String,
    device_evaluations: String,
    transfer_bytes: String,
    intermediate_bits: String,
}

#[derive(Clone, Debug, Serialize)]
struct CudaApertureRecord {
    schema: String,
    device: String,
    receivers: String,
    selected_primitives: String,
    device_primitives: String,
    conics: String,
    segments: String,
    cpu_primitives: String,
    cpu_conics: String,
    cpu_linear_primitives: String,
    aperture_members: String,
    device_output_bytes: String,
    device_threads: String,
    exact_support_evaluations: String,
    device_exact_support_evaluations: String,
    cpu_exact_support_evaluations: String,
    intermediate_bits: String,
    device_arithmetic: String,
    cpu_workers: String,
    selection_pack_nanoseconds: u128,
    device_prepare_nanoseconds: u128,
    device_execute_nanoseconds: u128,
    device_download_nanoseconds: u128,
    device_decode_nanoseconds: u128,
    cpu_trace_nanoseconds: u128,
    cpu_merge_nanoseconds: u128,
    wall_nanoseconds: u128,
    cpu_parity: bool,
    execution_backend: String,
    admission_candidate_nanoseconds: u128,
    admission_authority_nanoseconds: u128,
    admission: String,
    work_ordering: String,
    authority_work: CarrierWorkRecord,
    candidate_work: CarrierWorkRecord,
    display_frame: String,
}

#[derive(Clone, Debug, Serialize)]
struct CpuSample {
    worker_aperture: usize,
    repetition: usize,
    execution: CpuExecutionRecord,
    clock: ClockSection,
    support_face_sha256: String,
    agrees_with_first_cpu_face: bool,
}

#[derive(Clone, Debug, Serialize)]
struct GpuAdmissionSample {
    receipt: CudaApertureRecord,
    exact_work_by_semantic_occurrence: Vec<EventWorkRecord>,
    support_face_sha256: String,
    agrees_with_cpu_face: bool,
}

#[derive(Clone, Debug, Serialize)]
struct GpuSample {
    repetition: usize,
    receipt: CudaApertureRecord,
    exact_work_by_semantic_occurrence: Vec<EventWorkRecord>,
    clock: ClockSection,
    support_face_sha256: String,
    agrees_with_cpu_face: bool,
}

#[derive(Clone, Debug, Serialize)]
struct WorkerScale {
    worker_aperture: usize,
    median_tsc_ticks: u128,
    median_monotonic_raw_ns: u128,
    tsc_scale_from_one_worker: ExactRatio,
    exterior_scale_from_one_worker: ExactRatio,
}

#[derive(Clone, Debug, Serialize)]
struct ApparatusSnapshot {
    unix_epoch_ns: u128,
    process_id: u32,
    executable_sha256: String,
    proc_version: String,
    cpu_allowed_list: String,
    cpu_online: String,
    clocksource_current: String,
    clocksource_available: String,
    nvidia_gpu: String,
    nvidia_compute_processes: String,
}

#[derive(Clone, Debug, Serialize)]
struct BodyOccurrence {
    semantic_occurrence: usize,
    receiver: u64,
    native_conic_cell: u64,
    integer_coefficients: [i64; 6],
}

#[derive(Clone, Debug, Serialize)]
struct BodySpecification {
    schema: &'static str,
    boundary_name: &'static str,
    width: u32,
    height: u32,
    horizontal_span_numerator: String,
    horizontal_span_denominator: String,
    vertical_span_numerator: String,
    vertical_span_denominator: String,
    occurrences: Vec<BodyOccurrence>,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct FaceAddress {
    column: u32,
    row: u32,
}

#[derive(Clone, Debug, Serialize)]
struct AddressMultiplicity {
    address: FaceAddress,
    multiplicity: String,
}

#[derive(Clone, Debug, Serialize)]
struct PrimitiveFaceRecord {
    source: String,
    addresses: Vec<FaceAddress>,
    exact_support_queries: String,
}

#[derive(Clone, Debug, Serialize)]
struct ReceiverFaceRecord {
    receiver: u64,
    addresses: Vec<FaceAddress>,
    support_multiplicity: Vec<AddressMultiplicity>,
    primitive_traces: String,
    exact_support_queries: String,
    primitive_sections: Vec<PrimitiveFaceRecord>,
}

#[derive(Clone, Debug, Serialize)]
struct EventWorkRecord {
    semantic_occurrence: usize,
    exact_support_queries: String,
}

#[derive(Clone, Debug, Serialize)]
struct SemanticEventRecord {
    semantic_occurrence: usize,
    source_native_conic_cell: u64,
    receiver: u64,
    predecessors: Vec<usize>,
    target_support_population: usize,
    target_support_multiplicity: String,
    obstruction: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CausalProfile {
    semantic_fronts: Vec<Vec<usize>>,
    maximum_semantic_frontier_width: usize,
    semantic_critical_span: usize,
    reconvergent_sites: Vec<usize>,
    span_boundary: &'static str,
}

#[derive(Debug, Serialize)]
struct MeasurementArtifact {
    schema: &'static str,
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    body_sha256: String,
    body_population: usize,
    aperture_width: u32,
    aperture_height: u32,
    receiver_population: usize,
    warmups_per_apparatus: usize,
    repetitions_per_apparatus: usize,
    requested_worker_apertures: Vec<usize>,
    body: BodySpecification,
    semantic_events: Vec<SemanticEventRecord>,
    causal_profile: CausalProfile,
    system_before: ApparatusSnapshot,
    cpu_samples: Vec<CpuSample>,
    cpu_worker_scales: Vec<WorkerScale>,
    cpu_exact_work_by_semantic_occurrence: Vec<EventWorkRecord>,
    reference_cpu_receiver_face: Vec<ReceiverFaceRecord>,
    gpu_admission: Option<GpuAdmissionSample>,
    gpu_samples: Vec<GpuSample>,
    every_cpu_face_agrees: bool,
    every_gpu_face_agrees_with_cpu: Option<bool>,
    system_after: ApparatusSnapshot,
    boundaries: Vec<&'static str>,
}

#[repr(C)]
struct Timespec {
    tv_sec: i64,
    tv_nsec: i64,
}

unsafe extern "C" {
    fn clock_gettime(clock_id: i32, time: *mut Timespec) -> i32;
}

const CLOCK_MONOTONIC_RAW: i32 = 4;

fn main() {
    if let Err(error) = run() {
        eprintln!("Clocked Pantographic Swing measurement refused: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let config = parse_config()?;
    let (presentation, occurrences) = measurement_body(config.population)?;
    let terminal = terminal(config.width, config.height);
    let receivers = presentation
        .primitives
        .iter()
        .map(|primitive| primitive.receiver)
        .collect::<BTreeSet<_>>();
    let body = body_specification(&terminal, occurrences);
    let body_sha256 = sha256_serializable(&body)?;

    let system_before = apparatus_snapshot()?;
    if !config.cpu_only && !system_before.nvidia_compute_processes.trim().is_empty() {
        return Err(format!(
            "another CUDA compute process owns the card:\n{}",
            system_before.nvidia_compute_processes.trim()
        ));
    }

    let (cpu_samples, cpu_face) = measure_cpu(&config, &presentation, &terminal, &receivers)?;
    let cpu_worker_scales = worker_scales(&cpu_samples)?;
    let every_cpu_face_agrees = cpu_samples
        .iter()
        .all(|sample| sample.agrees_with_first_cpu_face);

    let (gpu_admission, gpu_samples) = if config.cpu_only {
        (None, Vec::new())
    } else {
        measure_gpu(&config, &presentation, &terminal, &receivers, &cpu_face)?
    };
    let every_gpu_face_agrees_with_cpu = (!config.cpu_only).then(|| {
        gpu_admission
            .as_ref()
            .is_some_and(|sample| sample.agrees_with_cpu_face)
            && gpu_samples.iter().all(|sample| sample.agrees_with_cpu_face)
    });
    let system_after = apparatus_snapshot()?;
    let semantic_events = semantic_event_records(&body, &cpu_face)?;
    let causal_profile = CausalProfile {
        semantic_fronts: vec![(0..config.population).collect()],
        maximum_semantic_frontier_width: config.population,
        semantic_critical_span: 1,
        reconvergent_sites: Vec::new(),
        span_boundary: "one independent semantic occurrence front; inner support-query dependency spans are not asserted by this receiver owner",
    };
    let cpu_exact_work_by_semantic_occurrence = event_work_records(&cpu_face);

    let artifact = MeasurementArtifact {
        schema: SCHEMA,
        truth_status: "measured",
        evidence_tags: ["implemented-exact", "hardware-testimony"],
        body_sha256,
        body_population: config.population,
        aperture_width: config.width,
        aperture_height: config.height,
        receiver_population: receivers.len(),
        warmups_per_apparatus: config.warmups,
        repetitions_per_apparatus: config.repetitions,
        requested_worker_apertures: config.workers.clone(),
        body,
        semantic_events,
        causal_profile,
        system_before,
        cpu_samples,
        cpu_worker_scales,
        cpu_exact_work_by_semantic_occurrence,
        reference_cpu_receiver_face: receiver_face_records(&cpu_face),
        gpu_admission,
        gpu_samples,
        every_cpu_face_agrees,
        every_gpu_face_agrees_with_cpu,
        system_after,
        boundaries: vec![
            "TSC is a local integer oscillator counter, not proper time and not a cost law.",
            "CLOCK_MONOTONIC_RAW is an exterior calibration chart and never selects a carrier.",
            "RDTSCP auxiliary values address only the observation thread; worker-local counter sections are not exposed by the current CPU owner.",
            "CUDA receipt timings are host-observed launch/synchronization sections; per-SM clock64 sections are not exposed by the current CUDA owner.",
            "Receiver equality is exact support equality; CPU and CUDA work populations and microtraces are not identified.",
        ],
    };

    if let Some(parent) = config.output.parent() {
        fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
    }
    let bytes = serde_json::to_vec_pretty(&artifact)
        .map_err(|error| format!("cannot encode measurement artifact: {error}"))?;
    fs::write(&config.output, &bytes)
        .map_err(|error| format!("cannot write {}: {error}", config.output.display()))?;
    let artifact_sha256 = sha256_bytes(&bytes);

    println!("CLOCKED PANTOGRAPHIC SWING MEASUREMENT");
    println!("body_sha256={}", artifact.body_sha256);
    println!("cpu_samples={}", artifact.cpu_samples.len());
    println!("every_cpu_face_agrees={}", artifact.every_cpu_face_agrees);
    println!("gpu_samples={}", artifact.gpu_samples.len());
    println!(
        "every_gpu_face_agrees_with_cpu={:?}",
        artifact.every_gpu_face_agrees_with_cpu
    );
    println!("artifact={}", config.output.display());
    println!("artifact_sha256={artifact_sha256}");
    Ok(())
}

fn parse_config() -> Result<Config, String> {
    let mut config = Config {
        cpu_only: false,
        workers: DEFAULT_WORKERS.to_vec(),
        repetitions: 7,
        warmups: 2,
        population: 96,
        width: 128,
        height: 96,
        output: PathBuf::from(".local/artifacts/the_clocked_pantographic_swing_is_measured/measurement.json"),
    };
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--cpu-only" => config.cpu_only = true,
            "--workers" => {
                let value = arguments
                    .next()
                    .ok_or_else(|| "--workers requires a comma-separated value".to_owned())?;
                config.workers = value
                    .split(',')
                    .map(|worker| {
                        worker
                            .parse::<usize>()
                            .map_err(|error| format!("invalid worker aperture {worker}: {error}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
            }
            "--repetitions" => {
                config.repetitions = parse_next(&mut arguments, "--repetitions")?;
            }
            "--warmups" => config.warmups = parse_next(&mut arguments, "--warmups")?,
            "--population" => config.population = parse_next(&mut arguments, "--population")?,
            "--width" => config.width = parse_next(&mut arguments, "--width")?,
            "--height" => config.height = parse_next(&mut arguments, "--height")?,
            "--output" => {
                config.output = PathBuf::from(
                    arguments
                        .next()
                        .ok_or_else(|| "--output requires a path".to_owned())?,
                );
            }
            other => return Err(format!("unknown argument: {other}")),
        }
    }
    if config.workers.is_empty()
        || config.workers.contains(&0)
        || config.repetitions == 0
        || config.population == 0
        || config.width == 0
        || config.height == 0
    {
        return Err(
            "workers, repetitions, population, width, and height must be positive".to_owned(),
        );
    }
    config.workers.sort_unstable();
    config.workers.dedup();
    if config.workers.first() != Some(&1) {
        return Err("the worker series must contain the one-worker calibration face".to_owned());
    }
    Ok(config)
}

fn parse_next<T: std::str::FromStr>(
    arguments: &mut impl Iterator<Item = String>,
    name: &str,
) -> Result<T, String>
where
    T::Err: std::fmt::Display,
{
    let value = arguments
        .next()
        .ok_or_else(|| format!("{name} requires a value"))?;
    value
        .parse::<T>()
        .map_err(|error| format!("invalid {name} value {value}: {error}"))
}

fn measurement_body(
    population: usize,
) -> Result<(ContinuousPresentation, Vec<BodyOccurrence>), String> {
    let mut primitives = Vec::with_capacity(population);
    let mut occurrences = Vec::with_capacity(population);
    for occurrence in 0..population {
        let coefficients = match occurrence % 3 {
            0 => [1, 0, 1, 0, 0, -1],
            1 => [4, 0, 1, 1, 0, -1],
            _ => [1, 0, -1, 0, 0, -1],
        };
        let form = HomogeneousConic::new(coefficients.map(integer))
            .map_err(|error| format!("conic occurrence {occurrence} refused: {error}"))?;
        let receiver = occurrence as u64 + 1;
        let native_conic_cell = 10_000 + occurrence as u64;
        primitives.push(PresentedPrimitive {
            receiver: ReceiverId(receiver),
            primitive: ReceiverPrimitive::Conic(ProjectedConic {
                source: ReceiverPrimitiveId::NativeConic(holonic_engine::ConicCellId(
                    native_conic_cell,
                )),
                class_in_receiver_chart: form.classify(),
                form,
                receiver_depth: ProjectiveDepthLaw {
                    numerator: ProjectiveLine2::homogeneous(integer(0), integer(0), integer(1)),
                    denominator: ProjectiveLine2::homogeneous(integer(0), integer(0), integer(1)),
                },
            }),
        });
        occurrences.push(BodyOccurrence {
            semantic_occurrence: occurrence,
            receiver,
            native_conic_cell,
            integer_coefficients: coefficients,
        });
    }
    Ok((
        ContinuousPresentation {
            schema: "holonic-engine.clocked-pantographic-swing-body.v1".to_owned(),
            boundary_name: "one repeated exact conic family measured through CPU and CUDA charts"
                .to_owned(),
            primitives,
            coordinate_fields: Vec::new(),
            relations: Vec::new(),
            seams: Vec::new(),
        },
        occurrences,
    ))
}

fn terminal(width: u32, height: u32) -> TerminalMatrixSpec {
    let horizontal_span = integer(2);
    TerminalMatrixSpec {
        width,
        height,
        boundary: PresentationBoundary {
            horizontal_span: horizontal_span.clone(),
            vertical_span: horizontal_span * Rat::from_integer(height.into())
                / Rat::from_integer(width.into()),
        },
    }
}

fn body_specification(
    terminal: &TerminalMatrixSpec,
    occurrences: Vec<BodyOccurrence>,
) -> BodySpecification {
    BodySpecification {
        schema: "holonic-engine.clocked-pantographic-swing-body.v1",
        boundary_name: "one repeated exact conic family measured through CPU and CUDA charts",
        width: terminal.width,
        height: terminal.height,
        horizontal_span_numerator: terminal.boundary.horizontal_span.numer().to_string(),
        horizontal_span_denominator: terminal.boundary.horizontal_span.denom().to_string(),
        vertical_span_numerator: terminal.boundary.vertical_span.numer().to_string(),
        vertical_span_denominator: terminal.boundary.vertical_span.denom().to_string(),
        occurrences,
    }
}

fn measure_cpu(
    config: &Config,
    presentation: &ContinuousPresentation,
    terminal: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
) -> Result<(Vec<CpuSample>, BTreeMap<ReceiverId, ReceiverApertureTrace>), String> {
    let mut samples = Vec::with_capacity(config.workers.len() * config.repetitions);
    let mut first_face = None;
    for &workers in &config.workers {
        let executor = if workers == 1 {
            CpuExecutor::serial()
        } else {
            CpuExecutor::multicore(
                NonZeroUsize::new(workers).expect("positive worker aperture was validated"),
            )
        };
        for _ in 0..config.warmups {
            trace_receivers_aperture_with_cpu(presentation, terminal, receivers, &executor)
                .map_err(|error| format!("CPU warmup at {workers} workers refused: {error}"))?;
        }
        for repetition in 0..config.repetitions {
            let source = counter_source()?;
            let (face, execution) =
                trace_receivers_aperture_with_cpu(presentation, terminal, receivers, &executor)
                    .map_err(|error| {
                        format!("CPU sample {repetition} at {workers} workers refused: {error}")
                    })?;
            let target = counter_target()?;
            let support_face_sha256 = support_face_sha256(&face)?;
            let agrees = first_face
                .as_ref()
                .is_none_or(|first| receiver_faces_agree(first, &face));
            if first_face.is_none() {
                first_face = Some(face);
            }
            samples.push(CpuSample {
                worker_aperture: workers,
                repetition,
                execution: cpu_execution_record(execution),
                clock: clock_section(source, target)?,
                support_face_sha256,
                agrees_with_first_cpu_face: agrees,
            });
        }
    }
    Ok((
        samples,
        first_face.expect("at least one CPU sample was validated"),
    ))
}

fn measure_gpu(
    config: &Config,
    presentation: &ContinuousPresentation,
    terminal: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    cpu_face: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> Result<(Option<GpuAdmissionSample>, Vec<GpuSample>), String> {
    let cpu = CpuExecutor::serial();
    let metric = DeclaredCarrierMetric::without_width(
        BigUint::from(1_u8),
        BigUint::from(1_u8),
        BigUint::from(1_u8),
    );
    let raw = CudaApertureExecutor::new()
        .map_err(|error| format!("CUDA apparatus refused to mount: {error}"))?;
    let admitted = raw.declaring(metric).in_frame(DisplayFrame::Undeclared);
    let (executor, admission_face, admission_receipt) = admitted
        .admit(presentation, terminal, receivers, &cpu)
        .map_err(|error| format!("CUDA admission refused: {error}"))?;
    let admission = GpuAdmissionSample {
        receipt: cuda_aperture_record(admission_receipt),
        exact_work_by_semantic_occurrence: event_work_records(&admission_face),
        support_face_sha256: support_face_sha256(&admission_face)?,
        agrees_with_cpu_face: receiver_faces_agree(cpu_face, &admission_face),
    };

    for _ in 0..config.warmups.saturating_sub(1) {
        executor
            .trace_through(
                ApertureExecutionBackend::HybridCuda,
                presentation,
                terminal,
                receivers,
                &cpu,
            )
            .map_err(|error| format!("CUDA warmup refused: {error}"))?;
    }
    let mut samples = Vec::with_capacity(config.repetitions);
    for repetition in 0..config.repetitions {
        let source = counter_source()?;
        let (face, receipt) = executor
            .trace_through(
                ApertureExecutionBackend::HybridCuda,
                presentation,
                terminal,
                receivers,
                &cpu,
            )
            .map_err(|error| format!("CUDA sample {repetition} refused: {error}"))?;
        let target = counter_target()?;
        samples.push(GpuSample {
            repetition,
            receipt: cuda_aperture_record(receipt),
            exact_work_by_semantic_occurrence: event_work_records(&face),
            clock: clock_section(source, target)?,
            support_face_sha256: support_face_sha256(&face)?,
            agrees_with_cpu_face: receiver_faces_agree(cpu_face, &face),
        });
    }
    Ok((Some(admission), samples))
}

fn receiver_faces_agree(
    left: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
    right: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> bool {
    left.len() == right.len()
        && left.iter().all(|(receiver, left_face)| {
            right
                .get(receiver)
                .is_some_and(|right_face| left_face.has_same_exact_support(right_face))
        })
}

fn cpu_execution_record(receipt: CpuExecutionReceipt) -> CpuExecutionRecord {
    CpuExecutionRecord {
        schema: receipt.schema,
        mode: receipt.mode,
        tasks: receipt.tasks.to_string(),
        worker_limit: receipt.worker_limit.to_string(),
        workers_used: receipt.workers_used.to_string(),
        batches: receipt.batches.to_string(),
        joins: receipt.joins.to_string(),
    }
}

fn carrier_work_record(work: CarrierWork) -> CarrierWorkRecord {
    CarrierWorkRecord {
        cpu_evaluations: work.cpu_evaluations.to_string(),
        device_evaluations: work.device_evaluations.to_string(),
        transfer_bytes: work.transfer_bytes.to_string(),
        intermediate_bits: work.intermediate_bits.to_string(),
    }
}

fn cuda_aperture_record(receipt: CudaApertureReceipt) -> CudaApertureRecord {
    CudaApertureRecord {
        schema: receipt.schema,
        device: receipt.device,
        receivers: receipt.receivers.to_string(),
        selected_primitives: receipt.selected_primitives.to_string(),
        device_primitives: receipt.device_primitives.to_string(),
        conics: receipt.conics.to_string(),
        segments: receipt.segments.to_string(),
        cpu_primitives: receipt.cpu_primitives.to_string(),
        cpu_conics: receipt.cpu_conics.to_string(),
        cpu_linear_primitives: receipt.cpu_linear_primitives.to_string(),
        aperture_members: receipt.aperture_members.to_string(),
        device_output_bytes: receipt.device_output_bytes.to_string(),
        device_threads: receipt.device_threads.to_string(),
        exact_support_evaluations: receipt.exact_support_evaluations.to_string(),
        device_exact_support_evaluations: receipt.device_exact_support_evaluations.to_string(),
        cpu_exact_support_evaluations: receipt.cpu_exact_support_evaluations.to_string(),
        intermediate_bits: receipt.intermediate_bits.to_string(),
        device_arithmetic: receipt.device_arithmetic,
        cpu_workers: receipt.cpu_workers.to_string(),
        selection_pack_nanoseconds: receipt.selection_pack_nanoseconds,
        device_prepare_nanoseconds: receipt.device_prepare_nanoseconds,
        device_execute_nanoseconds: receipt.device_execute_nanoseconds,
        device_download_nanoseconds: receipt.device_download_nanoseconds,
        device_decode_nanoseconds: receipt.device_decode_nanoseconds,
        cpu_trace_nanoseconds: receipt.cpu_trace_nanoseconds,
        cpu_merge_nanoseconds: receipt.cpu_merge_nanoseconds,
        wall_nanoseconds: receipt.wall_nanoseconds,
        cpu_parity: receipt.cpu_parity,
        execution_backend: receipt.execution_backend,
        admission_candidate_nanoseconds: receipt.admission_candidate_nanoseconds,
        admission_authority_nanoseconds: receipt.admission_authority_nanoseconds,
        admission: format!("{:?}", receipt.admission),
        work_ordering: format!("{:?}", receipt.work_ordering),
        authority_work: carrier_work_record(receipt.authority_work),
        candidate_work: carrier_work_record(receipt.candidate_work),
        display_frame: format!("{:?}", receipt.display_frame),
    }
}

fn support_face_sha256(
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> Result<String, String> {
    let mut support = receiver_face_records(traces);
    for trace in &mut support {
        trace.exact_support_queries = "0".to_owned();
        for primitive in &mut trace.primitive_sections {
            primitive.exact_support_queries = "0".to_owned();
        }
    }
    sha256_serializable(&support)
}

fn receiver_face_records(
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> Vec<ReceiverFaceRecord> {
    traces
        .iter()
        .map(|(receiver, trace)| ReceiverFaceRecord {
            receiver: receiver.0,
            addresses: trace
                .addresses
                .iter()
                .map(|address| FaceAddress {
                    column: address.column,
                    row: address.row,
                })
                .collect(),
            support_multiplicity: trace
                .support_multiplicity
                .iter()
                .map(|(address, multiplicity)| AddressMultiplicity {
                    address: FaceAddress {
                        column: address.column,
                        row: address.row,
                    },
                    multiplicity: multiplicity.to_string(),
                })
                .collect(),
            primitive_traces: trace.primitive_traces.to_string(),
            exact_support_queries: trace.exact_support_queries.to_string(),
            primitive_sections: trace
                .primitive_sections
                .iter()
                .map(|(source, section)| PrimitiveFaceRecord {
                    source: format!("{source:?}"),
                    addresses: section
                        .addresses
                        .iter()
                        .map(|address| FaceAddress {
                            column: address.column,
                            row: address.row,
                        })
                        .collect(),
                    exact_support_queries: section.exact_support_queries.to_string(),
                })
                .collect(),
        })
        .collect()
}

fn event_work_records(
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> Vec<EventWorkRecord> {
    traces
        .iter()
        .map(|(receiver, trace)| EventWorkRecord {
            semantic_occurrence: receiver.0.saturating_sub(1) as usize,
            exact_support_queries: trace.exact_support_queries.to_string(),
        })
        .collect()
}

fn semantic_event_records(
    body: &BodySpecification,
    traces: &BTreeMap<ReceiverId, ReceiverApertureTrace>,
) -> Result<Vec<SemanticEventRecord>, String> {
    body.occurrences
        .iter()
        .map(|occurrence| {
            let trace = traces
                .get(&ReceiverId(occurrence.receiver))
                .ok_or_else(|| {
                    format!(
                        "semantic occurrence {} has no returned receiver face",
                        occurrence.semantic_occurrence
                    )
                })?;
            let multiplicity = trace
                .support_multiplicity
                .values()
                .fold(BigUint::from(0_u8), |sum, value| sum + value);
            Ok(SemanticEventRecord {
                semantic_occurrence: occurrence.semantic_occurrence,
                source_native_conic_cell: occurrence.native_conic_cell,
                receiver: occurrence.receiver,
                predecessors: Vec::new(),
                target_support_population: trace.addresses.len(),
                target_support_multiplicity: multiplicity.to_string(),
                obstruction: None,
            })
        })
        .collect()
}

fn worker_scales(samples: &[CpuSample]) -> Result<Vec<WorkerScale>, String> {
    let mut grouped = BTreeMap::<usize, (Vec<u128>, Vec<u128>)>::new();
    for sample in samples {
        let group = grouped.entry(sample.worker_aperture).or_default();
        group.0.push(u128::from(sample.clock.tsc_ticks));
        group.1.push(sample.clock.monotonic_raw_elapsed_ns);
    }
    let one = grouped
        .get(&1)
        .ok_or_else(|| "one-worker calibration samples are absent".to_owned())?;
    let one_tsc = median(&one.0)?;
    let one_exterior = median(&one.1)?;
    grouped
        .into_iter()
        .map(|(worker_aperture, (ticks, exterior))| {
            let median_tsc_ticks = median(&ticks)?;
            let median_monotonic_raw_ns = median(&exterior)?;
            Ok(WorkerScale {
                worker_aperture,
                median_tsc_ticks,
                median_monotonic_raw_ns,
                tsc_scale_from_one_worker: exact_ratio(median_tsc_ticks, one_tsc)?,
                exterior_scale_from_one_worker: exact_ratio(median_monotonic_raw_ns, one_exterior)?,
            })
        })
        .collect()
}

fn median(values: &[u128]) -> Result<u128, String> {
    if values.is_empty() {
        return Err("a median requires at least one sample".to_owned());
    }
    let mut values = values.to_vec();
    values.sort_unstable();
    Ok(values[values.len() / 2])
}

fn counter_source() -> Result<CounterEndpoint, String> {
    let monotonic_raw_ns = monotonic_raw_ns()?;
    let (tsc, tsc_aux) = read_tsc();
    Ok(CounterEndpoint {
        tsc,
        tsc_aux,
        monotonic_raw_ns,
    })
}

fn counter_target() -> Result<CounterEndpoint, String> {
    let (tsc, tsc_aux) = read_tsc();
    let monotonic_raw_ns = monotonic_raw_ns()?;
    Ok(CounterEndpoint {
        tsc,
        tsc_aux,
        monotonic_raw_ns,
    })
}

fn clock_section(source: CounterEndpoint, target: CounterEndpoint) -> Result<ClockSection, String> {
    let tsc_ticks = target
        .tsc
        .checked_sub(source.tsc)
        .ok_or_else(|| "the local TSC counter moved backwards".to_owned())?;
    let monotonic_raw_elapsed_ns = target
        .monotonic_raw_ns
        .checked_sub(source.monotonic_raw_ns)
        .ok_or_else(|| "CLOCK_MONOTONIC_RAW moved backwards".to_owned())?;
    Ok(ClockSection {
        tsc_clock_domain: "x86_64.rdtscp.invariant-tsc",
        tsc_source: source.tsc,
        tsc_target: target.tsc,
        tsc_ticks,
        tsc_aux_source: source.tsc_aux,
        tsc_aux_target: target.tsc_aux,
        observation_thread_migrated: source.tsc_aux != target.tsc_aux,
        exterior_clock_domain: "linux.clock-monotonic-raw",
        monotonic_raw_source_ns: source.monotonic_raw_ns,
        monotonic_raw_target_ns: target.monotonic_raw_ns,
        monotonic_raw_elapsed_ns,
        tsc_ticks_per_exterior_nanosecond: exact_ratio(
            u128::from(tsc_ticks),
            monotonic_raw_elapsed_ns,
        )?,
    })
}

#[cfg(target_arch = "x86_64")]
fn read_tsc() -> (u64, u32) {
    use std::arch::x86_64::{__rdtscp, _mm_lfence};
    let mut auxiliary = 0_u32;
    // SAFETY: RDTSCP and LFENCE are available on the admitted x86_64 measurement host.  The
    // executable is an apparatus-specific driver and records that boundary in its artifact.
    let ticks = unsafe {
        _mm_lfence();
        let ticks = __rdtscp(&mut auxiliary);
        _mm_lfence();
        ticks
    };
    (ticks, auxiliary)
}

#[cfg(not(target_arch = "x86_64"))]
compile_error!("the current local-counter apparatus requires x86_64 RDTSCP");

fn monotonic_raw_ns() -> Result<u128, String> {
    let mut time = Timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: `time` is a valid writable `timespec`, and CLOCK_MONOTONIC_RAW returns no borrowed
    // state.  A nonzero result is retained as a measurement refusal.
    if unsafe { clock_gettime(CLOCK_MONOTONIC_RAW, &mut time) } != 0 {
        return Err(format!(
            "clock_gettime(CLOCK_MONOTONIC_RAW) refused: {}",
            std::io::Error::last_os_error()
        ));
    }
    if time.tv_sec < 0 || !(0..1_000_000_000).contains(&time.tv_nsec) {
        return Err("CLOCK_MONOTONIC_RAW returned an invalid section".to_owned());
    }
    Ok(time.tv_sec as u128 * 1_000_000_000_u128 + time.tv_nsec as u128)
}

fn exact_ratio(numerator: u128, denominator: u128) -> Result<ExactRatio, String> {
    if denominator == 0 {
        return Err("an exact clock ratio cannot have a zero denominator".to_owned());
    }
    let divisor = gcd(numerator, denominator);
    Ok(ExactRatio {
        numerator: numerator / divisor,
        denominator: denominator / divisor,
    })
}

fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left.max(1)
}

fn apparatus_snapshot() -> Result<ApparatusSnapshot, String> {
    Ok(ApparatusSnapshot {
        unix_epoch_ns: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("system clock lies before the Unix epoch: {error}"))?
            .as_nanos(),
        process_id: std::process::id(),
        executable_sha256: sha256_file(
            &std::env::current_exe()
                .map_err(|error| format!("cannot locate the measurement executable: {error}"))?,
        )?,
        proc_version: read_trimmed("/proc/version"),
        cpu_allowed_list: proc_status_value("Cpus_allowed_list"),
        cpu_online: read_trimmed("/sys/devices/system/cpu/online"),
        clocksource_current: read_trimmed(
            "/sys/devices/system/clocksource/clocksource0/current_clocksource",
        ),
        clocksource_available: read_trimmed(
            "/sys/devices/system/clocksource/clocksource0/available_clocksource",
        ),
        nvidia_gpu: command_output(&[
            "--query-gpu=index,name,uuid,driver_version,pstate,temperature.gpu,power.draw,clocks.sm,clocks.mem,utilization.gpu,memory.used,memory.total",
            "--format=csv,noheader,nounits",
        ]),
        nvidia_compute_processes: command_output(&[
            "--query-compute-apps=pid,process_name,used_memory",
            "--format=csv,noheader,nounits",
        ]),
    })
}

fn command_output(arguments: &[&str]) -> String {
    match Command::new("nvidia-smi").args(arguments).output() {
        Ok(output) if output.status.success() => {
            String::from_utf8_lossy(&output.stdout).trim().to_owned()
        }
        Ok(output) => format!(
            "nvidia-smi refused with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ),
        Err(error) => format!("nvidia-smi unavailable: {error}"),
    }
}

fn read_trimmed(path: &str) -> String {
    fs::read_to_string(path)
        .map(|value| value.trim().to_owned())
        .unwrap_or_else(|error| format!("unavailable: {error}"))
}

fn proc_status_value(name: &str) -> String {
    fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status.lines().find_map(|line| {
                line.strip_prefix(name)
                    .and_then(|value| value.strip_prefix(':'))
                    .map(str::trim)
                    .map(str::to_owned)
            })
        })
        .unwrap_or_else(|| "unavailable".to_owned())
}

fn sha256_serializable(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| sha256_bytes(&bytes))
        .map_err(|error| format!("cannot serialize an exact identity face: {error}"))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    fs::read(path)
        .map(|bytes| sha256_bytes(&bytes))
        .map_err(|error| format!("cannot hash {}: {error}", path.display()))
}

fn sha256_bytes(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
