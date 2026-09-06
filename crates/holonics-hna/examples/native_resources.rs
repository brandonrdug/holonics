//! Bounded native-phase resource measurement.
//!
//! This is a scoped receiver experiment. It preserves only public native session handles and
//! outputs, and reports scoped section/process residency without inferring power.

use holonic_engine::resident_section::TransferCensus;
use holonics_hna::native::{
    with_native_session, CurrentWire, JunctionSpec, NativeModelSpec, NativeSavedSession,
    NativeSessionError, ReceiverWire, NATIVE_MODEL_SPEC_SCHEMA,
};
use serde::Serialize;
use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

const RETAINED: [usize; 4] = [1, 64, 1024, 4096];
const WARM: usize = 16;

#[derive(Clone, Debug, Serialize)]
struct MemorySample {
    vm_rss_kib: Option<u64>,
    vm_hwm_kib: Option<u64>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
struct CensusDelta {
    ingress_octets: u64,
    egress_section_octets: u64,
    egress_receipt_octets: u64,
    device_to_device_octets: u64,
    captured_launches: u64,
    deed_launches: u64,
    control_launches: u64,
    synchronizations: u64,
    allocations: u64,
    section_read_outs: u64,
}

impl CensusDelta {
    fn between(before: &TransferCensus, after: &TransferCensus) -> Self {
        Self {
            ingress_octets: after
                .ingress_octets
                .checked_sub(before.ingress_octets)
                .expect("census subtraction requires one realized surface"),
            egress_section_octets: after
                .egress_section_octets
                .checked_sub(before.egress_section_octets)
                .expect("census subtraction requires one realized surface"),
            egress_receipt_octets: after
                .egress_receipt_octets
                .checked_sub(before.egress_receipt_octets)
                .expect("census subtraction requires one realized surface"),
            device_to_device_octets: after
                .device_to_device_octets
                .checked_sub(before.device_to_device_octets)
                .expect("census subtraction requires one realized surface"),
            captured_launches: after
                .captured_launches
                .checked_sub(before.captured_launches)
                .expect("census subtraction requires one realized surface"),
            deed_launches: after
                .deed_launches
                .checked_sub(before.deed_launches)
                .expect("census subtraction requires one realized surface"),
            control_launches: after
                .control_launches
                .checked_sub(before.control_launches)
                .expect("census subtraction requires one realized surface"),
            synchronizations: after
                .synchronizations
                .checked_sub(before.synchronizations)
                .expect("census subtraction requires one realized surface"),
            allocations: after
                .allocations
                .checked_sub(before.allocations)
                .expect("census subtraction requires one realized surface"),
            section_read_outs: after
                .section_read_outs
                .checked_sub(before.section_read_outs)
                .expect("census subtraction requires one realized surface"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct WarmSignature {
    deed_launches: u64,
    section_read_outs: u64,
}

impl From<&CensusDelta> for WarmSignature {
    fn from(delta: &CensusDelta) -> Self {
        Self {
            deed_launches: delta.deed_launches,
            section_read_outs: delta.section_read_outs,
        }
    }
}

#[derive(Debug, Serialize)]
struct CaseReport {
    retained_unlinked: usize,
    mount_callback_entry_ns: u128,
    warm_min_ns: u128,
    warm_median_ns: u128,
    warm_max_ns: u128,
    warm_operation_deltas: Vec<CensusDelta>,
    warm_signature: WarmSignature,
    census_before_warm: TransferCensus,
    census_after_warm: TransferCensus,
    census_before_checkpoint: TransferCensus,
    census_before_contact: TransferCensus,
    census_after_contact: TransferCensus,
    contact_delta: CensusDelta,
    contact_receiver: &'static str,
    contact_formed_pivot: Option<usize>,
    contact_source: u64,
    contact_received_from: Option<u64>,
    contact_reading: ReceiverWire,
    contact_ns: u128,
    learned_warm_min_ns: u128,
    learned_warm_median_ns: u128,
    learned_warm_max_ns: u128,
    learned_warm_delta: CensusDelta,
    checkpoint_write_ns: u128,
    checkpoint_octets: u64,
    checkpoint_read_ns: u128,
    remount_callback_entry_ns: u128,
    remount_deed_launches: u64,
    remount_has_source_zero: bool,
    remount_contact_occurrence: usize,
    memory_before: Option<MemorySample>,
    memory_after: Option<MemorySample>,
    memory_mounted: Option<MemorySample>,
    gpu_process_mib_mounted: Option<u64>,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    profile: &'static str,
    debug_assertions: bool,
    retained_counts: &'static [usize; 4],
    warm_operations: usize,
    cases: Vec<CaseReport>,
}

fn seed() -> NativeModelSpec {
    let node = || JunctionSpec {
        incoming_admittance: 1,
        held_admittance: 1,
        incoming_transport: CurrentWire::integers(1, 0),
        initial_held: CurrentWire::integers(1, 0),
    };
    NativeModelSpec {
        schema: NATIVE_MODEL_SPEC_SCHEMA.into(),
        nodes: vec![node(), node()],
    }
}

fn memory_sample() -> Option<MemorySample> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    let value = |name: &str| {
        status.lines().find_map(|line| {
            let rest = line.strip_prefix(name)?.trim();
            rest.strip_suffix(" kB")?.parse::<u64>().ok()
        })
    };
    Some(MemorySample {
        vm_rss_kib: value("VmRSS:"),
        vm_hwm_kib: value("VmHWM:"),
    })
}

/// Exterior driver observation, outside the timed native work. None means unavailable, not zero.
fn gpu_process_memory_mib() -> Option<u64> {
    let output = Command::new("nvidia-smi")
        .args([
            "--query-compute-apps=pid,used_gpu_memory",
            "--format=csv,noheader,nounits",
        ])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8(output.stdout).ok()?;
    let samples = text
        .lines()
        .filter_map(|line| {
            let (pid, memory) = line.split_once(',')?;
            (pid.trim().parse::<u32>().ok()? == std::process::id())
                .then(|| memory.trim().parse::<u64>().ok())
                .flatten()
        })
        .collect::<Vec<_>>();
    if samples.is_empty() {
        None
    } else {
        samples
            .into_iter()
            .try_fold(0u64, |sum, n| sum.checked_add(n))
    }
}

fn checkpoint_path(output: &Path, retained: usize) -> PathBuf {
    output.join(format!("native-resources-{retained}.hna"))
}

fn run_case(
    model: &NativeModelSpec,
    output: &Path,
    retained: usize,
    reference_signature: &mut Option<WarmSignature>,
) -> Result<CaseReport, NativeSessionError> {
    let checkpoint = checkpoint_path(output, retained);
    if checkpoint.exists() {
        return Err(NativeSessionError::Application(format!(
            "refusing reused checkpoint path {:?}",
            checkpoint
        )));
    }
    let current_one = CurrentWire::integers(1, 0);
    let current_two = CurrentWire::integers(2, 0);
    let memory_before = memory_sample();
    let mount_started = Instant::now();
    let report = with_native_session(model, |session| {
        let mount_callback_entry_ns = mount_started.elapsed().as_nanos();
        for _ in 0..retained {
            session.receive(&current_one, None)?;
        }
        let census_before_warm = session.inspect().census.clone();
        let mut warm_times = Vec::with_capacity(WARM);
        let mut warm_operation_deltas = Vec::with_capacity(WARM);
        for _ in 0..WARM {
            let before = session.inspect().census.clone();
            let started = Instant::now();
            let step = session.receive(&current_one, None)?;
            warm_times.push(started.elapsed().as_nanos());
            if !matches!(step.receiver, ReceiverWire::OutsideDomain { .. }) {
                return Err(NativeSessionError::Application(
                    "warm unlinked receive did not remain outside-domain".into(),
                ));
            }
            let after = session.inspect().census.clone();
            warm_operation_deltas.push(CensusDelta::between(&before, &after));
        }
        let census_after_warm = session.inspect().census.clone();
        let warm_signature = WarmSignature::from(&warm_operation_deltas[0]);
        if warm_operation_deltas
            .iter()
            .any(|delta| WarmSignature::from(delta) != warm_signature)
        {
            return Err(NativeSessionError::Application(
                "warm census deed/readout delta changed within one retained extent".into(),
            ));
        }
        if let Some(reference) = reference_signature.as_ref() {
            if reference != &warm_signature {
                return Err(NativeSessionError::Application(
                    "warm census deed/readout delta changed across retained extents".into(),
                ));
            }
        } else {
            *reference_signature = Some(warm_signature.clone());
        }
        let census_before_checkpoint = session.inspect().census.clone();
        let memory_mounted = memory_sample();
        let gpu_process_mib_mounted = gpu_process_memory_mib();
        if !session.has_source(0) {
            return Err(NativeSessionError::Application(
                "source zero was not retained before checkpoint".into(),
            ));
        }
        let write_started = Instant::now();
        let publication = session.checkpoint(&checkpoint)?;
        let checkpoint_write_ns = write_started.elapsed().as_nanos();
        Ok((
            mount_callback_entry_ns,
            warm_times,
            warm_operation_deltas,
            warm_signature,
            census_before_warm,
            census_after_warm,
            census_before_checkpoint,
            checkpoint_write_ns,
            publication.bytes,
            memory_before,
            memory_mounted,
            gpu_process_mib_mounted,
        ))
    })?;
    let (
        mount_callback_entry_ns,
        warm_times,
        warm_operation_deltas,
        warm_signature,
        census_before_warm,
        census_after_warm,
        census_before_checkpoint,
        checkpoint_write_ns,
        checkpoint_octets,
        memory_before,
        memory_mounted,
        gpu_process_mib_mounted,
    ) = report;
    let read_started = Instant::now();
    let saved = NativeSavedSession::read(&checkpoint)?;
    let checkpoint_read_ns = read_started.elapsed().as_nanos();
    let remount_started = Instant::now();
    let (
        remount_callback_entry_ns,
        remount_deed_launches,
        remount_has_source_zero,
        census_before_contact,
        contact,
        census_after_contact,
        contact_ns,
        mut learned_times,
        learned_warm_delta,
    ) = saved.with_session(|session, _stream| {
        let remount_callback_entry_ns = remount_started.elapsed().as_nanos();
        let anatomy = session.inspect();
        if anatomy.census.deed_launches != 0 {
            return Err(NativeSessionError::Application(
                "remount replayed native deeds".into(),
            ));
        }
        let remount_has_source_zero = session.has_source(0);
        if !remount_has_source_zero {
            return Err(NativeSessionError::Application(
                "remount lost outstanding source zero".into(),
            ));
        }
        let contact_started = Instant::now();
        let contact = session.receive(&current_two, Some(0))?;
        let contact_ns = contact_started.elapsed().as_nanos();
        if !matches!(contact.receiver, ReceiverWire::Unique { .. })
            || contact.formed_pivot.is_none()
        {
            return Err(NativeSessionError::Application(
                "actual source contact did not form a unique pivot receiver".into(),
            ));
        }
        let census_after_contact = session.inspect().census;
        let mut learned_times = Vec::with_capacity(WARM);
        for _ in 0..WARM {
            let started = Instant::now();
            let step = session.receive(&current_one, None)?;
            learned_times.push(started.elapsed().as_nanos());
            if !matches!(step.receiver, ReceiverWire::Unique { .. }) || step.successor_rank != 1 {
                return Err(NativeSessionError::Application(
                    "learned warm return left its admitted rank-one relation".into(),
                ));
            }
        }
        let learned_warm_delta =
            CensusDelta::between(&census_after_contact, &session.inspect().census);
        Ok((
            remount_callback_entry_ns,
            anatomy.census.deed_launches,
            remount_has_source_zero,
            anatomy.census,
            contact,
            census_after_contact,
            contact_ns,
            learned_times,
            learned_warm_delta,
        ))
    })?;
    let warm_min_ns = *warm_times.iter().min().unwrap_or(&0);
    let warm_max_ns = *warm_times.iter().max().unwrap_or(&0);
    let mut sorted = warm_times;
    sorted.sort_unstable();
    let warm_median_ns = sorted[sorted.len() / 2];
    let memory_after = memory_sample();
    let contact_delta = CensusDelta::between(&census_before_contact, &census_after_contact);
    learned_times.sort_unstable();
    Ok(CaseReport {
        retained_unlinked: retained,
        mount_callback_entry_ns,
        warm_min_ns,
        warm_median_ns,
        warm_max_ns,
        warm_operation_deltas,
        warm_signature,
        census_before_warm,
        census_after_warm,
        census_before_checkpoint,
        census_before_contact,
        census_after_contact: census_after_contact.clone(),
        contact_delta,
        contact_receiver: "unique",
        contact_formed_pivot: contact.formed_pivot,
        contact_source: contact.source,
        contact_received_from: contact.received_from,
        contact_reading: contact.receiver,
        contact_ns,
        learned_warm_min_ns: learned_times[0],
        learned_warm_median_ns: learned_times[WARM / 2],
        learned_warm_max_ns: learned_times[WARM - 1],
        learned_warm_delta,
        checkpoint_write_ns,
        checkpoint_octets,
        checkpoint_read_ns,
        remount_callback_entry_ns,
        remount_deed_launches,
        remount_has_source_zero,
        remount_contact_occurrence: contact.native_occurrence,
        memory_before,
        memory_after,
        memory_mounted,
        gpu_process_mib_mounted,
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args_os().skip(1);
    let output = args.next().map(PathBuf::from).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "usage: native_resources OUTPUT_DIRECTORY",
        )
    })?;
    if args.next().is_some() || !output.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "OUTPUT_DIRECTORY must be an existing directory and the only argument",
        )
        .into());
    }
    for retained in RETAINED {
        if checkpoint_path(&output, retained).exists() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                format!("refusing reused checkpoint path for {retained}"),
            )
            .into());
        }
    }
    let model = seed();
    let mut reference_signature = None;
    let mut cases = Vec::with_capacity(RETAINED.len());
    for retained in RETAINED {
        cases.push(run_case(
            &model,
            &output,
            retained,
            &mut reference_signature,
        )?);
    }
    let report = Report {
        schema: "org.holonics.hna.native-resources.v1",
        profile: if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        },
        debug_assertions: cfg!(debug_assertions),
        retained_counts: &RETAINED,
        warm_operations: WARM,
        cases,
    };
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
