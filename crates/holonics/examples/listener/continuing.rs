//! Continuing host consumer with comparison-derived receiving precision. Roles, CLI strings and receipt formats are exterior
//! run declarations. Field declarations live in octets; the octet/framing chart lives in sections.
//! All authored workload values below occur only in tests. An explicit evaluation suffix hears
//! sources only; its target bytes remain exterior comparison evidence.
use crate::octets::{
    BUDGET, RELEASE_KEY_BYTES, Result, drawn_code, elapsed, enclosure, field, read, scored_code,
    sections_of, shown, stepped_families,
};
use crate::sections::{self, CLASSES, Section};
use holonics::hnn::constitution::{Constitution, DepositReading, Locus};
use holonics::hnn::field::{ConstitutionRead, Current, Field};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::port::{Handle, ReceiptDetail};
use holonics::hnn::receiving::ActiveAddress;
use holonics::hnn::receiving::cells::CellLaw;
use holonics::hnn::reference::observed::{ObservedCrib, ObservedEpochExecution};
use holonics::hnn::reference::{ClosedLocated, ExposedResident, Reference, Resident};
use holonics::hnn::{ExecutionPort, Faces, HnnError, SourceMoment};
use holonics::ratio::Rat;
use holonics::receiver::release::KeyStream;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use std::time::Instant;

struct ContinuingOptions {
    learn: String,
    count: Option<usize>,
    chart_manifest: Option<String>,
    population: u64,
    keys: Option<String>,
    keys_sha256: Option<String>,
    work_deadline_ns: Option<u128>,
    block_upper_ns_per_cell: Option<u128>,
    sections_per_pass: Option<usize>,
    stage1_probe_cells: Option<usize>,
    evaluation_from_section: Option<usize>,
    diagnostic_release_faces: bool,
    diagnostic_solenoidal_lock: bool,
    diagnostic_step0: bool,
    diagnostic_calibration_only: bool,
    diagnostic_checkpoint: Option<String>,
    diagnostic_profile_trunk_cells: Option<usize>,
    diagnostic_profile_paired_cells64: bool,
    diagnostic_cost_profile_cells64: bool,
    diagnostic_report_reserve_ns: Option<u128>,
}

fn parse(args: &[String]) -> Result<ContinuingOptions> {
    let (mut learn, mut count, mut population, mut keys, mut diagnostic_checkpoint) =
        (None, None, None, None, None);
    let mut diagnostic_profile_trunk_cells = None;
    let mut chart_manifest = None;
    let mut keys_sha256 = None;
    let mut work_deadline_ns = None;
    let mut block_upper_ns_per_cell = None;
    let mut sections_per_pass = None;
    let mut stage1_probe_cells = None;
    let mut evaluation_from_section = None;
    let mut diagnostic_release_faces = false;
    let mut diagnostic_solenoidal_lock = false;
    let mut diagnostic_profile_paired_cells64 = false;
    let mut diagnostic_cost_profile_cells64 = false;
    let mut diagnostic_report_reserve_ns = None;
    let mut diagnostic_step0 = false;
    let mut diagnostic_calibration_only = false;
    let mut at = 0;
    while at < args.len() {
        let option = args[at].as_str();
        if option == "--diagnostic-solenoidal-lock" {
            diagnostic_solenoidal_lock = true;
            at += 1;
            continue;
        }
        if option == "--diagnostic-release-faces" {
            diagnostic_release_faces = true;
            at += 1;
            continue;
        }
        if option == "--diagnostic-step0" {
            diagnostic_step0 = true;
            at += 1;
            continue;
        }
        if option == "--diagnostic-calibration-only" {
            diagnostic_calibration_only = true;
            at += 1;
            continue;
        }
        if option == "--diagnostic-cost-profile-cells64" {
            diagnostic_cost_profile_cells64 = true;
            at += 1;
            continue;
        }
        if option == "--diagnostic-profile-paired-cells64" {
            diagnostic_profile_paired_cells64 = true;
            at += 1;
            continue;
        }
        if !matches!(
            option,
            "--learn"
                | "--learn-count"
                | "--chart-manifest"
                | "--population"
                | "--keys"
                | "--keys-sha256"
                | "--work-deadline-monotonic-ns"
                | "--block-upper-ns-per-cell"
                | "--sections-per-pass"
                | "--stage1-probe-cells"
                | "--evaluation-from-section"
                | "--diagnostic-checkpoint"
                | "--diagnostic-profile-trunk-cells"
                | "--diagnostic-report-reserve-ns"
        ) {
            return Err(format!("{option} is unsupported in --route observed: one open moment; section options, cap flags and resume are unavailable").into());
        }
        let value = args
            .get(at + 1)
            .ok_or_else(|| format!("{option} needs a value"))?;
        match option {
            "--learn" => learn = Some(value.clone()),
            "--learn-count" => count = Some(value.parse()?),
            "--chart-manifest" => chart_manifest = Some(value.clone()),
            "--population" => population = Some(value.parse()?),
            "--keys" => keys = Some(value.clone()),
            "--keys-sha256" => keys_sha256 = Some(value.clone()),
            "--work-deadline-monotonic-ns" => work_deadline_ns = Some(value.parse()?),
            "--block-upper-ns-per-cell" => block_upper_ns_per_cell = Some(value.parse()?),
            "--sections-per-pass" => sections_per_pass = Some(value.parse()?),
            "--stage1-probe-cells" => stage1_probe_cells = Some(value.parse()?),
            "--evaluation-from-section" => evaluation_from_section = Some(value.parse()?),
            "--diagnostic-checkpoint" => diagnostic_checkpoint = Some(value.clone()),
            "--diagnostic-profile-trunk-cells" => {
                diagnostic_profile_trunk_cells = Some(value.parse()?)
            }
            "--diagnostic-report-reserve-ns" => diagnostic_report_reserve_ns = Some(value.parse()?),
            _ => unreachable!(),
        }
        at += 2;
    }
    let population = population
        .ok_or("--route observed requires explicit --population before frames are read")?;
    if population == 0 {
        return Err("--population must be positive".into());
    }
    if keys_sha256.as_ref().is_some_and(|hash: &String| {
        hash.len() != 64
            || !hash
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    }) {
        return Err("--keys-sha256 requires one lowercase SHA256".into());
    }
    if keys_sha256.is_some() && keys.is_none() {
        return Err("--keys-sha256 requires --keys".into());
    }
    if work_deadline_ns == Some(0)
        || block_upper_ns_per_cell == Some(0)
        || sections_per_pass == Some(0)
        || stage1_probe_cells == Some(0)
    {
        return Err("observed work ceilings, pass extent and probe cells must be positive".into());
    }
    if diagnostic_step0
        && (work_deadline_ns.is_some()
            || block_upper_ns_per_cell.is_some()
            || sections_per_pass.is_some()
            || stage1_probe_cells.is_some())
    {
        return Err("stage1 observed options are separate from the historical diagnostic".into());
    }
    if evaluation_from_section.is_some()
        && (diagnostic_step0 || stage1_probe_cells.is_some() || chart_manifest.is_none())
    {
        return Err(
            "evaluation suffix requires --chart-manifest and cannot include a diagnostic or probe"
                .into(),
        );
    }
    if evaluation_from_section == Some(0) {
        return Err("evaluation suffix requires a nonempty training prefix".into());
    }
    if diagnostic_calibration_only && !diagnostic_step0 {
        return Err("--diagnostic-calibration-only requires --diagnostic-step0".into());
    }
    if !diagnostic_step0
        && (diagnostic_checkpoint.is_some()
            || diagnostic_profile_trunk_cells.is_some()
            || diagnostic_profile_paired_cells64
            || diagnostic_cost_profile_cells64
            || diagnostic_report_reserve_ns.is_some())
    {
        return Err("diagnostic options require --diagnostic-step0".into());
    }
    if diagnostic_profile_trunk_cells.is_some_and(|cells| cells == 0 || cells > 312) {
        return Err("--diagnostic-profile-trunk-cells must be between 1 and 312".into());
    }
    if diagnostic_profile_trunk_cells.is_some()
        && (diagnostic_calibration_only || diagnostic_checkpoint.is_some())
    {
        return Err("trunk profiling cannot include calibration or checkpoint/fork options".into());
    }
    if diagnostic_profile_paired_cells64
        && (diagnostic_profile_trunk_cells.is_some()
            || diagnostic_calibration_only
            || diagnostic_checkpoint.is_some())
    {
        return Err("paired 64+64 profiling is a separate calibration mode and cannot include trunk-only profiling, calibration-only, or checkpoint options".into());
    }
    if diagnostic_cost_profile_cells64
        && (diagnostic_profile_trunk_cells.is_some()
            || diagnostic_profile_paired_cells64
            || diagnostic_calibration_only
            || diagnostic_report_reserve_ns.is_some()
            || diagnostic_checkpoint.is_none())
    {
        return Err("cost profiling requires its own create-only checkpoint destination and cannot include another diagnostic mode".into());
    }
    if diagnostic_report_reserve_ns.is_some_and(|reserve| reserve >= 300_000_000_000) {
        return Err("diagnostic report reserve must fit inside the fixed 300-second budget".into());
    }
    if diagnostic_release_faces && diagnostic_step0 {
        return Err(
            "release-face diagnosis belongs to the ordinary observed life, not step0 calibration"
                .into(),
        );
    }
    if diagnostic_solenoidal_lock && diagnostic_step0 {
        return Err("solenoidal-lock diagnosis requires the ordinary observed life".into());
    }
    Ok(ContinuingOptions {
        learn: learn.ok_or("--route observed requires --learn HLSN1")?,
        count,
        chart_manifest,
        population,
        keys,
        keys_sha256,
        work_deadline_ns,
        block_upper_ns_per_cell,
        sections_per_pass,
        stage1_probe_cells,
        evaluation_from_section,
        diagnostic_release_faces,
        diagnostic_solenoidal_lock,
        diagnostic_step0,
        diagnostic_calibration_only,
        diagnostic_checkpoint,
        diagnostic_profile_trunk_cells,
        diagnostic_profile_paired_cells64,
        diagnostic_cost_profile_cells64,
        diagnostic_report_reserve_ns,
    })
}

/// `⌊log₂ x⌋` of a positive rational, the exponent `e` of its dyadic enclosure `2^e ≤ x < 2^(e+1)`;
/// zero is written `z`.
#[cfg(test)]
fn dyadic(x: &Rat) -> String {
    if x.is_zero() {
        return "z".into();
    }
    let (p, r) = (x.numer().magnitude(), x.denom().magnitude());
    let k = p.bits() as i64 - r.bits() as i64;
    let at_least = if k >= 0 {
        *p >= (r << k as usize)
    } else {
        (p << (-k) as usize) >= *r
    };
    let e = if at_least { k } else { k - 1 };
    if x.is_negative() {
        format!("-{e}")
    } else {
        e.to_string()
    }
}

/// [agent-inferred, October 16] **Each family's certified step with its terms**,
/// as `locus/family:k|kC|kc|a|C|c|gain|moves|bound|readout|amplitude`, every term by its dyadic
/// enclosure exponent ([`dyadic`]). `k` is the published exponent; `kC = ⌊log₂(a/C)⌋` and
/// `kc = ⌊log₂(1/c)⌋` are the family's own two bounds read at the published ray (`CertifiedStep`).
/// `k = kc` places the step at the covector cap; `k = kC` at its own curvature `C = ½·κ²·b`, whose
/// parts are the gain `κ²` (with the readout's `‖R‖₂²` and the amplitude growth `1 + ω`) and the
/// moves `b`; `k` below both was set by the joint certificate, a standing lobe, or `b`'s growth
/// along a longer ray, which this reading does not separate.
#[cfg(test)]
fn step_certificates(reading: &DepositReading) -> String {
    let out: Vec<String> = reading
        .steps
        .iter()
        .map(|(locus, read)| {
            let step = &read.step;
            let own = |bound: &Rat| {
                if bound.is_zero() {
                    "-".to_string()
                } else {
                    dyadic(&(Rat::one() / bound))
                }
            };
            let curvature_bound = if step.curvature.is_zero() {
                "-".to_string()
            } else {
                dyadic(&(&step.alignment / &step.curvature))
            };
            format!(
                "{locus:?}/{:?}:{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
                read.family,
                step.exponent,
                curvature_bound,
                own(&step.covector),
                dyadic(&step.alignment),
                dyadic(&step.curvature),
                dyadic(&step.covector),
                dyadic(&read.gain),
                dyadic(&read.moves),
                dyadic(&read.bound),
                dyadic(&read.readout),
                dyadic(&read.amplitude),
            )
        })
        .collect();
    format!("[{}]", out.join(","))
}

/// [agent-inferred, October 16] **The pair moves' two Hölder pairings**, per
/// source ring and offset, on the moment the deposit's comparison read. `Moves::Pair` bounds
/// `|a_ρᵀ W_c b_ρ|² ≤ |a_ρ|₂² |b_ρ|₂² ‖W_c‖_F²` and sums the operand over the phases as
/// `E₂ = Σ_c ‖W_c‖_F²` (the deposit's `energy`). The dual pairing bounds the same contraction by
/// `|a_ρ|_∞² |b_ρ|_∞² ‖W_c‖₁²`, summed as `E₁ = Σ_c ‖W_c‖₁²` (entrywise `ℓ₁` within a phase).
/// Printed as `g/δ:N|E₂|E₁|a₂|a∞|b₂|b∞|lo|hi`: `N` the most occupied pairs in one phase, the norms
/// the largest squared over the ranks, every term by its dyadic exponent, and `lo`/`hi` the least
/// and greatest over the ranks of `⌊log₂⌋` of the ratio `ℓ₂-bound / ℓ₁-bound`.
#[cfg(test)]
fn pair_pairings(field: &Field, material: &Constitution, moment: &SourceMoment) -> Result<String> {
    let alphabet = field.alphabet();
    let mut out = Vec::new();
    for &g in field.sources() {
        let d = field.ring(g).placements().len();
        for &offset in field.offsets() {
            let Some(pair) = material.pair_port(g, offset) else {
                continue;
            };
            let Some(table) = moment.offset_table(field, g, offset)? else {
                out.push(format!("{g}/{offset}:empty"));
                continue;
            };
            let (mut most, mut two, mut one) = (0usize, Rat::zero(), Rat::zero());
            for c in 0..d {
                let entries = table.normalized(c, alphabet);
                most = most.max(entries.len());
                let mut l1 = Rat::zero();
                for (_, value) in &entries {
                    two += value * value;
                    l1 += value.abs();
                }
                one += &l1 * &l1;
            }
            let squared = |x: &[Rat]| x.iter().map(|v| v * v).sum::<Rat>();
            let widest = |x: &[Rat]| x.iter().map(|v| v * v).max().unwrap_or_else(Rat::zero);
            let mut norms = [Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()];
            let (mut lo, mut hi): (Option<Rat>, Option<Rat>) = (None, None);
            for (a, b) in pair.current_reads().iter().zip(pair.earlier_reads()) {
                let ranked = [squared(a), widest(a), squared(b), widest(b)];
                let l2 = &ranked[0] * &ranked[2] * &two;
                let l1 = &ranked[1] * &ranked[3] * &one;
                if !l1.is_zero() {
                    let ratio = l2 / l1;
                    lo = Some(match lo {
                        Some(x) if x <= ratio => x,
                        _ => ratio.clone(),
                    });
                    hi = Some(match hi {
                        Some(x) if x >= ratio => x,
                        _ => ratio,
                    });
                }
                for (held, read) in norms.iter_mut().zip(ranked) {
                    if read > *held {
                        *held = read;
                    }
                }
            }
            let shown = |x: &Option<Rat>| x.as_ref().map_or_else(|| "-".to_string(), dyadic);
            out.push(format!(
                "{g}/{offset}:{most}|{}|{}|{}|{}|{}|{}|{}|{}",
                dyadic(&two),
                dyadic(&one),
                dyadic(&norms[0]),
                dyadic(&norms[1]),
                dyadic(&norms[2]),
                dyadic(&norms[3]),
                shown(&lo),
                shown(&hi),
            ));
        }
    }
    Ok(format!("[{}]", out.join(",")))
}

fn mounted(port: &Reference, population: u64) -> Result<(Resident, PairingDeclaration)> {
    let field = field(population)?;
    let pairing = PairingDeclaration::Family {
        table: (0..CLASSES).map(|c| (c, c ^ 1)).collect(),
    };
    let receiving = field.receivers()[0].ring;
    let founded = Constitution::initial(&field, BUDGET)?.with_locking_pump(&field, receiving)?;
    let material = PairedCarrier::found(&field, founded, 0, &pairing)?.0;
    Ok((
        port.mount_with(&field, &Current::at_rest(&field), material)?,
        pairing,
    ))
}

#[cfg(test)]
#[path = "continuing/lock.rs"]
mod lock;

/// The protocol register's own serialized address, with whitespace-free field framing.
fn address_text(address: &ActiveAddress) -> String {
    let mut text = String::new();
    address.write(&mut text);
    format!(
        "[{}]",
        text.lines()
            .next()
            .unwrap_or("address")
            .split_whitespace()
            .skip(1)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn keys_line(section: usize, owner: &str, closed: &ClosedLocated) -> Option<String> {
    let report = closed.key.as_ref()?;
    let ReceiptDetail::Keys {
        fibres,
        orbits,
        fell_back,
        jumps,
        ..
    } = &report.detail
    else {
        return None;
    };
    Some(format!(
        "keys section={section} owner={owner} crib_length={} fibres={} orbits={} fell_back={} jumps={}",
        closed.crib_len,
        packed(fibres),
        packed(orbits),
        packed(fell_back),
        packed(jumps)
    ))
}

fn packed<T: std::fmt::Display>(values: &[T]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

struct PairReadSnapshot {
    ring: usize,
    offset: usize,
    current: Vec<Vec<Rat>>,
    earlier: Vec<Vec<Rat>>,
    matches_retained_face: Option<bool>,
}

impl PairReadSnapshot {
    fn exact_values(&self) -> (usize, usize, Vec<Vec<String>>, Vec<Vec<String>>) {
        let shown = |rows: &[Vec<Rat>]| {
            rows.iter()
                .map(|row| row.iter().map(ToString::to_string).collect())
                .collect()
        };
        (
            self.ring,
            self.offset,
            shown(&self.current),
            shown(&self.earlier),
        )
    }
}

struct PairFaceBoundary {
    rebuilds: BigUint,
    total_builds: BigUint,
    reads: Vec<PairReadSnapshot>,
}

/// An exterior boundary observation; it does not materialize a face or enter either clock.
fn pair_face_boundary(resident: &Resident) -> Result<PairFaceBoundary> {
    let moment = resident
        .continuing()
        .and_then(|(id, _)| resident.moment(&id));
    let mut reads = Vec::new();
    for &ring in resident.field().sources() {
        for &offset in resident.field().offsets() {
            if let Some(port) = resident.constitution().pair_port(ring, offset) {
                reads.push(PairReadSnapshot {
                    ring,
                    offset,
                    current: port.current_reads().to_vec(),
                    earlier: port.earlier_reads().to_vec(),
                    matches_retained_face: moment
                        .and_then(|m| m.pair_face_read_matches(ring, offset, port)),
                });
            }
        }
    }
    Ok(PairFaceBoundary {
        rebuilds: moment
            .map(|m| m.pair_face_summary().into_iter().map(|r| r.4).sum())
            .unwrap_or_default(),
        total_builds: moment
            .map(SourceMoment::pair_face_total_builds)
            .unwrap_or_default(),
        reads,
    })
}

/// Exterior receipt, called only after both Native and report clocks have stopped.
fn pair_face_line(
    resident: &Resident,
    section: usize,
    role: &str,
    unit: u64,
    before: &PairFaceBoundary,
) -> Result<String> {
    let (id, _) = resident
        .continuing()
        .ok_or("pair face receipt has no continuing moment")?;
    let moment = resident
        .moment(&id)
        .ok_or("pair face receipt has no moment")?;
    let after = pair_face_boundary(resident)?;
    if after.rebuilds < before.rebuilds || after.total_builds < before.total_builds {
        return Err("pair face exterior build counter regressed".into());
    }
    let retained_builds = &after.rebuilds - &before.rebuilds;
    let total_builds = &after.total_builds - &before.total_builds;
    if total_builds < retained_builds {
        return Err("pair face exterior owner counts disagree".into());
    }
    let other_copy_builds = total_builds - &retained_builds;
    let prior_read_mismatch: Vec<_> = before
        .reads
        .iter()
        .map(|r| (r.ring, r.offset, r.matches_retained_face))
        .collect();
    let deposit_reads_changed: Vec<_> = before
        .reads
        .iter()
        .zip(&after.reads)
        .map(|(a, b)| {
            (
                a.ring,
                a.offset,
                a.current != b.current,
                a.earlier != b.earlier,
            )
        })
        .collect();
    let read_values_before: Vec<_> = before
        .reads
        .iter()
        .map(PairReadSnapshot::exact_values)
        .collect();
    let read_values_after: Vec<_> = after
        .reads
        .iter()
        .map(PairReadSnapshot::exact_values)
        .collect();
    let summary = moment.pair_face_summary();
    // Read the published port, excluding its separate carried remainders. This exterior
    // count identifies the first nonzero output without entering either measured clock.
    let output_nonzero_ring_offset_entries: Vec<_> = summary
        .iter()
        .filter_map(|&(ring, offset, _, _, _)| {
            resident.constitution().pair_port(ring, offset).map(|port| {
                let entries = port.outputs().iter().flatten();
                (
                    ring,
                    offset,
                    entries.clone().count(),
                    entries.filter(|entry| !entry.is_zero()).count(),
                )
            })
        })
        .collect();
    let mut count_checks = Vec::new();
    if unit == 1 || unit % 100 == 0 {
        for &(ring, offset, _, _, _) in &summary {
            let mut population = 0u64;
            let mut occupied = 0usize;
            for phase in 0..resident.field().ring(ring).placements().len() {
                let counts = moment.offset_counts(ring, offset, phase)?;
                population += counts.iter().sum::<u64>();
                occupied += counts.iter().filter(|&&count| count != 0).count();
            }
            count_checks.push((ring, offset, population, occupied));
        }
    }
    let started = Instant::now();
    let clone = std::hint::black_box(moment.clone());
    let clone_ns = elapsed(started);
    drop(clone);
    let phase_wall_ns: Vec<_> = resident
        .wall()
        .phases()
        .into_iter()
        .map(|(name, time)| (name.replace(' ', "_"), time.as_nanos()))
        .collect();
    Ok(format!(
        "pair_face section={section} role={role} unit={unit} ring_offset_population_occupied_bindings_rebuilds={summary:?} clone_ns={clone_ns} phase_wall_ns={phase_wall_ns:?} retained_builds={retained_builds} other_copy_builds={other_copy_builds} prior_read_match={prior_read_mismatch:?} deposit_reads_changed={deposit_reads_changed:?} count_checks={count_checks:?} read_values_before={read_values_before:?} read_values_after={read_values_after:?} output_nonzero_ring_offset_entries={output_nonzero_ring_offset_entries:?}"
    ))
}

#[cfg(test)]
fn deliver(
    port: &Reference,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    cells: &[usize],
    section: usize,
    role: &str,
    published_total: &mut usize,
    emit: &mut dyn FnMut(String),
) -> Result<()> {
    for &class in cells {
        let boundary_before = pair_face_boundary(resident)?;
        let started = Instant::now();
        let native = port.observe_cell_continuing(
            resident,
            crib,
            pairing,
            class,
            None,
            |_, material, moment, address, reading| {
                (
                    material.clone(),
                    moment.clone(),
                    address.clone(),
                    reading.clone(),
                )
            },
        )?;
        let native_ns = elapsed(started);
        *published_total += usize::from(native.precision.event.is_some());
        // Only committed owned operands leave the native call. Formatting, diagnostic
        // pairings and emission below are exterior report work, timed separately.
        let (material, moment, active, reading) = &native.view;
        let address = address_text(active);
        let certificate = step_certificates(reading);
        let pairings = pair_pairings(resident.field(), material, moment)?;
        let (code, tree) = scored_code(&native.compare.detail)?;
        let wave = native
            .prediction
            .faces
            .first()
            .ok_or("blind prediction has no wave face")?
            .code_length(class)?;
        let ReceiptDetail::Deposit { reading, .. } = &native.deposit.detail else {
            return Err("observed deposit returned no reading".into());
        };
        emit(format!(
            "cell section={section} role={role} class={class} delivered={} address={address} code={} tree={} wave={} steps={} cell_ns={}",
            native.cells,
            enclosure(&code),
            tree.as_ref()
                .map_or_else(|| "unavailable".to_owned(), enclosure),
            enclosure(&wave),
            stepped_families(reading),
            native_ns
        ));
        let precision = &native.precision;
        emit(format!(
            "precision section={section} role={role} delivered={} resident_state_bits={} precision_checked={} precision_event={} published={} receiving_exponent={}→{} balance_before={:?} balance_after={:?}",
            native.cells,
            resident.state_bits(),
            precision.checked,
            if precision.event.is_some() {
                "applied"
            } else {
                "none"
            },
            precision.event.is_some(),
            precision.before_exponent,
            precision.after_exponent,
            precision.balance_before,
            precision.balance_after,
        ));
        emit(format!(
            "cert section={section} role={role} delivered={} steps={certificate}",
            native.cells
        ));
        emit(format!(
            "pairing section={section} role={role} delivered={} pairings={pairings}",
            native.cells
        ));
        if let Some(line) = native
            .close
            .as_ref()
            .and_then(|closed| keys_line(section, "trunk", closed))
        {
            emit(line);
        }
        // This interval includes diagnostics and all preceding emissions, excluding
        // the whole native call; the timing line does not time its own emission.
        let report_ns = elapsed(started) - native_ns;
        emit(format!(
            "report section={section} role={role} delivered={} report_ns={report_ns}",
            native.cells
        ));
        // Outside both timed intervals: where the retained bits sit, by locus (its lattice
        // exponent, entry, remainder and solved-chart bits), and each source law's solved chart
        // (its exponent `L_s`, prior scale `k`, support width and certificate `δ`).
        let material = resident.constitution();
        let loci: Vec<_> = material
            .carrier_bits_by_locus()
            .into_iter()
            .map(|(locus, bits)| {
                let exponent = material.lattice(locus).ok().map(|l| l.exponent());
                (locus, exponent, bits.entries, bits.remainders, bits.solved)
            })
            .collect();
        let charts: Vec<_> = resident
            .field()
            .sources()
            .iter()
            .filter_map(|&ring| {
                material.source_law(ring).map(|law| {
                    let chart = law.chart();
                    (
                        ring,
                        chart.exponent(),
                        chart.scale(),
                        chart.support().len(),
                        chart.certificate().to_string(),
                    )
                })
            })
            .collect();
        let chart_rules: Vec<_> = resident
            .field()
            .sources()
            .iter()
            .map(|&ring| {
                let rule = material.chart_rule(Locus::SourcePort(ring))?;
                let law = material
                    .source_law(ring)
                    .ok_or(HnnError::MissingSourcePort { ring })?;
                Ok((
                    ring,
                    law.chart_rule_exponent(&rule)?,
                    rule.target().to_string(),
                ))
            })
            .collect::<std::result::Result<_, HnnError>>()?;
        emit(format!(
            "state section={section} role={role} delivered={} state_bits={} constitution_bits={} loci_exponent_entries_remainders_solved={loci:?} source_chart_ring_exponent_scale_support_certificate={charts:?} source_chart_ring_rule_exponent_target={chart_rules:?}",
            native.cells,
            resident.state_bits(),
            material.exact_bits()
        ));
        emit(pair_face_line(
            resident,
            section,
            role,
            native.cells,
            &boundary_before,
        )?);
        emit(format!(
            "marginal_face section={section} role={role} delivered={} held_matches={:?} totals={:?}",
            native.cells,
            resident
                .constitution()
                .source_port(0)
                .map(|_| moment.marginal_face_matches(resident.field(), material))
                .transpose()?,
            moment.marginal_face_audit(),
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stop {
    EndLetter,
    Held,
    Horizon {
        population: u64,
        source_operand_bound: u128,
    },
    Maximum,
    EntropyRate {
        drawn_cells: usize,
        lower: Rat,
        threshold: Rat,
    },
}
impl Stop {
    fn fields(&self) -> String {
        match self {
            Self::EndLetter => "stop=end_letter value=end_letter".to_owned(),
            Self::Held => "stop=held value=held".to_owned(),
            Self::Horizon {
                population,
                source_operand_bound,
            } => format!(
                "stop=horizon value=horizon population={population} source_operand_bound={source_operand_bound}"
            ),
            Self::Maximum => "stop=maximum value=maximum".to_owned(),
            Self::EntropyRate {
                drawn_cells,
                lower,
                threshold,
            } => format!(
                "stop=entropy_rate value=entropy_rate drawn_cells={drawn_cells} lower={lower} threshold={threshold}"
            ),
        }
    }
}

/// Release scale is learned only from targets already delivered on the same chart.
#[derive(Default)]
struct ReleaseHistory(std::collections::BTreeMap<sections::ChartKind, usize>);
impl ReleaseHistory {
    fn maximum(&self, chart: sections::ChartKind) -> usize {
        self.0.get(&chart).copied().unwrap_or(0)
    }
    fn heard_target(&mut self, chart: sections::ChartKind, target_cells: usize) {
        let maximum = self.0.entry(chart).or_default();
        *maximum = (*maximum).max(target_cells);
    }
}

const _: () = assert!(CLASSES.is_power_of_two());
const ENTROPY_RATE_BITS: u32 = CLASSES.trailing_zeros();

fn entropy_rate_stop(lower: &Rat, drawn_cells: usize) -> Option<Stop> {
    if drawn_cells == 0 {
        return None;
    }
    let threshold = Rat::from_integer(BigInt::from(drawn_cells) * BigInt::from(ENTROPY_RATE_BITS));
    (lower >= &threshold).then(|| Stop::EntropyRate {
        drawn_cells,
        lower: lower.clone(),
        threshold,
    })
}

/// The completed drawn prefix: the framing end precedes its code-rate stop.
fn completed_release_stop(classes: &[usize], lower: &Rat) -> Option<Stop> {
    if sections::closes(classes) {
        Some(Stop::EndLetter)
    } else {
        entropy_rate_stop(lower, classes.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Released {
    classes: Vec<usize>,
    stop: Stop,
    maximum: usize,
}
impl Released {
    fn line(&self, section: usize) -> String {
        format!(
            "observed_release section={section} classes={} {} maximum={} text={:?}",
            packed(&self.classes),
            self.stop.fields(),
            self.maximum,
            shown(&sections::pieces_of(&self.classes))
        )
    }
}

/// Only private clones receive draws and native ingest; the trunk and its crib stay exact.
#[cfg(test)]
fn release_fork(
    port: &Reference,
    trunk: &Resident,
    trunk_crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    maximum: usize,
    keys: &mut KeyStream,
    section: usize,
    emit: &mut dyn FnMut(String),
) -> Result<Released> {
    release_fork_accounted(
        port,
        trunk.clone(),
        trunk_crib.clone(),
        pairing,
        maximum,
        keys,
        section,
        None,
        true,
        None,
        None,
        emit,
    )
}

#[allow(clippy::too_many_arguments)]
fn release_fork_accounted(
    port: &Reference,
    mut fork: Resident,
    mut crib: ObservedCrib,
    pairing: &PairingDeclaration,
    maximum: usize,
    keys: &mut KeyStream,
    section: usize,
    mut work: Option<&mut work::ObservedWork>,
    detailed: bool,
    mut face_decisions: Option<&mut Vec<holonics::hnn::receiving::cells::CellDecision>>,
    mut solenoidal: Option<&mut solenoidal::Trace>,
    emit: &mut dyn FnMut(String),
) -> Result<Released> {
    if maximum == 0 {
        return Ok(Released {
            classes: Vec::new(),
            stop: Stop::Maximum,
            maximum,
        });
    }
    let mut classes = Vec::new();
    let mut stop = Stop::Maximum;
    let mut drawn_lower = Rat::zero();
    for index in 0..maximum {
        if let Some(work) = work.as_deref_mut() {
            work.check()?;
        }
        let started = Instant::now();
        let boundary_before = if detailed {
            Some(pair_face_boundary(&fork)?)
        } else {
            None
        };
        let (moment, _) = fork
            .continuing()
            .ok_or("question end has no continuing moment")?;
        let phases = fork
            .admitted()
            .first()
            .ok_or("no admitted receiver")?
            .clone();
        let active = fork.address().clone();
        let before_exponent = fork
            .constitution()
            .lattice(Locus::ReceivingMap(phases.ring()))?
            .exponent();
        let draw_started = Instant::now();
        let (pending, _) = port.refine(&mut fork, &moment, &phases)?;
        if let Some(trace) = solenoidal.as_deref_mut() {
            trace.before(fork.field(), fork.current());
        }
        let drawn = port
            .release_cells(&mut fork, &pending, CellLaw::Draw(keys))?
            .forward
            .into_present()
            .ok_or("native draw returned no cells")?;
        let draw_ns = elapsed(draw_started);
        let cell = drawn.cells.first().ok_or("native draw decided no cell")?;
        if let Some(decisions) = face_decisions.as_deref_mut() {
            decisions.push(cell.clone());
        }
        let Some(class) = cell.class() else {
            port.discard(&mut fork, Handle::Pending(pending))?;
            stop = Stop::Held;
            if let Some(work) = work.as_deref_mut() {
                work.complete(1, elapsed(started), emit)?;
            }
            break;
        };
        let ingest_started = Instant::now();
        let ingestion = port
            .ingest_released_cell_continuing(&mut fork, &mut crib, pairing, pending, cell, None);
        // The native join preserves its pending operand on refusal. This private caller
        // abandons the draw as before, including at the typed source horizon.
        if ingestion.is_err() {
            port.discard(&mut fork, Handle::Pending(pending))?;
        }
        let native_ns = draw_ns + elapsed(ingest_started);
        let address = address_text(&active);
        let code = drawn_code(cell, class)?;
        emit(format!(
            "drawn section={section} index={index} class={class} address={address} drawn_code={} cell_ns={} resident_state_bits={} precision_event=none published=false receiving_exponent={}→{}",
            enclosure(&code),
            native_ns,
            fork.state_bits(),
            before_exponent,
            fork.constitution()
                .lattice(Locus::ReceivingMap(phases.ring()))?
                .exponent()
        ));
        let mut horizon = false;
        match ingestion {
            Ok(native) => {
                if let Some(trace) = solenoidal.as_deref_mut() {
                    trace.accepted(fork.field(), fork.current());
                }
                if let Some(line) = native
                    .close
                    .as_ref()
                    .and_then(|closed| keys_line(section, "fork", closed))
                {
                    emit(line);
                }
            }
            Err(HnnError::Horizon {
                population,
                source_operand_bound,
            }) => {
                stop = Stop::Horizon {
                    population,
                    source_operand_bound,
                };
                horizon = true;
            }
            Err(error) => return Err(error.into()),
        }
        let report_ns = elapsed(started) - native_ns;
        emit(format!(
            "report section={section} role=drawn index={index} report_ns={report_ns}"
        ));
        if let Some(boundary_before) = boundary_before {
            emit(pair_face_line(
                &fork,
                section,
                "drawn",
                u64::try_from(index)?,
                &boundary_before,
            )?);
        }
        if let Some(work) = work.as_deref_mut() {
            work.complete(1, elapsed(started), emit)?;
        }
        if horizon {
            break;
        }
        classes.push(class);
        drawn_lower += &code.lower;
        if let Some(completed) = completed_release_stop(&classes, &drawn_lower) {
            stop = completed;
            break;
        }
    }
    Ok(Released {
        classes,
        stop,
        maximum,
    })
}

#[cfg(test)]
fn section(
    port: &Reference,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    input: &Section,
    index: usize,
    longest: &mut ReleaseHistory,
    keys: &mut KeyStream,
    published_total: &mut usize,
    emit: &mut dyn FnMut(String),
) -> Result<Released> {
    // A target belongs to its source chart. Reject ambiguous mixed/empty sources before
    // delivering anything; no target bytes are used to guess a chart.
    let chart_kind = input.chart_kind()?;
    for passage in &input.passages {
        let chart = passage.encode_chart()?;
        emit(format!(
            "observed_chart section={index} {}",
            chart.summary()
        ));
        let source = chart.cells();
        deliver(
            port,
            resident,
            crib,
            pairing,
            &source,
            index,
            "source",
            published_total,
            emit,
        )?;
    }
    let released = release_fork(
        port,
        resident,
        crib,
        pairing,
        longest.maximum(chart_kind),
        keys,
        index,
        emit,
    )?;
    emit(released.line(index));
    let answer = input.target_cells(index)?;
    deliver(
        port,
        resident,
        crib,
        pairing,
        &answer,
        index,
        "answer",
        published_total,
        emit,
    )?;
    longest.heard_target(chart_kind, answer.len());
    Ok(released)
}

fn header_line(resident: &Resident) -> Result<String> {
    let source = resident.field().sources()[0];
    let bound = resident
        .field()
        .source_operand_bound(Locus::SourcePort(source))
        .ok_or("source operand bound was not declared")?;
    let lattice = resident
        .field()
        .lattice(Locus::SourcePort(source))
        .ok_or("source lattice was not declared")?
        .exponent();
    let declaration = resident.field().crib();
    Ok(format!(
        "observed_continuing route=observed precision=derived population={} source_operand_bound={bound} source_lattice_exponent={lattice} crib_window={} crib_offset={} provenance=exterior",
        resident.field().population(),
        declaration.window,
        declaration.offset
    ))
}

/// The Python framer's HLCM1 boundary manifest, parsed without a JSON dependency.
/// Domain `HLCM1\n`, u64 BE record count; each record has section index (u64), passage
/// count (u32), then per passage kind (u8), chart length (u64), SHA256 (32 raw bytes),
/// canonical fibre length (u64) and SHA256 (32 raw bytes); finally target-octet length
/// (u64) and raw-octet SHA256 (32 bytes). Counts describe the framed sections, not hearings.
struct ChartManifestReader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl ChartManifestReader<'_> {
    fn take(&mut self, count: usize) -> Result<&[u8]> {
        let end = self
            .at
            .checked_add(count)
            .filter(|&end| end <= self.bytes.len())
            .ok_or("truncated chart manifest")?;
        let value = &self.bytes[self.at..end];
        self.at = end;
        Ok(value)
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into()?))
    }
    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into()?))
    }
    fn digest(&mut self) -> Result<String> {
        Ok(self
            .take(32)?
            .iter()
            .map(|value| format!("{value:02x}"))
            .collect())
    }
}

/// Native Rust codecs own this parity comparison. A mismatch refuses before any mount,
/// source delivery or diagnostic setup; an explicit frame limit can select a manifest prefix.
pub(super) fn validate_chart_manifest(
    frames: &[Section],
    bytes: &[u8],
    allow_prefix: bool,
) -> Result<()> {
    let mut reader = ChartManifestReader { bytes, at: 0 };
    if reader.take(6)? != b"HLCM1\n" {
        return Err("wrong chart manifest domain".into());
    }
    let count = usize::try_from(reader.u64()?)?;
    if count > bytes.len() / 52 || frames.len() > count || (!allow_prefix && frames.len() != count)
    {
        return Err("chart manifest section count differs from the selected frames".into());
    }
    for index in 0..count {
        if reader.u64()? != u64::try_from(index)? {
            return Err("chart manifest section order differs".into());
        }
        let passages = usize::try_from(reader.u32()?)?;
        if let Some(frame) = frames.get(index) {
            frame.chart_kind()?;
            if frame.passages.len() != passages {
                return Err(
                    format!("chart manifest passage count differs at section {index}").into(),
                );
            }
        }
        if passages > (reader.bytes.len() - reader.at) / 81 {
            return Err("chart manifest passage count exceeds its extent".into());
        }
        for passage_index in 0..passages {
            let kind = reader.take(1)?[0];
            let octets = reader.u64()?;
            let chart_digest = reader.digest()?;
            let fibre_bytes = reader.u64()?;
            let fibre_digest = reader.digest()?;
            if kind > 2 {
                return Err("unknown chart manifest kind".into());
            }
            if let Some(frame) = frames.get(index) {
                let summary = frame.passages[passage_index].encode_chart()?.summary();
                if summary.kind.byte() != kind
                    || u64::try_from(summary.chart_octets)? != octets
                    || summary.chart_sha256 != chart_digest
                    || summary.fibre_bytes != u128::from(fibre_bytes)
                    || summary.fibre_sha256 != fibre_digest
                {
                    return Err(format!("Rust/Python chart or fibre drift at section {index} passage {passage_index}").into());
                }
            }
        }
        let target_octets = reader.u64()?;
        let target_digest = reader.digest()?;
        if let Some(frame) = frames.get(index) {
            if u64::try_from(frame.target.len())? != target_octets
                || sections::sha256(&frame.target) != target_digest
            {
                return Err(format!("chart manifest target differs at section {index}").into());
            }
        }
    }
    if reader.at != bytes.len() {
        return Err("excess chart manifest bytes".into());
    }
    Ok(())
}

pub fn run(port: &Reference, args: &[String]) -> Result<()> {
    run_selected(port, args, None)
}

/// Select an actual observed-epoch realization without changing the native
/// comparison, transaction, exterior release, or checkpoint owners.
pub fn run_with_execution(
    port: &Reference,
    args: &[String],
    execution: &dyn ObservedEpochExecution,
) -> Result<()> {
    run_selected(port, args, Some(execution))
}

fn run_selected(
    port: &Reference,
    args: &[String],
    execution: Option<&dyn ObservedEpochExecution>,
) -> Result<()> {
    let options = parse(args)?;
    if execution.is_some() && options.diagnostic_step0 {
        return Err("selected epoch execution requires the ordinary observed route".into());
    }
    // Exterior codec parity is checked before either ordinary mounting or a diagnostic route.
    // Explicit --learn-count permits only a checked prefix, including the two-frame cost probe.
    let checked_frames = if let Some(path) = &options.chart_manifest {
        let frames = sections_of(Some(&options.learn), options.count)?;
        let manifest = read(path)?;
        validate_chart_manifest(&frames, &manifest, options.count.is_some())?;
        stage1::validate_evaluation_extent(frames.len(), options.evaluation_from_section)?;
        println!(
            "chart_manifest checked_sections={} sha256={} codec_owner=rust",
            frames.len(),
            sections::sha256(&manifest)
        );
        Some(frames)
    } else {
        None
    };
    if options.diagnostic_step0 {
        if options.diagnostic_cost_profile_cells64 {
            let checkpoint = options
                .diagnostic_checkpoint
                .clone()
                .ok_or("cost profiling requires --diagnostic-checkpoint DIR")?;
            return diagnostic::run(port, options, Some(&checkpoint), checked_frames);
        }
        if options.diagnostic_calibration_only
            || options.diagnostic_profile_trunk_cells.is_some()
            || options.diagnostic_profile_paired_cells64
        {
            return diagnostic::run(port, options, None, checked_frames);
        }
        if options.diagnostic_report_reserve_ns.is_none() {
            return Err("full diagnostic requires an explicit --diagnostic-report-reserve-ns within the fixed total budget".into());
        }
        let checkpoint = options
            .diagnostic_checkpoint
            .clone()
            .ok_or("full --diagnostic-step0 requires --diagnostic-checkpoint DIR")?;
        return diagnostic::run(port, options, Some(&checkpoint), checked_frames);
    }
    let keys = options
        .keys
        .as_deref()
        .ok_or("--route observed requires --keys for exterior native draws")?;
    let key_bytes = read(keys)?;
    let key_sha256 = sections::sha256(&key_bytes);
    if options
        .keys_sha256
        .as_ref()
        .is_some_and(|expected| expected != &key_sha256)
    {
        return Err("scientific draw-key file differs from --keys-sha256; nothing mounted".into());
    }
    println!(
        "observed_keys sha256={key_sha256} bytes={} key_width_bytes={RELEASE_KEY_BYTES} complete_keys={} trailing_bytes={} expected_pin_checked={}",
        key_bytes.len(),
        key_bytes.len() / RELEASE_KEY_BYTES,
        key_bytes.len() % RELEASE_KEY_BYTES,
        options.keys_sha256.is_some()
    );
    let (mut resident, pairing) = mounted(port, options.population)?;
    let mut crib = ObservedCrib::new(0);
    let mut keys = KeyStream::new(key_bytes, RELEASE_KEY_BYTES)?;
    let frames = match checked_frames {
        Some(frames) => frames,
        None => sections_of(Some(&options.learn), options.count)?,
    };
    println!("{}", header_line(&resident)?);
    stage1::run(
        port,
        execution,
        &mut resident,
        &mut crib,
        &pairing,
        &frames,
        &options,
        &mut keys,
        &mut |line| println!("{line}"),
    )
}

#[path = "continuing/diagnostic.rs"]
mod diagnostic;
#[path = "continuing/face_readings.rs"]
mod face_readings;
#[path = "continuing/mutual.rs"]
mod mutual;
#[path = "continuing/solenoidal.rs"]
mod solenoidal;
#[path = "continuing/stage1.rs"]
mod stage1;
#[path = "continuing/work.rs"]
mod work;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::octets::{Cost, ingest, options, take_route};
    use holonics::hnn::encoding::observed::PairedObservation;
    use holonics::ratio::integer;
    use std::collections::BTreeSet;

    fn boundary_manifest(frames: &[Section]) -> Vec<u8> {
        fn digest(bytes: &mut Vec<u8>, text: &str) {
            for i in (0..text.len()).step_by(2) {
                bytes.push(u8::from_str_radix(&text[i..i + 2], 16).unwrap());
            }
        }
        let mut bytes = b"HLCM1\n".to_vec();
        bytes.extend((frames.len() as u64).to_be_bytes());
        for (index, frame) in frames.iter().enumerate() {
            bytes.extend((index as u64).to_be_bytes());
            bytes.extend((frame.passages.len() as u32).to_be_bytes());
            for passage in &frame.passages {
                let summary = passage.encode_chart().unwrap().summary();
                bytes.push(summary.kind.byte());
                bytes.extend((summary.chart_octets as u64).to_be_bytes());
                digest(&mut bytes, &summary.chart_sha256);
                bytes.extend((summary.fibre_bytes as u64).to_be_bytes());
                digest(&mut bytes, &summary.fibre_sha256);
            }
            bytes.extend((frame.target.len() as u64).to_be_bytes());
            digest(&mut bytes, &sections::sha256(&frame.target));
        }
        bytes
    }

    #[test]
    fn native_manifest_refuses_chart_fibre_target_and_frame_count_drift() {
        let frames = vec![
            Section {
                passages: vec![sections::Passage::Octets(b"abc".to_vec())],
                target: b"7".to_vec(),
            },
            Section {
                passages: vec![sections::Passage::Pcm {
                    rate: 16000,
                    samples: vec![0, 1, -2],
                }],
                target: b"8".to_vec(),
            },
        ];
        let bytes = boundary_manifest(&frames);
        validate_chart_manifest(&frames, &bytes, false).unwrap();
        validate_chart_manifest(&frames[..1], &bytes, true).unwrap();
        assert!(validate_chart_manifest(&frames[..1], &bytes, false).is_err());
        let mut wrong_source = frames.clone();
        wrong_source[0].passages = vec![sections::Passage::Octets(b"abd".to_vec())];
        assert!(validate_chart_manifest(&wrong_source, &bytes, false).is_err());
        let mut wrong_target = frames.clone();
        wrong_target[0].target = b"9".to_vec();
        assert!(validate_chart_manifest(&wrong_target, &bytes, false).is_err());
        for at in [14 + 12, 14 + 21, 14 + 61] {
            let mut drift = bytes.clone();
            drift[at] ^= 1;
            assert!(validate_chart_manifest(&frames, &drift, false).is_err());
        }
        for length in [0, 5, 14, bytes.len() - 1] {
            assert!(validate_chart_manifest(&frames, &bytes[..length], false).is_err());
        }
        let mut excess = bytes;
        excess.push(0);
        assert!(validate_chart_manifest(&frames, &excess, false).is_err());
    }

    #[test]
    fn manifest_option_is_an_exterior_input_and_entropy_comes_from_the_aperture() {
        let options = parse(&args(&[
            "--population",
            "65536",
            "--chart-manifest",
            "micro.charts",
            "--learn-count",
            "2",
        ]))
        .unwrap();
        assert_eq!(options.chart_manifest.as_deref(), Some("micro.charts"));
        assert_eq!(options.count, Some(2));
        assert_eq!(1usize << ENTROPY_RATE_BITS, CLASSES);
    }
    fn args(extra: &[&str]) -> Vec<String> {
        ["--learn", "unread.hlsn", "--keys", "unread.keys"]
            .into_iter()
            .chain(extra.iter().copied())
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn evaluation_cli_requires_manifest_and_excludes_probe_and_diagnostic() {
        for extra in [
            vec!["--evaluation-from-section", "1"],
            vec!["--chart-manifest", "m", "--evaluation-from-section", "0"],
            vec![
                "--chart-manifest",
                "m",
                "--evaluation-from-section",
                "1",
                "--stage1-probe-cells",
                "1",
            ],
            vec![
                "--chart-manifest",
                "m",
                "--evaluation-from-section",
                "1",
                "--diagnostic-step0",
            ],
        ] {
            let mut supplied = vec!["--population", "65536"];
            supplied.extend(extra);
            assert!(parse(&args(&supplied)).is_err());
        }
        let options = parse(&args(&[
            "--population",
            "65536",
            "--chart-manifest",
            "m",
            "--evaluation-from-section",
            "30",
        ]))
        .unwrap();
        assert_eq!(options.evaluation_from_section, Some(30));
    }

    #[test]
    fn diagnostic_only_cli_options_require_explicit_diagnostic_mode() {
        let upper = [
            "--learn",
            "unread.hlsn",
            "--population",
            "1",
            "--diagnostic-unit-upper-ns",
            "10",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
        assert!(parse(&upper).is_err());
        let paired = [
            "--learn",
            "unread.hlsn",
            "--population",
            "1",
            "--diagnostic-profile-paired-cells64",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
        assert!(parse(&paired).is_err());
        let checkpoint = [
            "--learn",
            "unread.hlsn",
            "--population",
            "1",
            "--diagnostic-checkpoint",
            "unused",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
        assert!(parse(&checkpoint).is_err());
    }

    #[test]
    fn diagnostic_profile_is_a_bounded_separate_work_partition() {
        let declared = |extra: &[&str]| {
            [
                "--learn",
                "unread.hlsn",
                "--population",
                "65536",
                "--diagnostic-step0",
            ]
            .into_iter()
            .chain(extra.iter().copied())
            .map(str::to_owned)
            .collect::<Vec<_>>()
        };
        let profile = parse(&declared(&["--diagnostic-profile-trunk-cells", "64"])).unwrap();
        assert_eq!(profile.diagnostic_profile_trunk_cells, Some(64));
        assert!(!profile.diagnostic_profile_paired_cells64);
        assert!(profile.diagnostic_checkpoint.is_none());
        let paired = parse(&declared(&["--diagnostic-profile-paired-cells64"])).unwrap();
        assert!(paired.diagnostic_profile_paired_cells64);
        assert_eq!(paired.diagnostic_profile_trunk_cells, None);
        assert!(paired.diagnostic_checkpoint.is_none());
        for extra in [
            vec!["--diagnostic-profile-trunk-cells", "0"],
            vec!["--diagnostic-profile-trunk-cells", "313"],
            vec![
                "--diagnostic-profile-trunk-cells",
                "64",
                "--diagnostic-checkpoint",
                "unused",
            ],
            vec![
                "--diagnostic-profile-trunk-cells",
                "64",
                "--diagnostic-calibration-only",
            ],
            vec!["--diagnostic-unit-upper-ns", "195882064"],
            vec!["--diagnostic-report-reserve-ns", "300000000000"],
            vec![
                "--diagnostic-profile-paired-cells64",
                "--diagnostic-profile-trunk-cells",
                "64",
            ],
            vec![
                "--diagnostic-profile-paired-cells64",
                "--diagnostic-checkpoint",
                "unused",
            ],
        ] {
            assert!(parse(&declared(&extra)).is_err(), "{extra:?}");
        }
    }
    fn keys() -> KeyStream {
        KeyStream::new(vec![0; 1 << 16], RELEASE_KEY_BYTES).unwrap()
    }

    #[test]
    fn face_diagnosis_is_explicit_and_does_not_change_the_life_plan() {
        let base = args(&["--population", "65536"]);
        let plain = parse(&base).unwrap();
        assert!(!plain.diagnostic_release_faces);
        let mut traced = base;
        traced.push("--diagnostic-release-faces".to_owned());
        let traced = parse(&traced).unwrap();
        assert!(traced.diagnostic_release_faces);
        assert_eq!(traced.count, plain.count);
        assert_eq!(
            traced.evaluation_from_section,
            plain.evaluation_from_section
        );
        assert_eq!(traced.population, plain.population);
        assert_eq!(traced.keys, plain.keys);
        assert_eq!(traced.work_deadline_ns, plain.work_deadline_ns);
    }

    #[test]
    fn solenoidal_lock_diagnosis_is_opt_in_on_the_ordinary_life() {
        let plain = parse(&args(&["--population", "65536"])).unwrap();
        assert!(!plain.diagnostic_solenoidal_lock);
        let traced = parse(&args(&[
            "--population",
            "65536",
            "--diagnostic-solenoidal-lock",
        ]))
        .unwrap();
        assert!(traced.diagnostic_solenoidal_lock);
        assert_eq!(traced.population, plain.population);
        assert_eq!(traced.count, plain.count);
        assert_eq!(traced.keys, plain.keys);
        assert_eq!(traced.work_deadline_ns, plain.work_deadline_ns);
        assert!(parse(&args(&[
            "--population",
            "65536",
            "--diagnostic-step0",
            "--diagnostic-solenoidal-lock",
        ]))
        .is_err());
    }

    #[test]
    fn face_diagnosis_preserves_native_draw_stop_keys_and_trunk() {
        let port = Reference::new(4, BUDGET);
        let (mut resident, pairing) = mounted(&port, 65536).unwrap();
        let mut crib = ObservedCrib::new(0);
        for class in [0, 1, 2, 3] {
            port.observe_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                class,
                None,
                |_, _, _, _, _| (),
            )
            .unwrap();
        }
        let constitution = resident.constitution().clone();
        let current = resident.current().clone();
        let mut plain_keys = keys();
        let mut traced_keys = keys();
        let mut decisions = Vec::new();
        let mut solenoidal = solenoidal::Trace::new(resident.field(), resident.current());
        let plain = release_fork_accounted(
            &port,
            resident.clone(),
            crib.clone(),
            &pairing,
            4,
            &mut plain_keys,
            0,
            None,
            false,
            None,
            None,
            &mut |_| (),
        )
        .unwrap();
        let traced = release_fork_accounted(
            &port,
            resident.clone(),
            crib.clone(),
            &pairing,
            4,
            &mut traced_keys,
            0,
            None,
            false,
            Some(&mut decisions),
            Some(&mut solenoidal),
            &mut |_| (),
        )
        .unwrap();
        assert_eq!(traced, plain);
        assert_eq!(traced_keys.keys_read(), plain_keys.keys_read());
        assert!(!decisions.is_empty());
        for decision in &decisions {
            assert_eq!(
                decision.face,
                decision
                    .scored_face
                    .as_ref()
                    .unwrap()
                    .masses_at(decision.bits)
                    .unwrap()
            );
        }
        let key_count = traced_keys.keys_read();
        for target in [
            b"A".as_slice(),
            b"an entirely different exterior truth".as_slice(),
        ] {
            let mut lines = Vec::new();
            face_readings::report(
                0,
                4,
                &sections::closed_cells(target),
                &traced,
                &decisions,
                &[],
                false,
                (0, 4, 0),
                &mut |line| lines.push(line),
            )
            .unwrap();
            assert!(lines[0].contains("reference_was_heard=false"));
            assert!(
                lines
                    .iter()
                    .any(|line| line.starts_with("observed_release_face "))
            );
        }
        let mut solenoidal_lines = Vec::new();
        solenoidal.report(
            0,
            &traced.classes,
            &sections::closed_cells(b"A"),
            &mut |line| solenoidal_lines.push(line),
        );
        assert!(
            solenoidal_lines
                .iter()
                .any(|line| line.starts_with("observed_solenoidal_coupling "))
        );
        assert!(
            solenoidal_lines
                .iter()
                .any(|line| line.contains("status=available"))
        );
        assert_eq!(traced_keys.keys_read(), key_count);
        assert_eq!(resident.constitution(), &constitution);
        assert_eq!(resident.current(), &current);
    }
    fn one() -> Section {
        Section {
            passages: vec![sections::Passage::Octets(vec![b'A'])],
            target: vec![b'B'],
        }
    }
    fn fill(port: &Reference, trunk: &mut Resident, pairing: &PairingDeclaration, count: usize) {
        let encoded = PairedObservation::admit(trunk.field(), trunk.constitution(), pairing)
            .unwrap()
            .encode(&vec![0; count])
            .unwrap();
        ingest(port, trunk, None, &encoded, &mut Cost::default()).unwrap();
    }

    #[test]
    fn observed_cells_keep_the_retained_pair_faces_before_pending_copies_read() {
        let port = Reference::new(4, BUDGET);
        let (mut resident, pairing) = mounted(&port, 65536).unwrap();
        let mut crib = ObservedCrib::new(0);
        let mut published = 0;
        for class in (0..20).map(|i| i % 4) {
            let mut exterior = Vec::new();
            deliver(
                &port,
                &mut resident,
                &mut crib,
                &pairing,
                &[class],
                0,
                "source",
                &mut published,
                &mut |line| {
                    if line.starts_with("pair_face ") {
                        exterior.push(line);
                    }
                },
            )
            .unwrap();
            assert_eq!(exterior.len(), 1);
            assert!(
                exterior[0].contains("other_copy_builds=0 "),
                "{}",
                exterior[0]
            );
            let (id, _) = resident.continuing().unwrap();
            let moment = resident.moment(&id).unwrap();
            let rows = moment.pair_face_summary();
            assert_eq!(rows.len(), resident.field().offsets().len());
            for (ring, offset, population, occupied, _) in rows {
                assert_eq!(population, moment.pair_population(ring, offset).unwrap());
                let expected: usize = (0..resident.field().ring(ring).placements().len())
                    .map(|phase| {
                        moment
                            .offset_counts(ring, offset, phase)
                            .unwrap()
                            .iter()
                            .filter(|&&c| c != 0)
                            .count()
                    })
                    .sum();
                assert_eq!(occupied, expected);
            }
        }
    }
    #[test]
    fn release_history_uses_only_prior_targets_on_its_chart() {
        let mut history = ReleaseHistory::default();
        assert_eq!(history.maximum(sections::ChartKind::Octets), 0);
        history.heard_target(sections::ChartKind::Octets, 6);
        history.heard_target(sections::ChartKind::Octets, 4);
        assert_eq!(history.maximum(sections::ChartKind::Octets), 6);
        assert_eq!(history.maximum(sections::ChartKind::Raster), 0);
        history.heard_target(sections::ChartKind::Raster, 2);
        assert_eq!(history.maximum(sections::ChartKind::Raster), 2);
        assert_eq!(history.maximum(sections::ChartKind::Pcm), 0);
    }

    #[test]
    fn cost_profile_is_explicit_exclusive_and_requires_its_checkpoint() {
        let flag = "--diagnostic-cost-profile-cells64";
        let base = [
            "--population",
            "65536",
            "--diagnostic-step0",
            flag,
            "--diagnostic-checkpoint",
            "unused",
        ];
        assert!(parse(&args(&["--population", "65536", flag])).is_err());
        assert!(
            parse(&args(&[
                "--population",
                "65536",
                "--diagnostic-step0",
                flag
            ]))
            .is_err()
        );
        assert!(parse(&args(&base)).unwrap().diagnostic_cost_profile_cells64);
        for extra in [
            "--diagnostic-calibration-only",
            "--diagnostic-profile-paired-cells64",
        ] {
            let mut all = base.to_vec();
            all.push(extra);
            assert!(parse(&args(&all)).is_err());
        }
        let mut all = base.to_vec();
        all.extend(["--diagnostic-profile-trunk-cells", "64"]);
        assert!(parse(&args(&all)).is_err());
    }

    #[test]
    fn entropy_stop_uses_exact_lower_endpoint_at_first_drawn_cell() {
        use holonics::ratio::rat;
        assert!(entropy_rate_stop(&integer(100), 0).is_none());
        assert!(entropy_rate_stop(&rat(49, 10), 1).is_none());
        assert!(matches!(
            entropy_rate_stop(&integer(5), 1),
            Some(Stop::EntropyRate { drawn_cells: 1, .. })
        ));
        assert!(entropy_rate_stop(&rat(99, 10), 2).is_none());
        assert!(entropy_rate_stop(&integer(10), 2).is_some());
        assert!(entropy_rate_stop(&integer(2), 4).is_none());
    }

    #[test]
    fn scored_uniform_face_stops_first_cell_and_confident_face_reaches_end() {
        use holonics::hnn::receiving::cells::CellDecision;
        use holonics::ratio::algebraic::ExactInterval;
        use holonics::ratio::rat;
        use holonics::receiver::release::ReleaseReturn;
        // Scored-face fixtures exercise drawn_code and the same completed-prefix decision
        // used by release_fork. They are not a native generated-release observation.
        let face = |mass: Rat| CellDecision {
            phase: 0,
            release: ReleaseReturn::Hold,
            classes: Vec::new(),
            key: None,
            bits: 0,
            face: vec![ExactInterval::point(mass); CLASSES],
            scored_face: None,
        };
        let uniform = drawn_code(&face(rat(1, 32)), 1).unwrap();
        assert!(matches!(
            completed_release_stop(&[1], &uniform.lower),
            Some(Stop::EntropyRate { drawn_cells: 1, .. })
        ));
        let prefix = sections::closed_cells(b"A");
        let mut lower = Rat::zero();
        for end in 1..=prefix.len() {
            let class = prefix[end - 1];
            let mut confident_face = face(Rat::zero());
            confident_face.face[class] = ExactInterval::point(Rat::one());
            let confident = drawn_code(&confident_face, class).unwrap();
            lower += &confident.lower;
            let decision = completed_release_stop(&prefix[..end], &lower);
            if end == prefix.len() {
                assert!(matches!(decision, Some(Stop::EndLetter)));
            } else {
                assert!(decision.is_none());
            }
        }
        assert!(matches!(
            completed_release_stop(&sections::end_cells(), &integer(10)),
            Some(Stop::EndLetter)
        ));
    }

    #[test]
    fn explicit_population_and_routes_refuse_before_io() {
        assert!(parse(&args(&[])).is_err());
        assert_eq!(
            parse(&args(&["--population", "65536"])).unwrap().population,
            65536
        );
        for flag in [
            "--max-release-octets",
            "--held-out",
            "--checkpoint-in",
            "--precision",
            "--read",
            "--release",
            "--observed-continuing",
        ] {
            assert!(
                parse(&args(&["--population", "65536", flag, "1"])).is_err(),
                "{flag}"
            );
        }
        assert!(take_route(&mut Vec::new()).is_err());
        for route in ["sections", "observed"] {
            let mut value = ["--route", route].map(str::to_owned).to_vec();
            assert_eq!(take_route(&mut value).unwrap(), route);
            assert!(value.is_empty());
        }
        assert!(options(&[]).is_err());
    }
    #[test]
    fn g3_two_sections_keep_the_exact_trunk_and_match_raw_delivery() {
        let port = Reference::new(4, BUDGET);
        let (mut split, pairing) = mounted(&port, 65536).unwrap();
        let mut raw = split.clone();
        let (mut split_crib, mut raw_crib) = (ObservedCrib::new(0), ObservedCrib::new(0));
        let mut longest = ReleaseHistory::default();
        let mut keys = keys();
        let inputs = [
            one(),
            Section {
                passages: vec![sections::Passage::Octets(vec![b'C'])],
                target: vec![b'D'],
            },
        ];
        for (index, input) in inputs.iter().enumerate() {
            section(
                &port,
                &mut split,
                &mut split_crib,
                &pairing,
                input,
                index,
                &mut longest,
                &mut keys,
                &mut 0,
                &mut |_| {},
            )
            .unwrap();
            for class in input
                .source_cells(index)
                .unwrap()
                .into_iter()
                .chain(input.target_cells(index).unwrap())
            {
                port.observe_cell_continuing(
                    &mut raw,
                    &mut raw_crib,
                    &pairing,
                    class,
                    None,
                    |_, _, _, _, _| {},
                )
                .unwrap();
            }
        }
        fn without_wall(resident: &Resident) -> String {
            let text = format!("{resident:?}");
            let (before, rest) = text.split_once("wall: WallTimes {").unwrap();
            let (_, after) = rest.split_once('}').unwrap();
            format!("{before}wall: <exterior timing>{after}")
        }
        assert_eq!(without_wall(&split), without_wall(&raw));
        assert_eq!(split_crib, raw_crib);
        let before = format!("{split:?}");
        let before_crib = split_crib.clone();
        release_fork(
            &port,
            &split,
            &split_crib,
            &pairing,
            2,
            &mut keys,
            0,
            &mut |_| {},
        )
        .unwrap();
        assert_eq!(before, format!("{split:?}"), "fork changed the exact trunk");
        assert_eq!(before_crib, split_crib);
    }
    #[test]
    fn r5_fork_stops_with_typed_horizon_and_reports_both_bounds() {
        let port = Reference::new(4, BUDGET);
        let (opening, _) = mounted(&port, 65536).unwrap();
        let population = opening.field().capacity().n_star();
        let (mut trunk, pairing) = mounted(&port, population).unwrap();
        // Exhaust the ingress horizon before the first release draw. A uniform first
        // successful draw would now correctly stop at the entropy rate before a second.
        fill(&port, &mut trunk, &pairing, population as usize);
        let crib = ObservedCrib::new(population as usize);
        let before = format!("{trunk:?}");
        let mut lines = Vec::new();
        let released = release_fork(
            &port,
            &trunk,
            &crib,
            &pairing,
            2,
            &mut keys(),
            0,
            &mut |s| lines.push(s),
        )
        .unwrap();
        let bound = trunk
            .field()
            .source_operand_bound(Locus::SourcePort(0))
            .unwrap();
        assert_eq!(released.classes.len(), 0);
        assert_eq!(
            released.stop,
            Stop::Horizon {
                population,
                source_operand_bound: bound
            }
        );
        let line = released.line(0);
        assert!(line.contains("stop=horizon"));
        assert!(line.contains(&format!("population={population}")));
        assert!(line.contains(&format!("source_operand_bound={bound}")));
        assert_eq!(before, format!("{trunk:?}"));
    }
    #[test]
    fn r6_release_line_precedes_answer_and_survives_its_horizon_refusal() {
        let port = Reference::new(4, BUDGET);
        let (opening, _) = mounted(&port, 65536).unwrap();
        let population = opening.field().capacity().n_star();
        let (mut trunk, pairing) = mounted(&port, population).unwrap();
        fill(&port, &mut trunk, &pairing, population as usize - 6);
        let mut crib = ObservedCrib::new(population as usize - 6);
        let mut lines = Vec::new();
        let result = section(
            &port,
            &mut trunk,
            &mut crib,
            &pairing,
            &one(),
            0,
            &mut ReleaseHistory::default(),
            &mut keys(),
            &mut 0,
            &mut |s| lines.push(s),
        );
        assert!(matches!(
            result.unwrap_err().downcast_ref::<HnnError>(),
            Some(HnnError::Horizon { .. })
        ));
        let release = lines
            .iter()
            .position(|s| s.starts_with("observed_release "))
            .unwrap();
        let answer: Vec<_> = lines
            .iter()
            .enumerate()
            .filter(|(_, s)| s.starts_with("cell ") && s.contains("role=answer"))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(answer.len(), 2);
        assert!(answer.into_iter().all(|at| release < at));
    }
    #[test]
    #[allow(
        clippy::disallowed_methods,
        reason = "synthetic create-only checkpoint boundary control"
    )]
    fn cost_checkpoint_roundtrip_is_create_only_and_checks_before_io() {
        let port = Reference::new(4, BUDGET);
        let (mut resident, pairing) = mounted(&port, 65536).unwrap();
        let opening = resident.constitution().clone();
        let mut crib = ObservedCrib::new(0);
        port.observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            0,
            None,
            |_, _, _, _, _| (),
        )
        .unwrap();
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "holonics-cost-checkpoint-{}-{stamp}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap();
        let mut checked = Vec::new();
        crate::octets::save_checkpoint_cost_profile(
            &resident,
            &opening,
            0,
            directory.to_str().unwrap(),
            1,
            (2, 0),
            |label| {
                checked.push(label.to_owned());
                Ok(())
            },
        )
        .unwrap();
        let path = directory.join("step-000001.state");
        let staging = directory.join("step-000001.state.tmp");
        let bytes = std::fs::read(&path).unwrap();
        assert_eq!(bytes, std::fs::read(&staging).unwrap());
        let parsed = holonics::hnn::constitution::ContinuingState::from_text(
            std::str::from_utf8(&bytes).unwrap(),
        )
        .unwrap();
        assert_eq!(parsed.receiver_ingress_ticks(), Some((2, 0)));
        let fork = parsed.clone();
        assert_eq!(
            fork.receiver_ingress_ticks(),
            parsed.receiver_ingress_ticks()
        );
        let saved = resident.continuing_state(0).unwrap();
        // A fresh observed resident now owns its known zero ingress before the first crossing.
        assert_eq!(saved.receiver_ingress_ticks(), Some((2, 0)));
        assert!(saved.clone().with_receiver_ingress_ticks(3, 0).is_err());
        let carried = saved.with_receiver_ingress_ticks(2, 17).unwrap();
        assert_eq!(
            holonics::hnn::constitution::ContinuingState::from_text(&carried.to_text())
                .unwrap()
                .receiver_ingress_ticks(),
            Some((2, 17))
        );
        assert!(
            opening
                .continuing_state(0)
                .unwrap()
                .with_receiver_ingress_ticks(2, 0)
                .is_err()
        );
        assert!(
            checked
                .iter()
                .any(|label| label == "resident checkpoint parse")
        );
        assert!(checked.iter().any(|label| label == "checkpoint completion"));
        assert!(
            crate::octets::save_checkpoint_cost_profile(
                &resident,
                &opening,
                0,
                directory.to_str().unwrap(),
                1,
                (2, 0),
                |_| Ok(())
            )
            .is_err()
        );
        assert_eq!(bytes, std::fs::read(&path).unwrap());
        let refused = directory.join("refused");
        assert!(
            crate::octets::save_checkpoint_cost_profile(
                &resident,
                &opening,
                0,
                refused.to_str().unwrap(),
                1,
                (2, 0),
                |_| Err(std::io::Error::other("fixed cutoff").into())
            )
            .is_err()
        );
        assert!(!refused.exists());
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(&staging).unwrap();
        std::fs::remove_dir(&directory).unwrap();
    }

    #[test]
    fn header_and_keys_lines_parse_the_native_declarations_and_location() {
        use num_bigint::BigInt;
        let port = Reference::new(4, BUDGET);
        let (mounted, pairing) = mounted(&port, 65536).unwrap();
        let field = mounted.field();
        let mut lift: Vec<_> = field
            .rings()
            .iter()
            .map(|r| BigInt::from(r.period() - 1))
            .collect();
        lift[0] -= 1;
        let opening = Current::at(field, lift).unwrap();
        let mut resident = port
            .mount_with(field, &opening, mounted.constitution().clone())
            .unwrap();
        let mut crib = ObservedCrib::new(0);
        let header = header_line(&resident).unwrap();
        for key in [
            "route",
            "precision",
            "population",
            "source_operand_bound",
            "source_lattice_exponent",
            "crib_window",
            "crib_offset",
            "provenance",
        ] {
            assert!(
                header
                    .split_whitespace()
                    .any(|part| part.starts_with(&format!("{key}="))),
                "{header}"
            );
        }
        let mut lines = Vec::new();
        deliver(
            &port,
            &mut resident,
            &mut crib,
            &pairing,
            &[0, 0],
            0,
            "source",
            &mut 0,
            &mut |line| lines.push(line),
        )
        .unwrap();
        let keys = lines
            .iter()
            .find(|line| line.starts_with("keys "))
            .expect("carry returns key line");
        for key in [
            "section",
            "owner",
            "crib_length",
            "fibres",
            "orbits",
            "fell_back",
            "jumps",
        ] {
            assert!(
                keys.split_whitespace()
                    .any(|part| part.starts_with(&format!("{key}="))),
                "{keys}"
            );
        }
    }
    #[test]
    fn receipt_series_has_every_stable_field_and_maximum_is_delivered() {
        let port = Reference::new(4, BUDGET);
        let (mut trunk, pairing) = mounted(&port, 65536).unwrap();
        let mut crib = ObservedCrib::new(0);
        let mut lines = Vec::new();
        let mut maximum = ReleaseHistory::default();
        let released = section(
            &port,
            &mut trunk,
            &mut crib,
            &pairing,
            &one(),
            0,
            &mut maximum,
            &mut keys(),
            &mut 0,
            &mut |s| lines.push(s),
        )
        .unwrap();
        assert_eq!(released.maximum, 0);
        assert_eq!(maximum.maximum(sections::ChartKind::Octets), 4);
        assert!(released.classes.is_empty());
        assert!(!lines.iter().any(|line| line.starts_with("drawn ")));
        let repeated = section(
            &port,
            &mut trunk,
            &mut crib,
            &pairing,
            &one(),
            1,
            &mut maximum,
            &mut keys(),
            &mut 0,
            &mut |s| lines.push(s),
        )
        .unwrap();
        assert_eq!(repeated.maximum, 4);
        let fields = |line: &str| {
            line.split_whitespace()
                .skip(1)
                .filter_map(|s| s.split_once('=').map(|(k, _)| k.to_owned()))
                .collect::<BTreeSet<_>>()
        };
        for line in &lines {
            println!("{line}");
            let required: &[&str] = if line.starts_with("cell ") {
                &[
                    "section",
                    "role",
                    "class",
                    "delivered",
                    "address",
                    "code",
                    "tree",
                    "wave",
                    "steps",
                    "cell_ns",
                ]
            } else if line.starts_with("report ") {
                &["section", "role", "report_ns"]
            } else if line.starts_with("precision ") {
                &[
                    "section",
                    "role",
                    "delivered",
                    "resident_state_bits",
                    "precision_checked",
                    "precision_event",
                    "published",
                    "receiving_exponent",
                    "balance_before",
                    "balance_after",
                ]
            } else if line.starts_with("state ") {
                &[
                    "section",
                    "role",
                    "delivered",
                    "state_bits",
                    "constitution_bits",
                    "loci_exponent_entries_remainders_solved",
                    "source_chart_ring_exponent_scale_support_certificate",
                    "source_chart_ring_rule_exponent_target",
                ]
            } else if line.starts_with("pair_face ") {
                &[
                    "section",
                    "role",
                    "unit",
                    "ring_offset_population_occupied_bindings_rebuilds",
                    "clone_ns",
                    "phase_wall_ns",
                ]
            } else if line.starts_with("marginal_face ") {
                &["section", "role", "delivered", "held_matches", "totals"]
            } else if line.starts_with("cert ") {
                &["section", "role", "delivered", "steps"]
            } else if line.starts_with("pairing ") {
                &["section", "role", "delivered", "pairings"]
            } else if line.starts_with("drawn ") {
                &[
                    "section",
                    "index",
                    "class",
                    "address",
                    "drawn_code",
                    "cell_ns",
                    "resident_state_bits",
                    "precision_event",
                    "published",
                    "receiving_exponent",
                ]
            } else if line.starts_with("observed_chart ") {
                &[
                    "section",
                    "kind",
                    "chart_octets",
                    "chart_sha256",
                    "fibre_bytes",
                    "fibre_sha256",
                    "canonical_format",
                ]
            } else if line.starts_with("keys ") {
                &[
                    "section",
                    "owner",
                    "crib_length",
                    "fibres",
                    "orbits",
                    "fell_back",
                    "jumps",
                ]
            } else {
                &["section", "classes", "stop", "value", "maximum", "text"]
            };
            let parsed = fields(line);
            assert!(required.iter().all(|key| parsed.contains(*key)), "{line}");
        }
        for name in [
            "cell ",
            "precision ",
            "state ",
            "pair_face ",
            "marginal_face ",
            "cert ",
            "pairing ",
            "drawn ",
            "report ",
            "observed_release ",
        ] {
            assert!(lines.iter().any(|s| s.starts_with(name)), "{name}");
        }
        let release = lines
            .iter()
            .position(|s| s.starts_with("observed_release "))
            .unwrap();
        assert!(
            lines
                .iter()
                .enumerate()
                .filter(|(_, s)| s.starts_with("cell ") && s.contains("role=answer"))
                .all(|(i, _)| release < i)
        );
    }
}
