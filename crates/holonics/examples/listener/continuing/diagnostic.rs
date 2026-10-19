//! Read-only listener diagnostic: full mode reads one 231-cell A/A0 comparison.
//! Trunk, paired and calibration profiles remain explicit modes.
//! The optional hook returns exact receiving samples already staged in the ordinary transaction.

#[path = "diagnostic/epoch.rs"]
mod epoch;
#[path = "diagnostic/execution.rs"]
mod execution;
#[path = "diagnostic/timing.rs"]
mod timing;
#[path = "diagnostic/verdict.rs"]
mod verdict;

use super::*;
use holonics::hnn::constitution::Sample;
use holonics::hnn::constitution::{
    Carrier, NormalLaw, receiving_class_metric, receiving_metric_samples,
};
use holonics::hnn::receiving::ReceivingRead;
use holonics::hnn::reference::FrozenComparison;
use holonics::hnn::word::{EndChange, ReceptionCarry};
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use std::sync::atomic::{AtomicBool, Ordering};

fn guarded_worker<T>(
    abort: &AtomicBool,
    work: impl FnOnce() -> Result<T>,
) -> std::result::Result<T, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)) {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(error)) => {
            abort.store(true, Ordering::Release);
            Err(error.to_string())
        }
        Err(_) => {
            abort.store(true, Ordering::Release);
            Err("diagnostic branch worker panicked".to_owned())
        }
    }
}

fn guarded_report_work<T>(
    budget: &mut timing::ReportBudget,
    label: &str,
    work: impl FnOnce() -> Result<T>,
) -> Result<T> {
    let started = Instant::now();
    check_postwork_cutoff(budget, label, started)?;
    let value = work();
    budget.record_work(timing::ReportWorkKind::Other, started.elapsed().as_nanos());
    let value = value?;
    check_postwork_cutoff(budget, &format!("completion of {label}"), started)?;
    Ok(value)
}

fn check_postwork_cutoff(
    budget: &mut timing::ReportBudget,
    label: &str,
    started: Instant,
) -> Result<()> {
    match budget.check_before_work(label) {
        Ok(()) => Ok(()),
        Err(error) => {
            let summary = budget.finish();
            println!(
                "step0_main_postwork cutoff_position={label:?} elapsed_ns={} remaining_report_ns={}",
                started.elapsed().as_nanos(),
                summary.remaining_report_ns
            );
            Err(error.into())
        }
    }
}

#[derive(Clone)]
struct CutView {
    /// Post-deposit W and H shown by the listener's ordinary post-commit callback.
    map: ExactRatMatrix,
    gram: ExactRatMatrix,
    gram_remainder: ExactRatMatrix,
    /// Exact map and comparison context at the producing, pre-deposit cut.
    producing_map: ExactRatMatrix,
    frozen: Option<FrozenComparison>,
    producing: Option<Constitution>,
    moment_text: String,
    address_text: String,
    pre_lift: Vec<BigInt>,
    pre_clocks: Vec<(u64, u64, BigInt)>,
    /// The preceding reception's carry at the pre-call cut, distinct from this word's end.
    pre_carried: Option<ReceptionCarry>,
    /// The exact word end change aligned with the sealed prediction for this read.
    physical: Option<EndChange>,
    contact_j: Vec<ExactRatMatrix>,
    samples: Vec<Sample>,
    capture_record_bytes: usize,
    /// Actual released entries for this receiving Gram carrier from the native deposit receipt.
    gram_release: Vec<(usize, Rat)>,
    receiving_prior: Option<u32>,
    prior_scale: u32,
    support: Vec<usize>,
    symmetry: String,
    crossing_covectors: Vec<Vec<Rat>>,
    receiving_step: Rat,
    receiving_vanished: bool,
    law: NormalLaw,
    native_lattice_exponent: u32,
    /// Amended producer partition exponent, distinct from the receiver grain denominator.
    receiver_partition_exponent: Option<u32>,
    /// Actual receiver section crossings counted from successful ingest receipts at the mount.
    opening_crossings: Option<u64>,
    /// Amended-source epoch index. The receipt tick count is kept separate until joined.
    partition_epoch_index: Option<u64>,
    /// Amended producer's declared face-partition bound, distinct from a sample-record count.
    partition_cell_bound: Option<u64>,
}

fn cut_view(material: &Constitution, samples: &[Sample]) -> Result<CutView> {
    let law = material
        .receiving_law(2)
        .ok_or("receiver ring 2 has no single-map normal law")?;
    let native_lattice_exponent = material.lattice(Locus::ReceivingMap(2))?.exponent();
    Ok(CutView {
        map: law.map().clone(),
        gram: law.gram(),
        gram_remainder: law.gram_remainder(),
        producing_map: law.map().clone(),
        frozen: None,
        producing: None,
        moment_text: String::new(),
        address_text: String::new(),
        pre_lift: Vec::new(),
        pre_clocks: Vec::new(),
        pre_carried: None,
        physical: None,
        contact_j: Vec::new(),
        samples: samples.to_vec(),
        capture_record_bytes: 0,
        gram_release: Vec::new(),
        receiving_prior: law.receiving_prior(),
        prior_scale: law.prior_scale(),
        support: law.chart().support().to_vec(),
        symmetry: format!("{:?}", law.symmetry()),
        crossing_covectors: Vec::new(),
        receiving_step: Rat::zero(),
        receiving_vanished: false,
        law: law.clone(),
        native_lattice_exponent,
        receiver_partition_exponent: None,
        opening_crossings: None,
        partition_epoch_index: None,
        partition_cell_bound: None,
    })
}

fn held_wave(
    crossing: &ExactRatMatrix,
    current: &ExactRatMatrix,
    wave: &Faces,
    samples: &[Sample],
) -> Result<Faces> {
    if samples.is_empty() {
        return Ok(wave.clone());
    }
    if samples.len() != wave.faces.len() || wave.logits.len() != samples.len() {
        return Err("held-face pass cannot align receiving samples to actual wave stations".into());
    }
    let mut reads = Vec::with_capacity(samples.len());
    for (station, sample) in samples.iter().enumerate() {
        if sample.feature.len() != crossing.columns()
            || crossing.rows() != current.rows()
            || crossing.columns() != current.columns()
            || wave.logits[station].len() != crossing.rows()
        {
            return Err("held-face pass map, feature, and wave shapes disagree".into());
        }
        let mut logits = wave.logits[station].clone();
        for row in 0..crossing.rows() {
            let mut shift = Rat::zero();
            for column in 0..crossing.columns() {
                shift += (crossing.get(row, column)? - current.get(row, column)?)
                    * &sample.feature[column];
            }
            logits[row] += shift;
        }
        reads.push(ReceivingRead::of_logits(
            logits,
            wave.faces[station].grain(),
        ));
    }
    Ok(Faces::of_reads(&reads, wave.faces[0].grain())?)
}

#[cfg(test)]
fn add_sample_statistics(
    gradient: &mut [Vec<Rat>],
    gram_delta: &mut [Vec<Rat>],
    samples: &[Sample],
    covectors: &[Vec<Rat>],
) -> Result<()> {
    if samples.len() != covectors.len() {
        return Err("rebased covector count differs from staged receiving sample count".into());
    }
    for (sample, covector) in samples.iter().zip(covectors) {
        if sample.feature.len() != gram_delta.len()
            || covector.len() != gradient.len()
            || sample.weight < Rat::zero()
        {
            return Err(
                "receiving sample shape/weight differs from the declared normal law".into(),
            );
        }
        for (i, g) in covector.iter().enumerate() {
            for (j, f) in sample.feature.iter().enumerate() {
                gradient[i][j] += &sample.weight * g * f;
            }
        }
        for (i, f) in sample.feature.iter().enumerate() {
            for (j, other) in sample.feature.iter().enumerate() {
                gram_delta[i][j] += &sample.weight * f * other;
            }
        }
    }
    Ok(())
}

fn observe_branch(
    port: &Reference,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    classes: &[usize],
    branch: &str,
    crossing_map: &ExactRatMatrix,
    budget: &timing::RunBudget,
    abort: &AtomicBool,
    mut crossings: Option<&mut u64>,
) -> Result<(Vec<CutView>, Vec<Faces>, Vec<Vec<BigInt>>, Vec<u128>)> {
    let mut phase = budget.phase(branch, classes.len(), Some(180_000_000_000))?;
    let mut views = Vec::with_capacity(classes.len());
    let mut faces = Vec::with_capacity(classes.len());
    let mut lifts = Vec::with_capacity(classes.len());
    let mut native_ns = 0u128;
    let mut report_ns = 0u128;
    let mut cell_times = Vec::with_capacity(classes.len());
    for (index, &class) in classes.iter().enumerate() {
        phase.before_cell()?;
        if abort.load(Ordering::Acquire) {
            phase.mark_stop("shared diagnostic guard failure");
            return Err(
                format!("branch {branch} stopped after a shared diagnostic guard failure").into(),
            );
        }
        let cell_started = Instant::now();
        let cpu_started = timing::ThreadCpu::read();
        let wall_before = resident.wall().phases();
        let opening_crossings = crossings.as_deref().copied();
        let pre_lift = resident.current().lift().to_vec();
        let pre_clocks = clock_snapshot_at(resident.field(), resident.current())?;
        let pre_carried = resident.carried().cloned();
        let pre_moment = pre_call_moment_text(resident)?;
        let pre_contact_j = contact_j_signature(resident.field(), &pre_lift)?;
        let map_at_compare = cut_view(resident.constitution(), &[])?.map;
        let native_started = Instant::now();
        let native_result = port.observe_cell_continuing_with_samples(
            resident,
            crib,
            pairing,
            class,
            None,
            |_, material, moment, address, reading, samples, frozen| {
                let view = cut_view(material, samples).and_then(|mut view| {
                    view.gram_release = reading
                        .released
                        .iter()
                        .filter_map(|(locus, carrier, index, amount)| {
                            (*locus == Locus::ReceivingMap(2) && *carrier == Carrier::Gram)
                                .then(|| (*index, amount.clone()))
                        })
                        .collect();
                    let mut source_moment = String::new();
                    moment.write(&mut source_moment);
                    if source_moment != pre_moment {
                        return Err(
                            "callback SourceMoment differs from exact pre-call resident moment"
                                .into(),
                        );
                    }
                    view.producing_map = frozen
                        .and_then(|frozen| frozen.producing().receiving_law(2))
                        .map(|law| law.map().clone())
                        .unwrap_or_else(|| map_at_compare.clone());
                    view.frozen = frozen.cloned();
                    view.producing = frozen.map(|frozen| frozen.producing().clone());
                    view.moment_text = pre_moment.clone();
                    view.address_text = format!("{address:?}");
                    view.pre_lift = pre_lift.clone();
                    view.opening_crossings = opening_crossings;
                    view.pre_clocks = pre_clocks.clone();
                    view.pre_carried = pre_carried.clone();
                    view.contact_j = pre_contact_j.clone();
                    if view.producing_map != map_at_compare {
                        return Err(
                            "frozen producing map differs from the observer's pre-call map".into(),
                        );
                    }
                    Ok(view)
                });
                let crossing_covectors = if samples.is_empty() {
                    Ok(Vec::new())
                } else {
                    match frozen {
                        Some(frozen) => {
                            held_wave(crossing_map, &map_at_compare, frozen.wave(), samples)
                                .and_then(|wave| {
                                    frozen.recompare_covector(&wave).map_err(Into::into)
                                })
                        }
                        None => Err("diagnostic hook omitted the frozen comparison context".into()),
                    }
                };
                (
                    view.and_then(|view| Ok((view, crossing_covectors?))),
                    reading.clone(),
                )
            },
        );
        let native = match native_result {
            Ok(native) => native,
            Err(error) => {
                abort.store(true, Ordering::Release);
                return Err(error.into());
            }
        };
        if let Some(crossings) = crossings.as_deref_mut() {
            count_receiver_crossings(crossings, &native.ingest)?;
        }
        let native_elapsed = native_started.elapsed().as_nanos();
        native_ns += native_elapsed;
        let (view_result, reading) = native.view;
        let (mut view, crossing_covectors) = view_result?;
        view.crossing_covectors = crossing_covectors;
        view.physical = match &native.refine.detail {
            ReceiptDetail::Refine { word, .. } => Some(word.change.clone()),
            _ => return Err("observed cell did not return its actual refine word balance".into()),
        };
        view.receiving_step = reading.linear_step(Locus::ReceivingMap(2));
        view.receiving_vanished = reading
            .vanished
            .iter()
            .any(|(locus, _)| *locus == Locus::ReceivingMap(2));
        faces.push(native.prediction.clone());
        lifts.push(resident.current().lift().to_vec());
        // The report consumes exact structs already in memory. Formatting the complete
        // producing context created megabytes per cell and is not part of this read.
        // In particular, do not format Debug text merely to hash it.
        view.capture_record_bytes = 0;
        views.push(view);
        let overhead_elapsed = cell_started
            .elapsed()
            .as_nanos()
            .saturating_sub(native_elapsed);
        report_ns += overhead_elapsed;
        let cell_ns = native_elapsed + overhead_elapsed;
        cell_times.push(cell_ns);
        phase.finish_cell(cell_ns)?;
        let cpu_delta = cpu_started
            .zip(timing::ThreadCpu::read())
            .and_then(|(start, end)| end.delta_since(start));
        let wall_after = resident.wall().phases();
        let native_wall_phases: Vec<_> = wall_after
            .iter()
            .zip(wall_before)
            .map(|((name, after), (_, before))| (*name, after.saturating_sub(before).as_nanos()))
            .collect();
        println!(
            "step0_cell branch={branch} index={index} class={class} cell_ns={cell_ns} transaction_including_hook_ns={native_elapsed} exterior_ns={overhead_elapsed} native_wall_phases={native_wall_phases:?} thread_cpu={cpu_delta:?}"
        );
    }
    let summary = phase.finish_phase();
    println!(
        "step0_branch_timing branch={branch} cells={} transaction_including_hook_elapsed_ns={native_ns} exterior_overhead_ns={report_ns} phase_elapsed_wall_ns={} forecast_upper_ns_per_cell={:?}",
        classes.len(),
        summary.elapsed_wall_ns,
        summary.forecast_upper_ns_per_cell,
    );
    Ok((views, faces, lifts, cell_times))
}

fn observe_plain_branch(
    port: &Reference,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    classes: &[usize],
    branch: &str,
    budget: &timing::RunBudget,
    abort: &AtomicBool,
    mut crossings: Option<&mut u64>,
) -> Result<(Vec<Faces>, Vec<Vec<BigInt>>, Vec<u128>)> {
    let mut phase = budget.phase(branch, classes.len(), Some(180_000_000_000))?;
    let mut faces = Vec::with_capacity(classes.len());
    let mut lifts = Vec::with_capacity(classes.len());
    let mut native_ns = 0u128;
    let mut exterior_ns = 0u128;
    let mut cell_times = Vec::with_capacity(classes.len());
    for (index, &class) in classes.iter().enumerate() {
        phase.before_cell()?;
        if abort.load(Ordering::Acquire) {
            phase.mark_stop("shared diagnostic guard failure");
            return Err(
                format!("branch {branch} stopped after a shared diagnostic guard failure").into(),
            );
        }
        let cell_started = Instant::now();
        let cpu_started = timing::ThreadCpu::read();
        let wall_before = resident.wall().phases();
        let native_started = Instant::now();
        let native = match port.observe_cell_continuing(
            resident,
            crib,
            pairing,
            class,
            None,
            |_, _, _, _, _| (),
        ) {
            Ok(native) => native,
            Err(error) => {
                abort.store(true, Ordering::Release);
                return Err(error.into());
            }
        };
        if let Some(crossings) = crossings.as_deref_mut() {
            count_receiver_crossings(crossings, &native.ingest)?;
        }
        let native_elapsed = native_started.elapsed().as_nanos();
        native_ns += native_elapsed;
        faces.push(native.prediction.clone());
        lifts.push(resident.current().lift().to_vec());
        let exterior = cell_started
            .elapsed()
            .as_nanos()
            .saturating_sub(native_elapsed);
        exterior_ns += exterior;
        let cell_ns = native_elapsed + exterior;
        cell_times.push(cell_ns);
        phase.finish_cell(cell_ns)?;
        let cpu_delta = cpu_started
            .zip(timing::ThreadCpu::read())
            .and_then(|(start, end)| end.delta_since(start));
        let wall_after = resident.wall().phases();
        let native_wall_phases: Vec<_> = wall_after
            .iter()
            .zip(wall_before)
            .map(|((name, after), (_, before))| (*name, after.saturating_sub(before).as_nanos()))
            .collect();
        println!(
            "step0_cell branch={branch} index={index} class={class} cell_ns={cell_ns} transaction_including_hook_ns={native_elapsed} exterior_ns={exterior} native_wall_phases={native_wall_phases:?} thread_cpu={cpu_delta:?}"
        );
    }
    let summary = phase.finish_phase();
    println!(
        "step0_branch_timing branch={branch} cells={} transaction_elapsed_ns={native_ns} exterior_overhead_ns={exterior_ns} phase_elapsed_wall_ns={} forecast_upper_ns_per_cell={:?}",
        classes.len(),
        summary.elapsed_wall_ns,
        summary.forecast_upper_ns_per_cell
    );
    Ok((faces, lifts, cell_times))
}

fn matrix_delta(after: &ExactRatMatrix, before: &ExactRatMatrix) -> Result<ExactRatMatrix> {
    Ok(after.subtract(before)?)
}

fn from_worker<T>(result: std::result::Result<T, String>) -> Result<T> {
    result.map_err(|message| std::io::Error::other(message).into())
}

fn source_interventions(field: &Field, classes: &[usize]) -> Result<Vec<(String, usize, u64)>> {
    let first = *classes
        .first()
        .ok_or("no first source class for intervention")?;
    let source_ring = *field.sources().first().ok_or("source ring missing")?;
    let base_advance = field.class_advance(source_ring, first)?;
    let xor8 = first ^ 8;
    if xor8 >= field.alphabet() {
        return Err("the fixed XOR-8 alternate is outside the declared source alphabet".into());
    }
    let xor_advance = field.class_advance(source_ring, xor8)?;
    let mut alternatives = vec![if xor_advance == base_advance {
        ("B_same_advance_xor8".to_owned(), xor8, xor_advance)
    } else {
        ("B_advance_separating_xor8".to_owned(), xor8, xor_advance)
    }];
    let mut separating = None;
    for class in 0..field.alphabet() {
        if class == first {
            continue;
        }
        let advance = field.class_advance(source_ring, class)?;
        if advance != base_advance {
            separating = Some((class, advance));
            break;
        }
    }
    if let Some((class, advance)) = separating {
        if !alternatives
            .iter()
            .any(|(_, _, existing_advance)| *existing_advance != base_advance)
        {
            alternatives.push(("B_advance_separating".to_owned(), class, advance));
        }
    }
    let mut same = None;
    for class in 0..field.alphabet() {
        if class == first {
            continue;
        }
        let advance = field.class_advance(source_ring, class)?;
        if advance == base_advance {
            same = Some((class, advance));
            break;
        }
    }
    if let Some((class, advance)) = same {
        if !alternatives
            .iter()
            .any(|(_, _, existing_advance)| *existing_advance == base_advance)
        {
            alternatives.push(("B_same_advance".to_owned(), class, advance));
        }
    }
    Ok(alternatives)
}

fn clock_snapshot(resident: &Resident) -> std::result::Result<Vec<(u64, u64, BigInt)>, HnnError> {
    clock_snapshot_at(resident.field(), resident.current())
}

fn clock_snapshot_at(
    field: &Field,
    current: &Current,
) -> std::result::Result<Vec<(u64, u64, BigInt)>, HnnError> {
    (0..field.rings().len())
        .map(|ring| {
            Ok((
                field.rings()[ring].period(),
                current.phase(field, ring)?,
                current.winding(field, ring)?,
            ))
        })
        .collect()
}

fn contact_j_signature(field: &Field, lift: &[BigInt]) -> Result<Vec<ExactRatMatrix>> {
    field
        .contacts()
        .iter()
        .map(|contact| contact.pair(field, lift).slip().map_err(Into::into))
        .collect()
}

fn pre_call_moment_text(resident: &Resident) -> Result<String> {
    let (id, _) = resident
        .continuing()
        .ok_or("diagnostic cut has no continuing source moment")?;
    let moment = resident
        .moment(&id)
        .ok_or("continuing source moment id has no resident value")?;
    let mut text = String::new();
    moment.write(&mut text);
    Ok(text)
}

fn epoch_statistics_with_scale(
    crossing: &CutView,
    views: &[CutView],
) -> Result<(ExactRatMatrix, ExactRatMatrix, Option<Rat>)> {
    let mut actual_samples = Vec::new();
    let mut crossing_covectors = Vec::new();
    for view in views {
        if view.samples.len() != view.crossing_covectors.len() {
            return Err("crossing covector count differs from staged sample count".into());
        }
        actual_samples.extend(view.samples.iter().cloned());
        crossing_covectors.extend(view.crossing_covectors.iter().cloned());
    }
    let (reached, metric_samples, scale) =
        crossing_metric_samples(&actual_samples, &crossing_covectors)?;
    let (gradient, _) = crossing.law.projected_statistics(&metric_samples)?;
    let (_, gram_delta) = crossing.law.projected_statistics(&reached)?;
    Ok((gradient, gram_delta, scale))
}

fn crossing_metric_samples(
    actual_samples: &[Sample],
    crossing_covectors: &[Vec<Rat>],
) -> Result<(Vec<Sample>, Vec<Sample>, Option<Rat>)> {
    if actual_samples.len() != crossing_covectors.len() {
        return Err("crossing covector count differs from staged sample count".into());
    }
    let reached = actual_samples
        .iter()
        .zip(crossing_covectors)
        .map(|(sample, covector)| {
            let mut sample = sample.clone();
            sample.covector = covector.clone();
            // Recompute face masses from the crossing-map covector. The producer's attached
            // masses describe the live-map comparison and cannot set the crossing metric.
            sample.masses = None;
            sample
        })
        .collect::<Vec<_>>();
    let scale = receiving_class_metric(&reached);
    // This matches native prepare: when no class metric is available, its receiving law falls
    // back to the exact reached samples. Keep `None` visible in the readout rather than calling
    // that fallback a class-metric correction.
    let metric_samples = receiving_metric_samples(&reached).unwrap_or_else(|| reached.clone());
    Ok((reached, metric_samples, scale))
}

fn causal_differences(
    a_views: &[CutView],
    a_faces: &[Faces],
    b_views: &[CutView],
    b_faces: &[Faces],
    budget: &timing::ReportBudget,
) -> Result<(
    Rat,
    Option<(usize, usize, usize)>,
    Rat,
    Option<(usize, usize, usize)>,
)> {
    if a_views.len() != b_views.len()
        || a_faces.len() != b_faces.len()
        || a_views.len() != a_faces.len()
    {
        return Err("A/B causal comparison lengths differ".into());
    }
    let mut max_feature_delta = Rat::zero();
    let mut first_feature_delta = None;
    let mut max_logit_delta = Rat::zero();
    let mut first_logit_delta = None;
    for cell in 0..a_views.len() {
        budget.check_before_work(&format!("causal A/B cell {cell}"))?;
        let a_samples = &a_views[cell].samples;
        let b_samples = &b_views[cell].samples;
        if a_samples.len() != b_samples.len() {
            return Err(format!("A/B sample counts differ at cell {cell}").into());
        }
        for sample in 0..a_samples.len() {
            if a_samples[sample].feature.len() != b_samples[sample].feature.len() {
                return Err(
                    format!("A/B feature widths differ at cell {cell}, sample {sample}").into(),
                );
            }
            for coordinate in 0..a_samples[sample].feature.len() {
                let delta = (&a_samples[sample].feature[coordinate]
                    - &b_samples[sample].feature[coordinate])
                    .abs();
                if !delta.is_zero() && first_feature_delta.is_none() {
                    first_feature_delta = Some((cell, sample, coordinate));
                }
                max_feature_delta = max_feature_delta.max(delta);
            }
        }
        let a_logits = &a_faces[cell].logits;
        let b_logits = &b_faces[cell].logits;
        if a_logits.len() != b_logits.len() {
            return Err(format!("A/B wave station counts differ at cell {cell}").into());
        }
        for station in 0..a_logits.len() {
            if a_logits[station].len() != b_logits[station].len() {
                return Err(
                    format!("A/B logit widths differ at cell {cell}, station {station}").into(),
                );
            }
            for coordinate in 0..a_logits[station].len() {
                let delta = (&a_logits[station][coordinate] - &b_logits[station][coordinate]).abs();
                if !delta.is_zero() && first_logit_delta.is_none() {
                    first_logit_delta = Some((cell, station, coordinate));
                }
                max_logit_delta = max_logit_delta.max(delta);
            }
        }
        budget.check_before_work(&format!("causal A/B cell {cell} completion"))?;
    }
    Ok((
        max_feature_delta,
        first_feature_delta,
        max_logit_delta,
        first_logit_delta,
    ))
}

fn timed_causal_differences(
    a_views: &[CutView],
    a_faces: &[Faces],
    b_views: &[CutView],
    b_faces: &[Faces],
    budget: &mut timing::ReportBudget,
    label: &str,
) -> Result<(
    Rat,
    Option<(usize, usize, usize)>,
    Rat,
    Option<(usize, usize, usize)>,
)> {
    let started = Instant::now();
    check_postwork_cutoff(budget, label, started)?;
    let result = causal_differences(a_views, a_faces, b_views, b_faces, budget);
    budget.record_work(timing::ReportWorkKind::Other, started.elapsed().as_nanos());
    let result = match result {
        Ok(result) => result,
        Err(error) => {
            check_postwork_cutoff(budget, &format!("{label} interrupted"), started)?;
            return Err(error);
        }
    };
    check_postwork_cutoff(budget, &format!("{label} completion"), started)?;
    Ok(result)
}

#[derive(Debug, PartialEq, Eq)]
struct CoarseFace {
    grain: u64,
    cells: Vec<(BigInt, u64)>,
    phases: Vec<Rat>,
}

fn coarse_face_key(wave: &Faces) -> Vec<CoarseFace> {
    wave.faces
        .iter()
        .map(|face| {
            let top = face
                .cells()
                .iter()
                .map(|cell| cell.carry.clone())
                .max()
                .unwrap_or_default();
            CoarseFace {
                grain: face.grain(),
                cells: face
                    .cells()
                    .iter()
                    .map(|cell| (&cell.carry - &top, cell.phase))
                    .collect(),
                phases: face.phases().to_vec(),
            }
        })
        .collect()
}

// Historical conservative input from the earlier paired control. This is neither a new
// measurement nor a cost with Debug formatting subtracted. No deadline depends on raising it.
const HISTORICAL_NATIVE_CELL_NS: u128 = 549_667_971;

fn historical_native_projection(cells: usize) -> Result<u128> {
    HISTORICAL_NATIVE_CELL_NS
        .checked_mul(cells as u128)
        .ok_or_else(|| "historical native cost projection overflows nanoseconds".into())
}

fn admission_remaining(budget: &timing::RunBudget) -> Result<u128> {
    Ok(budget.remaining_ns()?.min(budget.remaining_report_ns()?))
}

/// Count only actual ingress ticks. Rekeying a lift and the physical word's ticks are distinct
/// operations; neither changes this exterior receipt count. It starts at the fresh mount.
fn count_receiver_crossings(
    count: &mut u64,
    ingest: &holonics::hnn::port::PortReceipt,
) -> Result<()> {
    let ticks = ingest
        .rings
        .readings()
        .get(2)
        .ok_or("ingest receipt omitted the receiving ring's tick count")?;
    if ticks.denom() != &BigInt::from(1) {
        return Err("ingest receiver tick count is not an exact integer".into());
    }
    let ticks = u64::try_from(ticks.numer().clone())
        .map_err(|_| "ingest receiver tick count is negative or exceeds u64")?;
    *count = count
        .checked_add(ticks)
        .ok_or("actual receiver crossing count overflows u64")?;
    Ok(())
}

/// Full mode has one captured A and one ordinary identical-input A0. Its only epoch report is
/// the compact stall read; the crossing-statistic producer still uses the frozen comparison.
fn run_full_aa0(
    port: &Reference,
    resident: &Resident,
    opening: &Constitution,
    crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    classes: &[usize],
    crossing: &CutView,
    budget: &timing::RunBudget,
    admission: &timing::ReportAdmission,
    opening_crossings: u64,
    checkpoint_path: &str,
    source_count: usize,
) -> Result<()> {
    if classes.len() != 231 || crossing.opening_crossings != Some(opening_crossings) {
        return Err("full A/A0 requires 231 cells and the actual opening crossing receipt".into());
    }
    epoch::require_partition_precision(crossing.receiver_partition_exponent)?;
    if crossing.partition_epoch_index.is_none() || crossing.partition_cell_bound.is_none() {
        return Err("amended partition epoch index or declared cell bound is unavailable at the actual opening".into());
    }
    let branch_native_ns = historical_native_projection(classes.len())?;
    let pre_checkpoint = admission.admit(
        branch_native_ns,
        1,
        admission_remaining(budget)?,
        180_000_000_000,
    )?;
    println!(
        "step0_full_protocol transactions=774 components=312_trunk+231_A+231_A0 branch_workers=2 historical_native_cell_ns={HISTORICAL_NATIVE_CELL_NS} historical_bound_not_new_measurement=true admission={pre_checkpoint:?} empirical_report_input={admission:?} opening_crossings={opening_crossings} partition_epoch_index={:?} no_in_process_calibration=true no_B_interventions=true no_held_map_report_passes=true",
        crossing.partition_epoch_index
    );
    let checkpoint_started = Instant::now();
    crate::octets::save_checkpoint(
        resident,
        opening,
        resident.field().sources()[0],
        checkpoint_path,
        source_count,
    )?;
    let post_checkpoint = admission.admit_after_checkpoint(
        branch_native_ns,
        1,
        admission_remaining(budget)?,
        180_000_000_000,
    )?;
    println!(
        "step0_checkpoint scope=resident_only crib_sidecar=false elapsed_ns={} admission={post_checkpoint:?}; caller_owned_crib_resume_not_claimed=true",
        checkpoint_started.elapsed().as_nanos()
    );
    let mut a = resident.clone();
    let mut a0 = resident.clone();
    let mut a_crib = crib.clone();
    let mut a0_crib = crib.clone();
    let mut a_crossings = opening_crossings;
    let mut a0_crossings = opening_crossings;
    let a_pool = execution::one_thread_pool()?;
    let a0_pool = execution::one_thread_pool()?;
    let abort = AtomicBool::new(false);
    let pre_spawn = admission.admit_after_checkpoint(
        branch_native_ns,
        1,
        admission_remaining(budget)?,
        180_000_000_000,
    )?;
    println!("step0_full_pre_spawn admission={pre_spawn:?} shared_fixed_deadline=true");
    let (a_result, a0_result) = std::thread::scope(|scope| {
        let a_worker = scope.spawn(|| {
            a_pool.install(|| {
                guarded_worker(&abort, || {
                    observe_branch(
                        port,
                        &mut a,
                        &mut a_crib,
                        pairing,
                        classes,
                        "A",
                        &crossing.map,
                        budget,
                        &abort,
                        Some(&mut a_crossings),
                    )
                })
            })
        });
        let a0_worker = scope.spawn(|| {
            a0_pool.install(|| {
                guarded_worker(&abort, || {
                    observe_plain_branch(
                        port,
                        &mut a0,
                        &mut a0_crib,
                        pairing,
                        classes,
                        "A0",
                        budget,
                        &abort,
                        Some(&mut a0_crossings),
                    )
                })
            })
        });
        (
            a_worker
                .join()
                .unwrap_or_else(|_| Err("A branch worker panicked".to_owned())),
            a0_worker
                .join()
                .unwrap_or_else(|_| Err("A0 branch worker panicked".to_owned())),
        )
    });
    let (a_views, _, _, _) = from_worker(a_result)?;
    let _ = from_worker(a0_result)?;
    let mut a_end = cut_view(a.constitution(), &[])?;
    a_end.opening_crossings = Some(a_crossings);
    let receiver_grain = resident
        .admitted()
        .first()
        .ok_or("full A/A0 has no admitted receiver")?
        .grain();
    let mut report_budget = timing::ReportBudget::new(budget, "A_stall", classes.len());
    let mut capture = epoch::ReportCapture::default();
    let report = a_pool.install(|| {
        epoch::report_stall_epoch(
            "A",
            crossing,
            &a_end,
            &a_views,
            receiver_grain,
            &mut report_budget,
            &mut capture,
        )
        .map_err(|error| error.to_string())
    });
    let mut failures = Vec::new();
    verdict::defer_report_result("A", report, &mut failures);
    println!(
        "step0_epoch_report_timing branch=A summary={:?}",
        report_budget.finish()
    );
    let mut postwork = timing::ReportBudget::new(budget, "AA0_postwork", classes.len());
    let (state_equal, crib_equal, crossing_count_equal) = guarded_report_work(
        &mut postwork,
        "A/A0 complete resident and crib equality",
        || {
            let source = resident.field().sources()[0];
            Ok((
                a.continuing_state(source)? == a0.continuing_state(source)?,
                a_crib == a0_crib,
                a_crossings == a0_crossings,
            ))
        },
    )?;
    println!(
        "step0_AA0 exact_resident_state_equal={state_equal} caller_owned_crib_equal={crib_equal} actual_crossing_count_equal={crossing_count_equal} A_end_crossings={a_crossings} A0_end_crossings={a0_crossings}"
    );
    verdict::defer_report_result(
        "A/A0",
        if state_equal && crib_equal && crossing_count_equal {
            Ok(())
        } else {
            Err(
                "identical-input replicas diverged in exact state, crib or actual crossing count"
                    .to_owned(),
            )
        },
        &mut failures,
    );
    postwork.check_before_work("full A/A0 report completion")?;
    verdict::finish_deferred_reports(&failures)
}

pub(super) fn run(
    port: &Reference,
    options: ContinuingOptions,
    checkpoint_path: Option<&str>,
) -> Result<()> {
    let profile_cells = options.diagnostic_profile_trunk_cells;
    let full_run = profile_cells.is_none()
        && !options.diagnostic_calibration_only
        && !options.diagnostic_profile_paired_cells64;
    let reserve_ns = if full_run {
        options
            .diagnostic_report_reserve_ns
            .ok_or("full diagnostic requires an explicit --diagnostic-report-reserve-ns")?
    } else {
        options.diagnostic_report_reserve_ns.unwrap_or(0)
    };
    if full_run && reserve_ns < 5_000_000_000 {
        return Err(
            "full diagnostic report reserve must be at least the fixed five-second floor".into(),
        );
    }
    let budget = timing::RunBudget::new(reserve_ns)?;
    let admission = if full_run {
        let pinned = timing::ReportAdmission::from_env()?;
        println!(
            "step0_reporting_growth empirical_forecast=true completion_not_certified=true input={pinned:?}"
        );
        let initial_native = historical_native_projection(312 + 231)?;
        pinned.admit(
            initial_native,
            1,
            admission_remaining(&budget)?,
            300_000_000_000,
        )?;
        // The native grain denominator supplies no amended partition exponent. Until the
        // producing source exposes it, refuse rather than manufacture b from that denominator.
        epoch::require_partition_precision(None)?;
        Some(pinned)
    } else {
        None
    };
    let checkpoint_target =
        checkpoint_path.map(|path| format!("{}/step-000312.state", path.trim_end_matches('/')));
    if let Some(checkpoint) = &checkpoint_target {
        if std::path::Path::new(checkpoint).exists()
            || std::path::Path::new(&format!("{checkpoint}.tmp")).exists()
        {
            return Err(format!(
                "step0 diagnostic is create-only and refuses existing checkpoint target {checkpoint:?}"
            )
            .into());
        }
    }
    let (mut resident, pairing) = mounted(port, options.population)?;
    let opening = resident.constitution().clone();
    let mut crib = ObservedCrib::new(0);
    let frames = sections_of(Some(&options.learn), options.count)?;
    let input = frames
        .first()
        .ok_or("step0 diagnostic requires section 0")?;
    let declared_source_count = input
        .passages
        .iter()
        .map(|passage| {
            Section {
                passages: vec![passage.clone()],
                target: Vec::new(),
            }
            .source_cells(0)
            .map(|cells| cells.len())
        })
        .collect::<std::result::Result<Vec<_>, _>>()?
        .into_iter()
        .sum::<usize>();
    let trunk_units = profile_cells.unwrap_or(declared_source_count);
    let mut trunk_phase = budget.phase("trunk", trunk_units, None)?;
    let mut source_count = 0usize;
    let mut receiver_crossings = 0_u64;
    let mut trunk_native_ns = 0u128;
    let mut trunk_source_classes = Vec::with_capacity(trunk_units.min(312));
    for passage in &input.passages {
        let source = Section {
            passages: vec![passage.clone()],
            target: Vec::new(),
        }
        .source_cells(0)?;
        for class in source {
            if source_count >= trunk_units {
                break;
            }
            trunk_phase.before_cell()?;
            let started = Instant::now();
            let cpu_started = timing::ThreadCpu::read();
            let wall_before = resident.wall().phases();
            let receipt = port.observe_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                class,
                None,
                |_, _, _, _, _| (),
            )?;
            count_receiver_crossings(&mut receiver_crossings, &receipt.ingest)?;
            trunk_source_classes.push(class);
            let cell_ns = started.elapsed().as_nanos();
            trunk_phase.finish_cell(cell_ns)?;
            let cpu_delta = cpu_started
                .zip(timing::ThreadCpu::read())
                .and_then(|(a, b)| b.delta_since(a));
            let wall_after = resident.wall().phases();
            let wall_delta: Vec<_> = wall_after
                .iter()
                .zip(wall_before)
                .map(|((name, after), (_, before))| {
                    (*name, after.saturating_sub(before).as_nanos())
                })
                .collect();
            trunk_native_ns = trunk_native_ns
                .checked_add(cell_ns)
                .ok_or("trunk elapsed counter overflow")?;
            println!(
                "step0_cell branch=trunk index={source_count} class={class} delivered={} cell_ns={cell_ns} transaction_elapsed_ns={cell_ns} exterior_ns=0 cumulative_transaction_ns={trunk_native_ns} wall_delta={wall_delta:?} thread_cpu={cpu_delta:?}",
                receipt.cells
            );
            source_count += 1;
        }
        if source_count >= trunk_units {
            break;
        }
    }
    let trunk_summary = trunk_phase.finish_phase();
    println!(
        "step0_trunk_timing completed={} declared={} elapsed_wall_ns={} reserve_ns={reserve_ns}",
        trunk_summary.completed_cells, trunk_summary.declared_cells, trunk_summary.elapsed_wall_ns
    );
    if profile_cells.is_some() {
        if source_count != trunk_units {
            return Err(format!(
                "profile requested exactly {trunk_units} trunk cells but source contained only {source_count}"
            ).into());
        }
        println!(
            "step0_profile_only source_cells={source_count}; returned before target fork, calibration, checkpoint, and epoch readouts"
        );
        return Ok(());
    }
    if source_count != 312 {
        return Err(
            format!("step0 section-0 source cut has {source_count} cells, expected 312").into(),
        );
    }
    if options.diagnostic_profile_paired_cells64 {
        let classes = trunk_source_classes
            .get(..64)
            .ok_or("paired profile requires at least 64 captured source classes")?;
        let crossing = cut_view(resident.constitution(), &[])?;
        let mut plain = resident.clone();
        let mut plain_crib = crib.clone();
        let mut capture = resident.clone();
        let mut capture_crib = crib.clone();
        let abort = AtomicBool::new(false);
        let calibration_pool = execution::one_thread_pool()?;
        let plain_started = Instant::now();
        let plain_result = calibration_pool.install(|| {
            observe_plain_branch(
                port,
                &mut plain,
                &mut plain_crib,
                &pairing,
                classes,
                "profile_plain",
                &budget,
                &abort,
                None,
            )
            .map_err(|error| error.to_string())
        });
        let (_, _, plain_times) = from_worker(plain_result)?;
        let plain_elapsed = plain_started.elapsed();
        let capture_started = Instant::now();
        let capture_result = calibration_pool.install(|| {
            observe_branch(
                port,
                &mut capture,
                &mut capture_crib,
                &pairing,
                classes,
                "profile_capture",
                &crossing.map,
                &budget,
                &abort,
                None,
            )
            .map_err(|error| error.to_string())
        });
        let (views, _, _, capture_times) = from_worker(capture_result)?;
        let capture_elapsed = capture_started.elapsed();
        if plain.continuing_state(resident.field().sources()[0])?
            != capture.continuing_state(resident.field().sources()[0])?
            || plain_crib != capture_crib
        {
            return Err(
                "paired profile changed native continuation or caller-owned crib between controls"
                    .into(),
            );
        }
        let block_upper = timing::completed_block_upper_ns_per_cell(&plain_times)
            .into_iter()
            .chain(timing::completed_block_upper_ns_per_cell(&capture_times))
            .max();
        let max_observed = plain_times
            .iter()
            .chain(&capture_times)
            .copied()
            .max()
            .unwrap_or(0);
        println!(
            "step0_paired_profile transactions=440 prefix_source_cells=312 ordinary=64 sample_view_hook=64 compared_prefix=the_same_312_source_cut physical_state_equal=true caller_owned_crib_equal=true plain_elapsed_ns={} capture_elapsed_ns={} largest_observed_transaction_ns={max_observed} completed_block_upper_ns_per_cell={block_upper:?} per_cell_exact_cuts={:?}; includes the 312-cell native prefix; no target stream read, forks, checkpoint, or epoch report",
            plain_elapsed.as_nanos(),
            capture_elapsed.as_nanos(),
            views
                .iter()
                .map(|v| (&v.map, &v.gram, &v.gram_remainder))
                .collect::<Vec<_>>()
        );
        return Ok(());
    }
    let target = input.target_cells(0)?;
    if target.len() < 231 {
        return Err(format!(
            "step0 section-0 target has {} cells, fewer than 231",
            target.len()
        )
        .into());
    }
    let crossing = cut_view(resident.constitution(), &[])?;
    let base_classes = target[..231].to_vec();
    if full_run {
        let mut crossing = crossing;
        crossing.opening_crossings = Some(receiver_crossings);
        return run_full_aa0(
            port,
            &resident,
            &opening,
            &crib,
            &pairing,
            &base_classes,
            &crossing,
            &budget,
            admission.as_ref().ok_or("full report admission missing")?,
            receiver_crossings,
            checkpoint_path.ok_or("full diagnostic requires checkpoint destination")?,
            source_count,
        );
    }
    let calibration_classes = &base_classes[..64];
    let mut calibration_plain = resident.clone();
    let mut calibration_plain_crib = crib.clone();
    let calibration_pool = execution::one_thread_pool()?;
    let plain_started = Instant::now();
    let calibration_abort = AtomicBool::new(false);
    let plain_calibration_result = calibration_pool.install(|| {
        observe_plain_branch(
            port,
            &mut calibration_plain,
            &mut calibration_plain_crib,
            &pairing,
            calibration_classes,
            "calibration_plain",
            &budget,
            &calibration_abort,
            None,
        )
        .map_err(|error| error.to_string())
    });
    let (_plain_faces, _plain_lifts, plain_cell_ns) = from_worker(plain_calibration_result)?;
    let plain_elapsed = plain_started.elapsed();
    let mut calibration_capture = resident.clone();
    let mut calibration_capture_crib = crib.clone();
    let capture_started = Instant::now();
    let capture_calibration_result = calibration_pool.install(|| {
        observe_branch(
            port,
            &mut calibration_capture,
            &mut calibration_capture_crib,
            &pairing,
            calibration_classes,
            "calibration_capture",
            &crossing.map,
            &budget,
            &calibration_abort,
            None,
        )
        .map_err(|error| error.to_string())
    });
    let (capture_views, _capture_faces, _capture_lifts, capture_cell_ns) =
        from_worker(capture_calibration_result)?;
    let capture_elapsed = capture_started.elapsed();
    let plain_state = calibration_plain.continuing_state(resident.field().sources()[0])?;
    let capture_state = calibration_capture.continuing_state(resident.field().sources()[0])?;
    if plain_state != capture_state || calibration_plain_crib != calibration_capture_crib {
        return Err(
            "sample-view calibration changed physical continuation or caller-owned crib".into(),
        );
    }
    let captured_samples = capture_views
        .iter()
        .map(|view| view.samples.len())
        .sum::<usize>();
    let capture_record_bytes = capture_views
        .iter()
        .map(|view| view.capture_record_bytes)
        .sum::<usize>();
    let max_observed_calibration_cell_ns = plain_cell_ns
        .iter()
        .chain(&capture_cell_ns)
        .copied()
        .max()
        .unwrap_or(0);
    let completed_block_upper = timing::completed_block_upper_ns_per_cell(&plain_cell_ns)
        .into_iter()
        .chain(timing::completed_block_upper_ns_per_cell(&capture_cell_ns))
        .max();
    println!(
        "step0_calibration cells_per_control=64 no_capture_elapsed_ms={} with_actual_capture_elapsed_ms={} captured_samples={captured_samples} plain_samples=0 capture_record_bytes_total={capture_record_bytes} capture_record_bytes_per_cell={}/{} max_observed_cell_ns={max_observed_calibration_cell_ns} completed_block_upper_ns_per_cell={completed_block_upper:?} exact_statistics=formed_once_inside_epoch_report physical_state_equal=true crib_equal=true total_report_output_bytes_per_cell=unavailable; held_reading_record_bytes_per_evaluated_cell=emitted_by_calibration_epoch_report",
        plain_elapsed.as_millis(),
        capture_elapsed.as_millis(),
        capture_record_bytes,
        capture_views.len()
    );
    let calibration_end = cut_view(calibration_capture.constitution(), &[])?;
    let mut calibration_report_budget =
        timing::ReportBudget::new(&budget, "calibration_capture", capture_views.len());
    let mut epoch_report_failures = Vec::new();
    let mut calibration_report_capture = epoch::ReportCapture::default();
    let calibration_report_result = calibration_pool.install(|| {
        epoch::report_epoch(
            "calibration_capture",
            &crossing,
            &calibration_end,
            &capture_views,
            resident
                .admitted()
                .first()
                .ok_or("no admitted receiving source")?
                .grain(),
            &mut calibration_report_budget,
            &mut calibration_report_capture,
        )
        .map_err(|error| error.to_string())
    });
    let calibration_report = calibration_report_budget.finish();
    println!(
        "step0_calibration_report branch={} held_eval={:?} gram_inverse={:?} other={:?} elapsed_ns={} projected_231_ns={:?} remaining_report_ns={}",
        calibration_report.branch,
        calibration_report.held_eval,
        calibration_report.gram_inverse,
        calibration_report.other,
        calibration_report.elapsed_ns,
        calibration_report.projected_231_ns,
        calibration_report.remaining_report_ns
    );
    verdict::defer_report_result(
        "calibration_capture",
        calibration_report_result,
        &mut epoch_report_failures,
    );
    println!(
        "step0_calibration_only exact_cells=440 (312 trunk + 64 plain + 64 actual capture); no checkpoint or fork written"
    );
    verdict::finish_deferred_reports(&epoch_report_failures)
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::ratio::{integer, rat};

    #[test]
    fn opening_crossings_count_ingress_receipts_and_refuse_overflow() {
        let receipt = holonics::hnn::port::port_receipt(
            &[17, 2, 1],
            &integer(1),
            holonics::ratio::work::ExactWork::nothing(),
            ReceiptDetail::Discard { bits: 0 },
        )
        .unwrap();
        let mut crossings = 7;
        count_receiver_crossings(&mut crossings, &receipt).unwrap();
        assert_eq!(crossings, 8);
        let mut fork_crossings = crossings;
        count_receiver_crossings(&mut fork_crossings, &receipt).unwrap();
        assert_eq!((crossings, fork_crossings), (8, 9));
        let mut overflow = u64::MAX;
        assert!(count_receiver_crossings(&mut overflow, &receipt).is_err());
        assert_eq!(overflow, u64::MAX);
    }

    #[test]
    fn complete_historical_native_horizon_alone_exceeds_fixed_native_cutoff() {
        assert_eq!(
            historical_native_projection(312 + 231).unwrap(),
            298_469_708_253
        );
        assert!(historical_native_projection(312 + 231).unwrap() > 290_000_000_000);
    }

    fn sample(weight: Rat, feature: Vec<Rat>, covector: Vec<Rat>) -> Sample {
        Sample {
            weight,
            feature,
            covector,
            masses: None,
        }
    }

    #[test]
    fn held_wave_applies_exact_zero_and_nonzero_fixed_map_shift() {
        let crossing = ExactRatMatrix::new(vec![vec![integer(3)], vec![integer(6)]]).unwrap();
        let same = crossing.clone();
        let zero = ExactRatMatrix::new(vec![vec![integer(0)], vec![integer(0)]]).unwrap();
        let sample = sample(integer(1), vec![integer(2)], vec![integer(0)]);
        let read = ReceivingRead::of_logits(vec![integer(10), integer(20)], 1);
        let wave = Faces::of_reads(&[read], 1).unwrap();

        let unchanged = held_wave(&crossing, &same, &wave, &[sample.clone()]).unwrap();
        assert_eq!(unchanged.logits, wave.logits);

        let shifted = held_wave(&crossing, &zero, &wave, &[sample]).unwrap();
        assert_eq!(shifted.logits, vec![vec![integer(16), integer(32)]]);
    }

    #[test]
    fn exact_epoch_statistics_preserve_sample_weight_and_signs() {
        let sample = sample(
            integer(3),
            vec![rat(1, 2), integer(-1)],
            vec![integer(2), integer(-1)],
        );
        let mut gradient = vec![vec![Rat::zero(); 2]; 2];
        let mut gram = vec![vec![Rat::zero(); 2]; 2];
        add_sample_statistics(
            &mut gradient,
            &mut gram,
            &[sample.clone()],
            &[sample.covector.clone()],
        )
        .unwrap();
        assert_eq!(
            gradient,
            vec![vec![integer(3), integer(-6)], vec![rat(-3, 2), integer(3)]]
        );
        assert_eq!(
            gram,
            vec![vec![rat(3, 4), rat(-3, 2)], vec![rat(-3, 2), integer(3)]]
        );
    }

    #[test]
    fn crossing_metric_recomputes_masses_and_changes_g_but_not_gram_delta() {
        let live = Sample {
            weight: integer(1),
            feature: vec![integer(2)],
            covector: vec![rat(1, 10), integer(0), rat(-1, 10), integer(0)],
            // These masses belong to the live-map comparison and would imply scale 2.
            masses: Some(vec![rat(1, 2), rat(1, 2)]),
        };
        let crossing_covector = vec![rat(1, 10), integer(0), rat(-1, 10), integer(0)];
        let (reached, metric, scale) =
            crossing_metric_samples(&[live.clone()], &[crossing_covector]).unwrap();
        assert_eq!(scale, Some(integer(4)));
        assert_eq!(reached[0].masses, None);
        assert_eq!(
            metric[0].covector,
            vec![rat(2, 5), integer(0), rat(-2, 5), integer(0)]
        );

        let law = NormalLaw::with_prior(ExactRatMatrix::zero(4, 1).unwrap());
        let (gradient_metric, gram_metric) = law.projected_statistics(&metric).unwrap();
        let (gradient_unscaled, gram_unscaled) = law.projected_statistics(&reached).unwrap();
        assert_ne!(gradient_metric, gradient_unscaled);
        assert_eq!(gradient_metric.get(0, 0).unwrap(), &rat(4, 5));
        assert_eq!(gradient_unscaled.get(0, 0).unwrap(), &rat(1, 5));
        assert_eq!(gram_metric, gram_unscaled);
        assert_eq!(gram_metric.to_rows(), vec![vec![integer(4)]]);
    }

    #[test]
    fn source_interventions_keep_one_branch_per_lock_advance_category() {
        fn source_field(lock: Vec<u64>) -> Field {
            let mut declaration = holonics::hnn::field::FieldDeclaration::campaign_one(1 << 17);
            let source = &mut declaration.rings[0];
            source.period = 16;
            source.placements = (0..16)
                .map(|node| holonics::hnn::field::FieldDeclaration::quarter_turn(node, 16))
                .collect();
            source.reflector = (0..16).map(|port| ((16 - port) % 16) as usize).collect();
            source.lock = lock;
            declaration.alphabet = 16;
            Field::declare(declaration.by_lattice_rule()).unwrap()
        }

        let partial = source_field(vec![0]);
        let partial_cases = source_interventions(&partial, &[1]).unwrap();
        let base = partial.class_advance(0, 1).unwrap();
        assert_eq!(partial_cases.len(), 2);
        assert!(partial_cases.iter().any(|(_, _, advance)| *advance == base));
        assert!(partial_cases.iter().any(|(_, _, advance)| *advance != base));

        let all_fit = source_field((0..16).collect());
        let all_fit_cases = source_interventions(&all_fit, &[1]).unwrap();
        assert_eq!(all_fit_cases.len(), 1);
        assert_eq!(all_fit_cases[0].1, 1 ^ 8);
    }

    #[test]
    fn coarse_face_projection_keeps_grain_phase_but_drops_fibre_and_logits() {
        let left = Faces::of_reads(
            &[ReceivingRead::of_logits(vec![rat(1, 7), integer(0)], 3)],
            3,
        )
        .unwrap();
        let right = Faces::of_reads(
            &[ReceivingRead::of_logits(vec![rat(1, 5), integer(0)], 3)],
            3,
        )
        .unwrap();
        let left_key = coarse_face_key(&left);
        let right_key = coarse_face_key(&right);
        // The projection intentionally discards exact logits and fibre coordinates. It keeps
        // only the declared grain and phase/carry chart used for this comparison.
        assert_eq!(left_key[0].grain, 3);
        assert_eq!(right_key[0].grain, 3);
        assert_eq!(left_key.len(), right_key.len());
        assert_eq!(left_key, right_key);
        assert_ne!(left.logits, right.logits);
    }
}
