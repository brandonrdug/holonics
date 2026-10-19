//! Read-only listener diagnostic with a target fork and dynamically selected lock-advance cases.
//! The optional hook returns exact receiving samples already staged in the ordinary transaction.

#[path = "diagnostic/epoch.rs"]
mod epoch;
#[path = "diagnostic/timing.rs"]
mod timing;

use super::*;
use holonics::hnn::constitution::Sample;
use holonics::hnn::constitution::{Carrier, NormalLaw};
use holonics::hnn::contact::{LockDeclaration, lock_address};
use holonics::hnn::moment::PopulationChart;
use holonics::hnn::receiving::ReceivingRead;
use holonics::hnn::reference::FrozenComparison;
use holonics::hnn::word::{EndChange, ReceptionCarry};
use holonics::ratio::integer;
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
        let serialization_started = Instant::now();
        let captured = format!(
            "moment_pre_ingest={} address_pre_ingest={} pre_clocks={:?} pre_lift={:?} pre_call_reception_carry={:?} producing_identity={:?} producing_map={:?} frozen_comparison={:?} samples_f_g_w_masses={:?} crossing_covectors={:?} refine_word_end_change={:?} contact_J={:?} postdeposit_map={:?} H_stored={:?} H_remainder={:?} actual_native_released_gram_entries={:?} receiving_prior={:?} current_prior_scale={}",
            view.moment_text,
            view.address_text,
            view.pre_clocks,
            view.pre_lift,
            view.pre_carried,
            view.producing,
            view.producing_map,
            view.frozen,
            view.samples,
            view.crossing_covectors,
            view.physical,
            view.contact_j,
            view.map,
            view.gram,
            view.gram_remainder,
            view.gram_release,
            view.receiving_prior,
            view.prior_scale,
        );
        let serialization_ns = serialization_started.elapsed().as_nanos();
        println!("step0_capture_data branch={branch} index={index} class={class} {captured}");
        println!(
            "step0_capture_serialization branch={branch} index={index} serialization_ns={serialization_ns} (formatting only; stdout I/O excluded)"
        );
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

fn epoch_statistics(
    crossing: &CutView,
    views: &[CutView],
) -> Result<(ExactRatMatrix, ExactRatMatrix)> {
    let mut reached = Vec::new();
    for view in views {
        if view.samples.len() != view.crossing_covectors.len() {
            return Err("crossing covector count differs from staged sample count".into());
        }
        for (sample, covector) in view.samples.iter().zip(&view.crossing_covectors) {
            let mut sample = sample.clone();
            sample.covector = covector.clone();
            reached.push(sample);
        }
    }
    crossing
        .law
        .projected_statistics(&reached)
        .map_err(Into::into)
}

fn causal_differences(
    a_views: &[CutView],
    a_faces: &[Faces],
    b_views: &[CutView],
    b_faces: &[Faces],
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
    }
    Ok((
        max_feature_delta,
        first_feature_delta,
        max_logit_delta,
        first_logit_delta,
    ))
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
    let budget = timing::RunBudget::new(reserve_ns)?;
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
        let plain_started = Instant::now();
        let (_, _, plain_times) = observe_plain_branch(
            port,
            &mut plain,
            &mut plain_crib,
            &pairing,
            classes,
            "profile_plain",
            &budget,
            &abort,
        )?;
        let plain_elapsed = plain_started.elapsed();
        let capture_started = Instant::now();
        let (views, _, _, capture_times) = observe_branch(
            port,
            &mut capture,
            &mut capture_crib,
            &pairing,
            classes,
            "profile_capture",
            &crossing.map,
            &budget,
            &abort,
        )?;
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
    let mut a = resident.clone();
    let mut a_crib = crib.clone();
    let mut a0 = resident.clone();
    let mut a0_crib = crib.clone();
    let base_classes = target[..231].to_vec();
    let calibration_classes = &base_classes[..64];
    let mut calibration_plain = resident.clone();
    let mut calibration_plain_crib = crib.clone();
    let plain_started = Instant::now();
    let calibration_abort = AtomicBool::new(false);
    let (_plain_faces, _plain_lifts, plain_cell_ns) = observe_plain_branch(
        port,
        &mut calibration_plain,
        &mut calibration_plain_crib,
        &pairing,
        calibration_classes,
        "calibration_plain",
        &budget,
        &calibration_abort,
    )?;
    let plain_elapsed = plain_started.elapsed();
    let mut calibration_capture = resident.clone();
    let mut calibration_capture_crib = crib.clone();
    let capture_started = Instant::now();
    let (capture_views, _capture_faces, _capture_lifts, capture_cell_ns) = observe_branch(
        port,
        &mut calibration_capture,
        &mut calibration_capture_crib,
        &pairing,
        calibration_classes,
        "calibration_capture",
        &crossing.map,
        &budget,
        &calibration_abort,
    )?;
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
    let postwork_started = Instant::now();
    let _ = epoch_statistics(&crossing, &capture_views)?;
    let exact_statistics_postwork = postwork_started.elapsed();
    println!(
        "step0_calibration cells_per_control=64 no_capture_elapsed_ms={} with_actual_capture_elapsed_ms={} captured_samples={captured_samples} plain_samples=0 max_observed_cell_ns={max_observed_calibration_cell_ns} completed_block_upper_ns_per_cell={completed_block_upper:?} exact_statistics_computed=true physical_state_equal=true crib_equal=true exact_statistics_postwork_ms={}",
        plain_elapsed.as_millis(),
        capture_elapsed.as_millis(),
        exact_statistics_postwork.as_millis()
    );
    if options.diagnostic_calibration_only {
        println!(
            "step0_calibration_only exact_cells=440 (312 trunk + 64 plain + 64 actual capture); no checkpoint or fork written"
        );
        return Ok(());
    }
    let first = base_classes[0];
    let source_ring = *resident
        .field()
        .sources()
        .first()
        .ok_or("source ring missing")?;
    let fit_ring = resident.field().ring(source_ring);
    let fit_all = (0..resident.field().alphabet()).all(|class| fit_ring.fits(fit_ring.port(class)));
    let intervention_specs = source_interventions(resident.field(), &base_classes)?;
    let branch_workers = 2usize + intervention_specs.len();
    let branch_waves = branch_workers.div_ceil(3);
    let Some(block_upper_ns_per_cell) = completed_block_upper else {
        return Err("calibration produced no completed eight-cell timing block; refusing a branch projection".into());
    };
    let branch_projection = block_upper_ns_per_cell.saturating_mul(231);
    let projection = branch_projection.saturating_mul(branch_waves as u128);
    let remaining_ns = budget.remaining_ns()?;
    println!(
        "step0_projection completed_block_upper_ns_per_cell={block_upper_ns_per_cell} branch_workers={branch_workers} declared_cpu_workers=3 conservative_waves={branch_waves} one_branch_projection_ns={branch_projection} parallel_branch_horizon_projection_ns={projection} branch_cap_ns=180000000000 remaining_global_ns={remaining_ns} forecast_only=true"
    );
    if branch_projection > 180_000_000_000 || projection > remaining_ns {
        return Err("measured branch projection exceeds the 180-second branch cap or remaining fixed run budget; aborting before fork".into());
    }
    let checkpoint_path =
        checkpoint_path.ok_or("full diagnostic requires checkpoint destination")?;
    crate::octets::save_checkpoint(
        &resident,
        &opening,
        resident.field().sources()[0],
        checkpoint_path,
        source_count,
    )?;
    println!(
        "step0_checkpoint scope=resident_only crib_sidecar=false; ObservedCrib is caller-owned and no validated roundtrip codec exists, so later observed resume is not claimed"
    );
    let mut b_branches: Vec<(String, usize, u64, Vec<usize>, Resident, ObservedCrib)> =
        intervention_specs
            .iter()
            .map(|(name, class, advance)| {
                let mut classes = base_classes.clone();
                classes[0] = *class;
                (
                    name.clone(),
                    *class,
                    *advance,
                    classes,
                    resident.clone(),
                    crib.clone(),
                )
            })
            .collect();
    let declared_transactions = 312usize + 64 + 64 + 231 * (2 + b_branches.len());
    println!(
        "step0_protocol transactions={declared_transactions} components=312_trunk+64_plain+64_capture+231*(A+A0+{}_B_variants) branch_workers={} variants={:?}",
        b_branches.len(),
        2 + b_branches.len(),
        b_branches
            .iter()
            .map(|(name, class, advance, _, _, _)| (name, class, advance))
            .collect::<Vec<_>>()
    );
    let source_fit_pattern = |classes: &[usize]| {
        classes
            .iter()
            .map(|&class| {
                if fit_ring.fits(fit_ring.port(class)) {
                    '1'
                } else {
                    '0'
                }
            })
            .collect::<String>()
    };
    println!(
        "step0_source_advance source_ring={source_ring} A_class={first} A_advance={} A_fit_pattern={} intervention_count={} interventions={intervention_specs:?}; source clock is distinct from receiver clock",
        resident.field().class_advance(source_ring, first)?,
        source_fit_pattern(&base_classes),
        b_branches.len()
    );
    let clock_phases = clock_snapshot(&resident)?;
    let contacts = resident
        .field()
        .contacts()
        .iter()
        .enumerate()
        .map(|(index, contact)| {
            let (from, to) = contact.ends();
            let from_winding = resident.current().winding(resident.field(), from)?;
            let to_winding = resident.current().winding(resident.field(), to)?;
            let bound = LockDeclaration::derived(resident.field(), index);
            let address = lock_address(&from_winding, &to_winding, &bound);
            let geometric_lock = contact
                .pair(resident.field(), resident.current().lift())
                .lock(&from_winding, &to_winding)
                .map(|reading| format!("reading={reading:?}"))
                .unwrap_or_else(|error| format!("typed_refusal={error}"));
            let lock_metadata = format!(
                "pre_from_winding={from_winding} pre_to_winding={to_winding} hnn_bound={bound:?} hnn_lock_address={address:?} geometric_pair_lock={geometric_lock}"
            );
            Ok((
                index,
                contact.ends(),
                contact.admittance().clone(),
                lock_metadata,
                holonics::hnn::propagation::contact_exponent(
                    resident.field(),
                    index,
                    resident.current().lift(),
                )?,
            ))
        })
        .collect::<std::result::Result<Vec<_>, HnnError>>()?;
    let receiver_grain = resident
        .admitted()
        .first()
        .ok_or("no admitted receiving source")?
        .grain();
    let lr_inverse = Rat::new(BigInt::from(1), BigInt::from(receiver_grain));
    let half_quantum = &lr_inverse / integer(2);
    let source_rings = resident.field().sources();
    let ring_metadata: Vec<_> = (0..resident.field().rings().len())
        .map(|ring| {
            let rho = resident.constitution().transport(ring);
            let resonator = resident
                .constitution()
                .resonator(ring)
                .map(|r| format!("pump={:?}", r.pump()));
            let rho0 = source_rings.contains(&ring).then(|| {
                match resident
                    .constitution()
                    .founding_transport(resident.field(), ring)
                {
                    Ok(candidate) => format!("candidate={candidate}"),
                    Err(error) => format!("refusal={error}"),
                }
            });
            (ring, rho, rho0, resonator)
        })
        .collect();
    println!(
        "step0_crossing source_cells={source_count} next_epoch_cells=231 target_cells={} checkpoint={checkpoint_path:?} crossing_W={:?} crossing_H_stored={:?} crossing_H_remainder={:?} L_R={} inverse_L_R={} native_half_quantum={} native_L_W={} declared_field_L_W={} L_nu={} clock_phases={clock_phases:?} ring_transport_resonators={ring_metadata:?}",
        target.len(),
        crossing.map,
        crossing.gram,
        crossing.gram_remainder,
        receiver_grain,
        lr_inverse,
        half_quantum,
        crossing.native_lattice_exponent,
        resident
            .field()
            .lattice(Locus::ReceivingMap(2))
            .ok_or("receiver map lattice missing")?
            .exponent(),
        PopulationChart::of(resident.field()).exponent(),
    );
    let path_contacts: Vec<_> = contacts
        .iter()
        .filter(|(_, ends, _, _, _)| *ends == (0, 1) || *ends == (1, 2))
        .collect();
    let path_product = if path_contacts.len() == 2 {
        let conductances = path_contacts
            .iter()
            .map(|(_, _, admittance, _, reading)| {
                Ok(holonics::ratio::exponentiated::power_of_two(&reading.carry)? * admittance)
            })
            .collect::<std::result::Result<Vec<Rat>, HnnError>>()?;
        Some(conductances.into_iter().product::<Rat>())
    } else {
        None
    };
    println!(
        "step0_contact_metadata pre_call_whole_windings_bounds_hnn_lock_address_and_geometry_J contacts={contacts:?} contact_carry_only_0_1_1_2_product={path_product:?} phase_class_factor=omitted causal_receiver_gain_claim=none; carry-only product is not an end-to-end input-to-face bound"
    );
    let branch_abort = AtomicBool::new(false);
    let (a_result, a0_result, b_results) = std::thread::scope(|scope| {
        let a_worker = scope.spawn(|| {
            guarded_worker(&branch_abort, || {
                observe_branch(
                    port,
                    &mut a,
                    &mut a_crib,
                    &pairing,
                    &base_classes,
                    "A",
                    &crossing.map,
                    &budget,
                    &branch_abort,
                )
            })
        });
        let a0_worker = scope.spawn(|| {
            guarded_worker(&branch_abort, || {
                observe_plain_branch(
                    port,
                    &mut a0,
                    &mut a0_crib,
                    &pairing,
                    &base_classes,
                    "A0",
                    &budget,
                    &branch_abort,
                )
            })
        });
        let branch_abort_ref = &branch_abort;
        let pairing_ref = &pairing;
        let crossing_map_ref = &crossing.map;
        let budget_ref = &budget;
        let port_ref = port;
        let b_workers: Vec<_> = b_branches
            .iter_mut()
            .map(|(name, _, _, classes, branch_resident, branch_crib)| {
                let name = name.clone();
                let worker_name = name.clone();
                let branch_abort = branch_abort_ref;
                let pairing = pairing_ref;
                let crossing_map = crossing_map_ref;
                let budget = budget_ref;
                let port = port_ref;
                let handle = scope.spawn(move || {
                    guarded_worker(branch_abort, || {
                        observe_branch(
                            port,
                            branch_resident,
                            branch_crib,
                            pairing,
                            classes,
                            &worker_name,
                            crossing_map,
                            budget,
                            branch_abort,
                        )
                    })
                });
                (name, handle)
            })
            .collect();
        let a_result = a_worker
            .join()
            .unwrap_or_else(|_| Err("A branch worker panicked".to_owned()));
        let a0_result = a0_worker
            .join()
            .unwrap_or_else(|_| Err("A0 branch worker panicked".to_owned()));
        let b_results = b_workers
            .into_iter()
            .map(|(name, worker)| {
                let result = worker
                    .join()
                    .unwrap_or_else(|_| Err(format!("{name} branch worker panicked")));
                (name, result)
            })
            .collect::<Vec<_>>();
        (a_result, a0_result, b_results)
    });
    let (a_views, a_faces, _a_lifts, _a_times) = from_worker(a_result)?;
    let (_a0_faces, _a0_lifts, _a0_times) = from_worker(a0_result)?;
    let a_end = cut_view(a.constitution(), &[])?;
    let mut b_outputs = Vec::with_capacity(b_branches.len());
    for ((name, class, advance, _, branch_resident, _), (result_name, result)) in
        b_branches.iter().zip(b_results)
    {
        if name != &result_name {
            return Err("dynamic branch result ordering changed".into());
        }
        let (views, faces, _lifts, _times) = from_worker(result)?;
        let end = cut_view(branch_resident.constitution(), &[])?;
        let clocks = clock_snapshot(branch_resident)?;
        b_outputs.push((name.clone(), *class, *advance, views, faces, end, clocks));
    }
    let base_advance = resident.field().class_advance(source_ring, first)?;
    let primary_b = b_outputs
        .iter()
        .position(|(_, _, advance, _, _, _, _)| *advance == base_advance)
        .unwrap_or(0);
    let (b_name, alternative, b_advance, b_views, b_faces, b_end, _) = &b_outputs[primary_b];
    println!(
        "step0_clock_registers crossing={clock_phases:?} A_end={:?} A0_end={:?} B_end={:?} feature_content_clock_split=not_declared_in_actual_feature_basis",
        clock_snapshot(&a)?,
        clock_snapshot(&a0)?,
        b_outputs
            .iter()
            .map(|(name, class, advance, _, _, _, clocks)| (name, class, advance, clocks))
            .collect::<Vec<_>>()
    );
    let spec_lw = epoch::spec_lattice_exponent(receiver_grain, crossing.support.len())?;
    println!(
        "step0_lattice_exponents spec_LW={spec_lw} crossing={} crossing_native_spec_mismatch={} A_end={} A_native_spec_mismatch={} B_end_and_native_spec_mismatch={:?}",
        crossing.native_lattice_exponent,
        crossing.native_lattice_exponent != spec_lw,
        a_end.native_lattice_exponent,
        a_end.native_lattice_exponent != spec_lw,
        b_outputs
            .iter()
            .map(|(name, _, _, _, _, end, _)| (
                name,
                end.native_lattice_exponent,
                end.native_lattice_exponent != spec_lw
            ))
            .collect::<Vec<_>>()
    );
    println!(
        "step0_specification_lattice_exponent b_R=log2(2*L_R) support_width={} spec_LW={spec_lw}",
        crossing.support.len()
    );
    let epoch_report_started = Instant::now();
    epoch::report_epoch("A", &crossing, &a_end, &a_views, receiver_grain)?;
    println!(
        "step0_epoch_report_timing branch=A wall_ns={}",
        epoch_report_started.elapsed().as_nanos()
    );
    for (name, _, _, views, _, end, _) in &b_outputs {
        let epoch_report_started = Instant::now();
        epoch::report_epoch(name, &crossing, end, views, receiver_grain)?;
        println!(
            "step0_epoch_report_timing branch={name} wall_ns={}",
            epoch_report_started.elapsed().as_nanos()
        );
    }
    let a_state = a.continuing_state(resident.field().sources()[0])?;
    let a0_state = a0.continuing_state(resident.field().sources()[0])?;
    let aa_equal = a_state == a0_state && a_crib == a0_crib;
    if !aa_equal {
        return Err(
            "A/A0 identical-input replicas diverged in exact resident state or crib".into(),
        );
    }
    println!("step0_AA0 exact_resident_state_equal=true caller_owned_crib_equal=true");
    let (g_a, _) = epoch_statistics(&crossing, &a_views)?;
    let (g_b, _) = epoch_statistics(&crossing, b_views)?;
    let (max_f_delta, first_f_delta, max_logit_delta, first_logit_delta) =
        causal_differences(&a_views, &a_faces, b_views, b_faces)?;
    println!(
        "step0_intervention all_alphabet_classes_fit_source_lock={fit_all} first_class={first} changed_class={alternative} primary_branch={b_name} changed_advance={b_advance} alternatives={intervention_specs:?} G_A={g_a:?} G_B={g_b:?} W_table_delta_A={:?} W_table_delta_B={:?}",
        matrix_delta(&a_end.map, &crossing.map)?,
        matrix_delta(&b_end.map, &crossing.map)?
    );
    let source_base_advance = resident.field().class_advance(source_ring, first)?;
    for (name, class, advance, views, faces, end, _) in &b_outputs {
        if name == b_name {
            continue;
        }
        let (max_f, first_f, max_logit, first_logit) =
            causal_differences(&a_views, &a_faces, views, faces)?;
        let (gradient, _) = epoch_statistics(&crossing, views)?;
        println!(
            "step0_intervention_variant_vs_A branch={name} changed_class={class} source_advance={advance} baseline_advance={source_base_advance} same_advance_category={} max_abs_delta_f={max_f} first_differing_feature_index={first_f:?} max_abs_delta_logits={max_logit} first_differing_logit_index={first_logit:?} G={gradient:?} W_table_delta={:?} native_LW_end={}",
            *advance == source_base_advance,
            matrix_delta(&end.map, &crossing.map)?,
            end.native_lattice_exponent
        );
    }
    println!(
        "step0_causal_AB max_abs_delta_f={max_f_delta} first_differing_feature_index={first_f_delta:?} max_abs_delta_logits={max_logit_delta} first_differing_logit_index={first_logit_delta:?} coordinates=(cell,sample_or_station,feature_or_class); clock_content_split=not_inferred"
    );
    fn different_indices<T: PartialEq>(left: &[T], right: &[T]) -> Vec<usize> {
        (0..left.len().max(right.len()))
            .filter(|&index| left.get(index) != right.get(index))
            .collect()
    }
    for (index, (left, right)) in a_views.iter().zip(b_views).enumerate() {
        let a_change = left.physical.as_ref().ok_or("A refine word end missing")?;
        let b_change = right.physical.as_ref().ok_or("B refine word end missing")?;
        println!(
            "step0_carried_AB index={index} preclock_equal={} pre_call_reception_carry_equal={} source_moment_counts_and_clock_equal={} producing_constitution_equal={} refine_end_storage_different_rings={:?} refine_end_arrivals_different_contacts={:?} refine_end_states_different_contacts={:?} refine_end_resonators_different_rings={:?} refine_end_resonator_phases_different_rings={:?}; comparisons_keep_pre_call_and_refine_end_cuts_separate",
            left.pre_clocks == right.pre_clocks,
            left.pre_carried == right.pre_carried,
            left.moment_text == right.moment_text,
            left.producing == right.producing,
            different_indices(&a_change.storage, &b_change.storage),
            different_indices(&a_change.arrivals, &b_change.arrivals),
            different_indices(&a_change.states, &b_change.states),
            different_indices(&a_change.resonators, &b_change.resonators),
            different_indices(&a_change.resonator_phases, &b_change.resonator_phases),
        );
    }
    let distinct_carried = (1..231).find(|&i| {
        coarse_face_key(&a_faces[i]) == coarse_face_key(&b_faces[i])
            && a_views[i].pre_clocks == b_views[i].pre_clocks
            && a_views[i].pre_carried == b_views[i].pre_carried
            && a_views[i].address_text == b_views[i].address_text
            && a_views[i].contact_j == b_views[i].contact_j
            && a_views[i]
                .physical
                .as_ref()
                .zip(b_views[i].physical.as_ref())
                .is_some_and(|(left, right)| {
                    left.states == right.states
                        && left.arrivals == right.arrivals
                        && (a_views[i].moment_text != b_views[i].moment_text
                            || a_views[i].producing != b_views[i].producing
                            || left != right)
                })
    });
    let suffix_readout = distinct_carried.map(|pair_index| {
        let start = pair_index + 1;
        let agrees = (start..231).all(|i| a_faces[i] == b_faces[i]);
        let first_divergence = (start..231).find(|&i| a_faces[i] != b_faces[i]);
        let max_logit_delta = a_faces[start..231]
            .iter()
            .zip(&b_faces[start..231])
            .flat_map(|(a, b)| a.logits.iter().zip(&b.logits))
            .flat_map(|(a, b)| a.iter().zip(b))
            .map(|(a, b)| (a - b).abs())
            .max()
            .unwrap_or_else(Rat::zero);
        (pair_index, agrees, first_divergence, max_logit_delta)
    });
    println!(
        "step0_finite_future after_candidate_pair={suffix_readout:?} divergence_indices_are_strictly_after_candidate; agreement is finite-horizon evidence only"
    );
    println!(
        "step0_reachable_pair_candidate index={distinct_carried:?} criterion=equal_coarse_grain_face_phase_key_preclock_address_contact_J_states_arrivals_and_distinct_full_carried_state pre_lifts_A={:?} pre_lifts_B={:?}; J_is_geometry_signature_only; realized_Ju_equality_and_unread_predicate_are_unavailable_and_not_established; no pair if absent",
        distinct_carried.map(|i| a_views[i].pre_lift.clone()),
        distinct_carried.map(|i| b_views[i].pre_lift.clone())
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::ratio::{integer, rat};

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
