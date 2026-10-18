//! One-fork, one-epoch read-only diagnostic. It uses the same observed-cell transaction as the
//! ordinary listener; the hook only returns the exact receiving samples already staged there.

use super::*;
use holonics::hnn::constitution::Sample;
use holonics::hnn::moment::PopulationChart;
use holonics::hnn::receiving::ReceivingRead;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use std::sync::atomic::{AtomicBool, Ordering};

const TRUNK_CELL_UPPER_NS: u128 = 186_000_000;
const CALIBRATION_CELL_UPPER_NS: u128 = 186_000_000;
const BRANCH_WALL_CAP_NS: u128 = 180_000_000_000;
const FIXED_RUN_WALL_CAP_NS: u128 = 300_000_000_000;

fn within_n_u(cumulative_ns: u128, completed: usize, unit_upper_ns: u128) -> bool {
    unit_upper_ns
        .checked_mul(completed as u128)
        .is_some_and(|allowance| cumulative_ns <= allowance)
}

fn projection_fits(projection_ns: u128, remaining_ns: u128) -> bool {
    projection_ns <= BRANCH_WALL_CAP_NS && projection_ns <= remaining_ns
}

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
    map: ExactRatMatrix,
    gram: ExactRatMatrix,
    samples: Vec<Sample>,
    receiving_prior: Option<u32>,
    prior_scale: u32,
    support: Vec<usize>,
    symmetry: String,
    crossing_covectors: Vec<Vec<Rat>>,
    receiving_step: Rat,
    receiving_vanished: bool,
}

fn cut_view(material: &Constitution, samples: &[Sample]) -> Result<CutView> {
    let law = material
        .receiving_law(2)
        .ok_or("receiver ring 2 has no single-map normal law")?;
    Ok(CutView {
        map: law.map().clone(),
        gram: law.gram(),
        samples: samples.to_vec(),
        receiving_prior: law.receiving_prior(),
        prior_scale: law.prior_scale(),
        support: law.chart().support().to_vec(),
        symmetry: format!("{:?}", law.symmetry()),
        crossing_covectors: Vec::new(),
        receiving_step: Rat::zero(),
        receiving_vanished: false,
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
    unit_upper_ns: u128,
    abort: &AtomicBool,
) -> Result<(Vec<CutView>, Vec<Faces>, Vec<Vec<BigInt>>, Vec<u128>)> {
    let mut views = Vec::with_capacity(classes.len());
    let mut faces = Vec::with_capacity(classes.len());
    let mut lifts = Vec::with_capacity(classes.len());
    let mut native_ns = 0u128;
    let mut report_ns = 0u128;
    let mut cumulative_native_ns = 0u128;
    let mut cell_times = Vec::with_capacity(classes.len());
    for (index, &class) in classes.iter().enumerate() {
        if abort.load(Ordering::Acquire) {
            return Err(
                format!("branch {branch} stopped after a shared diagnostic guard failure").into(),
            );
        }
        let cell_started = Instant::now();
        let map_at_compare = cut_view(resident.constitution(), &[])?.map;
        let native_started = Instant::now();
        let native_result = port.observe_cell_continuing_with_samples(
            resident,
            crib,
            pairing,
            class,
            None,
            |_, material, _, _, reading, samples, frozen| {
                let view = cut_view(material, samples);
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
        cumulative_native_ns = cumulative_native_ns
            .checked_add(native_elapsed)
            .ok_or("branch native elapsed counter overflow")?;
        let allowance = unit_upper_ns
            .checked_mul((index + 1) as u128)
            .ok_or("branch n*u allowance overflow")?;
        if !within_n_u(cumulative_native_ns, index + 1, unit_upper_ns) {
            abort.store(true, Ordering::Release);
            return Err(format!(
                "branch {branch} exceeded cumulative n*u guard after cell {}: {cumulative_native_ns} ns > {allowance} ns",
                index + 1
            )
            .into());
        }
        let (view_result, reading) = native.view;
        let (mut view, crossing_covectors) = view_result?;
        view.crossing_covectors = crossing_covectors;
        view.receiving_step = reading.linear_step(Locus::ReceivingMap(2));
        view.receiving_vanished = reading
            .vanished
            .iter()
            .any(|(locus, _)| *locus == Locus::ReceivingMap(2));
        faces.push(native.prediction.clone());
        lifts.push(resident.current().lift().to_vec());
        views.push(view);
        let overhead_elapsed = cell_started
            .elapsed()
            .as_nanos()
            .saturating_sub(native_elapsed);
        report_ns += overhead_elapsed;
        let cell_ns = native_elapsed + overhead_elapsed;
        cell_times.push(cell_ns);
        println!(
            "step0_cell branch={branch} index={index} class={class} cell_ns={cell_ns} native_ns={native_elapsed} exterior_ns={overhead_elapsed} cumulative_native_ns={cumulative_native_ns} n_u_allowance_ns={allowance}"
        );
    }
    println!(
        "step0_branch_timing branch={branch} cells={} native_elapsed_ns={native_ns} exterior_overhead_ns={report_ns}",
        classes.len(),
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
    unit_upper_ns: u128,
    abort: &AtomicBool,
) -> Result<(Vec<Faces>, Vec<Vec<BigInt>>, Vec<u128>)> {
    let mut faces = Vec::with_capacity(classes.len());
    let mut lifts = Vec::with_capacity(classes.len());
    let mut native_ns = 0u128;
    let mut exterior_ns = 0u128;
    let mut cumulative_native_ns = 0u128;
    let mut cell_times = Vec::with_capacity(classes.len());
    for (index, &class) in classes.iter().enumerate() {
        if abort.load(Ordering::Acquire) {
            return Err(
                format!("branch {branch} stopped after a shared diagnostic guard failure").into(),
            );
        }
        let cell_started = Instant::now();
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
        cumulative_native_ns = cumulative_native_ns
            .checked_add(native_elapsed)
            .ok_or("branch native elapsed counter overflow")?;
        let allowance = unit_upper_ns
            .checked_mul((index + 1) as u128)
            .ok_or("branch n*u allowance overflow")?;
        if !within_n_u(cumulative_native_ns, index + 1, unit_upper_ns) {
            abort.store(true, Ordering::Release);
            return Err(format!("branch {branch} exceeded cumulative n*u guard after cell {}: {cumulative_native_ns} ns > {allowance} ns", index + 1).into());
        }
        faces.push(native.prediction.clone());
        lifts.push(resident.current().lift().to_vec());
        let exterior = cell_started
            .elapsed()
            .as_nanos()
            .saturating_sub(native_elapsed);
        exterior_ns += exterior;
        let cell_ns = native_elapsed + exterior;
        cell_times.push(cell_ns);
        println!(
            "step0_cell branch={branch} index={index} class={class} cell_ns={cell_ns} native_ns={native_elapsed} exterior_ns={exterior} cumulative_native_ns={cumulative_native_ns} n_u_allowance_ns={allowance}"
        );
    }
    println!(
        "step0_branch_timing branch={branch} cells={} native_elapsed_ns={native_ns} exterior_overhead_ns={exterior_ns}",
        classes.len()
    );
    Ok((faces, lifts, cell_times))
}

fn matrix_delta(after: &ExactRatMatrix, before: &ExactRatMatrix) -> Result<ExactRatMatrix> {
    Ok(after.subtract(before)?)
}

fn from_worker<T>(result: std::result::Result<T, String>) -> Result<T> {
    result.map_err(|message| std::io::Error::other(message).into())
}

fn clock_snapshot(resident: &Resident) -> std::result::Result<Vec<(u64, u64, BigInt)>, HnnError> {
    (0..resident.field().rings().len())
        .map(|ring| {
            Ok((
                resident.field().rings()[ring].period(),
                resident.current().phase(resident.field(), ring)?,
                resident.current().winding(resident.field(), ring)?,
            ))
        })
        .collect()
}

fn epoch_statistics(
    crossing: &CutView,
    views: &[CutView],
) -> Result<(ExactRatMatrix, ExactRatMatrix)> {
    let rows = crossing.map.rows();
    let columns = crossing.map.columns();
    let mut g = vec![vec![Rat::zero(); columns]; rows];
    let mut dh = vec![vec![Rat::zero(); columns]; columns];
    for view in views {
        add_sample_statistics(&mut g, &mut dh, &view.samples, &view.crossing_covectors)?;
    }
    let gradient = ExactRatMatrix::new(g)?;
    let dh = ExactRatMatrix::new(dh)?;
    Ok((gradient, dh))
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

fn report_epoch(crossing: &CutView, end: &CutView, views: &[CutView]) -> Result<()> {
    let (gradient, dh) = epoch_statistics(crossing, views)?;
    let actual_delta = matrix_delta(&end.map, &crossing.map)?;
    let actual_gram_delta = matrix_delta(&end.gram, &crossing.gram)?;
    let candidate = if crossing.symmetry == "None" {
        end.gram
            .inverse()
            .ok()
            .map(|inverse| crossing.map.add(&gradient.multiply(&inverse).ok()?).ok())
            .flatten()
    } else {
        None
    };
    let residual = candidate
        .as_ref()
        .map(|candidate| {
            gradient.subtract(&candidate.subtract(&crossing.map)?.multiply(&end.gram)?)
        })
        .transpose()?;
    println!(
        "step0_epoch samples={} W_cross={:?} H_cross={:?} G_cross={:?} sample_H_delta={:?} H_end={:?} H_table_delta={:?} W_end={:?} W_table_delta={:?}",
        views.iter().map(|view| view.samples.len()).sum::<usize>(),
        crossing.map,
        crossing.gram,
        gradient,
        dh,
        end.gram,
        actual_gram_delta,
        end.map,
        actual_delta
    );
    println!(
        "step0_receiver_law receiving_prior={:?} current_prior_scale={} support={:?} symmetry={} radial_mode=not_exposed; actual_prior_and_support_are_retained_in_H_end",
        crossing.receiving_prior, crossing.prior_scale, crossing.support, crossing.symmetry
    );
    if let (Some(candidate), Some(residual)) = (candidate, residual) {
        println!(
            "step0_prox_quadratic_candidate W_star={candidate:?} exact_normal_residual={residual:?} objective=unconstrained_full_coordinate_local_exact_prox_quadratic_only; support={:?} symmetry={} radial_mode=not_exposed; not_cross_entropy_optimum; W_end_gap_is_not_a_deposit_law_defect_and_sets_no_order",
            crossing.support, crossing.symmetry
        );
    } else {
        println!(
            "step0_prox_quadratic_candidate status=unavailable reason=symmetry_constraint_or_singular_H_end; no projected solve was fabricated"
        );
    }
    let max_feature = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.feature)
        .map(|value| value.abs())
        .max()
        .unwrap_or_else(Rat::zero);
    let max_covector = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.covector)
        .map(|value| value.abs())
        .max()
        .unwrap_or_else(Rat::zero);
    let newest_sample_weight = views
        .iter()
        .rev()
        .find_map(|view| view.samples.last())
        .map(|sample| &sample.weight);
    let max_cross_covector = views
        .iter()
        .flat_map(|view| &view.crossing_covectors)
        .flatten()
        .map(|value| value.abs())
        .max()
        .unwrap_or_else(Rat::zero);
    let zero_step_cells = views
        .iter()
        .filter(|view| view.receiving_step.is_zero())
        .count();
    let vanished_map_cells = views.iter().filter(|view| view.receiving_vanished).count();
    println!(
        "step0_exact_observables max_abs_f={max_feature} max_abs_live_sample_g={max_covector} max_abs_G_cross={max_cross_covector} last_staged_sample_weight={newest_sample_weight:?} newest_datum_weight=unavailable_from_actual_nu_based_age_weight zero_step_cells={zero_step_cells} vanished_map_cells={vanished_map_cells} max_abs_D=unavailable_from_receipt; prepared unit D is not exposed; stalls=unavailable_without_per-step-certified-family-read"
    );
    Ok(())
}

pub(super) fn run(
    port: &Reference,
    options: ContinuingOptions,
    checkpoint_path: Option<&str>,
) -> Result<()> {
    let run_started = Instant::now();
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
    let mut source_count = 0usize;
    let mut trunk_native_ns = 0u128;
    for passage in &input.passages {
        let source = Section {
            passages: vec![passage.clone()],
            target: Vec::new(),
        }
        .source_cells(0)?;
        for class in source {
            let started = Instant::now();
            let receipt = port.observe_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                class,
                None,
                |_, _, _, _, _| (),
            )?;
            let cell_ns = started.elapsed().as_nanos();
            trunk_native_ns = trunk_native_ns
                .checked_add(cell_ns)
                .ok_or("trunk elapsed counter overflow")?;
            let trunk_allowance = TRUNK_CELL_UPPER_NS
                .checked_mul((source_count + 1) as u128)
                .ok_or("trunk n*u allowance overflow")?;
            println!(
                "step0_cell branch=trunk index={source_count} class={class} delivered={} cell_ns={cell_ns} native_ns={cell_ns} exterior_ns=0 cumulative_native_ns={trunk_native_ns} n_u_allowance_ns={trunk_allowance}",
                receipt.cells
            );
            if cell_ns > TRUNK_CELL_UPPER_NS
                || !within_n_u(trunk_native_ns, source_count + 1, TRUNK_CELL_UPPER_NS)
            {
                return Err(format!("trunk cell {source_count} exceeded declared per-cell or cumulative n*u upper {TRUNK_CELL_UPPER_NS} ns").into());
            }
            source_count += 1;
        }
    }
    if source_count != 312 {
        return Err(
            format!("step0 section-0 source cut has {source_count} cells, expected 312").into(),
        );
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
    let mut b = resident.clone();
    let mut b_crib = crib.clone();
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
        CALIBRATION_CELL_UPPER_NS,
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
        CALIBRATION_CELL_UPPER_NS,
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
    let max_calibration_cell_ns = plain_cell_ns
        .iter()
        .chain(&capture_cell_ns)
        .copied()
        .max()
        .unwrap_or(0);
    let postwork_started = Instant::now();
    let _ = epoch_statistics(&crossing, &capture_views)?;
    let exact_statistics_postwork = postwork_started.elapsed();
    println!(
        "step0_calibration cells_per_control=64 no_capture_elapsed_ms={} with_actual_capture_elapsed_ms={} captured_samples={captured_samples} plain_samples=0 max_measured_cell_ns={max_calibration_cell_ns} exact_statistics_computed=true physical_state_equal=true crib_equal=true exact_statistics_postwork_ms={}",
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
    let branch_unit_ns = options
        .diagnostic_unit_upper_ns
        .unwrap_or(CALIBRATION_CELL_UPPER_NS)
        .max(CALIBRATION_CELL_UPPER_NS)
        .max(max_calibration_cell_ns);
    let branch_projection_ns = branch_unit_ns
        .checked_mul(231)
        .ok_or("branch wall projection overflow")?;
    let elapsed_ns = run_started.elapsed().as_nanos();
    let remaining_ns = FIXED_RUN_WALL_CAP_NS.saturating_sub(elapsed_ns);
    println!(
        "step0_projection branch_unit_upper_ns={branch_unit_ns} parallel_wall_projection_ns={branch_projection_ns} projected_three_branch_cpu_ns={} remaining_fixed_300s_ns={remaining_ns}",
        branch_unit_ns.saturating_mul(693)
    );
    if !projection_fits(branch_projection_ns, remaining_ns) {
        return Err("calibrated three-branch projection exceeds the 180-second branch cap or remaining fixed 300-second run budget; aborting before fork".into());
    }
    let checkpoint_path =
        checkpoint_path.ok_or("full diagnostic requires checkpoint destination")?;
    println!(
        "step0_protocol_exact_cells=1133 (312 trunk + 64 plain calibration + 64 actual-capture calibration + 3*231 fork cells); workers=3"
    );
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
    let first = base_classes[0];
    let alternative = first ^ 8;
    let source_ring = *b.field().sources().first().ok_or("source ring missing")?;
    let fit_ring = b
        .field()
        .rings()
        .get(source_ring)
        .ok_or("declared source ring missing")?;
    let fit_all = (0..b.field().alphabet()).all(|class| fit_ring.fits(fit_ring.port(class)));
    if !fit_all
        || !fit_ring.fits(fit_ring.port(alternative))
        || !fit_ring.fits(fit_ring.port(first))
    {
        return Err("step0 A/B source classes require the declared XOR-8 intervention and every class fitting the source ring".into());
    }
    let mut changed_classes = base_classes.clone();
    changed_classes[0] = alternative;
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
        "step0_source_advance source_ring={source_ring} ring_advance={:?} A_fit_pattern={} B_fit_pattern={} source_clock_is_distinct_from_receiver_clock=true",
        fit_ring.advance(),
        source_fit_pattern(&base_classes),
        source_fit_pattern(&changed_classes)
    );
    let clock_phases = clock_snapshot(&resident)?;
    let contacts = resident
        .field()
        .contacts()
        .iter()
        .enumerate()
        .map(|(index, contact)| {
            Ok((
                index,
                contact.ends(),
                contact.admittance().clone(),
                holonics::hnn::propagation::contact_exponent(
                    resident.field(),
                    index,
                    resident.current().lift(),
                )?,
            ))
        })
        .collect::<std::result::Result<Vec<_>, HnnError>>()?;
    println!(
        "step0_crossing source_cells={source_count} next_epoch_cells=231 target_cells={} checkpoint={checkpoint_path:?} crossing_W={:?} crossing_H={:?} L_R={} L_W={} L_nu={} clock_phases={clock_phases:?} pump_present={} rho=1",
        target.len(),
        crossing.map,
        crossing.gram,
        resident.constitution().grain(),
        resident
            .field()
            .lattice(Locus::ReceivingMap(2))
            .ok_or("receiver map lattice missing")?
            .exponent(),
        PopulationChart::of(resident.field()).exponent(),
        resident.constitution().resonator(2).is_some()
    );
    let path_contacts: Vec<_> = contacts
        .iter()
        .filter(|(_, ends, _, _)| *ends == (0, 1) || *ends == (1, 2))
        .collect();
    let path_product = if path_contacts.len() == 2 {
        let conductances = path_contacts
            .iter()
            .map(|(_, _, admittance, reading)| {
                Ok(holonics::ratio::exponentiated::power_of_two(&reading.carry)? * admittance)
            })
            .collect::<std::result::Result<Vec<Rat>, HnnError>>()?;
        Some(conductances.into_iter().product::<Rat>())
    } else {
        None
    };
    println!(
        "step0_contact_metadata contacts={contacts:?} effective_0_1_1_2_product={path_product:?} causal_receiver_gain_claim=none; path product alone is not an end-to-end input-to-face bound"
    );
    let branch_abort = AtomicBool::new(false);
    let (a_result, a0_result, b_result) = std::thread::scope(|scope| {
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
                    branch_unit_ns,
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
                    branch_unit_ns,
                    &branch_abort,
                )
            })
        });
        let b_worker = scope.spawn(|| {
            guarded_worker(&branch_abort, || {
                observe_branch(
                    port,
                    &mut b,
                    &mut b_crib,
                    &pairing,
                    &changed_classes,
                    "B",
                    &crossing.map,
                    branch_unit_ns,
                    &branch_abort,
                )
            })
        });
        let a_result = a_worker
            .join()
            .unwrap_or_else(|_| Err("A branch worker panicked".to_owned()));
        let a0_result = a0_worker
            .join()
            .unwrap_or_else(|_| Err("A0 branch worker panicked".to_owned()));
        let b_result = b_worker
            .join()
            .unwrap_or_else(|_| Err("B branch worker panicked".to_owned()));
        (a_result, a0_result, b_result)
    });
    let (a_views, a_faces, a_lifts, _a_times) = from_worker(a_result)?;
    let (_a0_faces, _a0_lifts, _a0_times) = from_worker(a0_result)?;
    let (b_views, b_faces, b_lifts, _b_times) = from_worker(b_result)?;
    let a_end = cut_view(a.constitution(), &[])?;
    let b_end = cut_view(b.constitution(), &[])?;
    println!(
        "step0_clock_registers crossing={clock_phases:?} A_end={:?} A0_end={:?} B_end={:?} feature_content_clock_split=not_declared_in_actual_feature_basis",
        clock_snapshot(&a)?,
        clock_snapshot(&a0)?,
        clock_snapshot(&b)?
    );
    report_epoch(&crossing, &a_end, &a_views)?;
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
    let (g_b, _) = epoch_statistics(&crossing, &b_views)?;
    let (max_f_delta, first_f_delta, max_logit_delta, first_logit_delta) =
        causal_differences(&a_views, &a_faces, &b_views, &b_faces)?;
    println!(
        "step0_intervention fit_all={fit_all} first_class={first} changed_class={alternative} G_A={g_a:?} G_B={g_b:?} W_table_delta_A={:?} W_table_delta_B={:?}",
        matrix_delta(&a_end.map, &crossing.map)?,
        matrix_delta(&b_end.map, &crossing.map)?
    );
    println!(
        "step0_causal_AB max_abs_delta_f={max_f_delta} first_differing_feature_index={first_f_delta:?} max_abs_delta_logits={max_logit_delta} first_differing_logit_index={first_logit_delta:?} coordinates=(cell,sample_or_station,feature_or_class); clock_content_split=not_inferred"
    );
    let later_same_face_different_lift =
        (1..231).find(|&i| a_faces[i] == b_faces[i] && a_lifts[i] != b_lifts[i]);
    println!(
        "step0_reachable_pair index={later_same_face_different_lift:?} criterion=equal_present_faces_and_different_current_lift; this is not a slip-equivalence claim"
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
    fn n_u_and_projection_guards_are_exact_and_bounded() {
        assert!(within_n_u(7, 2, 4));
        assert!(!within_n_u(9, 2, 4));
        assert!(!within_n_u(u128::MAX, 2, u128::MAX));
        assert!(projection_fits(BRANCH_WALL_CAP_NS, FIXED_RUN_WALL_CAP_NS));
        assert!(!projection_fits(
            BRANCH_WALL_CAP_NS + 1,
            FIXED_RUN_WALL_CAP_NS
        ));
        assert!(!projection_fits(1, 0));
    }
}
