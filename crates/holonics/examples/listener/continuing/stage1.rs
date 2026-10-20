//! Production exterior for one finite selected life. Section and pass boundaries are report
//! cuts only. Mid-epoch release forks come from native prefix snapshots at the opening medium.

use super::*;
use std::ops::Range;

#[derive(Debug, PartialEq, Eq)]
struct Span {
    range: Range<usize>,
    section: usize,
    chart: sections::ChartKind,
    pass: usize,
    role: &'static str,
}

#[derive(Debug, PartialEq, Eq)]
struct ReleaseCut {
    at: usize,
    section: usize,
    maximum: usize,
}

fn append_span(
    classes: &mut Vec<usize>,
    spans: &mut Vec<Span>,
    cells: Vec<usize>,
    section: usize,
    chart: sections::ChartKind,
    pass: usize,
    role: &'static str,
) {
    if cells.is_empty() {
        return;
    }
    let start = classes.len();
    classes.extend(cells);
    spans.push(Span {
        range: start..classes.len(),
        section,
        chart,
        pass,
        role,
    });
}

/// Only the training prefix contributes answer cells or target-derived release scale.
#[derive(Debug, PartialEq, Eq)]
struct LifePlan {
    classes: Vec<usize>,
    spans: Vec<Span>,
    cuts: Vec<ReleaseCut>,
    pass_ends: Vec<(usize, usize)>,
}

pub(super) fn validate_evaluation_extent(
    sections: usize,
    evaluation_from_section: Option<usize>,
) -> Result<()> {
    if evaluation_from_section.is_some_and(|first| first == 0 || first >= sections) {
        return Err("evaluation suffix needs nonempty training and evaluation sections".into());
    }
    Ok(())
}

fn life_plan(
    frames: &[Section],
    sections_per_pass: Option<usize>,
    evaluation_from_section: Option<usize>,
) -> Result<LifePlan> {
    validate_evaluation_extent(frames.len(), evaluation_from_section)?;
    let mut classes = Vec::new();
    let mut spans = Vec::new();
    let mut cuts = Vec::new();
    let mut pass_ends = Vec::new();
    let mut longest = ReleaseHistory::default();
    for (section, frame) in frames.iter().enumerate() {
        let evaluation = evaluation_from_section.is_some_and(|first| section >= first);
        let chart = frame.chart_kind()?;
        let pass = sections_per_pass.map_or(0, |count| section / count);
        append_span(
            &mut classes,
            &mut spans,
            frame.source_cells(section)?,
            section,
            chart,
            pass,
            if evaluation {
                "evaluation_source"
            } else {
                "source"
            },
        );
        cuts.push(ReleaseCut {
            at: classes.len(),
            section,
            maximum: longest.maximum(chart),
        });
        if !evaluation {
            let target = frame.target_cells(section)?;
            longest.heard_target(chart, target.len());
            append_span(
                &mut classes,
                &mut spans,
                target,
                section,
                chart,
                pass,
                "answer",
            );
        }
        if sections_per_pass.is_some_and(|count| (section + 1) % count == 0) {
            pass_ends.push((classes.len(), pass));
        }
    }
    if sections_per_pass.is_none() && !frames.is_empty() {
        pass_ends.push((classes.len(), 0));
    }
    Ok(LifePlan {
        classes,
        spans,
        cuts,
        pass_ends,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run(
    port: &Reference,
    execution: Option<&dyn ObservedEpochExecution>,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    frames: &[Section],
    options: &ContinuingOptions,
    keys: &mut KeyStream,
    emit: &mut dyn FnMut(String),
) -> Result<()> {
    let mut work =
        work::ObservedWork::new(options.work_deadline_ns, options.block_upper_ns_per_cell)?;
    let mut codes = work::CodeBook::default();
    let result = run_inner(
        port, execution, resident, crib, pairing, frames, options, keys, &mut work, &mut codes,
        emit,
    );
    // Every exit reports the unfinished code partition and fixed stop, including refused tails.
    codes.report_pending(emit);
    work.finish(emit);
    result
}

#[allow(clippy::too_many_arguments)]
fn run_inner(
    port: &Reference,
    execution: Option<&dyn ObservedEpochExecution>,
    resident: &mut Resident,
    crib: &mut ObservedCrib,
    pairing: &PairingDeclaration,
    frames: &[Section],
    options: &ContinuingOptions,
    keys: &mut KeyStream,
    work: &mut work::ObservedWork,
    codes: &mut work::CodeBook,
    emit: &mut dyn FnMut(String),
) -> Result<()> {
    work.check()?;
    let LifePlan {
        mut classes,
        spans,
        mut cuts,
        mut pass_ends,
    } = life_plan(
        frames,
        options.sections_per_pass,
        options.evaluation_from_section,
    )?;
    for (section, frame) in frames.iter().enumerate() {
        for passage in &frame.passages {
            emit(format!(
                "observed_chart section={section} {}",
                passage.encode_chart()?.summary()
            ));
        }
    }
    if let Some(first) = options.evaluation_from_section {
        emit(format!(
            "observed_evaluation first_section={first} sections={} targets_heard=false release_scale=training_targets_only source_heard=true fresh_life=true",
            frames.len() - first
        ));
    }
    let declared_cells = classes.len();
    if let Some(limit) = options.stage1_probe_cells {
        if limit > classes.len() {
            return Err("stage1 probe prefix exceeds the selected framed life".into());
        }
        classes.truncate(limit);
    }
    cuts.retain(|cut| cut.at <= classes.len());
    pass_ends.retain(|(at, _)| *at <= classes.len());
    emit(format!(
        "observed_stage1 mode={} selected_sections={} declared_heard_cells={declared_cells} selected_heard_cells={} section_ends_publish=false terminal_partial_policy=declared_finite_life_sealed_no_resume legacy_diagnostic=false",
        if options.stage1_probe_cells.is_some() {
            "bounded_probe"
        } else {
            "finite_life"
        },
        frames.len(),
        classes.len()
    ));
    let mut at = 0usize;
    let mut span_index = 0usize;
    let mut cut_index = 0usize;
    let mut mutual_book = mutual::Book::default();
    let mut pass_index = 0usize;
    let mut batch = 0usize;
    let mut published = 0usize;
    // The mounted ordinary Lock chain drives source 0 by one cell. The product of
    // periods below the sole receiving ring bounds its next ingress; rekeys can shorten it.
    let receiver = resident
        .admitted()
        .first()
        .ok_or("stage1 life has no receiver")?
        .ring();
    let maximum_batch_cells = resident.field().rings()[..receiver].iter().try_fold(
        1usize,
        |bound, ring| -> Result<usize> {
            bound
                .checked_mul(usize::try_from(ring.period())?)
                .ok_or_else(|| "ordinary receiver interval overflows host extent".into())
        },
    )?;
    while at < classes.len() {
        work.check()?;
        let started = Instant::now();
        let opening_operands = work::operands(resident)?;
        let submitted_end = at
            .checked_add(maximum_batch_cells)
            .ok_or("observed batch extent overflow")?
            .min(classes.len());
        let relative_cuts: Vec<_> = cuts[cut_index..]
            .iter()
            .take_while(|cut| cut.at <= submitted_end)
            .map(|cut| cut.at - at)
            .collect();
        // `terminal` names the end of this selected finite life, not this section or pass.
        // The native owner consumes only through its next actual receiver crossing when one
        // exists, and marks/seals a terminal partial separately if it reaches the selected end.
        let native = match execution {
            Some(execution) => port.observe_epoch_continuing_at_cuts_with_execution(
                resident,
                crib,
                pairing,
                &classes[at..submitted_end],
                None,
                &relative_cuts,
                submitted_end == classes.len(),
                execution,
            ),
            None => port.observe_epoch_continuing_at_cuts(
                resident,
                crib,
                pairing,
                &classes[at..submitted_end],
                None,
                &relative_cuts,
                submitted_end == classes.len(),
            ),
        }?;
        let native_ns = elapsed(started);
        if native.consumed == 0
            || native.consumed > submitted_end - at
            || native.reads.len() != native.consumed
            || native.cells != u64::try_from(at + native.consumed)?
            || (native.terminal_partial && at + native.consumed != classes.len())
        {
            return Err(
                "stage1 native receipt extent differs from its submitted heard prefix".into(),
            );
        }
        published = published
            .checked_add(usize::from(native.precision.event.is_some()))
            .ok_or("observed precision publication count overflow")?;
        for (offset, read) in native.reads.iter().enumerate() {
            let absolute = at + offset;
            while spans[span_index].range.end <= absolute {
                span_index += 1;
            }
            let span = &spans[span_index];
            let class = classes[absolute];
            let wave = read
                .prediction
                .faces
                .first()
                .ok_or("stage1 blind prediction has no wave face")?
                .code_length(class)?;
            let released_nonzero = read
                .released
                .iter()
                .filter(|value| !value.is_zero())
                .count();
            codes.add(span.pass, span.chart, &read.code, read.tree.as_ref(), &wave);
            emit(format!(
                "cell stage1=true batch={batch} section={} pass={} chart={} role={} class={class} delivered={} material_commit={} partition_exponent={} released_terms={} released_nonzero={released_nonzero} code_exact=[{},{}] tree_exact={} wave_exact=[{},{}] word_charts=[{}] operands={opening_operands}",
                span.section,
                span.pass,
                span.chart.byte(),
                span.role,
                absolute + 1,
                native.comparison_commit,
                native.partition_exponent,
                read.released.len(),
                read.code.lower,
                read.code.upper,
                read.tree.as_ref().map_or_else(
                    || "unavailable".to_owned(),
                    |tree| format!("[{},{}]", tree.lower, tree.upper)
                ),
                wave.lower,
                wave.upper,
                work::word_charts(&read.word_charts)
            ));
        }
        emit(format!(
            "observed_epoch batch={batch} heard_cells={} consumed={} comparison_commit={} partition_exponent={} closed_section={} terminal_partial={} carry_out={} native_and_opening_report_ns={native_ns} deposit_commit={} deposit_bits={} released_bits={} landmarks={} charts={} published_events_total={published}",
            native.cells,
            native.consumed,
            native.comparison_commit,
            native.partition_exponent,
            native.closed_section,
            native.terminal_partial,
            native.carry_out,
            native.deposit.commit,
            native.deposit.bits,
            native.deposit.released_bits,
            native.deposit.landmarks,
            work::charts(&native.deposit)
        ));
        emit(format!(
            "observed_epoch_wall batch={batch} forward_batch_ns={} compare_return_compose_batch_ns={} grouped_deposit_ns={} final_arrived_reread_ns={} precision_close_ns={} prefix_forks_ns={} worker_walls_summed=false",
            native.wall.forward_batch.as_nanos(),
            native.wall.compare_return_compose_batch.as_nanos(),
            native.wall.grouped_deposit.as_nanos(),
            native.wall.final_arrived_reread.as_nanos(),
            native.wall.precision_close.as_nanos(),
            native.wall.prefix_forks.as_nanos()
        ));
        emit(format!(
            "observed_compare_wall batch={batch} preparation_ns={} joined_return_ns={} ordered_publication_ns={} prefix_forks_excluded=true",
            native.wall.compare_preparation.as_nanos(),
            native.wall.return_join.as_nanos(),
            native.wall.ordered_publication.as_nanos()
        ));
        for (phase, elapsed) in [
            "face_partition",
            "pull_back",
            "compose",
            "receiving_records",
        ]
        .iter()
        .zip(&native.wall.return_worker_sums)
        {
            emit(format!(
                "observed_return_worker_sum batch={batch} phase={phase} elapsed_ns={} critical_path=false",
                elapsed.as_nanos()
            ));
        }
        for (phase, elapsed) in &native.wall.deposit_subphases {
            emit(format!(
                "observed_deposit_wall batch={batch} phase={phase} elapsed_ns={} disjoint_intervals=true",
                elapsed.as_nanos()
            ));
        }
        work::epoch(batch, &native.deposit, emit);
        emit(format!(
            "observed_operands batch={batch} cut=committed_end {}",
            work::operands(resident)?
        ));
        if let Some(line) = native
            .close
            .as_ref()
            .and_then(|close| keys_line(spans[span_index].section, "trunk", close))
        {
            emit(line);
        }
        // The whole receiver operation is atomic to this exterior guard. The receipt states
        // any excess over the eight-cell measurement threshold before another draw or epoch.
        work.complete(native.consumed, elapsed(started), emit)?;
        let consumed = native.consumed;
        for (prefix, fork, fork_crib) in native.prefixes {
            let cut = cuts
                .get(cut_index)
                .ok_or("native returned an unrequested prefix fork")?;
            if prefix == 0 || prefix > consumed || cut.at != at + prefix {
                return Err("native prefix fork differs from its exterior source-end cut".into());
            }
            let anchor_started = Instant::now();
            // Snapshot only the actual admitted draw site. No answer, target length,
            // target fibre or learned injection enters the fixed count transport.
            let anchor = if cut.maximum == 0 || fork.admitted().is_empty() {
                None
            } else {
                let boundary = holonics::hnn::encoding::observed::PairedObservation::admit(
                    fork.field(),
                    fork.constitution(),
                    pairing,
                )?;
                Some(mutual::Anchor::new(
                    fork.field(),
                    fork.current(),
                    &boundary,
                )?)
            };
            let mut solenoidal = options
                .diagnostic_solenoidal_lock
                .then(|| solenoidal::Trace::new(fork.field(), fork.current()));
            work.complete(0, elapsed(anchor_started), emit)?;
            let mut face_decisions = Vec::new();
            let released = release_fork_accounted(
                port,
                fork,
                fork_crib,
                pairing,
                cut.maximum,
                keys,
                cut.section,
                Some(work),
                false,
                options
                    .diagnostic_release_faces
                    .then_some(&mut face_decisions),
                solenoidal.as_mut(),
                emit,
            )?;
            let report_started = Instant::now();
            emit(released.line(cut.section));
            if options.diagnostic_release_faces {
                face_readings::report(
                    cut.section,
                    cut.at,
                    &frames[cut.section].target_cells(cut.section)?,
                    &released,
                    &face_decisions,
                    native.reads.get(prefix..).unwrap_or(&[]),
                    options
                        .evaluation_from_section
                        .is_none_or(|first| cut.section < first),
                    (at, at + native.consumed, native.comparison_commit),
                    emit,
                )?;
            }
            let reading = mutual::compare(
                anchor.as_ref(),
                &released.classes,
                &frames[cut.section].target_cells(cut.section)?,
            )?;
            emit(reading.line(cut.section));
            if let Some(trace) = solenoidal {
                // Exterior acceptance only: target cells become available after all draws.
                trace.report(
                    cut.section,
                    &released.classes,
                    &frames[cut.section].target_cells(cut.section)?,
                    emit,
                );
            }
            if options
                .evaluation_from_section
                .is_none_or(|first| cut.section < first)
            {
                let count = options.sections_per_pass.unwrap_or(frames.len());
                mutual_book.record(
                    frames[cut.section].chart_kind()?,
                    cut.section % count,
                    cut.section / count,
                    reading,
                )?;
            }
            work.complete(0, elapsed(report_started), emit)?;
            cut_index += 1;
        }
        at = at
            .checked_add(consumed)
            .ok_or("observed heard-cell cursor overflow")?;
        if cuts.get(cut_index).is_some_and(|cut| cut.at <= at) {
            return Err("native omitted a requested source-end prefix fork".into());
        }
        while pass_ends.get(pass_index).is_some_and(|(end, _)| *end <= at) {
            let report_started = Instant::now();
            codes.report_pass(pass_ends[pass_index].1, true, emit);
            work.complete(0, elapsed(report_started), emit)?;
            pass_index += 1;
        }
        batch = batch
            .checked_add(1)
            .ok_or("observed receiver batch count overflow")?;
        work.check()?;
    }
    let report_started = Instant::now();
    let training_sections = options.evaluation_from_section.unwrap_or(frames.len());
    if training_sections != 0 {
        let count = options.sections_per_pass.unwrap_or(training_sections);
        for totals in mutual_book.totals(training_sections.div_ceil(count))? {
            emit(format!(
                "observed_mutual_totals chart={} eligible_items={:?} locks_by_pass={:?} fixed_count_kernel=true evaluation_suffix_excluded=true",
                totals.chart.byte(),
                totals.eligible_items,
                totals.locks_by_pass
            ));
        }
    }
    work.complete(0, elapsed(report_started), emit)?;
    emit(format!(
        "observed_selected_life completed=true heard_cells={at} receiver_batches={batch} released_source_cuts={cut_index} keys_read={} published_events_total={published}",
        keys.keys_read()
    ));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frames() -> Vec<Section> {
        [
            (&b"train"[..], &b"0"[..]),
            (b"held-a", b"4"),
            (b"held-b", b"5"),
        ]
        .into_iter()
        .map(|(source, target)| Section {
            passages: vec![sections::Passage::Octets(source.to_vec())],
            target: target.to_vec(),
        })
        .collect()
    }

    #[test]
    fn evaluation_targets_cannot_change_heard_cells_cuts_or_release_scale() {
        let original = frames();
        let before = life_plan(&original, Some(1), Some(1)).unwrap();
        let mut altered = original.clone();
        altered[1].target = b"a much longer changed held-out answer".to_vec();
        altered[2].target.clear();
        assert_eq!(before, life_plan(&altered, Some(1), Some(1)).unwrap());
        assert_eq!(
            before
                .cuts
                .iter()
                .map(|cut| cut.maximum)
                .collect::<Vec<_>>(),
            vec![0, 4, 4]
        );
        assert_eq!(
            before
                .spans
                .iter()
                .filter(|span| span.role == "answer")
                .count(),
            1
        );
        assert_eq!(
            before
                .spans
                .iter()
                .filter(|span| span.role == "evaluation_source")
                .count(),
            2
        );
        let mut expected = original[0].source_cells(0).unwrap();
        expected.extend(original[0].target_cells(0).unwrap());
        expected.extend(original[1].source_cells(1).unwrap());
        expected.extend(original[2].source_cells(2).unwrap());
        assert_eq!(before.classes, expected);
        altered[1].passages = vec![sections::Passage::Octets(b"different source".to_vec())];
        assert_ne!(
            before.classes,
            life_plan(&altered, Some(1), Some(1)).unwrap().classes
        );
    }

    #[test]
    fn ordinary_plan_still_hears_every_source_and_answer() {
        let frames = frames();
        let plan = life_plan(&frames, Some(1), None).unwrap();
        let mut expected = Vec::new();
        for (index, frame) in frames.iter().enumerate() {
            expected.extend(frame.source_cells(index).unwrap());
            assert_eq!(plan.cuts[index].at, expected.len());
            expected.extend(frame.target_cells(index).unwrap());
            assert_eq!(plan.pass_ends[index], (expected.len(), index));
        }
        assert_eq!(plan.classes, expected);
        assert!(
            plan.spans
                .iter()
                .all(|span| span.role != "evaluation_source")
        );
    }

    #[test]
    fn evaluation_requires_nonempty_training_and_test_extents() {
        for extent in [0, 3, 4] {
            assert!(life_plan(&frames(), None, Some(extent)).is_err());
        }
        assert!(life_plan(&frames(), None, Some(1)).is_ok());
    }
}
