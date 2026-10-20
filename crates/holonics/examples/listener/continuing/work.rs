//! Exterior accounting for the ordinary observed path and its bounded development probe.
//! No reporting choice changes the native deposition law.

use super::*;
use crate::octets::CodeSum;
use holonics::hnn::constitution::NormalLaw;
use holonics::ratio::algebraic::ExactInterval;
use std::collections::BTreeMap;

const MEASUREMENT_BLOCK_CELLS: usize = 8;

pub(super) struct ObservedWork {
    cutoff: Option<diagnostic::WorkCutoff>,
    upper_ns_per_cell: Option<u128>,
    block_cells: usize,
    block_ns: u128,
    blocks: usize,
    stopped: bool,
}

impl ObservedWork {
    pub(super) fn new(deadline_ns: Option<u128>, upper_ns_per_cell: Option<u128>) -> Result<Self> {
        Ok(Self {
            cutoff: deadline_ns
                .map(|deadline| {
                    diagnostic::WorkCutoff::at_deadline("observed native/exterior work", deadline)
                })
                .transpose()?,
            upper_ns_per_cell,
            block_cells: 0,
            block_ns: 0,
            blocks: 0,
            stopped: false,
        })
    }

    pub(super) fn check(&mut self) -> Result<()> {
        if self.stopped {
            return Err("observed work already stopped; no later epoch or draw may start".into());
        }
        if let Some(cutoff) = &self.cutoff {
            if let Err(error) = cutoff.check() {
                self.stopped = true;
                return Err(error.into());
            }
        }
        Ok(())
    }

    /// A physical receiver epoch is atomic to the exterior stop. The block contains at least
    /// eight completed heard/drawn cells; an epoch may overshoot that threshold. Never split its
    /// duration into invented per-cell timings or call a program block a receiver epoch.
    pub(super) fn complete(
        &mut self,
        cells: usize,
        elapsed_ns: u128,
        emit: &mut dyn FnMut(String),
    ) -> Result<()> {
        self.block_cells = self
            .block_cells
            .checked_add(cells)
            .ok_or("observed block cell count overflow")?;
        self.block_ns = self
            .block_ns
            .checked_add(elapsed_ns)
            .ok_or("observed block time overflow")?;
        if self.block_cells >= MEASUREMENT_BLOCK_CELLS {
            self.blocks = self
                .blocks
                .checked_add(1)
                .ok_or("observed block count overflow")?;
            let limit = self
                .upper_ns_per_cell
                .map(|upper| {
                    upper
                        .checked_mul(self.block_cells as u128)
                        .ok_or("observed block ceiling overflow")
                })
                .transpose()?;
            let over = limit.is_some_and(|limit| self.block_ns > limit);
            emit(format!(
                "observed_block index={} completed_cells={} elapsed_ns={} minimum_cells={MEASUREMENT_BLOCK_CELLS} atomic_epoch_overshoot_cells={} upper_ns_per_cell={} over_bound={over}",
                self.blocks - 1,
                self.block_cells,
                self.block_ns,
                self.block_cells - MEASUREMENT_BLOCK_CELLS,
                self.upper_ns_per_cell
                    .map_or_else(|| "unmeasured".to_owned(), |value| value.to_string()),
            ));
            self.block_cells = 0;
            self.block_ns = 0;
            if over {
                self.stopped = true;
                return Err("observed completed block exceeded its fixed measured upper rate; later work refused".into());
            }
        }
        self.check()
    }

    pub(super) fn finish(&self, emit: &mut dyn FnMut(String)) {
        emit(format!(
            "observed_work completed_blocks={} partial_cells={} partial_elapsed_ns={} stopped={} partial_block_has_no_rate_admission=true",
            self.blocks, self.block_cells, self.block_ns, self.stopped
        ));
    }
}

#[derive(Default)]
pub(super) struct CodeBook {
    sums: BTreeMap<(usize, sections::ChartKind), [CodeSum; 3]>,
}

impl CodeBook {
    pub(super) fn add(
        &mut self,
        pass: usize,
        chart: sections::ChartKind,
        combined: &ExactInterval,
        tree: Option<&ExactInterval>,
        wave: &ExactInterval,
    ) {
        let sums = self.sums.entry((pass, chart)).or_default();
        sums[0].add(combined);
        if let Some(tree) = tree {
            sums[1].add(tree);
        }
        sums[2].add(wave);
    }

    pub(super) fn report_pass(
        &mut self,
        pass: usize,
        complete: bool,
        emit: &mut dyn FnMut(String),
    ) {
        let mut total: [CodeSum; 3] = Default::default();
        for chart in [
            sections::ChartKind::Octets,
            sections::ChartKind::Raster,
            sections::ChartKind::Pcm,
        ] {
            if let Some(sums) = self.sums.remove(&(pass, chart)) {
                emit(format!(
                    "observed_code pass={pass} chart={} complete={complete} combined_cells={} combined_exact={} tree_cells={} tree_exact={} wave_cells={} wave_exact={}",
                    chart.byte(),
                    sums[0].cells(),
                    sums[0].exact_endpoints(),
                    sums[1].cells(),
                    sums[1].exact_endpoints(),
                    sums[2].cells(),
                    sums[2].exact_endpoints()
                ));
                for (sum, chart_sum) in total.iter_mut().zip(&sums) {
                    sum.merge(chart_sum);
                }
            }
        }
        emit(format!(
            "observed_pass pass={pass} complete={complete} combined_cells={} combined_exact={} tree_cells={} tree_exact={} wave_cells={} wave_exact={}",
            total[0].cells(),
            total[0].exact_endpoints(),
            total[1].cells(),
            total[1].exact_endpoints(),
            total[2].cells(),
            total[2].exact_endpoints()
        ));
    }

    pub(super) fn report_pending(&mut self, emit: &mut dyn FnMut(String)) {
        let passes: std::collections::BTreeSet<_> =
            self.sums.keys().map(|(pass, _)| *pass).collect();
        for pass in passes {
            self.report_pass(pass, false, emit);
        }
    }
}

fn locus_name(locus: Locus) -> String {
    let (name, index) = match locus {
        Locus::Element(index) => ("element", index),
        Locus::Junction(index) => ("junction", index),
        Locus::Channel(index) => ("channel", index),
        Locus::Conductance(index) => ("conductance", index),
        Locus::SourcePort(index) => ("source", index),
        Locus::Standing(index) => ("standing", index),
        Locus::Resonator(index) => ("resonator", index),
        Locus::ReceivingMap(index) => ("receiving", index),
    };
    format!("{name}:{index}")
}

pub(super) fn charts(reading: &DepositReading) -> String {
    reading.charts.iter().map(|(locus, chart)| format!("{}:exponent={},target={},warm={},certificate={},refinements={},cold={},released={},read={},residual_bits={},prior={},radial={},receiving_block={}", locus_name(*locus), chart.exponent, chart.target, chart.warm.as_ref().map_or_else(|| "none".to_owned(), ToString::to_string), chart.certificate, chart.refinements, chart.cold, chart.released, chart.read, chart.residual_bits, chart.prior.is_some(), chart.radial.is_some(), chart.receiving_block.is_some())).collect::<Vec<_>>().join(";")
}

pub(super) fn word_charts(readings: &[holonics::hnn::chart::ChartReading]) -> String {
    readings
        .iter()
        .map(|chart| {
            let operator = chart.operator.as_ref().map_or_else(
                || "unavailable".to_owned(),
                |operator| {
                    format!(
                        "D_bits={},S_bits={},entry_bits={},wide={:?}",
                        operator.denominator_bits,
                        operator.scale_bits,
                        operator.entry_bits,
                        operator.wide_reasons
                    )
                },
            );
            format!(
                "{:?}:width={},start={:?},steps={},certificate={},target={},operator=[{}]",
                chart.key,
                chart.width,
                chart.start,
                chart.steps,
                chart.certificate,
                chart.target,
                operator
            )
        })
        .collect::<Vec<_>>()
        .join(";")
}

fn epoch_array(reading: &holonics::hnn::constitution::EpochArrayReading) -> String {
    format!(
        "{}x{}:exponent={},max_bits={},limbs={},row_odd_divisors={},l1={}",
        reading.rows,
        reading.columns,
        reading.exponent,
        reading.maximum_integer_bits,
        reading.magnitude_limbs,
        packed(&reading.row_odd_divisors),
        reading.numerator_l1_bound
    )
}

/// Once per crossing. Exact receiving series use sparse row-major indices; omitted entries are
/// zero. These are readings of the owner's arrays, with no reconstructed solve or census.
pub(super) fn epoch(batch: usize, reading: &DepositReading, emit: &mut dyn FnMut(String)) {
    let Some(epoch) = &reading.epoch else {
        return;
    };
    emit(format!(
        "observed_epoch_partition batch={batch} actual_receiving_ingress={} heard_cells={} declared_cells={} receiver_partition_bits={} partition_exponent={}",
        epoch.actual_receiving_ingress,
        epoch.heard_cells,
        epoch.declared_cells,
        epoch.receiver_partition_bits,
        epoch.partition_exponent
    ));
    for locus in &epoch.loci {
        emit(format!(
            "observed_epoch_locus batch={batch} locus={} records={} fresh_covector_scale={} fresh_alignment={} odometer_alignment_defect={} partition_alignment_extra={} certificate_alignment={} certificate_moves={} certificate_covector_scale={} gamma={} eta={} fall={} shares={} gram_update=[{}] fresh_news=[{}] direction=[{}] represented_step=[{}] retained_map=[{}] retained_gram=[{}] retained_news=[{}] crossings={} gram_departed_prior_rows={} spectral_gram_bound={} spectral_move_bound={}",
            locus_name(locus.locus.locus()),
            locus.records,
            locus.fresh_covector_scale,
            locus.fresh_alignment,
            locus.odometer_alignment_defect,
            locus.partition_alignment_extra,
            locus.certificate_alignment,
            locus.certificate_moves,
            locus.certificate_covector_scale,
            locus.gamma,
            locus.eta,
            locus.fall,
            packed(&locus.shares),
            epoch_array(&locus.gram_update),
            epoch_array(&locus.fresh_news),
            epoch_array(&locus.direction),
            epoch_array(&locus.represented_step),
            epoch_array(&locus.storage.map),
            epoch_array(&locus.storage.gram),
            epoch_array(&locus.storage.news),
            locus.storage.crossings,
            locus.storage.gram_departed_prior_rows,
            locus.storage.spectral_gram_bound,
            locus.storage.spectral_move_bound
        ));
    }
    for (name, series) in [
        ("positive", &epoch.receiving.positive),
        ("foil", &epoch.receiving.foil),
        ("phase", &epoch.receiving.phase),
    ] {
        let sparse = series
            .numerators
            .iter()
            .enumerate()
            .filter(|(_, value)| !value.is_zero())
            .map(|(at, value)| format!("{at}:{value}"))
            .collect::<Vec<_>>()
            .join(",");
        emit(format!(
            "observed_epoch_receiving batch={batch} series={name} rows={} columns={} exponent={} row_odd_divisors={} zero_implicit=true row_major_numerators=[{sparse}]",
            series.rows,
            series.columns,
            series.exponent,
            packed(&series.row_odd_divisors)
        ));
    }
}

fn normal_shape(locus: Locus, law: &NormalLaw) -> Result<String> {
    if let Some(storage) = law.epoch_storage() {
        return Ok(format!(
            "{}:gram_departed_prior_rows={},crossings={},map={}x{},gram={}x{},news={}x{},map_lattice={},map_exponent={},gram_exponent={},news_exponent={},map_max_integer_bits={},gram_max_integer_bits={},news_max_integer_bits={},map_limbs={},gram_limbs={},news_limbs={},news_row_odd_divisors={},spectral_gram_bound={},spectral_move_bound={}",
            locus_name(locus),
            storage.gram_departed_prior_rows,
            storage.crossings,
            storage.map.rows,
            storage.map.columns,
            storage.gram.rows,
            storage.gram.columns,
            storage.news.rows,
            storage.news.columns,
            storage.map_lattice,
            storage.map.exponent,
            storage.gram.exponent,
            storage.news.exponent,
            storage.map.maximum_integer_bits,
            storage.gram.maximum_integer_bits,
            storage.news.maximum_integer_bits,
            storage.map.magnitude_limbs,
            storage.gram.magnitude_limbs,
            storage.news.magnitude_limbs,
            packed(&storage.news.row_odd_divisors),
            storage.spectral_gram_bound,
            storage.spectral_move_bound,
        ));
    }
    let map = law.map();
    let mut numerator_bits = 0;
    let mut denominator_bits = 0;
    let mut nonzero = 0usize;
    for row in 0..map.rows() {
        for value in map.row(row)? {
            numerator_bits = numerator_bits.max(value.numer().bits());
            denominator_bits = denominator_bits.max(value.denom().bits());
            nonzero += usize::from(!value.is_zero());
        }
    }
    Ok(format!(
        "{}:stored_solved_chart_support={},map={}x{},gram={}x{},map_nonzero={nonzero},map_max_numerator_bits={numerator_bits},map_max_denominator_bits={denominator_bits},chart_exponent={},epoch_storage=false,gram_entry_bit_widths=unavailable",
        locus_name(locus),
        law.chart().support().len(),
        map.rows(),
        map.columns(),
        map.columns(),
        map.columns(),
        law.chart().exponent()
    ))
}

/// Once per material boundary, reused by every cell read on that same material. Gram shape is
/// declared by the normal map's input width; no dense inverse or Gram is materialized to report it.
pub(super) fn operands(resident: &Resident) -> Result<String> {
    let material = resident.constitution();
    let mut shapes = Vec::new();
    for ring in 0..resident.field().rings().len() {
        if let Some(law) = material.source_law(ring) {
            shapes.push(normal_shape(Locus::SourcePort(ring), law)?);
        }
        shapes.push(normal_shape(
            Locus::Standing(ring),
            material.contrast_law(ring),
        )?);
        if let Some(law) = material.receiving_law(ring) {
            shapes.push(normal_shape(Locus::ReceivingMap(ring), law)?);
        } else if let Some(blocks) = material.receiving_blocks(ring) {
            for (index, block) in blocks.iter().enumerate() {
                shapes.push(format!(
                    "block:{index}/{}",
                    normal_shape(Locus::ReceivingMap(ring), block.law())?
                ));
            }
        }
    }
    Ok(format!(
        "resident_bits={},constitution_bits={},normal_operands=[{}]",
        resident.state_bits(),
        material.exact_bits(),
        shapes.join(";")
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_rate_stop_keeps_atomic_epoch_overshoot_and_cannot_restart() {
        let mut work = ObservedWork::new(None, Some(10)).unwrap();
        let mut lines = Vec::new();
        work.complete(7, 70, &mut |line| lines.push(line)).unwrap();
        assert!(lines.is_empty());
        // One atomic receiver operation completes sixteen more cells. Its total is
        // judged at all 23 cells, not as a fabricated eight-cell timing.
        assert!(
            work.complete(16, 161, &mut |line| lines.push(line))
                .is_err()
        );
        assert!(lines[0].contains("completed_cells=23 elapsed_ns=231"));
        assert!(lines[0].contains("atomic_epoch_overshoot_cells=15"));
        assert!(work.check().is_err());
    }

    #[test]
    fn equality_at_measured_rate_admits_and_partial_block_has_no_rate_verdict() {
        let mut work = ObservedWork::new(None, Some(10)).unwrap();
        let mut lines = Vec::new();
        work.complete(8, 80, &mut |line| lines.push(line)).unwrap();
        work.complete(1, 1000, &mut |line| lines.push(line))
            .unwrap();
        work.finish(&mut |line| lines.push(line));
        assert!(lines[0].contains("over_bound=false"));
        assert!(lines[1].contains("partial_cells=1 partial_elapsed_ns=1000"));
        assert!(lines[1].contains("partial_block_has_no_rate_admission=true"));
    }

    #[test]
    fn code_reports_keep_fractional_endpoints_and_missing_tree_count() {
        let interval = |ln, ld, un, ud| {
            ExactInterval::new(
                Rat::new(BigInt::from(ln), BigInt::from(ld)),
                Rat::new(BigInt::from(un), BigInt::from(ud)),
            )
            .unwrap()
        };
        let first = interval(1, 3, 1, 2);
        let second = interval(2, 3, 3, 4);
        let mut codes = CodeBook::default();
        codes.add(0, sections::ChartKind::Octets, &first, Some(&first), &first);
        codes.add(0, sections::ChartKind::Octets, &second, None, &second);
        let mut lines = Vec::new();
        codes.report_pass(0, true, &mut |line| lines.push(line));
        assert!(
            lines
                .iter()
                .all(|line| line.contains("combined_cells=2 combined_exact=[1,5/4]"))
        );
        assert!(
            lines
                .iter()
                .all(|line| line.contains("tree_cells=1 tree_exact=[1/3,1/2]"))
        );
        assert!(codes.sums.is_empty());
    }
}
