//! **The exterior-telemetry join of Deed H0** — a site, not a library owner. It reads the `.tsv`
//! faces an exterior profiling receiver wrote beside the deed's own `.form` receipts and returns
//! the product-ordered surface-utility reading and one deterministic classification per
//! load-bearing kernel class and per boundary.
//!
//! Nothing here measures anything. Every number it prints was either returned by the passage (via
//! the `.form` files the same driver wrote on the card) or written into a `.tsv` by the exterior
//! apparatus. A column that is absent, blank or literally `unknown` stays `unknown`: it is never
//! read as zero and never inferred from a neighbour.
//!
//! The classification rubric is declared before the measurement and applied as code: the FIRST
//! class that applies in the rubric's order decides, the rest are listed as secondary. Where the
//! deciding metric is an `ncu`-only face and `ncu` could not run, the class is neither asserted
//! nor denied — it is returned `unknown` with the metric that would decide it named.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

pub const UNKNOWN: &str = "unknown";

/// The load-bearing kernel classes the rubric names, by their kernel-timeline name.
pub const LOAD_BEARING: [&str; 11] = [
    "section_contract",
    "section_rms_rebase",
    "section_contact",
    "section_gelu_tanh",
    "section_hadamard",
    "section_re_entry",
    "section_scale",
    "section_chronology",
    "section_census",
    "section_from_bfloat16",
    "section_carry",
];

/// A kernel whose name begins with this prefix is a mount kernel of the `bfloat16_*` family.
pub const MOUNT_PREFIX: &str = "bfloat16_";
/// The census family, by name, for the CENSUS-OVERHEAD reading.
pub const CENSUS_PREFIX: &str = "section_census";

// ---------------------------------------------------------------------------------------------
// reading what the other half wrote
// ---------------------------------------------------------------------------------------------

/// A tab-separated face with one header row. Absent file → `None`; absent column → `unknown`.
pub struct Table {
    pub path: String,
    pub header: Vec<String>,
    pub rows: Vec<Vec<String>>,
}

impl Table {
    pub fn read(dir: &Path, name: &str) -> Option<Table> {
        let path = dir.join(name);
        let text = std::fs::read_to_string(&path).ok()?;
        let mut lines = text.lines();
        let header: Vec<String> = lines
            .next()?
            .split('\t')
            .map(|c| c.trim().to_owned())
            .collect();
        let rows: Vec<Vec<String>> = lines
            .filter(|line| !line.trim().is_empty())
            .map(|line| line.split('\t').map(|c| c.trim().to_owned()).collect())
            .collect();
        Some(Table {
            path: path.display().to_string(),
            header,
            rows,
        })
    }

    pub fn index(&self, column: &str) -> Option<usize> {
        self.header.iter().position(|c| c == column)
    }

    /// The cell, or `unknown` — for an absent column, a short row, an empty cell, or the literal.
    pub fn cell<'a>(&'a self, row: &'a [String], column: &str) -> &'a str {
        let Some(index) = self.index(column) else {
            return UNKNOWN;
        };
        let Some(value) = row.get(index) else {
            return UNKNOWN;
        };
        if value.is_empty() {
            UNKNOWN
        } else {
            value.as_str()
        }
    }

    pub fn u64_at(&self, row: &[String], column: &str) -> Option<u64> {
        let cell = self.cell(row, column);
        if cell == UNKNOWN {
            None
        } else {
            cell.parse::<u64>().ok()
        }
    }

    pub fn f64_at(&self, row: &[String], column: &str) -> Option<f64> {
        let cell = self.cell(row, column);
        if cell == UNKNOWN {
            None
        } else {
            cell.parse::<f64>().ok()
        }
    }
}

/// The machine-readable half of a `.form` receipt: every `  key = value` line, keyed by the key.
pub struct FormFacts {
    pub facts: BTreeMap<String, String>,
    pub read: Vec<String>,
    pub missing: Vec<String>,
}

impl FormFacts {
    pub fn read_all(dir: &Path, names: &[&str]) -> FormFacts {
        let mut facts = BTreeMap::new();
        let mut read = Vec::new();
        let mut missing = Vec::new();
        for name in names {
            let path = dir.join(name);
            match std::fs::read_to_string(&path) {
                Ok(text) => {
                    for line in text.lines() {
                        let line = line.trim();
                        if let Some((key, value)) = line.split_once(" = ") {
                            if !key.contains(' ') {
                                facts.insert(key.to_owned(), value.trim().to_owned());
                            }
                        }
                    }
                    read.push((*name).to_owned());
                }
                Err(_) => missing.push((*name).to_owned()),
            }
        }
        FormFacts {
            facts,
            read,
            missing,
        }
    }

    pub fn get(&self, key: &str) -> &str {
        self.facts.get(key).map(|s| s.as_str()).unwrap_or(UNKNOWN)
    }

    pub fn u64(&self, key: &str) -> Option<u64> {
        self.facts.get(key).and_then(|v| v.parse::<u64>().ok())
    }
}

// ---------------------------------------------------------------------------------------------
// the derived faces
// ---------------------------------------------------------------------------------------------

fn median(values: &mut Vec<u64>) -> Option<u64> {
    if values.is_empty() {
        return None;
    }
    values.sort_unstable();
    Some(values[values.len() / 2])
}

/// One kernel class as the timeline shows it.
pub struct KernelClass {
    pub name: String,
    pub launches: usize,
    pub summed_ns: Option<u64>,
    pub median_ns: Option<u64>,
    pub min_ns: Option<u64>,
    pub max_ns: Option<u64>,
    /// Distinct launch geometries: (grid, block) → (count, median, min, max duration).
    pub geometries: Vec<(
        (u64, u64, u64, u64, u64, u64),
        usize,
        Option<u64>,
        Option<u64>,
        Option<u64>,
    )>,
    pub registers_per_thread: Option<u64>,
    pub static_shared_octets: Option<u64>,
    pub dynamic_shared_octets: Option<u64>,
    /// The WIDEST launch of this class: if even that one cannot fill the resident lanes, every
    /// launch of the class is under-parallel. The narrowest is carried beside it.
    pub threads_per_launch: Option<u64>,
    pub threads_per_launch_min: Option<u64>,
    /// How many launches of this class could not fill the card's resident lanes even once, and how
    /// many launches were counted at all. A class of heterogeneous launches has no single answer;
    /// this is the population, not an average of it.
    pub launches_under_one_wave: Option<usize>,
    pub launches_with_extent: usize,
    pub launch_indices: Vec<u64>,
}

impl KernelClass {
    /// Threads in the widest launch ÷ the whole card's resident lanes. Below 1, one launch of this
    /// class cannot occupy the card even once.
    pub fn waves_per_sm(&self, resident_lanes: Option<u64>) -> Option<f64> {
        let threads = self.threads_per_launch? as f64;
        let lanes = resident_lanes? as f64;
        if lanes == 0.0 {
            None
        } else {
            Some(threads / lanes)
        }
    }
}

pub struct Timeline {
    pub classes: Vec<KernelClass>,
    pub total_launches: usize,
    /// Per graph launch: (index, first start, last end, summed kernel ns, kernels, max concurrent,
    /// overlap fraction, census summed ns)
    pub graphs: Vec<GraphLaunch>,
}

pub struct GraphLaunch {
    pub index: u64,
    pub kernels: usize,
    pub first_start_ns: Option<u64>,
    pub last_end_ns: Option<u64>,
    pub wall_ns: Option<u64>,
    pub summed_kernel_ns: Option<u64>,
    pub union_kernel_ns: Option<u64>,
    pub max_concurrent: Option<usize>,
    pub overlap_fraction: Option<f64>,
    pub census_ns: Option<u64>,
}

pub fn read_timeline(table: &Table) -> Timeline {
    let mut by_name: BTreeMap<String, Vec<&Vec<String>>> = BTreeMap::new();
    let mut by_graph: BTreeMap<u64, Vec<&Vec<String>>> = BTreeMap::new();
    for row in &table.rows {
        let name = table.cell(row, "kernel").to_owned();
        by_name.entry(name).or_default().push(row);
        if let Some(graph) = table.u64_at(row, "graph_launch_index") {
            by_graph.entry(graph).or_default().push(row);
        }
    }
    let mut classes = Vec::new();
    for (name, rows) in &by_name {
        let mut durations: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "duration_ns"))
            .collect();
        let summed = if durations.is_empty() {
            None
        } else {
            Some(durations.iter().sum())
        };
        let min = durations.iter().copied().min();
        let max = durations.iter().copied().max();
        let med = median(&mut durations);
        let mut geometry_groups: BTreeMap<(u64, u64, u64, u64, u64, u64), Vec<u64>> =
            BTreeMap::new();
        for row in rows {
            let g = (
                table.u64_at(row, "grid_x").unwrap_or(0),
                table.u64_at(row, "grid_y").unwrap_or(0),
                table.u64_at(row, "grid_z").unwrap_or(0),
                table.u64_at(row, "block_x").unwrap_or(0),
                table.u64_at(row, "block_y").unwrap_or(0),
                table.u64_at(row, "block_z").unwrap_or(0),
            );
            let entry = geometry_groups.entry(g).or_default();
            if let Some(d) = table.u64_at(row, "duration_ns") {
                entry.push(d);
            }
        }
        let geometries: Vec<_> = geometry_groups
            .into_iter()
            .map(|(g, mut ds)| {
                let count = ds.len();
                let low = ds.iter().copied().min();
                let high = ds.iter().copied().max();
                let med = median(&mut ds);
                (g, count, med, low, high)
            })
            .collect();
        let first = rows[0];
        let mut extents: Vec<(u64, usize)> = Vec::new();
        for (g, count, _, _, _) in &geometries {
            if g.0 > 0 && g.3 > 0 {
                extents.push((
                    g.0 * g.1.max(1) * g.2.max(1) * g.3 * g.4.max(1) * g.5.max(1),
                    *count,
                ));
            }
        }
        let threads = extents.iter().map(|(e, _)| *e).max();
        let threads_min = extents.iter().map(|(e, _)| *e).min();
        let with_extent: usize = extents.iter().map(|(_, c)| *c).sum();
        classes.push(KernelClass {
            name: name.clone(),
            launches: rows.len(),
            summed_ns: summed,
            median_ns: med,
            min_ns: min,
            max_ns: max,
            geometries,
            registers_per_thread: table.u64_at(first, "registers_per_thread"),
            static_shared_octets: table.u64_at(first, "static_shared_octets"),
            dynamic_shared_octets: table.u64_at(first, "dynamic_shared_octets"),
            threads_per_launch: threads,
            threads_per_launch_min: threads_min,
            launches_under_one_wave: None,
            launches_with_extent: with_extent,
            launch_indices: rows
                .iter()
                .filter_map(|r| table.u64_at(r, "launch_index"))
                .collect(),
        });
    }
    let mut graphs = Vec::new();
    for (index, rows) in &by_graph {
        let starts: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "start_ns"))
            .collect();
        let ends: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "end_ns"))
            .collect();
        let first_start = starts.iter().copied().min();
        let last_end = ends.iter().copied().max();
        let wall = match (first_start, last_end) {
            (Some(a), Some(b)) if b >= a => Some(b - a),
            _ => None,
        };
        let summed: Option<u64> = {
            let ds: Vec<u64> = rows
                .iter()
                .filter_map(|r| table.u64_at(r, "duration_ns"))
                .collect();
            if ds.len() == rows.len() && !ds.is_empty() {
                Some(ds.iter().sum())
            } else {
                None
            }
        };
        // intervals: the union and the greatest simultaneous population
        let mut intervals: Vec<(u64, u64)> = Vec::new();
        for row in rows {
            if let (Some(s), Some(e)) = (table.u64_at(row, "start_ns"), table.u64_at(row, "end_ns"))
            {
                intervals.push((s, e));
            }
        }
        let (union, concurrent) = if intervals.len() == rows.len() && !intervals.is_empty() {
            let mut events: Vec<(u64, i64)> = Vec::new();
            for (s, e) in &intervals {
                events.push((*s, 1));
                events.push((*e, -1));
            }
            events.sort_unstable();
            let mut depth = 0i64;
            let mut peak = 0i64;
            let mut union_ns = 0u64;
            let mut open_from = 0u64;
            for (at, delta) in events {
                if depth == 0 && delta == 1 {
                    open_from = at;
                }
                depth += delta;
                if depth > peak {
                    peak = depth;
                }
                if depth == 0 {
                    union_ns += at.saturating_sub(open_from);
                }
            }
            (Some(union_ns), Some(peak as usize))
        } else {
            (None, None)
        };
        let overlap = match (summed, union) {
            (Some(s), Some(u)) if s > 0 => Some((s.saturating_sub(u)) as f64 / s as f64),
            _ => None,
        };
        let census: Option<u64> = {
            let ds: Vec<u64> = rows
                .iter()
                .filter(|r| table.cell(r, "kernel").starts_with(CENSUS_PREFIX))
                .filter_map(|r| table.u64_at(r, "duration_ns"))
                .collect();
            if ds.is_empty() {
                None
            } else {
                Some(ds.iter().sum())
            }
        };
        graphs.push(GraphLaunch {
            index: *index,
            kernels: rows.len(),
            first_start_ns: first_start,
            last_end_ns: last_end,
            wall_ns: wall,
            summed_kernel_ns: summed,
            union_kernel_ns: union,
            max_concurrent: concurrent,
            overlap_fraction: overlap,
            census_ns: census,
        });
    }
    Timeline {
        classes,
        total_launches: table.rows.len(),
        graphs,
    }
}

/// The `ncu` faces, per kernel name, when `scheduler-states.tsv` carried them.
pub struct SchedulerFace {
    pub kernel: String,
    pub rows: usize,
    pub dram_throughput_pct: Option<f64>,
    pub sm_throughput_pct: Option<f64>,
    pub no_eligible_pct: Option<f64>,
    pub stall_top1: Option<String>,
    pub stall_top1_pct: Option<f64>,
    pub achieved_occupancy_pct: Option<f64>,
    pub active_warps_per_cycle: Option<f64>,
    pub eligible_warps_per_cycle: Option<f64>,
    pub issued_warps_per_cycle: Option<f64>,
    pub l1_hit_pct: Option<f64>,
    pub l2_hit_pct: Option<f64>,
}

/// The median across every profiled launch of that kernel, per column, and the most frequent
/// `stall_top1`. A single row would speak for one launch; the median speaks for the population the
/// profiler actually reached, and the row count is carried beside it so the reader knows how many.
pub fn read_scheduler(table: &Table) -> BTreeMap<String, SchedulerFace> {
    let mut grouped: BTreeMap<String, Vec<&Vec<String>>> = BTreeMap::new();
    for row in &table.rows {
        grouped
            .entry(table.cell(row, "kernel").to_owned())
            .or_default()
            .push(row);
    }
    let mut out: BTreeMap<String, SchedulerFace> = BTreeMap::new();
    for (kernel, rows) in grouped {
        let median_of = |column: &str| -> Option<f64> {
            let mut values: Vec<f64> = rows
                .iter()
                .filter_map(|r| table.f64_at(r, column))
                .collect();
            if values.is_empty() {
                return None;
            }
            values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            Some(values[values.len() / 2])
        };
        let mut stalls: BTreeMap<String, usize> = BTreeMap::new();
        for row in &rows {
            let stall = table.cell(row, "stall_top1");
            if stall != UNKNOWN {
                *stalls.entry(stall.to_owned()).or_default() += 1;
            }
        }
        let stall_top1 = stalls
            .iter()
            .max_by_key(|(_, count)| **count)
            .map(|(name, count)| {
                format!("{name} (in {count} of {} profiled launches)", rows.len())
            });
        out.insert(
            kernel.clone(),
            SchedulerFace {
                kernel,
                rows: rows.len(),
                dram_throughput_pct: median_of("dram_throughput_pct"),
                sm_throughput_pct: median_of("sm_throughput_pct"),
                no_eligible_pct: median_of("no_eligible_pct"),
                stall_top1,
                stall_top1_pct: median_of("stall_top1_pct"),
                achieved_occupancy_pct: median_of("achieved_occupancy_pct"),
                active_warps_per_cycle: median_of("active_warps_per_cycle"),
                eligible_warps_per_cycle: median_of("eligible_warps_per_cycle"),
                issued_warps_per_cycle: median_of("issued_warps_per_cycle"),
                l1_hit_pct: median_of("l1_hit_pct"),
                l2_hit_pct: median_of("l2_hit_pct"),
            },
        );
    }
    out
}

// ---------------------------------------------------------------------------------------------
// the rubric, as code
// ---------------------------------------------------------------------------------------------

/// One classification row: the object, the class the rubric's ORDER selected, every other class
/// that also applied, the metrics that decided it with their values, the raw rows cited, the
/// confidence, and what `ncu` would have been needed for.
pub struct Classification {
    pub object: String,
    pub class: String,
    pub secondary: Vec<String>,
    pub deciding: Vec<(String, String)>,
    pub cited: String,
    pub confidence: String,
    pub ncu_needed_for: Vec<String>,
    pub verdict: String,
}

pub const RUBRIC_ORDER: [&str; 9] = [
    "CPU-FOREMAN-BOUND",
    "LAUNCH-LATENCY-BOUND",
    "UNDER-PARALLEL",
    "INNER-SERIAL",
    "MEMORY-BOUND",
    "ISSUE/COMPUTE-BOUND",
    "STALL-BOUND",
    "TRANSFER-BOUND",
    "CENSUS-OVERHEAD",
];

fn fmt_opt_u64(value: Option<u64>) -> String {
    value
        .map(|v| v.to_string())
        .unwrap_or_else(|| UNKNOWN.to_owned())
}

fn fmt_opt_f64(value: Option<f64>, places: usize) -> String {
    value
        .map(|v| format!("{v:.places$}", places = places))
        .unwrap_or_else(|| UNKNOWN.to_owned())
}

/// Classify one kernel class. The order of the rubric decides; every class that applied is kept.
#[allow(clippy::too_many_arguments)]
pub fn classify_kernel(
    class: &KernelClass,
    resident_lanes: Option<u64>,
    class_share: Option<f64>,
    equal_share: Option<f64>,
    scheduler: Option<&SchedulerFace>,
) -> Classification {
    let mut applied: Vec<String> = Vec::new();
    let mut deciding: Vec<(String, String)> = Vec::new();
    let mut ncu_needed: Vec<String> = Vec::new();

    // LAUNCH-LATENCY-BOUND: median duration <= 8 us and the class's launch count per graph
    // dominates — operationalized as: its share of the profiled graph's kernel launches is at or
    // above the equal share 1/(number of distinct classes).
    let median_ns = class.median_ns;
    deciding.push(("median_duration_ns".to_owned(), fmt_opt_u64(median_ns)));
    deciding.push(("launches".to_owned(), class.launches.to_string()));
    deciding.push((
        "launch_share_of_graph".to_owned(),
        fmt_opt_f64(class_share, 4),
    ));
    deciding.push(("equal_share".to_owned(), fmt_opt_f64(equal_share, 4)));
    let launch_latency = match (median_ns, class_share, equal_share) {
        (Some(m), Some(s), Some(e)) => Some(m <= 8_000 && s >= e),
        _ => None,
    };
    if launch_latency == Some(true) {
        applied.push("LAUNCH-LATENCY-BOUND".to_owned());
    }

    // UNDER-PARALLEL: threads per launch < the card's resident lanes. A class whose launches have
    // several geometries has no single answer, so the POPULATION is returned: how many of its
    // launches could not fill the card even once. The class carries it when the majority could not.
    let waves = class.waves_per_sm(resident_lanes);
    let mut under_one: Option<usize> = None;
    if let Some(lanes) = resident_lanes {
        let mut count = 0usize;
        for (g, launches, _, _, _) in &class.geometries {
            let threads = g.0 * g.1.max(1) * g.2.max(1) * g.3 * g.4.max(1) * g.5.max(1);
            if threads < lanes {
                count += launches;
            }
        }
        under_one = Some(count);
    }
    deciding.push((
        "threads_per_launch_widest".to_owned(),
        fmt_opt_u64(class.threads_per_launch),
    ));
    deciding.push((
        "threads_per_launch_narrowest".to_owned(),
        fmt_opt_u64(class.threads_per_launch_min),
    ));
    deciding.push((
        "device_resident_lanes".to_owned(),
        fmt_opt_u64(resident_lanes),
    ));
    deciding.push((
        "waves_per_card_widest_launch".to_owned(),
        fmt_opt_f64(waves, 4),
    ));
    deciding.push((
        "launches_below_one_wave".to_owned(),
        match under_one {
            Some(count) => format!(
                "{count} of {} launch(es) with a stated extent",
                class.launches_with_extent
            ),
            None => UNKNOWN.to_owned(),
        },
    ));
    let under_parallel = match (under_one, class.launches_with_extent) {
        (Some(count), total) if total > 0 => Some(count * 2 > total),
        _ => None,
    };
    if under_parallel == Some(true) {
        applied.push("UNDER-PARALLEL".to_owned());
    }

    // INNER-SERIAL: section_contract, UNDER-PARALLEL holds, and duration varies at fixed output
    // extent. The inner dimension K is not a column of any telemetry face, so what is measurable
    // is: two launch geometries with the SAME grid extent whose median durations differ. That is
    // reported as the deciding metric and its confidence is inferred-from-nsys-only.
    let mut fixed_extent_ratio: Option<f64> = None;
    if class.name == "section_contract" {
        for (g, launches, _, low, high) in &class.geometries {
            if *launches >= 2 {
                if let (Some(low), Some(high)) = (low, high) {
                    let ratio = *high as f64 / (*low).max(1) as f64;
                    fixed_extent_ratio = Some(
                        fixed_extent_ratio
                            .map(|held: f64| held.max(ratio))
                            .unwrap_or(ratio),
                    );
                    let _ = g;
                }
            }
        }
        deciding.push((
            "fixed_extent_duration_ratio".to_owned(),
            fmt_opt_f64(fixed_extent_ratio, 3),
        ));
        deciding.push((
            "fixed_extent_rule".to_owned(),
            "same grid AND block (so the same output count), widest ÷ narrowest duration; K is in no telemetry column".to_owned(),
        ));
        if under_parallel == Some(true) && fixed_extent_ratio.map(|r| r >= 2.0) == Some(true) {
            applied.push("INNER-SERIAL".to_owned());
        }
    }

    // the three ncu-only classes
    let dram = scheduler.and_then(|s| s.dram_throughput_pct);
    let sm = scheduler.and_then(|s| s.sm_throughput_pct);
    let no_eligible = scheduler.and_then(|s| s.no_eligible_pct);
    let stall_top1 = scheduler.and_then(|s| s.stall_top1.clone());
    deciding.push(("dram_throughput_pct".to_owned(), fmt_opt_f64(dram, 2)));
    deciding.push(("sm_throughput_pct".to_owned(), fmt_opt_f64(sm, 2)));
    deciding.push(("no_eligible_pct".to_owned(), fmt_opt_f64(no_eligible, 2)));
    deciding.push((
        "stall_top1".to_owned(),
        stall_top1.clone().unwrap_or_else(|| UNKNOWN.to_owned()),
    ));
    if dram.is_none() {
        ncu_needed.push("MEMORY-BOUND (dram_throughput_pct)".to_owned());
    } else if dram.unwrap() >= 60.0 {
        applied.push("MEMORY-BOUND".to_owned());
    }
    if sm.is_none() {
        ncu_needed.push("ISSUE/COMPUTE-BOUND (sm_throughput_pct)".to_owned());
    } else if sm.unwrap() >= 60.0 {
        applied.push("ISSUE/COMPUTE-BOUND".to_owned());
    }
    if no_eligible.is_none() || stall_top1.is_none() {
        ncu_needed.push("STALL-BOUND (no_eligible_pct, stall_top1)".to_owned());
    } else if no_eligible.unwrap() >= 50.0 {
        applied.push("STALL-BOUND".to_owned());
    }

    // the order of the rubric decides
    let mut ordered: Vec<String> = Vec::new();
    for name in RUBRIC_ORDER {
        if applied.iter().any(|a| a == name) {
            ordered.push(name.to_owned());
        }
    }
    let class_name = ordered.first().cloned().unwrap_or_else(|| {
        if median_ns.is_none() {
            UNKNOWN.to_owned()
        } else {
            "UNCLASSIFIED (no rubric class applied)".to_owned()
        }
    });
    // measured: every metric the rubric can ask for was reachable, ncu included, so the classes it
    // did NOT select were rejected on measurement rather than on absence.
    let confidence = if class_name == UNKNOWN {
        UNKNOWN.to_owned()
    } else if scheduler.is_some() {
        "measured".to_owned()
    } else if median_ns.is_some() {
        "inferred-from-nsys-only".to_owned()
    } else {
        UNKNOWN.to_owned()
    };
    let cited = if class.launch_indices.is_empty() {
        UNKNOWN.to_owned()
    } else {
        let lo = class.launch_indices.iter().copied().min().unwrap_or(0);
        let hi = class.launch_indices.iter().copied().max().unwrap_or(0);
        format!(
            "kernel-timeline.tsv launch_index {lo}..{hi} ({} rows)",
            class.launch_indices.len()
        )
    };
    let verdict = format!(
        "{} → {} ({})",
        class.name,
        class_name,
        if ordered.len() > 1 {
            format!("secondary {}", ordered[1..].join(", "))
        } else {
            "no secondary class".to_owned()
        }
    );
    Classification {
        object: class.name.clone(),
        class: class_name,
        secondary: ordered.into_iter().skip(1).collect(),
        deciding,
        cited,
        confidence,
        ncu_needed_for: ncu_needed,
        verdict,
    }
}

/// The CPU-side phases, from the api timeline. Each boundary is a named span family.
pub struct ApiFace {
    pub api: String,
    pub calls: usize,
    pub summed_ns: Option<u64>,
    pub median_ns: Option<u64>,
    pub first_index: Option<u64>,
    pub last_index: Option<u64>,
}

pub fn read_api(table: &Table) -> Vec<ApiFace> {
    let mut by_api: BTreeMap<String, Vec<&Vec<String>>> = BTreeMap::new();
    for row in &table.rows {
        by_api
            .entry(table.cell(row, "api").to_owned())
            .or_default()
            .push(row);
    }
    let mut out = Vec::new();
    for (api, rows) in by_api {
        let mut ds: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "duration_ns"))
            .collect();
        let summed = if ds.is_empty() {
            None
        } else {
            Some(ds.iter().sum())
        };
        let med = median(&mut ds);
        let indices: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "index"))
            .collect();
        out.push(ApiFace {
            api,
            calls: rows.len(),
            summed_ns: summed,
            median_ns: med,
            first_index: indices.iter().copied().min(),
            last_index: indices.iter().copied().max(),
        });
    }
    out.sort_by(|a, b| b.summed_ns.unwrap_or(0).cmp(&a.summed_ns.unwrap_or(0)));
    out
}

/// The inter-graph CPU gaps: from one graph launch's last kernel end to the next graph launch's
/// first kernel start, taken on the kernel timeline's own timebase.
pub fn inter_graph_gaps(timeline: &Timeline) -> Vec<(u64, u64, Option<u64>, Option<u64>)> {
    let mut graphs: Vec<&GraphLaunch> = timeline.graphs.iter().collect();
    graphs.sort_by_key(|g| g.index);
    let mut out = Vec::new();
    for window in graphs.windows(2) {
        let (a, b) = (window[0], window[1]);
        let gap = match (a.last_end_ns, b.first_start_ns) {
            (Some(end), Some(start)) if start >= end => Some(start - end),
            _ => None,
        };
        out.push((a.index, b.index, gap, a.wall_ns));
    }
    out
}

/// The transfer face: per kind, octets and the rate the octets and durations imply.
pub struct TransferFace {
    pub kind: String,
    pub count: usize,
    pub octets: Option<u64>,
    pub summed_ns: Option<u64>,
    pub octets_per_second: Option<f64>,
}

pub fn read_transfers(table: &Table) -> Vec<TransferFace> {
    let mut by_kind: BTreeMap<String, Vec<&Vec<String>>> = BTreeMap::new();
    for row in &table.rows {
        by_kind
            .entry(table.cell(row, "kind").to_owned())
            .or_default()
            .push(row);
    }
    let mut out = Vec::new();
    for (kind, rows) in by_kind {
        let octets: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "octets"))
            .collect();
        let durations: Vec<u64> = rows
            .iter()
            .filter_map(|r| table.u64_at(r, "duration_ns"))
            .collect();
        let total_octets =
            (octets.len() == rows.len() && !octets.is_empty()).then(|| octets.iter().sum::<u64>());
        let total_ns = (durations.len() == rows.len() && !durations.is_empty())
            .then(|| durations.iter().sum::<u64>());
        let rate = match (total_octets, total_ns) {
            (Some(o), Some(t)) if t > 0 => Some(o as f64 * 1e9 / t as f64),
            _ => None,
        };
        out.push(TransferFace {
            kind,
            count: rows.len(),
            octets: total_octets,
            summed_ns: total_ns,
            octets_per_second: rate,
        });
    }
    out
}

/// Classify one boundary. Same rubric, same order; boundaries can only take the boundary classes.
pub fn classify_boundary(
    object: &str,
    cpu_foreman: Option<bool>,
    transfer_bound: Option<bool>,
    census_overhead: Option<bool>,
    deciding: Vec<(String, String)>,
    cited: String,
) -> Classification {
    let mut applied: Vec<String> = Vec::new();
    if cpu_foreman == Some(true) {
        applied.push("CPU-FOREMAN-BOUND".to_owned());
    }
    if transfer_bound == Some(true) {
        applied.push("TRANSFER-BOUND".to_owned());
    }
    if census_overhead == Some(true) {
        applied.push("CENSUS-OVERHEAD".to_owned());
    }
    let mut ordered: Vec<String> = Vec::new();
    for name in RUBRIC_ORDER {
        if applied.iter().any(|a| a == name) {
            ordered.push(name.to_owned());
        }
    }
    let measured = cpu_foreman.is_some() || transfer_bound.is_some() || census_overhead.is_some();
    let class = ordered.first().cloned().unwrap_or_else(|| {
        if measured {
            "UNCLASSIFIED (no rubric class applied)".to_owned()
        } else {
            UNKNOWN.to_owned()
        }
    });
    let confidence = if measured {
        "inferred-from-nsys-only".to_owned()
    } else {
        UNKNOWN.to_owned()
    };
    let verdict = format!(
        "{object} → {class} ({})",
        if ordered.len() > 1 {
            format!("secondary {}", ordered[1..].join(", "))
        } else {
            "no secondary class".to_owned()
        }
    );
    Classification {
        object: object.to_owned(),
        class,
        secondary: ordered.into_iter().skip(1).collect(),
        deciding,
        cited,
        confidence,
        ncu_needed_for: Vec::new(),
        verdict,
    }
}

/// Every kernel name the timeline carried that the rubric does not name as load-bearing.
pub fn unnamed_classes(timeline: &Timeline) -> Vec<String> {
    let named: BTreeSet<&str> = LOAD_BEARING.iter().copied().collect();
    timeline
        .classes
        .iter()
        .filter(|c| !named.contains(c.name.as_str()) && !c.name.starts_with(MOUNT_PREFIX))
        .map(|c| c.name.clone())
        .collect()
}

/// **Do the transfers overlap the kernels, or do they take turns?** The rubric's TRANSFER-BOUND has
/// a second clause — *transfers serialize with compute* — and it is measurable from the two
/// timelines alone, because both are on one timebase: intersect every transfer interval with the
/// UNION of the kernel intervals and return how much of the transfer time was concurrent with any
/// kernel at all. Returns `(overlapping ns, total transfer ns)`; `None` when either timeline is
/// missing an endpoint.
pub fn transfer_overlap(kernels: &Table, transfers: &Table, kind: &str) -> Option<(u64, u64)> {
    let mut intervals: Vec<(u64, u64)> = Vec::new();
    for row in &kernels.rows {
        let (start, end) = (
            kernels.u64_at(row, "start_ns")?,
            kernels.u64_at(row, "end_ns")?,
        );
        if end > start {
            intervals.push((start, end));
        }
    }
    intervals.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (start, end) in intervals {
        match merged.last_mut() {
            Some(last) if start <= last.1 => last.1 = last.1.max(end),
            _ => merged.push((start, end)),
        }
    }
    let mut overlapping = 0u64;
    let mut total = 0u64;
    for row in &transfers.rows {
        if !transfers.cell(row, "kind").contains(kind) {
            continue;
        }
        let (start, end) = match (
            transfers.u64_at(row, "start_ns"),
            transfers.u64_at(row, "end_ns"),
        ) {
            (Some(a), Some(b)) if b > a => (a, b),
            _ => continue,
        };
        total += end - start;
        let index = merged.partition_point(|(_, kernel_end)| *kernel_end <= start);
        for (kernel_start, kernel_end) in merged.iter().skip(index) {
            if *kernel_start >= end {
                break;
            }
            overlapping += kernel_end
                .min(&end)
                .saturating_sub(*kernel_start.max(&start));
        }
    }
    Some((overlapping, total))
}

/// The greatest number of transfers in flight at one instant — the honest demand against the
/// card's copy engines. A COUNT of transfers is not a demand; a concurrent population is.
pub fn max_concurrent_transfers(transfers: &Table) -> Option<usize> {
    let mut events: Vec<(u64, i64)> = Vec::new();
    for row in &transfers.rows {
        match (
            transfers.u64_at(row, "start_ns"),
            transfers.u64_at(row, "end_ns"),
        ) {
            (Some(start), Some(end)) if end > start => {
                events.push((start, 1));
                events.push((end, -1));
            }
            _ => return None,
        }
    }
    if events.is_empty() {
        return None;
    }
    events.sort_unstable();
    let mut depth = 0i64;
    let mut peak = 0i64;
    for (_, delta) in events {
        depth += delta;
        if depth > peak {
            peak = depth;
        }
    }
    Some(peak as usize)
}
