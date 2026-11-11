//! The field's commands on the card (`holonics::hnn::tower::field`, `holonics_cuda::hnn::CardField`;
//! record `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`).
//!
//! - `field_pass parity complete-language parity-field ARGS…`: the host's field against the card's on
//!   `train-field`'s sections, read for read (faces, covectors, learners) and write for write.
//! - `field_pass time complete-language time-field ARGS…`: the card alone on the opening sections and
//!   writes, and a lap and the held problems' writes projected from them.
//! - `field_pass train complete-language train-field ARGS…` and `sample-field ARGS…`: the commands with every read and
//!   return on the card.
//!
//! Each run prints `FIELD_CARD` with the card's reads, returns, their time, the site pairs met, the landmark reads and the
//! largest batch's allocations, and the card's free memory at the open and its batch budget; with
//! `FIELD_PROFILE` set, each kernel's launches and time and the run's copies and allocations; with `FIELD_COLUMNS` set,
//! each contact column launch's longest column beside its card time (`FIELD_COLUMN` lines).
#![allow(dead_code, clippy::disallowed_methods, clippy::disallowed_types, reason = "explicit exterior CLI file/process boundary")]

#[path = "../../holonics/examples/solenoidal_alpha.rs"]
mod exterior;

use holonics_cuda::hnn::{Card, CardField};
use std::error::Error;
use std::time::Instant;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn run(args: &[String]) -> Result<()> {
    let (mode, rest) = args.split_first().ok_or("field_pass parity|time|train complete-language COMMAND ARGS…")?;
    if rest.first().map(String::as_str) != Some("complete-language") {
        return Err("field_pass parity|time|train complete-language COMMAND ARGS…".into());
    }
    println!("FIELD_COMMAND {}", rest[1..].join(" "));
    let opened = Card::open(0)?;
    let mut card = CardField::open(&opened)?;
    // [agent-inferred, November 1] A declared reading (`FIELD_PROFILE`): every launch, transfer and
    // allocation timed alone (`CardField::profile`), printed at the end as `FIELD_PROFILE` lines.
    if std::env::var_os("FIELD_PROFILE").is_some() {
        card.profile();
    }
    if std::env::var_os("FIELD_PHASES").is_some() {
        card.trace_phases();
    }
    // [agent-inferred, November 7] A declared reading (`FIELD_EVENTS`): every launch timed on the card's own clock
    // (`CardField::stamp`), printed at the end as `FIELD_EVENT` lines.
    if std::env::var_os("FIELD_EVENTS").is_some() {
        card.stamp()?;
    }
    // [measurement; agent-inferred, November 8] A declared reading (`FIELD_COLUMNS`, off unless set): each contact column
    // launch's longest column (the receivers one source walks) beside its card time (`CardField::stamp_columns`, which also
    // stamps every launch), printed at the end as `FIELD_COLUMN` lines by head and the longest column's octave.
    if std::env::var_os("FIELD_COLUMNS").is_some() {
        card.stamp_columns()?;
    }
    let memory = opened.census().memory;
    println!("FIELD_CARD_OPEN card={} free={} total={} batch_budget={}", opened.census().name, memory.free_bytes, memory.total_bytes, card.budget());
    let started = Instant::now();
    let result = match mode.as_str() {
        "parity" | "time" => exterior::run_field_parity(&rest[1..], &mut card),
        // [definition; Brandon, November 7 19:22] `FIELD_HOST_LANES`: the energy reads split between the host's cores and
        // the card at once (`LanesField`), the same bits at any partition; its receipt is the `FIELD_LANES` line.
        "train" if std::env::var_os("FIELD_HOST_LANES").is_some() => {
            let mut lanes = holonics::hnn::tower::field::LanesField::new(&mut card);
            let r = exterior::run_field_with_realization(&rest[1..], &mut lanes);
            println!(
                "FIELD_LANES splits={} host_regions={} card_regions={} host_ms={} card_ms={} split_wall_ms={} share_permille={} host_threads={}",
                lanes.splits,
                lanes.host_regions,
                lanes.card_regions,
                lanes.host_us / 1000,
                lanes.card_us / 1000,
                lanes.wall_us / 1000,
                lanes.share() * 1000 >> 16,
                rayon::current_num_threads()
            );
            r
        }
        "train" => exterior::run_field_with_realization(&rest[1..], &mut card),
        _ => Err("field_pass parity|time|train complete-language COMMAND ARGS…".into()),
    };
    let t = card.times();
    println!(
        "FIELD_CARD reads={} read_ms={} returns={} return_ms={} pairs={} batches={} peak_store={} landmarks={} landmark_ms={} elapsed_ms={}",
        t.reads,
        t.read_ns / 1_000_000,
        t.returns,
        t.return_ns / 1_000_000,
        t.pairs,
        t.batches,
        t.peak_store,
        t.landmarks,
        t.landmark_ns / 1_000_000,
        started.elapsed().as_millis()
    );
    if let Some(phases) = card.phased() {
        for (name, marks, ns) in phases {
            println!("FIELD_PHASE name={name} marks={marks} ms={} us_a_mark={}", ns / 1_000_000, ns / 1_000 / (marks as u128).max(1));
        }
    }
    if let Some(kernels) = card.stamped() {
        let total: u128 = kernels.values().map(|v| v.1).sum();
        let mut rows: Vec<_> = kernels.iter().collect();
        rows.sort_by_key(|(_, v)| std::cmp::Reverse(v.1));
        for ((entry, head), (calls, ns)) in rows {
            let head = if *head == u32::MAX { "all".to_string() } else { head.to_string() };
            println!("FIELD_EVENT entry={entry} head={head} launches={calls} card_us={} us_a_launch={} share_permille={}", ns / 1_000, ns / 1_000 / (*calls as u128).max(1), ns * 1000 / total.max(1));
        }
        println!("FIELD_EVENT_SPLIT card_kernels_ms={} elapsed_ms={}", total / 1_000_000, started.elapsed().as_millis());
    }
    if let Some(rows) = card.columned() {
        for line in holonics_cuda::hnn::ColumnRow::lines(&rows) {
            println!("FIELD_COLUMN {line}");
        }
    }
    if let Some(p) = card.profiled() {
        let kernels: u128 = p.kernels.values().map(|v| v.1).sum();
        for (entry, (calls, ns)) in &p.kernels {
            let threads = p.threads.get(entry).copied().unwrap_or(0);
            println!("FIELD_PROFILE entry={entry} launches={calls} ms={} us_a_launch={} grid_threads={threads} mean_grid_threads={}", ns / 1_000_000, ns / 1_000 / (*calls as u128).max(1), threads / (*calls as u128).max(1));
        }
        println!(
            "FIELD_PROFILE_SPLIT kernels_ms={} copies={} copies_ms={} allocations={} allocations_ms={} elapsed_ms={}",
            kernels / 1_000_000,
            p.copies.0,
            p.copies.1 / 1_000_000,
            p.allocations.0,
            p.allocations.1 / 1_000_000,
            started.elapsed().as_millis()
        );
    }
    result
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(error) = run(&args) {
        eprintln!("field_pass: {error}");
        std::process::exit(1);
    }
}
