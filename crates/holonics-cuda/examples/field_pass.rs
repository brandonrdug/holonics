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
//! `FIELD_PROFILE` set, each kernel's launches and time and the run's copies and allocations.
#![allow(dead_code, clippy::disallowed_methods, clippy::disallowed_types, reason = "explicit exterior CLI file/process boundary")]

#[path = "../../holonics/examples/solenoidal_alpha.rs"]
mod exterior;

use holonics_cuda::hnn::{Card, CardField};
use std::error::Error;
use std::time::Instant;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn run(args: &[String]) -> Result<()> {
    let (mode, rest) = args.split_first().ok_or("field_pass parity|time|train complete-language COMMAND ARGS…")?;
    if mode == "yardstick" {
        return yardstick(rest);
    }
    if mode == "reserve" {
        return reserve(rest);
    }
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
    let memory = opened.census().memory;
    println!("FIELD_CARD_OPEN card={} free={} total={} batch_budget={}", opened.census().name, memory.free_bytes, memory.total_bytes, card.budget());
    let started = Instant::now();
    let result = match mode.as_str() {
        "parity" | "time" => exterior::run_field_parity(&rest[1..], &mut card),
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
    // [measurement; theory, November 12, P50 step 1 and P51] The clock's skin store: octets a reserved entry and a site, the support entries beside the
    // dense pairs, the largest batch's, the reservation's peak and its cut, and the card's free memory at the open (P52: a split is read as the
    // desktop's use of the card, never the build's).
    println!(
        "FIELD_SKIN octets_a_entry={} octets_a_site={} clock_octets_a_site={} entries={} dense_pairs={} peak_batch_entries={} peak_batch_dense_pairs={} peak_skin_store={} peak_store={} batch_cut={} free_at_open={}",
        t.skin_entry_octets, t.skin_site_octets, t.clock_site_octets, t.skin_entries, t.skin_dense_pairs, t.skin_peak_entries, t.skin_peak_pairs, t.skin_store, t.peak_store, t.batch_cut, memory.free_bytes
    );
    // [measurement; theory, November 13, P55 A2 and A3] The counting build's tally by entry, head, row and kind, its samples' counts, and the helpers'
    // yardsticks at the entries' launch shape (`RULER_SITES=rows,pace`, a launch's rows; not a `FIELD_` variable, which the store's commands refuse).
    #[cfg(feature = "ruler-calls")]
    {
        match card.ruler_tally() {
            Ok(t) => {
                for entry in 0..2 {
                    for h in 0..8 {
                        for open in 0..2 {
                            for k in 0..32 {
                                let v = t[((entry * 8 + h) * 2 + open) * 32 + k];
                                if v != 0 {
                                    println!("FIELD_TALLY entry={} head={h} row={} kind={k} calls={v}", ["rows", "pace"][entry], ["definite", "open"][open]);
                                }
                            }
                        }
                    }
                }
                for (k, c) in t[2 * 8 * 2 * 32..].iter().enumerate() {
                    println!("FIELD_SAMPLES kind={k} taken={c}");
                }
            }
            Err(e) => println!("FIELD_TALLY error={e}"),
        }
        // [measurement; theory, November 13, P56 item 3] The rows' fill: by head and row, the rows, chunks, met entries (the pairs) and K's quantiles.
        if let (Ok(fill), Ok(t)) = (card.ruler_fill(), card.ruler_tally()) {
            for h in 0..8 {
                for open in 0..2 {
                    let chunks = fill[h * 2 + open];
                    let k = &fill[16 + (h * 2 + open) * 4096..16 + (h * 2 + open + 1) * 4096];
                    let rows: u64 = k.iter().sum();
                    if rows == 0 {
                        continue;
                    }
                    let q = |f: f64| {
                        let mut acc = 0u64;
                        (0..4096).find(|&b| {
                            acc += k[b];
                            acc as f64 >= f * rows as f64
                        }).unwrap_or(4095)
                    };
                    let max = (0..4096).rev().find(|&b| k[b] > 0).unwrap_or(0);
                    let met = t[((0 * 8 + h) * 2 + open) * 32 + 2];
                    let crowds = t[((0 * 8 + h) * 2 + open) * 32 + 4];
                    println!(
                        "FIELD_FILL head={h} row={} rows={rows} chunks={chunks} met={met} fill={:.4} k_median={} k_q90={} k_q99={} k_max={max} live_crowds={crowds} live_crowds_a_row={:.3} live_crowds_max={}",
                        ["definite", "open"][open],
                        met as f64 / (32.0 * chunks.max(1) as f64),
                        q(0.5),
                        q(0.9),
                        q(0.99),
                        crowds as f64 / rows as f64,
                        if open == 0 { fill[16 + 8 * 2 * 4096 + h] } else { 0 }
                    );
                }
            }
        }
        let at: Vec<u64> = std::env::var("RULER_SITES").ok().map(|v| v.split(',').filter_map(|x| x.parse().ok()).collect()).unwrap_or_default();
        if let [rows, pace] = at[..] {
            match card.helper_yardsticks(rows, pace, 0.5) {
                Ok(v) => {
                    for (kind, blocks, reps, took, warps, lanes) in v {
                        println!(
                            "FIELD_HELPER kind={kind} blocks={blocks} threads_a_block=128 reps={reps} seconds={took:.4} warp_issues={warps} lane_calls={lanes} ns_a_warp_issue={:.4} ns_a_lane_call={:.5}",
                            took * 1e9 / warps as f64,
                            took * 1e9 / lanes as f64
                        );
                    }
                }
                Err(e) => println!("FIELD_HELPER error={e}"),
            }
        }
    }
    if let Some(phases) = card.phased() {
        for (name, marks, ns) in phases {
            println!("FIELD_PHASE name={name} marks={marks} ms={} us_a_mark={}", ns / 1_000_000, ns / 1_000 / (marks as u128).max(1));
        }
    }
    if let Some(p) = card.profiled() {
        let kernels: u128 = p.kernels.values().map(|v| v.1).sum();
        for (entry, (calls, ns)) in &p.kernels {
            let threads = p.threads.get(entry).copied().unwrap_or(0);
            println!("FIELD_PROFILE entry={entry} launches={calls} ms={} us_a_launch={} grid_threads={threads} mean_grid_threads={}", ns / 1_000_000, ns / 1_000 / (*calls as u128).max(1), threads / (*calls as u128).max(1));
        }
        // [measurement; theory, November 12, P50 step 0] The launches made a head at a time, by head, with the head's kind and
        // the pairs its forward contact met.
        for (h, pairs) in p.pairs_by_head.iter().enumerate() {
            println!("FIELD_PROFILE_PAIRS head={h} kind={} pairs={pairs}", p.head_kinds.get(h).copied().unwrap_or("-"));
        }
        for ((entry, h), (calls, ns)) in &p.by_head {
            let pairs = p.pairs_by_head.get(*h as usize).copied().unwrap_or(0);
            println!(
                "FIELD_PROFILE_HEAD entry={entry} head={h} kind={} launches={calls} us={} pairs={pairs} ns_a_pair_milli={}",
                p.head_kinds.get(*h as usize).copied().unwrap_or("-"),
                ns / 1_000,
                ns * 1_000 / pairs.max(1)
            );
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

/// [measurement; theory, November 12, P50 step 0b] `field_pass yardstick [ENTRIES] [SECONDS]`: the card's yardsticks
/// ([`CardField::yardsticks`]), narrow products a second and octets a second, each timed alone to at least SECONDS (default 1.5)
/// of the card's time; ENTRIES (default 209) is a gathered row's count of entries of eight words.
fn yardstick(args: &[String]) -> Result<()> {
    let entries: u32 = args.first().map(|a| a.parse()).transpose()?.unwrap_or(209);
    let seconds: f64 = args.get(1).map(|a| a.parse()).transpose()?.unwrap_or(1.5);
    let opened = Card::open(0)?;
    let card = CardField::open(&opened)?;
    let y = card.yardsticks(entries, seconds)?;
    println!("YARDSTICK card={} multiprocessors={} product_blocks={} stream_blocks={} threads_a_block=256", opened.census().name, y.multiprocessors, y.product_blocks, y.stream_blocks);
    for (name, (rate, count, took)) in [("products_cell", y.cell), ("products_tile", y.tile)] {
        println!("YARDSTICK reading={name} map=64x64 products={count} seconds={took:.4} products_a_second={rate:.4e}");
    }
    for (name, (rate, count, took)) in [("read_in_order", y.read), ("write_in_order", y.write)] {
        println!("YARDSTICK reading={name} store_octets={} octets={count} seconds={took:.4} octets_a_second={rate:.4e}", y.store_octets);
    }
    let (rate, count, took) = y.gather;
    println!("YARDSTICK reading=gather_eight_words rows={} entries={} octets_a_gather=32 octets={count} seconds={took:.4} octets_a_second={rate:.4e} gathers_a_second={:.4e}", y.gather_rows, y.gather_entries, rate / 32.0);
    Ok(())
}

/// [measurement; theory, November 12, P51] `field_pass reserve KEY=VALUE…` (a STORE_DECLARATION line's fields: alphabet, lanes, lane_width, heads,
/// still, modes, contacts, carry, triads, ticks, frames, reach): the reservation of a training region (a return) as its coefficients, a region of `S`
/// sites, `D` definite, needing `pair S² + site S + region + entry S (near_slots + D) + crowd_site S` octets ([`holonics_cuda::hnn::field::read_octets`],
/// [`holonics_cuda::hnn::field::skin_octets`]). Host arithmetic, no card.
fn reserve(args: &[String]) -> Result<()> {
    use holonics::hnn::tower::field::FieldDeclaration;
    use holonics_cuda::hnn::field::{read_octets, skin_octets};
    let kv: std::collections::HashMap<&str, usize> = args.iter().filter_map(|a| a.split_once('=')).filter_map(|(k, v)| v.parse().ok().map(|v| (k, v))).collect();
    let get = |k: &str| kv.get(k).copied().ok_or_else(|| format!("reserve: {k}= is owed"));
    let d = FieldDeclaration { alphabet: get("alphabet")?, width: get("lanes")? * get("lane_width")?, heads: get("heads")?, modes: get("modes")?, still: get("still")?, contacts: get("contacts")?, ticks: get("ticks")?, frames: get("frames")?, reach: get("reach")?, lanes: get("lanes")?, depth: kv.get("depth").copied().unwrap_or(0), carry: get("carry")?, triads: get("triads")? };
    let f = |s: usize| read_octets(&d, true, false, s);
    let (f1, f2, f3) = (f(1), f(2), f(3));
    let pair = (f3 + f1 - 2 * f2) / 2;
    let site = f2 - f1 - 3 * pair;
    let region = f1 - pair - site;
    assert_eq!(f(1000), pair * 1_000_000 + site * 1000 + region, "the reservation is quadratic in a region's sites");
    let (_, entry, crowd_site, clock_site) = skin_octets(&d, 0, 0);
    println!("RESERVE pair={pair} site={site} region={region} entry={entry} crowd_site={crowd_site} clock_site={clock_site} near_slots={}", 2 * (holonics::hnn::tower::field::NEAR - 1));
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(error) = run(&args) {
        eprintln!("field_pass: {error}");
        std::process::exit(1);
    }
}
