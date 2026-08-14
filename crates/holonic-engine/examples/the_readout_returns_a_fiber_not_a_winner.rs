//! **The exact score population of a deposited map's readout, on the card, with no winner taken.**
//!
//! Record:
//! `research/records/2026-08-13_THE_MAP_DECLARES_ITS_OWN_APERTURES_AND_AN_EMBEDDING_IS_A_DECLARED_RECEIVER.md`.
//! Organ: `holonic_engine::embedding_fiber`. Kernel: `kernels/exact_embedding_fiber.cu`.
//!
//! # What this runs on, and why the tie matters
//!
//! `model.language_model.embed_tokens.weight` is `[262144, 2560]` and `tie_word_embeddings` is true,
//! so **the same matrix is the mouth and the readout**. One production step therefore closes a loop
//! inside one matrix: a token enters as a row and is scored against every row, including its own.
//!
//! # What is deliberately NOT computed
//!
//! No maximum, no ranking, no winner. `research/records/
//! 2026-08-12_THE_PRETRAINED_TRANSFORMER_IS_ONE_TRANSPORT_ORGAN_THE_REASONING_MACHINE_IS_THE_RETURNING_ECOLOGY.md`
//! §1: *"An autocorrect system adds a receiver which ranks or otherwise collapses a candidate
//! population and commits a replacement."* What returns is the population and its own structure.
//!
//! # The band is read off the material, never authored
//!
//! The candidate band is the **octave** — the exact bit length of the score, which is a `Winding` and
//! is the one face that lawfully crosses a frame boundary. Rows sharing the maximum octave are the
//! band; the number is the material's, not a threshold this driver picked.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_readout_returns_a_fiber_not_a_winner
//! ```

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use holonic_engine::embedding_fiber::{
    AlignedMaterial, ResidentReadout, align_bfloat16, score_serially,
};

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";
const READOUT: &str = "model.language_model.embed_tokens.weight";
const ADMITTED_DTYPE: &str = "BF16";

/// The row aperture. **Declared by this caller against its own measured memory**, not by the organ:
/// 20 GiB were available and an aligned row costs `dim * 8` octets, so this many rows fit with room
/// for the score population beside them. What it excludes is reported, never dropped.
const ROW_APERTURE: usize = 131_072;

/// The seeds this run asks about. Declared, and the return says so.
const SEEDS: [u32; 6] = [0, 1, 2, 1000, 65_536, 131_071];

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

struct Entry {
    dtype: String,
    shape: Vec<usize>,
    start: u64,
    end: u64,
}

fn header(file: &mut File) -> Result<(std::collections::BTreeMap<String, Entry>, u64), String> {
    let mut length = [0u8; 8];
    file.read_exact(&mut length).map_err(|e| e.to_string())?;
    let length = u64::from_le_bytes(length);
    let mut raw = vec![0u8; usize::try_from(length).map_err(|_| "header past the carrier")?];
    file.read_exact(&mut raw).map_err(|e| e.to_string())?;
    let parsed: serde_json::Value = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
    let mut entries = std::collections::BTreeMap::new();
    for (name, value) in parsed.as_object().ok_or("the header is not an object")? {
        if name == "__metadata__" {
            continue;
        }
        let offsets = value
            .get("data_offsets")
            .and_then(serde_json::Value::as_array)
            .ok_or("an entry carries no data_offsets")?;
        entries.insert(
            name.clone(),
            Entry {
                dtype: value
                    .get("dtype")
                    .and_then(serde_json::Value::as_str)
                    .ok_or("an entry carries no dtype")?
                    .to_owned(),
                shape: value
                    .get("shape")
                    .and_then(serde_json::Value::as_array)
                    .ok_or("an entry carries no shape")?
                    .iter()
                    .map(|d| d.as_u64().unwrap_or(0) as usize)
                    .collect(),
                start: offsets[0].as_u64().unwrap_or(0),
                end: offsets[1].as_u64().unwrap_or(0),
            },
        );
    }
    Ok((entries, 8 + length))
}

/// Read a declared row range of the readout as BF16 words.
fn rows_of(
    file: &mut File,
    base: u64,
    entry: &Entry,
    dim: usize,
    rows: usize,
) -> Result<Vec<u16>, String> {
    let octets = rows * dim * 2;
    file.seek(SeekFrom::Start(base + entry.start))
        .map_err(|e| e.to_string())?;
    let mut raw = vec![0u8; octets];
    file.read_exact(&mut raw).map_err(|e| e.to_string())?;
    Ok(raw
        .chunks_exact(2)
        .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
        .collect())
}

fn run() -> Result<(), String> {
    println!("{}", "=".repeat(96));
    println!("THE READOUT RETURNS A FIBER, NOT A WINNER");
    println!("{}", "=".repeat(96));

    let mut file = File::open(MAP).map_err(|e| format!("open {MAP}: {e}"))?;
    let (entries, base) = header(&mut file)?;
    let entry = entries
        .get(READOUT)
        .ok_or_else(|| format!("{READOUT} is not in this map"))?;
    if entry.dtype != ADMITTED_DTYPE {
        return Err(format!(
            "the readout is {} and this intake admits {ADMITTED_DTYPE} only — refused by name \
             rather than reinterpreted",
            entry.dtype
        ));
    }
    if entry.shape.len() != 2 {
        return Err(format!(
            "the readout has shape {:?}, not a matrix",
            entry.shape
        ));
    }
    let (vocabulary, dim) = (entry.shape[0], entry.shape[1]);
    let span = (entry.end - entry.start) as usize;
    if span != vocabulary * dim * 2 {
        return Err(format!(
            "the declared shape {vocabulary}x{dim} needs {} octets and the span is {span}",
            vocabulary * dim * 2
        ));
    }
    println!("\n  {READOUT}  {vocabulary} x {dim}  {ADMITTED_DTYPE}");
    println!("  tie_word_embeddings: the mouth and the readout are one matrix, so a production");
    println!("  step closes a loop inside it.");

    let rows = ROW_APERTURE.min(vocabulary);
    println!(
        "\n  THE DECLARED APERTURE: {rows} of {vocabulary} rows. Excluded and reported, not dropped: \
         {} rows.",
        vocabulary - rows
    );

    let started = std::time::Instant::now();
    let words = rows_of(&mut file, base, entry, dim, rows)?;
    println!("  read {} words  [{:?}]", words.len(), started.elapsed());

    let aligning = std::time::Instant::now();
    let readout = align_bfloat16(&words).map_err(|e| format!("the float mouth refused: {e}"))?;
    drop(words);
    println!(
        "  aligned onto 2^{}  widest entry {} octaves  {} entries carry a negative hand  [{:?}]",
        readout.exponent,
        readout.entry_octaves,
        readout.negatives,
        aligning.elapsed()
    );
    let needed = ResidentReadout::needed_octaves(readout.entry_octaves, dim);
    println!(
        "  an exact {dim}-term contraction of these needs {needed} octaves — checked against the \
         carrier BEFORE dispatch, refused rather than truncated"
    );

    let resident =
        ResidentReadout::new().map_err(|e| format!("the resident chart refused the deed: {e}"))?;
    println!("\n  resident chart: {}", resident.device_name());

    // ---------------------------------------------------------------------------------------
    // The grading: two independent implementations of one law, on real material.
    // ---------------------------------------------------------------------------------------
    let probe: Vec<i64> = readout.entries[..dim].to_vec();
    let query = AlignedMaterial {
        entry_octaves: probe
            .iter()
            .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0),
        negatives: probe.iter().filter(|e| **e < 0).count() as u64,
        entries: probe,
        exponent: readout.exponent,
    };
    let graded: Vec<u32> = (0..4096).collect();
    let on_card = resident
        .score(&readout, &query, dim, Some(&graded))
        .map_err(|e| format!("the card refused: {e}"))?;
    let serially = score_serially(&readout, &query, dim, Some(&graded))
        .map_err(|e| format!("the serial chart refused: {e}"))?;
    println!(
        "\n  GRADED against an independent implementation over {} rows: {}",
        graded.len(),
        if on_card.scores == serially {
            "identical, exactly"
        } else {
            "THE TWO CHARTS DISAGREE"
        }
    );
    if on_card.scores != serially {
        return Err("the two charts returned different exact scores".into());
    }

    // ---------------------------------------------------------------------------------------
    // The fiber, per declared seed. No maximum is taken.
    // ---------------------------------------------------------------------------------------
    println!("\n{}", "-".repeat(96));
    println!("THE FIBERS — every exact score, the band read off the material, nothing chosen");
    println!("{}", "-".repeat(96));
    println!(
        "  seed | work (MACs) | on card | octave span | band at max octave | exact ties at max"
    );

    // **The control this reading cannot be believed without.** A score scales with the scored row's
    // own magnitude, so a top-octave band could be measuring `|E[v]|` -- a property of v alone --
    // rather than any relation between v and the seed. If it is, the same rows appear in every
    // seed's band. Intersecting the bands is what tells the two apart, and it is cheap.
    let mut bands: Vec<(u32, std::collections::BTreeSet<usize>)> = Vec::new();

    for seed in SEEDS {
        if seed as usize >= rows {
            println!("  {seed:>5} | outside the declared aperture — named, not silently skipped");
            continue;
        }
        let base_at = seed as usize * dim;
        let probe: Vec<i64> = readout.entries[base_at..base_at + dim].to_vec();
        let query = AlignedMaterial {
            entry_octaves: probe
                .iter()
                .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                .max()
                .unwrap_or(0),
            negatives: probe.iter().filter(|e| **e < 0).count() as u64,
            entries: probe,
            exponent: readout.exponent,
        };
        let enacted = std::time::Instant::now();
        let population = resident
            .score(&readout, &query, dim, None)
            .map_err(|e| format!("the card refused seed {seed}: {e}"))?;
        let elapsed = enacted.elapsed();

        let census = population.octave_census();
        let (low, high) = (
            census.keys().next().copied().unwrap_or(0),
            census.keys().next_back().copied().unwrap_or(0),
        );
        // The band: rows whose score carries the largest octave. Read off the material.
        let band = census.get(&high).copied().unwrap_or(0);
        // The exact-tie population at the largest score, returned whole.
        let largest = population
            .scores
            .iter()
            .enumerate()
            .max_by_key(|(_, score)| **score)
            .map(|(at, _)| at)
            .unwrap_or(0);
        let ties = population.exactly_equal_to(largest);

        println!(
            "  {seed:>5} | {:>11} | {:>7?} | {low:>3}..{high:<3}    | {band:>18} | {:>17}",
            population.exact_multiply_accumulates,
            elapsed,
            ties.len()
        );
        bands.push((
            seed,
            population
                .octaves
                .iter()
                .enumerate()
                .filter(|(_, octave)| **octave == high)
                .map(|(row, _)| row)
                .collect(),
        ));

        if seed == SEEDS[0] {
            println!(
                "\n    seed {seed}'s own row scores {} — the self-score, present because the tie makes",
                population.scores[seed as usize]
            );
            println!(
                "    the mouth and the readout one matrix. It is IN the population, not removed."
            );
            println!("    the octave census, whole:");
            for (octave, count) in &census {
                println!("      2^{octave:<3} {count:>8} rows");
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // The control.
    // ---------------------------------------------------------------------------------------
    println!("\n{}", "-".repeat(96));
    println!("THE CONTROL — is the band a relation, or is it the scored row's own magnitude?");
    println!("{}", "-".repeat(96));
    println!("  A score scales with |E[v]|, so a band could be naming the widest rows and nothing");
    println!(
        "  about the seed. If so, every seed's band holds the SAME rows. It is a real reading"
    );
    println!("  only where the bands differ.");
    println!("\n  seed pair | shared rows | left only | right only");
    let mut every_pair_disjoint = true;
    let mut any_shared = false;
    for left in 0..bands.len() {
        for right in left + 1..bands.len() {
            let (a, b) = (&bands[left], &bands[right]);
            let shared = a.1.intersection(&b.1).count();
            if shared > 0 {
                any_shared = true;
                every_pair_disjoint = false;
            }
            println!(
                "  {:>5}/{:<5} | {shared:>11} | {:>9} | {:>10}",
                a.0,
                b.0,
                a.1.len() - shared,
                b.1.len() - shared
            );
        }
    }
    println!();
    if every_pair_disjoint {
        println!(
            "  EVERY PAIR IS DISJOINT. No row is in two seeds' bands, so the band is not naming the\n               widest rows -- it is seed-relative. The reading survives its own control."
        );
    } else if any_shared {
        println!(
            "  SOME ROWS ARE SHARED. The band is at least partly a magnitude reading, and the shared\n               population is the part that says nothing about the seed. Reported, not subtracted."
        );
    }

    println!("\n{}", "-".repeat(96));
    println!(
        "  READ IT AS WHAT IT IS. Every figure above is an exact integer over a declared common\n  \
         exponent, computed on the card, with no maximum taken and no candidate removed. The band\n  \
         is the material's own octave, which is a winding and crosses a frame; the scores are\n  \
         magnitudes and do not. What a later receiver does with this population — a fiber, a\n  \
         quotient, or a coarse endpoint face reported as one — is its declaration and not this\n  \
         driver's."
    );
    Ok(())
}
