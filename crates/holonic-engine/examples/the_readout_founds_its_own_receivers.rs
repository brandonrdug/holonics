//! **The readout's own relation, with the receiver panel FOUNDED and the founding order read as a
//! group element.**
//!
//! Organs: `embedding_fiber` (the transport, exact, resident), `founded_receiver`
//! (`found_to_exhaustion`, `gyration`, `gyration_holonomy`), `receiver_exact_compression`.
//!
//! # What this fixes about its predecessor
//!
//! An earlier driver declared a probe panel and a construction basis by hand, then found by control
//! that the class ceiling was its own declaration. Two things were wrong and both have owners.
//!
//! **The panel is founded, not declared.** `found_to_exhaustion` grows a receiver panel at the
//! junctions the material leaves unwitnessed, with the axes read off the system's own successor
//! relation. This driver declares **one** receiver and lets the organ found the rest.
//!
//! **The successor comes from the map.** The predecessor's successor was "append a basis row" —
//! uniform over every item, so `continuation_aperture` and `conduct_reach` would have read nothing.
//! Here the successor is the readout's own relation: from a construction, the constructions it
//! places above others, **all of them retained in rank order, none committed**. That is the region
//! rather than a winner, and it is the map's structure rather than this driver's.
//!
//! # The notation
//!
//! ```text
//!   |t>          a construction: one row of the readout
//!   E            the transport: the deposited readout itself
//!   <p|E|t>      the face, exact
//!   successor    the rank-ordered relation those faces induce -- a RELATION, nothing chosen
//! ```
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_readout_founds_its_own_receivers
//! ```

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout, align_bfloat16};
use holonic_engine::founded_receiver::{
    AxisSpecies, FoundingPressure, found_to_exhaustion, gyration_of, gyration_holonomy,
};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";
const READOUT: &str = "model.language_model.embed_tokens.weight";
const ADMITTED_DTYPE: &str = "BF16";

/// Rows read. Declared against measured memory; the excluded population is reported.
const ROW_APERTURE: usize = 4_096;
/// How many rank slots the successor relation retains. **Every one is kept**: this is the region,
/// and a single slot would be the committed replacement the deposits refuse.
const RANK_SLOTS: usize = 4;

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

fn header(file: &mut File) -> Result<(BTreeMap<String, Entry>, u64), String> {
    let mut length = [0u8; 8];
    file.read_exact(&mut length).map_err(|e| e.to_string())?;
    let length = u64::from_le_bytes(length);
    let mut raw = vec![0u8; usize::try_from(length).map_err(|_| "header past the carrier")?];
    file.read_exact(&mut raw).map_err(|e| e.to_string())?;
    let parsed: serde_json::Value = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
    let mut entries = BTreeMap::new();
    for (name, value) in parsed.as_object().ok_or("the header is not an object")? {
        if name == "__metadata__" {
            continue;
        }
        let offsets = value
            .get("data_offsets")
            .and_then(serde_json::Value::as_array)
            .ok_or("no data_offsets")?;
        entries.insert(
            name.clone(),
            Entry {
                dtype: value.get("dtype").and_then(serde_json::Value::as_str).ok_or("no dtype")?.to_owned(),
                shape: value
                    .get("shape")
                    .and_then(serde_json::Value::as_array)
                    .ok_or("no shape")?
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

/// The readout as an observed system. **One declared receiver; the rest are founded.**
struct Readout {
    /// `successor[t][k]` — the k-th row the transport places above the others, from t.
    successor: Vec<Vec<Option<usize>>>,
    /// The one declared face: whether the construction's own row is inside its own region.
    /// Coarse on purpose — the panel is meant to be grown by the organ, not by this driver.
    self_in_region: Vec<u64>,
}

impl ObservedSystem for Readout {
    fn items(&self) -> Vec<ItemId> {
        (0..self.successor.len() as u64).map(ItemId).collect()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0)]
    }
    fn inputs(&self) -> Vec<InputId> {
        (0..RANK_SLOTS as u64).map(InputId).collect()
    }
    fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
        Observation(self.self_in_region[item.0 as usize])
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.successor[item.0 as usize][input.0 as usize].map(|at| ItemId(at as u64))
    }
}

fn run() -> Result<(), String> {
    println!("{}", "=".repeat(96));
    println!("THE READOUT FOUNDS ITS OWN RECEIVERS");
    println!("{}", "=".repeat(96));

    let mut file = File::open(MAP).map_err(|e| format!("open {MAP}: {e}"))?;
    let (entries, base) = header(&mut file)?;
    let entry = entries.get(READOUT).ok_or("the readout is not in this map")?;
    if entry.dtype != ADMITTED_DTYPE {
        return Err(format!("the readout is {} — refused by name", entry.dtype));
    }
    let (vocabulary, dim) = (entry.shape[0], entry.shape[1]);
    let rows = ROW_APERTURE.min(vocabulary);
    println!("\n  {READOUT}  {vocabulary} x {dim}  {ADMITTED_DTYPE}");
    println!("  aperture {rows} rows; excluded and reported: {} rows", vocabulary - rows);

    file.seek(SeekFrom::Start(base + entry.start)).map_err(|e| e.to_string())?;
    let mut raw = vec![0u8; rows * dim * 2];
    file.read_exact(&mut raw).map_err(|e| e.to_string())?;
    let words: Vec<u16> = raw.chunks_exact(2).map(|p| u16::from_le_bytes([p[0], p[1]])).collect();
    drop(raw);
    let readout = align_bfloat16(&words).map_err(|e| format!("the float mouth refused: {e}"))?;
    drop(words);

    let resident = ResidentReadout::new().map_err(|e| format!("the resident chart refused: {e}"))?;
    println!("  resident chart: {}", resident.device_name());

    // ---------------------------------------------------------------------------------------
    // The successor relation, read off the map. Every rank slot retained; nothing committed.
    // ---------------------------------------------------------------------------------------
    let transporting = std::time::Instant::now();
    let all: Vec<u32> = (0..rows as u32).collect();
    let mut successor = Vec::with_capacity(rows);
    let mut self_in_region = Vec::with_capacity(rows);
    for item in 0..rows {
        let base_at = item * dim;
        let entries_of = &readout.entries[base_at..base_at + dim];
        let query = AlignedMaterial {
            entry_octaves: entries_of.iter().map(|e| e.unsigned_abs().max(1).ilog2() + 1).max().unwrap_or(0),
            negatives: entries_of.iter().filter(|e| **e < 0).count() as u64,
            entries: entries_of.to_vec(),
            exponent: readout.exponent,
        };
        let population = resident
            .score(&readout, &query, dim, Some(&all))
            .map_err(|e| format!("the card refused item {item}: {e}"))?;
        // The rank order, exact. Ties break by row so the relation is a function of the material.
        let mut order: Vec<usize> = (0..rows).collect();
        order.sort_by(|a, b| population.scores[*b].cmp(&population.scores[*a]).then(a.cmp(b)));
        let region: Vec<usize> = order.into_iter().take(RANK_SLOTS).collect();
        self_in_region.push(u64::from(region.contains(&item)));
        successor.push(region.into_iter().map(Some).collect());
    }
    println!(
        "  {} constructions transported, region of {RANK_SLOTS} retained each  [{:?}]",
        rows,
        transporting.elapsed()
    );
    println!(
        "  constructions whose own row is inside their own region: {} of {rows}",
        self_in_region.iter().filter(|v| **v == 1).count()
    );

    let system = Readout { successor, self_in_region };

    // ---------------------------------------------------------------------------------------
    // The panel is FOUNDED. One receiver declared; the organ grows the rest.
    // ---------------------------------------------------------------------------------------
    println!("\n{}", "-".repeat(96));
    println!("THE FOUNDED PANEL — one receiver declared, the rest read off the material");
    println!("{}", "-".repeat(96));
    let founding = std::time::Instant::now();
    let panel = found_to_exhaustion(&system, &[]);
    println!(
        "  declared {} · founded {} · rounds {} · bound {}  [{:?}]",
        panel.declared.len(),
        panel.founded.len(),
        panel.rounds,
        panel.bound,
        founding.elapsed()
    );
    println!(
        "  one-shot before {} blocks -> after {} blocks · conduct {} blocks · unwitnessed remaining {}",
        panel.one_shot_before.blocks.len(),
        panel.one_shot_after.blocks.len(),
        panel.conduct.blocks.len(),
        panel.unwitnessed_remaining
    );
    println!("  exhausted: {}", panel.exhausted());
    let mut species: BTreeMap<&str, usize> = BTreeMap::new();
    let mut pressures: BTreeMap<&str, usize> = BTreeMap::new();
    for found in &panel.founded {
        *species
            .entry(match found.species {
                AxisSpecies::ContinuationAperture => "ContinuationAperture",
                AxisSpecies::ConductReach => "ConductReach",
            })
            .or_default() += 1;
        *pressures
            .entry(match found.pressure {
                FoundingPressure::Blindness { .. } => "Blindness",
                FoundingPressure::Congestion { .. } => "Congestion",
            })
            .or_default() += 1;
    }
    println!("  founded by species: {species:?}");
    println!("  founded under pressure: {pressures:?}");
    if !panel.refused.is_empty() {
        println!("  refusals ({}), first few:", panel.refused.len());
        for refusal in panel.refused.iter().take(4) {
            println!("    {refusal:?}");
        }
    }

    // ---------------------------------------------------------------------------------------
    // The founding ORDER as a group element. This is the group structure, computed.
    // ---------------------------------------------------------------------------------------
    println!("\n{}", "-".repeat(96));
    println!("THE FOUNDING ORDER AS A GROUP ELEMENT");
    println!("{}", "-".repeat(96));
    if panel.founded.len() < 2 {
        println!("  fewer than two junctions were founded; there is no order to vary, so the");
        println!("  question is not posed. That is a return about this material, not a failure.");
    } else {
        // A second order over the same panel: skip the first junction the first order took.
        let skipped = [panel.order()[0]];
        let other = found_to_exhaustion(&system, &skipped);
        let gyration = gyration_of(&panel, &other);
        println!(
            "  partitions agree {} · conduct agrees {} · founded the same {} · orbit trivial {}",
            gyration.partitions_agree,
            gyration.conduct_agrees,
            gyration.founded_agree,
            gyration.orbit_is_trivial()
        );
        println!("  is a holonomy (same arrival, different route): {}", gyration.is_holonomy());
        match gyration_holonomy(&gyration) {
            None => println!("  the two orders share no junction, so no walk is posed."),
            Some(holonomy) => {
                println!(
                    "  shared junctions {} · unshared {} · cycle type {:?} · even {} · trivial {}",
                    holonomy.shared.len(),
                    holonomy.unshared,
                    holonomy.cycle_type,
                    holonomy.is_even,
                    holonomy.is_trivial
                );
                if holonomy.is_trivial {
                    println!(
                        "\n  THE WALK CLOSED CARRYING NOTHING. The two founding orders founded the\n  \
                         shared population identically, so the gauge measured no orbit here."
                    );
                } else {
                    println!(
                        "\n  THE WALK CARRIES A PERMUTATION. Its conjugacy class is the invariant —\n  \
                         relabelling the junctions conjugates it and the cycle type does not move."
                    );
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // The conduct quotient, which founding must not have moved.
    // ---------------------------------------------------------------------------------------
    let compression = compress(&system);
    println!("\n{}", "-".repeat(96));
    println!(
        "  conduct blocks before founding {} · after {} — founding sharpens what is SEEN, never\n  \
         what the material DOES, and a difference here would be a defect rather than a finding.",
        compression.conduct.len(),
        panel.conduct.blocks.len()
    );
    println!(
        "  collapsed pairs the one declared receiver could not tell apart: {}",
        compression.collapsed.len()
    );
    Ok(())
}
