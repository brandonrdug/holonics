//! **The goal, on foreign material: the map arrives, lands where it lands, deposits, and a later
//! arrival rides the deposit — with the withdrawal control that makes the difference attributable.**
//!
//! `the_later_current_rides_the_deposit` runs this loop on the machine's own text. This runs it on
//! `/home/b/models/gemma-4-E4B-it/model.safetensors`, so the arrival is material the machine did
//! not author.
//!
//! # What enters, and at what grain
//!
//! Not scores, not a spectrum, not a frozen edge.
//! `archive/cpp-engine/evidence/observations/eros-transformer-seeded-regional-ecology-01/RESULTS.md`
//! rejected freezing a finished outcome into a cell: *"Preserving that finished winner does not
//! preserve the ecology which selected it."* So what enters is the **material itself** — the map's
//! own octets, cut by a declared codec into patches — through the mouth the grain rotation opened on
//! 2026-08-13. `Patch { octets, identity }` takes any carrier; text was only ever one of them.
//!
//! The identity is the codec's declaration of what makes two patches the same patch. Here it is the
//! **octave of the aligned entry** — an integer, a winding, the one face that crosses a frame
//! boundary. A magnitude would not cross it and is not used as an identity.
//!
//! # The loop, and the two controls
//!
//! ```text
//!   1  admit A (rows of one region of the map)   -> what it deposited
//!   1b the attachment                            -> both outcomes retained; it did not choose
//!   2  admit B (rows of a different region)      -> B's reading WITH A standing
//!   3  withdraw A                                -> bit-identical to base, or this run is void
//!   4  admit B on base                           -> B's reading WITHOUT the deposit
//!   5  compare                                   -> the difference is what B rode
//! ```
//!
//! Step 3 is what makes step 5 mean anything; step 4 is the negative control. If the two readings of
//! B agree in every coordinate, B rode nothing and this driver says so.
//!
//! ```text
//! cargo run --release -p life --example the_map_deposits_and_a_later_current_rides_it
//! ```

use std::collections::BTreeSet;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use holonic_engine::embedding_fiber::align_bfloat16;
use holonic_engine::running_integral::CoefficientGroup;
use life::incidence_production::{
    ArrivalResponse, DeclaredOccurrence, IncidenceComplex, Patch, PhaseChart,
};

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";
const READOUT: &str = "model.language_model.embed_tokens.weight";
const ADMITTED_DTYPE: &str = "BF16";

/// How many inscription patches of each occurrence participate. A caller declaration; the excluded
/// population is returned by the complex.
const DECLARED_EXTENT: usize = 8;

/// How many rows of the map each occurrence carries, and how many entries of a row make one patch.
/// Both are this caller's declaration against its own memory.
const ROWS_PER_OCCURRENCE: usize = 3;
const ENTRIES_PER_PATCH: usize = 320;

/// The three regions of the map this run reads. Disjoint, declared, and named in the return.
const BASE_ROWS: [usize; 6] = [0, 1, 2, 3, 4, 5];
const DEPOSIT_ROWS: [usize; 3] = [1_024, 1_025, 1_026];
const LATER_ROWS: [usize; 3] = [2_048, 2_049, 2_050];

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

struct Reading {
    new_constituents: usize,
    new_contacts: usize,
    founded: usize,
    dissolved: usize,
    reached: usize,
    reopened: usize,
    saturated: usize,
    untouched: usize,
    moved: usize,
}

fn read(response: &ArrivalResponse) -> Reading {
    Reading {
        new_constituents: response.new_constituents,
        new_contacts: response.new_contacts,
        founded: response.founded.len(),
        dissolved: response.dissolved.len(),
        reached: response.reached.len(),
        reopened: response.reopened.len(),
        saturated: response.saturated.len(),
        untouched: response.untouched.len(),
        moved: response.moved().len(),
    }
}

fn print_reading(label: &str, reading: &Reading) {
    println!(
        "  {label}\n    constituents {} · contacts {} · founded {} · dissolved {}\n    reached {} \
         · reopened {} · saturated {} · untouched {} · earlier successors MOVED {}",
        reading.new_constituents,
        reading.new_contacts,
        reading.founded,
        reading.dissolved,
        reading.reached,
        reading.reopened,
        reading.saturated,
        reading.untouched,
        reading.moved
    );
}

struct MapReader {
    file: File,
    base: u64,
    start: u64,
    dim: usize,
}

impl MapReader {
    fn open() -> Result<Self, String> {
        let mut file = File::open(MAP).map_err(|e| format!("open {MAP}: {e}"))?;
        let mut length = [0u8; 8];
        file.read_exact(&mut length).map_err(|e| e.to_string())?;
        let length = u64::from_le_bytes(length);
        let mut raw = vec![0u8; usize::try_from(length).map_err(|_| "header past the carrier")?];
        file.read_exact(&mut raw).map_err(|e| e.to_string())?;
        let parsed: serde_json::Value =
            serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
        let entry = parsed
            .get(READOUT)
            .ok_or("the readout is not in this map")?;
        let dtype = entry
            .get("dtype")
            .and_then(serde_json::Value::as_str)
            .ok_or("no dtype")?;
        if dtype != ADMITTED_DTYPE {
            return Err(format!("the readout is {dtype} — refused by name"));
        }
        let shape: Vec<usize> = entry
            .get("shape")
            .and_then(serde_json::Value::as_array)
            .ok_or("no shape")?
            .iter()
            .map(|d| d.as_u64().unwrap_or(0) as usize)
            .collect();
        let offsets = entry
            .get("data_offsets")
            .and_then(serde_json::Value::as_array)
            .ok_or("no data_offsets")?;
        Ok(Self {
            file,
            base: 8 + length,
            start: offsets[0].as_u64().unwrap_or(0),
            dim: shape[1],
        })
    }

    /// One row of the map, aligned exactly through the declared float mouth, cut into patches.
    ///
    /// **The patch identity is the OCTAVE of the aligned entry** — an integer, a winding, which is
    /// what crosses a frame boundary. The octets are the material's own; nothing is normalised and
    /// nothing is rounded.
    fn patches(&mut self, row: usize) -> Result<Vec<Patch>, String> {
        self.file
            .seek(SeekFrom::Start(
                self.base + self.start + (row * self.dim * 2) as u64,
            ))
            .map_err(|e| e.to_string())?;
        let mut raw = vec![0u8; self.dim * 2];
        self.file.read_exact(&mut raw).map_err(|e| e.to_string())?;
        let words: Vec<u16> = raw
            .chunks_exact(2)
            .map(|p| u16::from_le_bytes([p[0], p[1]]))
            .collect();
        let aligned = align_bfloat16(&words).map_err(|e| format!("the float mouth refused: {e}"))?;
        let mut patches = Vec::new();
        for (slot, chunk) in aligned.entries.chunks(ENTRIES_PER_PATCH).enumerate() {
            let widest = chunk
                .iter()
                .map(|e| if *e == 0 { 0 } else { e.unsigned_abs().ilog2() + 1 })
                .max()
                .unwrap_or(0);
            let negatives = chunk.iter().filter(|e| **e < 0).count();
            let octets: Vec<u8> = raw
                [slot * ENTRIES_PER_PATCH * 2..((slot + 1) * ENTRIES_PER_PATCH * 2).min(raw.len())]
                .to_vec();
            if octets.is_empty() {
                continue;
            }
            // The identity is two windings: the octave span and the negative-hand count. Both are
            // integers read off the material, and neither is a magnitude.
            patches.push(
                Patch::new(octets, format!("o{widest}h{negatives}"))
                    .map_err(|e| format!("the patch refused: {e:?}"))?,
            );
        }
        Ok(patches)
    }

    fn occurrence(
        &mut self,
        identity: &str,
        ordinal: u64,
        caused_by: BTreeSet<String>,
        rows: &[usize],
    ) -> Result<DeclaredOccurrence, String> {
        let mut inscription = Vec::new();
        for row in rows {
            inscription.extend(self.patches(*row)?);
        }
        Ok(DeclaredOccurrence {
            identity: identity.to_owned(),
            storage_ordinal: ordinal,
            caused_by,
            inscription,
        })
    }
}

fn run() -> Result<(), String> {
    let chart = PhaseChart::WindingAdjacent;
    let group = CoefficientGroup::Integers;
    let mut map = MapReader::open()?;

    println!("{}", "=".repeat(96));
    println!("THE MAP DEPOSITS, AND A LATER CURRENT RIDES IT");
    println!("{}", "=".repeat(96));
    println!(
        "\n  material: {READOUT} of {MAP}\n  the arrival is the map's own octets, cut by a declared \
         codec; the patch identity is a pair of windings"
    );

    // -- the standing terrain -----------------------------------------------------------------
    let mut material = Vec::new();
    for (slot, row) in BASE_ROWS.chunks(ROWS_PER_OCCURRENCE).enumerate() {
        material.push(map.occurrence(
            &format!("base-{slot}"),
            slot as u64,
            BTreeSet::new(),
            row,
        )?);
    }
    let base = IncidenceComplex::found(&material, DECLARED_EXTENT)
        .map_err(|e| format!("found the base complex: {e:?}"))?;
    println!("\nTHE STANDING TERRAIN");
    println!(
        "  {} constituents · {} contacts · {} closed boundaries · {} ⪯ edges",
        base.sites().len(),
        base.bonds().len(),
        base.compounds().len(),
        base.dependencies().len()
    );
    println!(
        "  the aperture returned its outside: {} patches present and not admitted",
        base.patches_outside_extent()
    );

    // -- 1 · the deposit ----------------------------------------------------------------------
    println!("\n1 · THE MAP ARRIVES");
    let a = map.occurrence("deposit", 100, BTreeSet::new(), &DEPOSIT_ROWS)?;
    let a_response = base
        .admit_later(&a, chart, &group)
        .map_err(|e| format!("admit the deposit: {e:?}"))?;
    let a_reading = read(&a_response);
    print_reading("A = rows 1024..1026 of the map", &a_reading);
    if a_reading.new_constituents == 0 && a_reading.new_contacts == 0 && a_reading.founded == 0 {
        println!(
            "\n  IT FLOATED. reached {} · saturated {} · untouched {} — the passage deposited \
             nothing, so nothing passed. That is the return, not a failure to engineer away.",
            a_reading.reached, a_reading.saturated, a_reading.untouched
        );
        return Ok(());
    }
    let with_deposit = a_response.complex.clone();

    // -- 1b · it did not choose where it landed ------------------------------------------------
    println!("\n1b · WHERE IT LANDED WAS NOT ITS OWN CHOICE");
    let attempts = with_deposit.attachment(&a_response.trace);
    let met = attempts.iter().filter(|a| a.connected).count();
    println!(
        "  {} upward attempts from the standing terrain · {met} met · {} did not",
        attempts.len(),
        attempts.len() - met
    );
    if attempts.is_empty() {
        return Err("the terrain reached for nothing; the arrival landed passively".into());
    }

    // -- 2 · the later current, WITH the deposit standing ---------------------------------------
    println!("\n2 · A LATER CURRENT, WITH THE DEPOSIT STANDING");
    let b = map.occurrence("later", 200, BTreeSet::new(), &LATER_ROWS)?;
    let with = with_deposit
        .admit_later(&b, chart, &group)
        .map_err(|e| format!("admit the later current: {e:?}"))?;
    let with_reading = read(&with);
    print_reading("B on (base + A)", &with_reading);

    // -- 3 · the withdrawal control -------------------------------------------------------------
    println!("\n3 · THE WITHDRAWAL — the control that makes step 5 mean anything");
    let restored = with_deposit
        .withdraw(&a_response.trace)
        .map_err(|e| format!("withdraw the deposit: {e:?}"))?;
    let exact = restored.sites() == base.sites()
        && restored.bonds() == base.bonds()
        && restored.compounds() == base.compounds()
        && restored.dependencies() == base.dependencies();
    println!("  the complex returned bit-identical to the base: {exact}");
    if !exact {
        return Err(
            "the withdrawal was not exact, so any difference below could be a damaged complex \
             rather than a missing deposit. This run is void."
                .into(),
        );
    }

    // -- 4 · the later current, WITHOUT the deposit ---------------------------------------------
    println!("\n4 · THE SAME LATER CURRENT, WITHOUT THE DEPOSIT");
    let without = restored
        .admit_later(&b, chart, &group)
        .map_err(|e| format!("admit the later current on base: {e:?}"))?;
    let without_reading = read(&without);
    print_reading("B on base", &without_reading);

    // -- 5 · what B rode ------------------------------------------------------------------------
    println!("\n{}", "-".repeat(96));
    println!("5 · WHAT THE LATER CURRENT RODE");
    println!("{}", "-".repeat(96));
    let moved = with_reading.new_constituents != without_reading.new_constituents
        || with_reading.new_contacts != without_reading.new_contacts
        || with_reading.founded != without_reading.founded
        || with_reading.dissolved != without_reading.dissolved
        || with_reading.reached != without_reading.reached
        || with_reading.reopened != without_reading.reopened
        || with_reading.saturated != without_reading.saturated
        || with_reading.untouched != without_reading.untouched
        || with_reading.moved != without_reading.moved;
    println!(
        "  reached   {} with · {} without\n  reopened  {} with · {} without\n  contacts  {} with · \
         {} without\n  founded   {} with · {} without\n  saturated {} with · {} without\n  \
         untouched {} with · {} without\n  moved     {} with · {} without",
        with_reading.reached,
        without_reading.reached,
        with_reading.reopened,
        without_reading.reopened,
        with_reading.new_contacts,
        without_reading.new_contacts,
        with_reading.founded,
        without_reading.founded,
        with_reading.saturated,
        without_reading.saturated,
        with_reading.untouched,
        without_reading.untouched,
        with_reading.moved,
        without_reading.moved
    );
    if !moved {
        println!(
            "\n  THE TWO READINGS AGREE IN EVERY COORDINATE. B did not ride A's deposit. The loop \
             ran, the withdrawal was exact, and the answer is negative — reported rather than \
             engineered away."
        );
        return Ok(());
    }

    // The named difference: which constituents B reached only because A stood.
    let reached_with: BTreeSet<_> = with.reached.iter().collect();
    let reached_without: BTreeSet<_> = without.reached.iter().collect();
    let only_with: Vec<_> = reached_with.difference(&reached_without).collect();
    println!(
        "\n  B reached {} compounds only because A stood; A itself deposited {} new constituents \
         and {} new contacts into the terrain.",
        only_with.len(),
        a_reading.new_constituents,
        a_reading.new_contacts
    );
    if with_reading.reached > without_reading.reached || with_reading.reopened > without_reading.reopened {
        println!(
            "\n  THE LATER CURRENT RODE THE DEPOSIT: it reached or reopened more with A standing \
             than without, and the withdrawal was exact."
        );
    } else if with_reading.untouched > without_reading.untouched {
        println!(
            "\n  THE READINGS DIFFER, AND THE DIFFERENCE IS THE OPPOSITE OF A RIDE. With A standing \
             the later arrival leaves {} compounds UNTOUCHED against {} without — so A's deposit \
             added terrain the later current did not reach at all. `THE_INFORMATION_ENGINE` §5: \
             perception is landing, and unreached material is not perceived. The deposit stands and \
             is inert to this arrival.",
            with_reading.untouched, without_reading.untouched
        );
    } else {
        println!(
            "\n  THE READINGS DIFFER, but not in reached or reopened. Named above; not a ride."
        );
    }
    Ok(())
}
