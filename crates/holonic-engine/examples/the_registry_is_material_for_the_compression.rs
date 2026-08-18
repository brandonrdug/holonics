//! **The registry's own dependency graph as material for `receiver_exact_compression`.**
//!
//! ```text
//! python3 tools/registry_incidence.py
//! cargo run --release --example the_registry_is_material_for_the_compression
//! ```
//!
//! `CONSTRUCTION_STATE.md` carries a falsifier standing open since 2026-08-07: if coarse-graining
//! is genuinely the common method, then `receiver_exact_compression` must return the same *kind* of
//! artifact — a counted, exhibitable collapsed population with the shortest separating context — on
//! **materially unrelated sources**, and the shapes must differ. Identical shapes would mean the
//! instrument is reading itself rather than the material.
//!
//! This is one such source, and it is chosen because it is unrelated to every material the organ
//! has been run on: not a corpus, not a lattice, not a physical field, but **the registry's own
//! dependency graph**. Items are registry entries; the successor is "follow the k-th declared
//! dependency"; the receivers are the entry's grade and whether any Rust file cites it.
//!
//! **The material is generated, not authored.** `tools/registry_incidence.py` reads the registry
//! and greps the Rust tree, so no partition here can be arranged to come out pleasingly — which is
//! the defect `CLAUDE.md` names as the dangerous one, because it returns a green plural result.
//!
//! **What the reading is and is not.** A collapsed pair is two registry entries that no dependency
//! word separates under the declared receivers. That measures how much of the stated law is
//! distinguishable by grade and realization, and nothing deeper. It is a second frame for the
//! organ, not a discovery about mathematics.

use std::collections::BTreeMap;
use std::fs;

use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

/// One registry entry, read off the generated ledger.
struct Entry {
    id: String,
    grade: String,
    cited: bool,
    depends: Vec<String>,
}

struct Registry {
    entries: Vec<Entry>,
    by_id: BTreeMap<String, usize>,
    grades: BTreeMap<String, u64>,
    widest: usize,
}

impl Registry {
    fn read(text: &str) -> Self {
        let mut entries = Vec::new();
        for line in text.lines().skip(1) {
            let column: Vec<&str> = line.split('\t').collect();
            if column.len() < 5 {
                continue;
            }
            entries.push(Entry {
                id: column[0].to_owned(),
                grade: column[2].to_owned(),
                cited: column[3] == "1",
                depends: column[4]
                    .split(';')
                    .filter(|name| !name.is_empty())
                    .map(ToOwned::to_owned)
                    .collect(),
            });
        }
        let by_id = entries
            .iter()
            .enumerate()
            .map(|(at, entry)| (entry.id.clone(), at))
            .collect();
        let mut grades = BTreeMap::new();
        for entry in &entries {
            let next = u64::try_from(grades.len()).expect("a bounded grade vocabulary") + 1;
            grades.entry(entry.grade.clone()).or_insert(next);
        }
        let widest = entries
            .iter()
            .map(|entry| entry.depends.len())
            .max()
            .unwrap_or(0);
        Self {
            entries,
            by_id,
            grades,
            widest,
        }
    }
}

impl ObservedSystem for Registry {
    fn items(&self) -> Vec<ItemId> {
        (0..self.entries.len())
            .map(|at| ItemId(u64::try_from(at).expect("a bounded population")))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1)]
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.widest)
            .map(|slot| InputId(u64::try_from(slot).expect("a bounded arity")))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(entry) = self.entries.get(usize::try_from(item.0).unwrap_or(usize::MAX)) else {
            return Observation(0);
        };
        match receiver.0 {
            // The grade, as its own address inside the declared vocabulary. Never a magnitude:
            // the ordinals are assignment order and carry no order relation of their own.
            0 => Observation(self.grades.get(&entry.grade).copied().unwrap_or(0)),
            // Whether any Rust file names this entry.
            _ => Observation(u64::from(entry.cited)),
        }
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let entry = self
            .entries
            .get(usize::try_from(item.0).unwrap_or(usize::MAX))?;
        let name = entry
            .depends
            .get(usize::try_from(input.0).unwrap_or(usize::MAX))?;
        let at = self.by_id.get(name)?;
        Some(ItemId(u64::try_from(*at).ok()?))
    }
}

fn main() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../meta/REGISTRY_INCIDENCE.tsv");
    let Ok(text) = fs::read_to_string(path) else {
        println!("meta/REGISTRY_INCIDENCE.tsv is absent — run tools/registry_incidence.py first");
        return;
    };
    let registry = Registry::read(&text);
    println!("-- the material, generated and not authored --");
    println!("  registry entries          {}", registry.entries.len());
    println!("  declared grades           {}", registry.grades.len());
    println!("  widest dependency arity   {}", registry.widest);
    let cited = registry.entries.iter().filter(|entry| entry.cited).count();
    println!(
        "  cited from Rust           {cited} of {}",
        registry.entries.len()
    );

    let reading = compress(&registry);
    println!();
    println!("-- what the organ returns on this material --");
    println!("  one-shot blocks           {}", reading.one_shot.len());
    println!("  conduct blocks            {}", reading.conduct.len());
    println!("  collapsed pairs           {}", reading.collapsed.len());
    match reading.memory_order() {
        Some(order) => println!("  memory order              {order}"),
        None => println!("  memory order              none — a genuine zero, not a gap"),
    }

    println!();
    println!("-- the collapsed population, with what would have separated each pair --");
    let mut shown = 0usize;
    for pair in &reading.collapsed {
        if shown == 12 {
            println!(
                "  ... {} further pairs, all retained in the reading",
                reading.collapsed.len() - shown
            );
            break;
        }
        let left = &registry.entries[usize::try_from(pair.left.0).expect("in range")];
        let right = &registry.entries[usize::try_from(pair.right.0).expect("in range")];
        let word: Vec<String> = pair
            .distinguishing_word
            .iter()
            .map(|input| format!("dep{}", input.0))
            .collect();
        println!(
            "  {} ~ {}   grade {} / {}   word [{}]",
            left.id,
            right.id,
            left.grade,
            right.grade,
            word.join(" ")
        );
        shown += 1;
    }

    println!();
    println!("-- the falsifier this run is a second frame for --");
    println!("  CONSTRUCTION_STATE.md asks the same KIND of artifact on materially unrelated");
    println!("  sources, with DIFFERENT shapes. This material is a dependency graph over a");
    println!("  grade vocabulary; it shares no carrier with the canon-tablet runs. The shape to");
    println!("  compare is the triple (blocks, collapsed pairs, memory order) above.");
    println!();
    println!("  What this does NOT say: the collapsed population measures how much stated law is");
    println!("  distinguishable by grade and realization. It is not a claim about mathematics.");
}
