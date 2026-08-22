//! **Does group content appear when the material is genuinely periodic?**
//!
//! Measured today: the transition monoid of this repository's prose is **aperiodic at both grains** —
//! 3,125 word generators over 25,030 classes and 164 character generators over 110,849, and **zero**
//! orbits of length above one in either. Every attractor is a single fixed point.
//!
//! That says the material is amorphous, and it leaves one question open that decides whether a
//! crystal can be **built**: is the aperiodicity a property of the *material*, or of the
//! *construction*? If periodic material produces group content, a crystal is a material choice and
//! the operator can aim for it. If periodic material is **also** aperiodic here, then `carry` — the
//! longest-suffix fallback — destroys periodicity by construction, and no material will ever give a
//! space group through this organ. That is the sharper finding and it forecloses the route.
//!
//! **The controls are declared and both arms are run.** A genuinely periodic sequence, a modular
//! arithmetic table with real cyclic structure, an aperiodic sequence as the negative control, and
//! prose as the reference.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{fiber_bytes, CausalLanguageEcology, CausalLanguagePassage};
use soma_abi::active::ActionCurrent;

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

/// A purely periodic sequence of period `p`. If any material has a `Z/p`, this does.
fn periodic(period: usize, length: usize) -> String {
    (0..length)
        .map(|at| (at % period).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// The additive group `Z/n` written out as a walk: every element followed by its successor. The
/// cyclic structure is the material's own, not an encoding of it.
fn modular_walk(modulus: u64, steps: usize) -> String {
    let mut held = Vec::with_capacity(steps * 2);
    let mut at = 0u64;
    for _ in 0..steps {
        held.push(format!("s{at}"));
        at = (at + 1) % modulus;
        held.push(format!("t{at}"));
    }
    held.join(" ")
}

/// Thue–Morse: aperiodic, cube-free, and the classical negative control for periodicity.
fn thue_morse(length: usize) -> String {
    (0..length)
        .map(|at: usize| (at.count_ones() % 2).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

struct Reading {
    classes: usize,
    generators: usize,
    mean_image: usize,
    nontrivial: usize,
    longest_cycle: usize,
}

fn census(name: &str, text: String) -> Result<Reading, String> {
    let passages = vec![CausalLanguagePassage::new(name, 1, text)];
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("{name}: conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();
    let classes = atlas.state_count();

    let mut vocabulary: BTreeMap<String, u16> = BTreeMap::new();
    {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity()).map_err(|e| format!("{e:?}"))?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            vocabulary.insert(token, at as u16);
        }
    }
    let mut indptr: Vec<u32> = vec![0];
    let mut germ: Vec<u16> = Vec::new();
    let mut target: Vec<u32> = Vec::new();
    let mut suffix: Vec<u32> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(u16, u32)> = atlas
            .outgoing(state)
            .into_iter()
            .map(|(g, t)| {
                (
                    vocabulary[&fiber_bytes(g.identity()).unwrap_or_default()],
                    t,
                )
            })
            .collect();
        rows.sort();
        for (index, reaches) in rows {
            germ.push(index);
            target.push(reaches);
        }
        indptr.push(germ.len() as u32);
        suffix.push(atlas.suffix_link(state).unwrap_or(0));
    }

    let carry = |state: u32, symbol: u16| -> u32 {
        let mut at = state;
        loop {
            let from = indptr[at as usize] as usize;
            let to = indptr[at as usize + 1] as usize;
            if let Some(slot) = (from..to).find(|slot| germ[*slot] == symbol) {
                return target[slot];
            }
            let parent = suffix[at as usize];
            if parent == at {
                return 0;
            }
            at = parent;
        }
    };

    let mut total_image = 0usize;
    let mut nontrivial = 0usize;
    let mut longest_cycle = 1usize;
    for symbol in 0..vocabulary.len() as u16 {
        let map: Vec<u32> = (0..classes as u32)
            .map(|state| carry(state, symbol))
            .collect();
        let image: BTreeSet<u32> = map.iter().copied().collect();
        total_image += image.len();
        let mut live = image.clone();
        for _ in 0..64 {
            let next: BTreeSet<u32> = live.iter().map(|s| map[*s as usize]).collect();
            if next.len() == live.len() {
                live = next;
                break;
            }
            live = next;
        }
        let mut seen: BTreeSet<u32> = BTreeSet::new();
        for start in &live {
            if seen.contains(start) {
                continue;
            }
            let mut length = 0usize;
            let mut at = *start;
            loop {
                seen.insert(at);
                at = map[at as usize];
                length += 1;
                if at == *start || length > live.len() {
                    break;
                }
            }
            if length > 1 {
                nontrivial += 1;
                longest_cycle = longest_cycle.max(length);
            }
        }
    }
    Ok(Reading {
        classes,
        generators: vocabulary.len(),
        mean_image: total_image / vocabulary.len().max(1),
        nontrivial,
        longest_cycle,
    })
}

fn run() -> Result<(), String> {
    let prose = std::fs::read_to_string("canon/TABLET_THE_COMPRESSION.md")
        .map_err(|error| format!("{error}"))?;
    let materials: Vec<(&str, String)> = vec![
        ("periodic, period 5", periodic(5, 4000)),
        ("periodic, period 7", periodic(7, 4000)),
        ("periodic, period 12", periodic(12, 4000)),
        ("Z/5 additive walk", modular_walk(5, 2000)),
        ("Z/12 additive walk", modular_walk(12, 2000)),
        ("Thue-Morse (aperiodic control)", thue_morse(4000)),
        ("prose (reference)", prose),
    ];

    println!("DOES GROUP CONTENT APPEAR WHEN THE MATERIAL IS PERIODIC?\n");
    println!(
        "  {:<34} {:>8} {:>7} {:>10} {:>10} {:>8}",
        "material", "classes", "gens", "mean image", "orbits>1", "longest"
    );
    let mut any = false;
    for (name, text) in materials {
        let reading = census(name, text)?;
        println!(
            "  {:<34} {:>8} {:>7} {:>10} {:>10} {:>8}",
            name,
            reading.classes,
            reading.generators,
            reading.mean_image,
            reading.nontrivial,
            reading.longest_cycle
        );
        if reading.nontrivial > 0 {
            any = true;
        }
    }
    println!();
    if any {
        println!(
            "  GROUP CONTENT APPEARS. Periodic material gives the monoid nontrivial orbits, so"
        );
        println!(
            "  aperiodicity is a property of the MATERIAL and not of the construction. A crystal"
        );
        println!("  is therefore a material choice an operator can aim for, and the orbit is the");
        println!("  symmetry that can be stored as a generator instead of enumerated.");
    } else {
        println!("  NO GROUP CONTENT ANYWHERE, INCLUDING IN PURELY PERIODIC MATERIAL.");
        println!("  So the aperiodicity is a property of the CONSTRUCTION, not of the material:");
        println!("  `carry` takes the longest matching suffix, and a longest-suffix map cannot");
        println!(
            "  permute — it either extends or falls, and both are monotone in matched length."
        );
        println!("  No material will yield a space group through this organ, and a crystal model");
        println!("  would need a DIFFERENT transport law rather than different material.");
        println!("  That forecloses the route by measurement, which is worth more than the plan.");
    }
    Ok(())
}
