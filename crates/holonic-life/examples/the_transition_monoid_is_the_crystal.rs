//! **THE CRYSTAL — what the material's own inference dynamics converge to, with nothing imposed.**
//!
//! Brandon, 2026-08-18: *"What would happen if we used actual inference with I/O about an embedding
//! space with forward and shifting throughout junctions? Emergent charts of the embedding space, as
//! opposed to constraining them to arbitrary techniques and layer-types and needing to manually
//! impose all of these dimensionalities… we could as operators focus the machine during its training
//! into a perfectly crafted **crystal** model that diffuses information on a hyper efficient scale."*
//!
//! # The object
//!
//! *Forward and shifting through junctions* is one operator: `carry` takes a forward transition when
//! the channel conducts and **arcs down a suffix link** when it does not. So each germ `a` is a
//! **total function** `f_a` on all classes, and the germs generate a **transformation monoid** — the
//! syntactic monoid of the material. That monoid is the material's algebra, and it is what a crystal
//! is made of: a space group is a monoid too, and a crystal is compressible because the whole
//! structure is a unit cell plus a group action rather than an enumeration of sites.
//!
//! **Nothing here is imposed.** No layer type, no head count, no dimension. Every quantity below is
//! a property of `f_a` and is read, not chosen.
//!
//! # What is measured, and why each is the question
//!
//! - **`|image(f_a)|`** — how far one symbol contracts the whole state space. This is diffusion in
//!   one step, exactly.
//! - **The eventual image** `f_a^∞` — the attractor. Repeated application stabilises, and what it
//!   stabilises onto is the chart that symbol's dynamics live in. **These are the emergent charts.**
//! - **The index** — how many applications until it stabilises. The mixing time.
//! - **The cycle structure on the eventual image** — `f_a` restricted to its attractor is a
//!   permutation, and its cycle lengths are **group content**. A cycle longer than one is a `ℤ/p`
//!   acting: real symmetry, storable as a generator instead of an enumeration. All cycles of length
//!   one means the monoid is **aperiodic** at this generator — no group content, and the material is
//!   amorphous rather than crystalline in that direction.
//! - **The union of every attractor** — if it is small, the machine lives in a small set after one
//!   token and everything outside is transient. That number is the compression.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{fiber_bytes, CausalLanguageEcology, CausalLanguagePassage};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("docs/canon/THE_DOCUMENT_LAW.md", 1),
    ("docs/canon/TABLET_THE_OPERATIONS.md", 2),
    ("docs/canon/THE_RECOVERED_LAW.md", 3),
    ("docs/canon/TABLET_THE_COMPRESSION.md", 4),
];

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

/// The transport as flat integer arrays — the same three tensors ATHENA-001 emits.
struct Transport {
    indptr: Vec<u32>,
    germ: Vec<u16>,
    target: Vec<u32>,
    suffix: Vec<u32>,
    classes: usize,
}

impl Transport {
    /// **`carry` — forward while the channel conducts, arc down a suffix link when it does not.**
    /// Total on every class, which is what makes the germs generate a monoid.
    fn carry(&self, state: u32, germ: u16) -> u32 {
        let mut at = state;
        loop {
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            if let Some(slot) = (from..to).find(|slot| self.germ[*slot] == germ) {
                return self.target[slot];
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                return 0;
            }
            at = parent;
        }
    }

    /// `f_a` as a total map on every class.
    fn map_of(&self, germ: u16) -> Vec<u32> {
        (0..self.classes as u32)
            .map(|state| self.carry(state, germ))
            .collect()
    }
}

/// The eventual image of a transformation, its index, and the cycle structure on the attractor.
///
/// Iterating a finite transformation stabilises: `im(f) ⊇ im(f²) ⊇ …` must halt, and on the stable
/// set `f` is a **permutation**. That set is the attractor and those cycles are the group content.
fn attractor(map: &[u32]) -> (BTreeSet<u32>, usize, BTreeMap<usize, usize>) {
    let mut live: BTreeSet<u32> = map.iter().copied().collect();
    let mut index = 1usize;
    loop {
        let next: BTreeSet<u32> = live.iter().map(|state| map[*state as usize]).collect();
        if next.len() == live.len() {
            live = next;
            break;
        }
        live = next;
        index += 1;
        if index > 64 {
            break;
        }
    }
    // On the stable set `f` permutes. Read its cycle lengths.
    let mut cycles: BTreeMap<usize, usize> = BTreeMap::new();
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
            if at == *start {
                break;
            }
            if length > live.len() {
                break;
            }
        }
        *cycles.entry(length).or_default() += 1;
    }
    (live, index, cycles)
}

/// Split by the declared grain. **The grain decides what a germ is**, and the monoid is a property
/// of the germs, so this is the one declaration the whole census rests on.
fn segment(text: &str, grain: Grain) -> String {
    match grain {
        Grain::Word => text.to_owned(),
        // Whitespace-separated single characters: the tokenizer downstream splits on whitespace, so
        // spacing every character makes each one a germ. `exposure_codec::ladder` founds the
        // CHARACTER codec exactly on this repository's records, so this is the founded grain rather
        // than an invented one.
        Grain::Character => text
            .chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join(" "),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Grain {
    Word,
    Character,
}

fn run() -> Result<(), String> {
    for grain in [Grain::Word, Grain::Character] {
        let label = if grain == Grain::Word {
            "WORD GRAIN"
        } else {
            "CHARACTER GRAIN"
        };
        println!("\n================ {label} ================\n");
        census(grain)?;
    }
    Ok(())
}

fn census(grain: Grain) -> Result<(), String> {
    let mut passages = Vec::new();
    for (path, receiver) in MATERIAL {
        let raw = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        let text = segment(&raw, grain);
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas: &ExactSuffixEcology = ecology.global_suffix();
    let classes = atlas.state_count();

    // ---- lay the transport flat, exactly as the container carries it ----
    let mut vocabulary: BTreeMap<String, u16> = BTreeMap::new();
    let mut surfaces: Vec<String> = Vec::new();
    {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity()).map_err(|e| format!("{e:?}"))?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            vocabulary.insert(token.clone(), at as u16);
            surfaces.push(token);
        }
    }
    let mut indptr: Vec<u32> = vec![0];
    let mut germ: Vec<u16> = Vec::new();
    let mut target: Vec<u32> = Vec::new();
    let mut suffix: Vec<u32> = Vec::with_capacity(classes);
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(u16, u32)> = atlas
            .outgoing(state)
            .into_iter()
            .map(|(g, t)| {
                let token = fiber_bytes(g.identity()).unwrap_or_default();
                (vocabulary[&token], t)
            })
            .collect();
        rows.sort();
        for (index, reaches) in rows {
            germ.push(index);
            target.push(reaches);
        }
        indptr.push(germ.len() as u32);
        suffix.push(atlas.suffix_link(state).unwrap_or(0));
        standing.push(atlas.standing_at(state).unwrap_or(0));
    }
    let transport = Transport {
        indptr,
        germ,
        target,
        suffix,
        classes,
    };

    println!(
        "THE TRANSITION MONOID — {classes} classes, {} generators\n",
        surfaces.len()
    );
    println!("  Each generator is `carry` for one germ: a TOTAL map on every class, arc included.");
    println!("  Nothing below is imposed. No layer, no head, no dimension.\n");

    // ---- the census ----
    let mut contraction: BTreeMap<usize, usize> = BTreeMap::new();
    let mut attractor_sizes: BTreeMap<usize, usize> = BTreeMap::new();
    let mut indices: BTreeMap<usize, usize> = BTreeMap::new();
    let mut group_content: BTreeMap<usize, usize> = BTreeMap::new();
    // **The union of IMAGES, not of attractors.** An attractor is where repeating ONE symbol
    // forever lands; it says nothing about where a walk over arbitrary words can be. The set
    // reachable in one step from anywhere is the union of the images, and an earlier form of this
    // driver labelled the attractor union as that set, which was simply a different quantity.
    let mut reachable: BTreeSet<u32> = BTreeSet::new();
    let mut fixed_points: BTreeSet<u32> = BTreeSet::new();
    let mut largest: Vec<(usize, usize, usize, String)> = Vec::new();
    let mut nontrivial_cycles = 0usize;

    // At character grain the class population is large and the generator population small, so the
    // whole generator set is swept either way. What is declared is that every generator is taken --
    // nothing is sampled.
    for (index, surface) in surfaces.iter().enumerate() {
        let map = transport.map_of(index as u16);
        let image: BTreeSet<u32> = map.iter().copied().collect();
        let (stable, steps, cycles) = attractor(&map);
        reachable.extend(image.iter().copied());
        fixed_points.extend(stable.iter().copied());

        // Buckets, base-2, so the shape is legible rather than 3,125 rows.
        let bucket = |value: usize| {
            if value == 0 {
                0
            } else {
                64 - (value as u64).leading_zeros() as usize
            }
        };
        *contraction.entry(bucket(image.len())).or_default() += 1;
        *attractor_sizes.entry(bucket(stable.len())).or_default() += 1;
        *indices.entry(steps).or_default() += 1;
        for (length, count) in &cycles {
            *group_content.entry(*length).or_default() += count;
            if *length > 1 {
                nontrivial_cycles += count;
            }
        }
        largest.push((image.len(), stable.len(), steps, surface.clone()));
    }

    println!("ONE STEP — how far a single symbol contracts the state space");
    println!(
        "  |image(f_a)| bucketed by octave, over {} generators",
        surfaces.len()
    );
    for (octave, count) in &contraction {
        let low = if *octave == 0 { 0 } else { 1 << (octave - 1) };
        println!("    2^{:<2} ({:>6}..)   {count:>6} generators", octave, low);
    }
    let mean_image: usize =
        largest.iter().map(|(image, _, _, _)| *image).sum::<usize>() / largest.len().max(1);
    println!(
        "  mean image {mean_image} of {classes} — a single symbol collapses the space by {}x",
        classes / mean_image.max(1)
    );

    println!();
    println!("THE ATTRACTORS — the emergent charts, where each symbol's dynamics live");
    for (octave, count) in &attractor_sizes {
        let low = if *octave == 0 { 0 } else { 1 << (octave - 1) };
        println!("    2^{:<2} ({:>6}..)   {count:>6} generators", octave, low);
    }
    let mean_attractor: usize = largest
        .iter()
        .map(|(_, stable, _, _)| *stable)
        .sum::<usize>()
        / largest.len().max(1);
    println!("  mean attractor {mean_attractor} classes");
    println!(
        "  union of the FIXED POINTS: {} of {classes}",
        fixed_points.len()
    );
    println!(
        "  union of the IMAGES:      {} of {classes} = every class reachable in ONE step",
        reachable.len()
    );
    println!("  from anywhere. That is the set a walk can occupy; the rest is reachable only");
    println!("  through longer words.");

    println!();
    println!("THE MIXING TIME — applications until the image stabilises");
    for (steps, count) in &indices {
        println!("    {steps:>3} step(s)     {count:>6} generators");
    }

    println!();
    println!("THE GROUP CONTENT — cycle lengths on the attractors");
    for (length, count) in group_content.iter().take(12) {
        println!("    cycle length {length:<5} {count:>8} orbits");
    }
    println!("  orbits of length > 1: {nontrivial_cycles}");
    if nontrivial_cycles == 0 {
        println!("  ZERO. Every attractor is a set of FIXED POINTS, so the monoid is APERIODIC:");
        println!("  it contains no nontrivial group. The material is amorphous, not crystalline —");
        println!("  there is no space group to store in place of the sites, and a crystal model");
        println!("  would have to be BUILT rather than found. That is a real negative about this");
        println!("  material and it is exactly the measurement that decides the question.");
    } else {
        println!("  NONZERO. Some symbol permutes its attractor with a period > 1, which is a");
        println!("  Z/p acting: genuine symmetry, storable as a generator rather than enumerated.");
        println!("  That is crystalline content and it is where the compression lives.");
    }

    println!();
    println!("THE SHARPEST CONTRACTORS — symbols that collapse the space furthest");
    largest.sort_by_key(|(image, _, _, _)| *image);
    for (image, stable, steps, surface) in largest.iter().take(8) {
        println!(
            "    {:<24} image {image:>7}   attractor {stable:>6}   stabilises in {steps}",
            format!("{surface:?}")
        );
    }
    println!("  and the widest:");
    for (image, stable, steps, surface) in largest.iter().rev().take(8) {
        println!(
            "    {:<24} image {image:>7}   attractor {stable:>6}   stabilises in {steps}",
            format!("{surface:?}")
        );
    }
    Ok(())
}
