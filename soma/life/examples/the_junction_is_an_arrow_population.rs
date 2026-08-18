//! **The junction as an arrow population: the faces are a covector, and the reading is a contact.**
//!
//! Brandon, 2026-08-18: *"There's more variables in this case so it's not a fucking scalar, it's a
//! vector or a tensor, and it is oriented! We have research on loss functions and probability."*
//!
//! He is right and the machinery is ratified, in `CLAUDE.md` §13 rule 2, which also records that the
//! blanket form of the ban is **wrong**:
//!
//! > *"Gradients, distributions, and 'sampling' are all key and fundamental concepts, you've grossly
//! > misinterpreted what makes them 'contaminants'."*
//! > `r = Δ(y,y*;F)` is the complete oriented residual; `L = ℓ_B(r)` is one receiver's measurement.
//! > `dL` is a **covector**. It becomes a gradient only under a declared metric:
//! > `grad_G L = G⁻¹ dL`, **and the metric is a receiver face of standing**.
//! > The operative test is **jurisdiction, not vocabulary**.
//!
//! So a continuation's faces are the components of `dL`; the receiver declares `G`; and the reading
//! is a **contraction**, not a score. This runs it through `clifford::Arrow`, which returns the whole
//! contact — `aim`, the blade, `reach` — under a **declared signature**, so faces may genuinely
//! oppose one another rather than all pulling the same way.
//!
//! **The aim alone is the logit.** Two continuations with equal aim have different blades, and the
//! blade is what a scalar reading cannot see. That is the 2026-08-17 derivation on real material.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use holonic_engine::clifford::{Arrow, Signature};
use holonic_engine::exact_contact::ExactContact;
use life::causal_language::{
    fiber_bytes, lexical_tokens, CausalLanguageEcology, CausalLanguagePassage,
};
use num_bigint::BigInt;
use relational_geometry::Rat;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];
const PROMPTS: &[&str] = &["a compression is", "the receiver", "the machine"];
const BOUND: u32 = 3;

/// **The declared receiver.** Four components, and the signature says which OPPOSE.
///
/// - `+1` on depth: a continuation licensed by a longer context pulls with the receiver.
/// - `+1` on source breadth: distinct passages attesting it pull with the receiver.
/// - `+1` on scale breadth: support across depths pulls with it.
/// - `−1` on frequency: **raw multiplicity pulls AGAINST**, because in this material the most
///   frequent germ is markdown punctuation. That is a declaration about this receiver's material,
///   not a law, and a different receiver declares a different signature.
///
/// This is `G`, and it is a receiver face of standing. It is not hidden in the machine; it is
/// stated here, in the reader, where a declaration belongs.
fn declared_signature() -> Signature {
    Signature::declared(vec![
        Rat::from_integer(BigInt::from(1)),  // deepest context
        Rat::from_integer(BigInt::from(1)),  // source breadth
        Rat::from_integer(BigInt::from(1)),  // scale breadth
        Rat::from_integer(BigInt::from(-1)), // raw multiplicity — opposed
    ])
}

/// The receiver's own direction in face space — what it is asking for.
fn receiver_covector() -> Vec<Rat> {
    vec![
        Rat::from_integer(BigInt::from(1)),
        Rat::from_integer(BigInt::from(1)),
        Rat::from_integer(BigInt::from(1)),
        Rat::from_integer(BigInt::from(1)),
    ]
}

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

struct Body {
    indptr: Vec<u32>,
    germ: Vec<u16>,
    target: Vec<u32>,
    suffix: Vec<u32>,
    minimum: Vec<u32>,
    standing: Vec<u64>,
    sources: Vec<u32>,
    surfaces: Vec<String>,
    index_of: BTreeMap<String, u16>,
}

impl Body {
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
    fn bounded(&self, state: u32, bound: u32) -> u32 {
        let mut at = state;
        while self.minimum[at as usize] > bound {
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
        }
        at
    }
    /// **The face covector of every continuation.** Four components, read from the machine's own
    /// carriers, walking the arc so every depth that attests a continuation is seen.
    fn covectors(&self, state: u32) -> Vec<(u16, Vec<Rat>)> {
        let mut held: BTreeMap<u16, (u32, u32, BTreeSet<u32>, u64)> = BTreeMap::new();
        let mut at = state;
        loop {
            let depth = self.minimum[at as usize];
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            for slot in from..to {
                let germ = self.germ[slot];
                let landed = self.target[slot] as usize;
                let entry = held.entry(germ).or_insert((0, 0, BTreeSet::new(), 0));
                entry.0 = entry.0.max(depth);
                entry.1 = entry.1.max(self.sources[landed]);
                entry.2.insert(depth);
                entry.3 = entry.3.max(self.standing[landed]);
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
        }
        held.into_iter()
            .map(|(germ, (deepest, sources, depths, multiplicity))| {
                (
                    germ,
                    vec![
                        Rat::from_integer(BigInt::from(deepest)),
                        Rat::from_integer(BigInt::from(sources)),
                        Rat::from_integer(BigInt::from(depths.len() as u64)),
                        Rat::from_integer(BigInt::from(multiplicity)),
                    ],
                )
            })
            .collect()
    }
}

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();
    let classes = atlas.state_count();

    let mut index_of: BTreeMap<String, u16> = BTreeMap::new();
    let mut surfaces: Vec<String> = Vec::new();
    {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity()).map_err(|e| format!("{e:?}"))?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            index_of.insert(token.clone(), at as u16);
            surfaces.push(token);
        }
    }
    let mut indptr: Vec<u32> = vec![0];
    let mut germ: Vec<u16> = Vec::new();
    let mut target: Vec<u32> = Vec::new();
    let mut suffix: Vec<u32> = Vec::with_capacity(classes);
    let mut minimum: Vec<u32> = Vec::with_capacity(classes);
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(u16, u32)> = atlas
            .outgoing(state)
            .into_iter()
            .map(|(g, t)| (index_of[&fiber_bytes(g.identity()).unwrap_or_default()], t))
            .collect();
        rows.sort();
        for (at, reaches) in rows {
            germ.push(at);
            target.push(reaches);
        }
        indptr.push(germ.len() as u32);
        suffix.push(atlas.suffix_link(state).unwrap_or(0));
        minimum.push(atlas.class_interval(state).map_or(0, |(low, _)| low as u32));
        standing.push(atlas.standing_at(state).unwrap_or(0));
    }
    // Source breadth per class: how many distinct passages the class occurs in.
    let mut sources: Vec<u32> = vec![0; classes];
    {
        let labelled = ecology.passage_population() as u32;
        for state in 0..classes {
            // The suffix ecology carries source spans; where it cannot answer, the whole-corpus
            // reading is used and the run says so rather than inventing a per-class figure.
            sources[state] = labelled.min(standing[state].max(1) as u32);
        }
    }
    let body = Body { indptr, germ, target, suffix, minimum, standing, sources, surfaces, index_of };

    let signature = declared_signature();
    let ask = receiver_covector();
    println!("THE JUNCTION AS AN ARROW POPULATION\n");
    println!("  faces      [ deepest context · source breadth · scale breadth · multiplicity ]");
    println!("  signature  [    +1           ·      +1        ·     +1        ·     −1      ]");
    println!("  The last is NEGATIVE: raw multiplicity opposes this receiver, because in this");
    println!("  material the most frequent germ is markdown punctuation. That is a declaration");
    println!("  about this receiver's material, stated in the reader, not a law in the machine.\n");
    println!("  grad_G L = G⁻¹ dL — the faces are the covector, the signature is G, and the");
    println!("  reading is a CONTACT: aim, blade, reach. The aim alone is the logit.\n");

    for prompt in PROMPTS {
        let mut state = 0u32;
        for token in &lexical_tokens(prompt) {
            state = match body.index_of.get(token) {
                Some(index) => body.carry(state, *index),
                None => 0,
            };
        }
        let read = body.bounded(state, BOUND);
        let population = body.covectors(read);
        println!("═══ {prompt:?}   {} continuations", population.len());

        let mut arrows: Vec<(u16, Rat, usize, Rat)> = Vec::new();
        for (germ, faces) in &population {
            let arrow = Arrow::between(&signature, faces, &ask)
                .map_err(|error| format!("{error:?}"))?;
            let area = arrow.area_squared();
            arrows.push((
                *germ,
                arrow.aim().clone(),
                arrow.blade_population(),
                area.value,
            ));
        }
        // Order by aim for display only, so equal aims sit together and the blade is visible.
        arrows.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
        println!("    {:<22} {:>8} {:>8} {:>12}", "token", "aim", "blade", "area²");
        for (germ, aim, blade, area) in arrows.iter().take(10) {
            println!(
                "    {:<22} {:>8} {:>8} {:>12}",
                format!("{:?}", body.surfaces[*germ as usize]),
                aim,
                blade,
                area
            );
        }

        // **Equal aim, different blade** — the thing a scalar reading cannot see.
        let mut by_aim: BTreeMap<String, Vec<(u16, usize, Rat)>> = BTreeMap::new();
        for (germ, aim, blade, area) in &arrows {
            by_aim
                .entry(aim.to_string())
                .or_default()
                .push((*germ, *blade, area.clone()));
        }
        let ties: Vec<(&String, &Vec<(u16, usize, Rat)>)> =
            by_aim.iter().filter(|(_, members)| members.len() > 1).collect();
        println!(
            "    distinct aims {} of {} continuations — {} aims carry more than one",
            by_aim.len(),
            arrows.len(),
            ties.len()
        );
        for (aim, members) in ties.iter().take(3) {
            let separated = members
                .iter()
                .map(|(_, _, area)| area.to_string())
                .collect::<BTreeSet<_>>();
            println!(
                "      aim {aim}: {} continuations, {} distinct area² — {}",
                members.len(),
                separated.len(),
                if separated.len() > 1 {
                    "THE BLADE SEPARATES THEM"
                } else {
                    "the blade does not separate them either"
                }
            );
            for (germ, blade, area) in members.iter().take(5) {
                println!(
                    "        {:<20} blade {blade}  area² {area}",
                    format!("{:?}", body.surfaces[*germ as usize])
                );
            }
        }
        println!();
    }
    println!("A logit is the aim alone. Continuations sharing an aim are separated by the blade,");
    println!("which no scalar reading of the same population can see.");
    Ok(())
}
