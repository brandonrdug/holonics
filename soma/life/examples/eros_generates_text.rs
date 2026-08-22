//! **Eros generates text.**
//!
//! The machine returns the whole licensed population at every step. **A reader declares how to read
//! it**, and this reader declares standing — `Π`, the lived construction, how many times the
//! material actually carried that continuation. That is a declared receiver face, which the
//! jurisdiction doctrine admits explicitly; what is banned is `G_authored`, a scalar governor inside
//! Soma's law. Nothing here is inside the law: the population is returned whole and the declaration
//! lives in the reader.
//!
//! The context bound is the diffusion. Unbounded, the walk recites — a licensed walk emits
//! substrings by construction. Bounded, it arcs, and the arc is the composition operator.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{
    fiber_bytes, lexical_tokens, token_germs_public, CausalLanguageEcology, CausalLanguagePassage,
};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

const PROMPTS: &[&str] = &[
    "a compression is",
    "the receiver",
    "every claim",
    "the trace",
    "a probability distribution",
    "the machine",
];

/// Context bounds. `0` is unbounded — the undiffused substrate, which recites.
const BOUNDS: [u32; 4] = [0, 8, 5, 3];
const TOKENS: usize = 40;

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
    extent: Vec<u32>,
    standing: Vec<u64>,
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

    /// **The whole licensed population**, each with the standing behind it. Nothing is dropped here;
    /// this is the return, and the reader below declares how to read it.
    fn population(&self, state: u32) -> Vec<(u16, u64)> {
        let from = self.indptr[state as usize] as usize;
        let to = self.indptr[state as usize + 1] as usize;
        (from..to)
            .map(|slot| {
                let germ = self.germ[slot];
                (germ, self.standing[self.target[slot] as usize])
            })
            .collect()
    }

    fn bounded(&self, state: u32, bound: u32) -> u32 {
        if bound == 0 {
            return state;
        }
        let mut at = state;
        while self.extent[at as usize] > bound {
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
        }
        at
    }
}

fn is_span(atlas: &ExactSuffixEcology, tokens: &[String]) -> bool {
    if tokens.is_empty() {
        return true;
    }
    let Ok(germs) = token_germs_public(tokens) else {
        return false;
    };
    let Ok(current) = atlas.receive_path(&germs) else {
        return false;
    };
    current.matched_length() as usize == tokens.len()
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
    let mut extent: Vec<u32> = Vec::with_capacity(classes);
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
        extent.push(atlas.class_extent(state).unwrap_or(0) as u32);
        standing.push(atlas.standing_at(state).unwrap_or(0));
    }
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        extent,
        standing,
        surfaces,
        index_of,
    };

    println!("EROS GENERATES\n");
    println!("  The machine returns the whole licensed population at every step.");
    println!("  THIS READER declares standing — how many times the material carried it.");
    println!("  The context bound is the diffusion: 0 recites, smaller composes.\n");

    for prompt in PROMPTS {
        println!("═════════ {prompt:?}");
        for bound in BOUNDS {
            let mut state = 0u32;
            for token in &lexical_tokens(prompt) {
                state = match body.index_of.get(token) {
                    Some(index) => body.carry(state, *index),
                    None => 0,
                };
            }
            let mut emitted: Vec<String> = Vec::new();
            let mut plural_steps = 0usize;
            let mut widest = 0usize;
            for _ in 0..TOKENS {
                let read = body.bounded(state, bound);
                let population = body.population(read);
                if population.is_empty() {
                    break;
                }
                if population.len() > 1 {
                    plural_steps += 1;
                    widest = widest.max(population.len());
                }
                // THE READER'S DECLARATION: greatest standing, ties by canonical germ order.
                let (chosen, _) = population
                    .iter()
                    .copied()
                    .max_by_key(|(germ, standing)| (*standing, std::cmp::Reverse(*germ)))
                    .expect("non-empty");
                emitted.push(body.surfaces[chosen as usize].clone());
                state = body.carry(read, chosen);
            }
            let verdict = if is_span(atlas, &emitted) {
                "VERBATIM"
            } else {
                "COMPOSED"
            };
            let label = if bound == 0 {
                "unbounded".to_owned()
            } else {
                format!("context ≤ {bound}")
            };
            println!("  ── {label:<14} [{verdict}]  {plural_steps} plural steps, widest {widest}");
            println!("     {}", emitted.join(" "));
        }
        println!();
    }
    Ok(())
}
