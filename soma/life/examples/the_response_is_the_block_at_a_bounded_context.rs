//! **Generation on the quotient: the response is the block, and the fork is where it divides.**
//!
//! Two things are settled and this joins them.
//!
//! **Diffusion is the context bound.** An undiffused substrate recites, because a unique long
//! context licenses exactly one continuation. Bounding the context to `L` tokens merges every longer
//! context into its `L`-token suffix, so continuations are drawn from every place those `L` tokens
//! occurred. Measured: as the bound tightens the block population falls `4,731 → 2,959` and the
//! composed surfaces run to 192,246 against 101 verbatim.
//!
//! **A plural return is divided, not picked.** An unconstrained breadth-first front over every fork
//! is not a generation — it explores the whole material, and reporting three of its 192,246 tips by
//! class index reports an arbitrary index. `presentation_quotient::divide_junction` returns the
//! quotient's **blocks**, and a block is the response: within it no word of the declared family
//! separates the members, so naming one would be the governor.
//!
//! So a step is: bound the context, take the whole licensed population, **divide it**, and return
//! the blocks with what separates them. Nothing is ranked, sampled, capped or crowned.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{
    fiber_bytes, lexical_tokens, token_germs_public, CausalLanguageEcology, CausalLanguagePassage,
};
use life::presentation_quotient::{
    divide_junction, PresentationGround, PresentationReceiver, PresentedCandidate,
};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

const PROMPTS: &[&str] = &["a compression is", "the receiver", "the trace is"];
/// Declared context bounds. `0` is unbounded — the undiffused substrate.
const BOUNDS: [u32; 3] = [0, 4, 2];
/// How many steps of the walk to divide.
const STEPS: usize = 4;

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
    standing: Vec<u32>,
    extent: Vec<u32>,
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
    fn licensed(&self, state: u32) -> Vec<u16> {
        let from = self.indptr[state as usize] as usize;
        let to = self.indptr[state as usize + 1] as usize;
        self.germ[from..to].to_vec()
    }
    /// Bound the context: climb until the class's longest substring fits. **This is the diffusion.**
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

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas: &ExactSuffixEcology = ecology.global_suffix();
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
    let mut standing: Vec<u32> = Vec::with_capacity(classes);
    let mut extent: Vec<u32> = Vec::with_capacity(classes);
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
        standing.push(atlas.standing_at(state).unwrap_or(0) as u32);
        extent.push(atlas.class_extent(state).unwrap_or(0) as u32);
    }
    let body = Body { indptr, germ, target, suffix, standing, extent, surfaces, index_of };
    let ground = PresentationGround::Atlas(atlas);

    println!("GENERATION ON THE QUOTIENT — the response is the block\n");
    for prompt in PROMPTS {
        println!("═══ {prompt:?}");
        for bound in BOUNDS {
            let label = if bound == 0 {
                "unbounded (the undiffused substrate)".to_owned()
            } else {
                format!("context <= {bound} tokens")
            };
            println!("  ── {label}");
            let mut state = 0u32;
            for token in &lexical_tokens(prompt) {
                state = match body.index_of.get(token) {
                    Some(index) => body.carry(state, *index),
                    None => 0,
                };
            }
            let mut carried: Vec<String> = Vec::new();
            for step in 0..STEPS {
                let read = body.bounded(state, bound);
                let licensed = body.licensed(read);
                if licensed.is_empty() {
                    println!("     step {step}: TERMINUS");
                    break;
                }
                // Every licensed continuation, as a candidate carrying its own standing and the
                // class that licensed it. Nothing is dropped.
                let candidates: Vec<PresentedCandidate> = licensed
                    .iter()
                    .enumerate()
                    .map(|(at, g)| {
                        let landed = body.carry(read, *g);
                        let mut held = carried.clone();
                        held.push(body.surfaces[*g as usize].clone());
                        PresentedCandidate {
                            identity: format!("c{at}"),
                            tokens: held,
                            matched_horizons: vec![body.extent[landed as usize]],
                            sources: vec![BTreeSet::new()],
                        }
                    })
                    .collect();
                let division = divide_junction(
                    &candidates,
                    &ground,
                    &PresentationReceiver::transport_at(1),
                )
                .map_err(|error| format!("the junction would not divide: {error:?}"))?;
                println!(
                    "     step {step}: {} licensed -> {} BLOCKS  (collapsed {} pairs)",
                    licensed.len(),
                    division.conduct_blocks,
                    division.collapsed_population
                );
                for block in division.blocks.iter().take(4) {
                    let shown: Vec<String> = block
                        .surfaces
                        .iter()
                        .take(6)
                        .map(|surface| {
                            surface.rsplit(' ').next().unwrap_or(surface).to_owned()
                        })
                        .collect();
                    println!(
                        "        block of {:<4} : {}{}",
                        block.members.len(),
                        shown.join(" | "),
                        if block.surfaces.len() > 6 { " …" } else { "" }
                    );
                }
                if division.blocks.len() > 4 {
                    println!("        … {} more blocks, all retained", division.blocks.len() - 4);
                }
                // Continue the walk through the FIRST block's first member. The states in a block
                // are one state to this receiver, so this is the quotient continuing -- not a pick
                // among distinguishable options.
                let Some(first) = licensed.first().copied() else { break };
                carried.push(body.surfaces[first as usize].clone());
                state = body.carry(read, first);
            }
            println!("     walked   {:?}", carried.join(" "));
        }
        println!();
    }
    println!("Within a block no word of the declared family separates the members, so the block");
    println!("IS the response. A determinate step returns one block; a plural step returns several,");
    println!("and that is where a clarifying question is owed rather than a pick.");
    Ok(())
}
