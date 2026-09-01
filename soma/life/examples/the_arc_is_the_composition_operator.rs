//! **The arc is the composition operator — and here is what it emits, as text.**
//!
//! A suffix automaton accepts exactly the substrings of its material. `carry` along a **licensed**
//! transition lands in the class of a longer substring that still occurs, so a walk that only
//! follows licensed transitions emits a substring **by construction**. Measured: joining forced runs
//! at forks produced **0 composed surfaces of 20 emissions** — a fork does not recombine, it only
//! means the substring extends several ways.
//!
//! Composition requires a continuation licensed by a **shorter** context than the one carried, which
//! is to say **deliberately arcing**. Bounding the context to `L` tokens forces exactly that, and it
//! is why the bounded run produced 192,246 non-spans where the fork-joining run produced none.
//!
//! **So the arc is the composition operator**, and it is the same coordinate the winding lives on.
//!
//! This driver emits with the arc and **prints the text**. Population is bounded by dividing the
//! front at each step — tips in one class at the declared bound are one tip — and never by ranking.

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

const PROMPTS: &[&str] = &["a compression is", "the receiver", "every claim"];
/// The declared context bound — how much context is carried before the arc takes over.
const BOUND: u32 = 5;
const STEPS: usize = 16;
/// How many emissions to print. **Canonical order, not a quality selection**, and the whole
/// population is counted beside it.
const SHOWN: usize = 10;

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
    /// **The arc, taken deliberately**: hold the context to `bound` tokens by climbing until the
    /// class's longest substring fits. Everything longer merges into its `bound`-token suffix, so
    /// the licensed set is drawn from every place that suffix occurred.
    fn bounded(&self, state: u32, bound: u32) -> u32 {
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

/// The longest suffix of `tokens` that occurs contiguously — where the last arc handed off.
fn longest_contiguous_tail(atlas: &ExactSuffixEcology, tokens: &[String]) -> usize {
    let Ok(germs) = token_germs_public(tokens) else {
        return 0;
    };
    let Ok(current) = atlas.receive_path(&germs) else {
        return 0;
    };
    current.matched_length() as usize
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
    }
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        extent,
        surfaces,
        index_of,
    };

    println!("EMISSION WITH THE ARC — context bounded to {BOUND} tokens\n");
    for prompt in PROMPTS {
        let mut state = 0u32;
        for token in &lexical_tokens(prompt) {
            state = match body.index_of.get(token) {
                Some(index) => body.carry(state, *index),
                None => 0,
            };
        }
        let mut front: Vec<(u32, Vec<String>)> = vec![(state, Vec::new())];
        for _ in 0..STEPS {
            let mut next: Vec<(u32, Vec<String>)> = Vec::new();
            for (at, emitted) in &front {
                let read = body.bounded(*at, BOUND);
                for germ in body.licensed(read) {
                    let mut carried = emitted.clone();
                    carried.push(body.surfaces[germ as usize].clone());
                    next.push((body.carry(read, germ), carried));
                }
            }
            if next.is_empty() {
                break;
            }
            // Divide the front: tips in one class at this bound are ONE tip to this receiver.
            let mut blocks: BTreeMap<u32, Vec<(u32, Vec<String>)>> = BTreeMap::new();
            for (at, emitted) in next {
                blocks
                    .entry(body.bounded(at, BOUND))
                    .or_default()
                    .push((at, emitted));
            }
            front = blocks
                .into_values()
                .map(|mut members| {
                    members.sort_by(|left, right| left.1.cmp(&right.1));
                    members.remove(0)
                })
                .collect();
        }

        let mut composed: Vec<&(u32, Vec<String>)> = front
            .iter()
            .filter(|(_, tokens)| !is_span(atlas, tokens))
            .collect();
        composed.sort_by(|left, right| left.1.cmp(&right.1));

        println!("═════ {prompt:?}");
        println!(
            "  emissions {}   COMPOSED (a window of no single source) {}\n",
            front.len(),
            composed.len()
        );
        for (_, tokens) in composed.iter().take(SHOWN) {
            let tail = longest_contiguous_tail(atlas, tokens);
            // Mark where the material stops being contiguous: everything before the last `tail`
            // tokens came from somewhere else.
            let split = tokens.len().saturating_sub(tail);
            let head = tokens[..split].join(" ");
            let rest = tokens[split..].join(" ");
            println!("  ▸ {head} ⟨arc⟩ {rest}");
        }
        if composed.is_empty() {
            println!("  NONE — every emission is a window of one source, so the arc did not");
            println!("  recombine and this run says so.");
        } else {
            println!(
                "\n  ({} shown in canonical order — NOT a quality selection; the population is {})",
                SHOWN.min(composed.len()),
                composed.len()
            );
        }
        println!();
    }
    println!("⟨arc⟩ marks where the emission stopped being contiguous with any single source.");
    println!("Everything after it occurs somewhere; the whole occurs nowhere. That join is the");
    println!("composition, and the arc is the operator that made it.");
    Ok(())
}
