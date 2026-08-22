//! **Composition as it actually reads: forced spans, joined where the material forks.**
//!
//! 85% of classes admit exactly one continuation, so a walk conducts through long **forced runs**,
//! and a forced run is a readable verbatim span. At a fork the branches lead into forced runs
//! belonging to **different sources**. So an emission is span + span + span, each readable, joined
//! exactly where the material licenses the join — and the join is the composition.
//!
//! That is recombination that reads, rather than token salad. Nothing is ranked, sampled or
//! crowned: every branch of every fork is taken and the whole population is returned.
//!
//! **The declared aperture is the number of forks crossed**, not which branch is taken. What it
//! excludes is reported.

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
    "the receiver",
    "a probability distribution over",
    "the quotient is",
];
/// **How many forks may be crossed.** A declared aperture on composition depth — never on which
/// branch is taken, and every branch of every crossed fork is followed.
const FORKS: usize = 3;
/// The most tokens one forced run contributes before the aperture stops it.
const RUN: usize = 24;

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
}

/// Is this token sequence a contiguous window of the material? One walk, no corpus search.
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
    let mut standing: Vec<u32> = Vec::with_capacity(classes);
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
    }
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        standing,
        surfaces,
        index_of,
    };

    for prompt in PROMPTS {
        println!("═════ PROMPT {prompt:?}\n");
        let mut state = 0u32;
        for token in &lexical_tokens(prompt) {
            state = match body.index_of.get(token) {
                Some(index) => body.carry(state, *index),
                None => 0,
            };
        }
        // (state, emitted, forks crossed, where the joins are)
        let mut live: Vec<(u32, Vec<String>, usize, Vec<usize>)> =
            vec![(state, Vec::new(), 0, Vec::new())];
        let mut finished: Vec<(Vec<String>, Vec<usize>)> = Vec::new();
        while let Some((mut at, mut emitted, crossed, mut joins)) = live.pop() {
            // Conduct the forced run: nothing is decided here.
            let mut ran = 0usize;
            loop {
                let licensed = body.licensed(at);
                if licensed.len() != 1 || ran >= RUN {
                    if licensed.len() > 1 && crossed < FORKS {
                        // **The fork: every branch is taken.** This is where a continuation from a
                        // different source joins, and that join is the composition.
                        joins.push(emitted.len());
                        for germ in licensed {
                            let mut carried = emitted.clone();
                            carried.push(body.surfaces[germ as usize].clone());
                            live.push((body.carry(at, germ), carried, crossed + 1, joins.clone()));
                        }
                    } else {
                        finished.push((emitted.clone(), joins.clone()));
                    }
                    break;
                }
                let only = licensed[0];
                emitted.push(body.surfaces[only as usize].clone());
                at = body.carry(at, only);
                ran += 1;
            }
            if finished.len() > 400 {
                break;
            }
        }

        let composed: Vec<&(Vec<String>, Vec<usize>)> = finished
            .iter()
            .filter(|(tokens, _)| !is_span(atlas, tokens))
            .collect();
        println!(
            "  emissions {}   of which COMPOSED (not a window of any source) {}",
            finished.len(),
            composed.len()
        );
        println!();
        for (tokens, joins) in composed.iter().take(6) {
            // Mark where a source handed off to another source.
            let mut rendered = String::new();
            for (at, token) in tokens.iter().enumerate() {
                if joins.contains(&at) {
                    rendered.push_str(" ⟨join⟩ ");
                }
                rendered.push_str(token);
                rendered.push(' ');
            }
            println!("  ▸ {}", rendered.trim());
            println!("    {} joins, {} tokens", joins.len(), tokens.len());
            println!();
        }
        if composed.is_empty() {
            println!("  NONE — every emission is a contiguous window of a single source, so the");
            println!("  forks did not recombine and this run says so.");
        }
        println!();
    }
    println!("⟨join⟩ marks a fork the material licensed: the tokens before it and after it are");
    println!("contiguous in DIFFERENT places, so the whole is a window of none of them.");
    Ok(())
}
