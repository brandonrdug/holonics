//! **Composition: branch at the fork, and let the quotient bound the front.**
//!
//! Brandon, 2026-08-18: *"It shouldn't be a forced law causing it to recite verbatim, that just
//! means you're not allowing the information as a substrate to diffuse and reduce in 'training'."*
//!
//! He is right and the mechanism is exact. A walk inside a **unique** context — standing 1 — has
//! exactly one licensed continuation, so conducting through it reproduces the source. That is not a
//! law about generation; it is what an **undiffused substrate** does. 25,030 classes hold 19,970
//! occurrences, so nothing has been quotiented and every path is its own path.
//!
//! **Diffusion is the quotient**, and this repository already computes it: climbing `k` suffix links
//! coarsens a class, and `receiver_exact_compression` returns the coarsest partition whose conduct
//! is determined by the block. Measured 2026-08-18, the compression curve on a real junction ran
//! `2,033 → 1,201 → 53` over two climbs.
//!
//! # The law this runs
//!
//! ```text
//!   forced (1 licensed)  -> conduct; nothing is decided there
//!   fork   (n licensed)  -> BRANCH into n tips; the fork is where composition happens
//!   front too wide       -> DIVIDE it: tips landing in one coarsened class are
//!                           indistinguishable to that declared receiver, so they are
//!                           one tip. That is the quotient, not a selection.
//! ```
//!
//! **Nothing is ranked, sampled, capped or crowned.** The front is bounded by the number of blocks
//! the material has at the declared grain, which is a property of the material.
//!
//! # The falsifier
//!
//! An emitted surface is **recitation** exactly when it is a contiguous window of the material, and
//! the atlas answers that in one walk: `matched_length == len`. At grain 0 every emission should be
//! a span. **If no grain produces a non-span, the front is not composing and the run says so.**

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

const PROMPTS: &[&str] = &["the receiver", "a compression is", "the trace is"];
/// Grains swept. Grain 0 is the raw class — the undiffused substrate, which recites.
/// **Context bounds swept.** `0` is unbounded — the undiffused substrate, which recites. Each
/// smaller bound merges more distinct contexts into one class, which is the diffusion.
const GRAINS: [u32; 5] = [0, 6, 4, 3, 2];
const STEPS: usize = 14;

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
    /// The longest substring each class represents — its `maxlen`.
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

    /// **Diffuse the substrate by bounding the CONTEXT LENGTH.**
    ///
    /// A class covers substring lengths `[minlen, maxlen]`. Holding the current to at most `bound`
    /// tokens of context means climbing until the class's longest substring fits, which merges
    /// every longer context into its `bound`-token suffix. **That is the diffusion**: distinct long
    /// contexts that occurred in different places become one class, so their continuations are drawn
    /// from all of those places at once and the emission recombines.
    ///
    /// An earlier form climbed a fixed NUMBER OF LINKS instead. That is the right coarsening for
    /// dividing a junction population — it produced the measured `2,033 → 53` curve — and the wrong
    /// one for driving a walk: this tree is 8 deep, so two links land nearly everything at the root,
    /// the front collapses to one block, and the root licenses the whole vocabulary. Measured: grain
    /// 2 and grain 3 both returned exactly 1 block and emitted the alphabetically first germ
    /// forever.
    fn coarsen(&self, state: u32, bound: u32) -> u32 {
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
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        standing,
        extent,
        surfaces,
        index_of,
    };

    println!("COMPOSITION BY FORK, WITH THE QUOTIENT BOUNDING THE FRONT\n");
    println!("  forced -> conduct · fork -> BRANCH · front -> DIVIDE at the declared grain");
    println!("  Two tips in one coarsened class are indistinguishable to that receiver, so they");
    println!("  are one tip. Nothing is ranked, sampled, capped or crowned.\n");

    for prompt in PROMPTS {
        println!("═══ PROMPT {prompt:?}");
        let seed_tokens = lexical_tokens(prompt);
        let mut seed = 0u32;
        for token in &seed_tokens {
            if let Some(index) = body.index_of.get(token) {
                seed = body.carry(seed, *index);
            } else {
                seed = 0;
            }
        }

        for grain in GRAINS {
            // The front: (state, emitted tokens). One tip to start.
            let mut front: Vec<(u32, Vec<String>)> = vec![(seed, Vec::new())];
            let mut peak = 1usize;
            let mut forks = 0usize;
            let mut collapses = 0usize;
            let mut surface_population = 0usize;
            let mut retained: Vec<Vec<String>> = Vec::new();
            for _ in 0..STEPS {
                let mut next: Vec<(u32, Vec<String>)> = Vec::new();
                for (state, emitted) in &front {
                    // **THE WALK HAPPENS AT THE DECLARED GRAIN, both halves.** An earlier form read
                    // the licensed set at the coarsened class and then carried from the ORIGINAL
                    // state, so the reading grain and the walking grain disagreed and every step
                    // arced. Coarsening first and carrying from there is reading the material at
                    // that grain -- a coarser automaton, which is what a diffused substrate IS.
                    let read = body.coarsen(*state, grain);
                    let licensed = body.licensed(read);
                    if licensed.is_empty() {
                        continue;
                    }
                    if licensed.len() > 1 {
                        forks += 1;
                    }
                    for germ in licensed {
                        let mut carried = emitted.clone();
                        carried.push(body.surfaces[germ as usize].clone());
                        next.push((body.carry(read, germ), carried));
                    }
                }
                if next.is_empty() {
                    break;
                }
                // ---- DIVIDE the front by the quotient at this grain ----
                //
                // **A block keeps its whole surface population.** An earlier form used
                // `or_insert`, which keeps whichever tip the iteration reached first -- a partition
                // chosen by loop order, which is the authored-partition defect and is why a
                // low-index germ dominated every emission. Two tips in one block are
                // indistinguishable AS STATES at this grain; their emitted SURFACES are not, and
                // discarding them is a selection rather than a quotient.
                let before = next.len();
                let mut blocks: BTreeMap<u32, (u32, Vec<Vec<String>>)> = BTreeMap::new();
                for (state, emitted) in next {
                    let block = body.coarsen(state, grain);
                    blocks
                        .entry(block)
                        .or_insert_with(|| (state, Vec::new()))
                        .1
                        .push(emitted);
                }
                collapses += before - blocks.len();
                // The front carries one tip per block, and the block's surfaces are its plural
                // return. The canonically-first surface continues the walk because the states are
                // one state at this grain; the rest are retained and reported.
                let mut carried_front = Vec::with_capacity(blocks.len());
                surface_population = 0;
                for (state, mut population) in blocks.into_values() {
                    population.sort();
                    surface_population += population.len();
                    let head = population.first().cloned().unwrap_or_default();
                    retained.extend(population.into_iter().skip(1));
                    carried_front.push((state, head));
                }
                front = carried_front;
                peak = peak.max(front.len());
            }

            let mut spans = 0usize;
            let mut composed: Vec<&Vec<String>> = Vec::new();
            // Read the whole return -- the front's tips AND every surface a block retained.
            let whole: Vec<(u32, Vec<String>)> = front
                .iter()
                .cloned()
                .chain(retained.iter().map(|held| (0u32, held.clone())))
                .collect();
            for (_, emitted) in &whole {
                if is_span(atlas, emitted) {
                    spans += 1;
                } else {
                    composed.push(emitted);
                }
            }
            println!(
                "  context <= {grain}: blocks {:<5} peak {:<5} forks {:<6} surfaces {:<6} | verbatim {:<5} COMPOSED {}",
                front.len(),
                peak,
                forks,
                whole.len(),
                spans,
                composed.len()
            );
            let _ = (collapses, surface_population);
            for emitted in composed.iter().take(3) {
                println!("      COMPOSED: {:?}", emitted.join(" "));
            }
            if composed.is_empty() && !front.is_empty() {
                if let Some((_, emitted)) = front.first() {
                    println!("      verbatim: {:?}", emitted.join(" "));
                }
            }
        }
        println!();
    }
    println!(
        "A surface that is not a contiguous window of any source did not come from one place."
    );
    println!("If no grain produces one, the front is not composing and this run says so.");
    Ok(())
}
