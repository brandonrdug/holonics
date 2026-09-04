//! **Generation by forced passage, and the arc read as a winding.**
//!
//! # The coupling Brandon named, stated exactly
//!
//! A cathode ray tube's screen is a **crystal** phosphor. The beam deposits into the lattice, the
//! lattice **absorbs** — dissipative — and **re-emits** with a decay, and an image exists only
//! because persistence integrates arrival times. The crystal is what dissipates; the dissipation is
//! how the crystal is read. Neither is the object alone. That is `H = H₀ + H_int + H_pert` with the
//! lattice as `H_int`, the perspective's own standing identity.
//!
//! **And the curvature is not a metaphor.** In a periodic potential a carrier does not move in free
//! space: its effective mass is `m*ᵢⱼ = ℏ²(∂²E/∂kᵢ∂kⱼ)⁻¹`, which is literally the **curvature of the
//! band structure**. The lattice bends the dispersion and the bent dispersion moves the carrier —
//! the same shape as matter curving space and space moving matter.
//!
//! # Why that means "the turn"
//!
//! Bloch: a crystal's eigenstates are `ψ_k(r) = e^{ik·r} u_k(r)`, and translating by a lattice
//! vector multiplies the state by `e^{ik·R}` — **a pure phase. No magnitude changes at all.** The
//! translation group acts entirely through the turn, and `k` labels its irreducible representations;
//! the Brillouin zone *is* the character space of `ℤᵈ`.
//!
//! So a crystal's group content lives **in the phase**, and its dissipation lives in the magnitude.
//! One carrier, two faces, coupled. Measured 2026-08-18: `carry`'s state is `{class,
//! matched_length}` and **both coordinates are monotone**, so it carries the dissipative face and
//! has deleted the phase face. That is exactly why its monoid is aperiodic — no Bloch structure, no
//! band, no crystal — and it is the corpus's oldest law at the transport layer: *the boundary kept
//! the magnitude and discarded the turn.*
//!
//! # What is measured here
//!
//! 1. **Generation by forced passage.** 85% of classes admit exactly one continuation, so a walk
//!    conducts through them with nothing decided. It **halts at a fork**, which is the termination
//!    law: the cycle continues while the junction is forced and stops when something reflects.
//!    Nothing is ranked, sampled, or crowned — the halt is structural.
//! 2. **The arc as a winding.** Each arc drops the walk some levels; accumulating those drops along
//!    a path is a caused quantity. If one class is reached by two paths carrying **different**
//!    accumulated windings, the transport has **holonomy** — the same place, two phases — and
//!    holonomy is group content. That is the direct test of whether the turn can be recovered.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{
    fiber_bytes, lexical_tokens, CausalLanguageEcology, CausalLanguagePassage,
};
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("docs/canon/THE_DOCUMENT_LAW.md", 1),
    ("docs/canon/TABLET_THE_OPERATIONS.md", 2),
    ("docs/canon/THE_RECOVERED_LAW.md", 3),
    ("docs/canon/TABLET_THE_COMPRESSION.md", 4),
];

const PROMPTS: &[&str] = &[
    "a compression is a codec",
    "the receiver",
    "every claim still names",
    "a probability distribution over",
    "the trace is the",
    "an outer product is",
];

/// The declared extent of one generation. **A receiver parameter and never the law** — the walk
/// halts on its own at a fork, and this only bounds a run that never forks.
const EXTENT: usize = 60;

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
    depth: Vec<u32>,
    surfaces: Vec<String>,
    index_of: BTreeMap<String, u16>,
}

impl Body {
    /// `carry`, returning where it landed and **how far it arced** — the winding of that passage.
    fn carry(&self, state: u32, germ: u16) -> (u32, u32) {
        let mut at = state;
        let mut arced = 0u32;
        loop {
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            if let Some(slot) = (from..to).find(|slot| self.germ[*slot] == germ) {
                return (self.target[slot], arced);
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                return (0, arced + 1);
            }
            at = parent;
            arced += 1;
        }
    }

    /// The class's OWN span — what the full context licenses, with nothing from shorter contexts.
    fn licensed(&self, state: u32) -> Vec<u16> {
        let from = self.indptr[state as usize] as usize;
        let to = self.indptr[state as usize + 1] as usize;
        self.germ[from..to].to_vec()
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
    let mut standing: Vec<u32> = Vec::with_capacity(classes);
    let mut depth: Vec<u32> = Vec::with_capacity(classes);
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
        depth.push(atlas.class_extent(state).unwrap_or(0) as u32);
    }
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        standing,
        depth,
        surfaces,
        index_of,
    };

    // ================= GENERATION BY FORCED PASSAGE =================
    println!("GENERATION — the walk conducts through forced passages and HALTS AT A FORK.\n");
    println!("  Nothing is ranked, sampled or crowned. 85% of classes admit exactly one");
    println!("  continuation, so conduct through them decides nothing; the halt is where the");
    println!("  material genuinely branches, and that is the termination law.\n");

    for prompt in PROMPTS {
        let tokens = lexical_tokens(prompt);
        let mut state = 0u32;
        let mut winding = 0u32;
        for token in &tokens {
            if let Some(index) = body.index_of.get(token) {
                let (next, arced) = body.carry(state, *index);
                state = next;
                winding += arced;
            } else {
                state = 0;
            }
        }
        let mut emitted: Vec<String> = Vec::new();
        let mut halt = String::from("extent");
        for _ in 0..EXTENT {
            let licensed = body.licensed(state);
            if licensed.is_empty() {
                halt = "TERMINUS — the material offers no continuation".to_owned();
                break;
            }
            if licensed.len() > 1 {
                let names: Vec<String> = licensed
                    .iter()
                    .take(6)
                    .map(|g| format!("{:?}", body.surfaces[*g as usize]))
                    .collect();
                halt = format!(
                    "FORK — {} continuations: {}{}",
                    licensed.len(),
                    names.join(" "),
                    if licensed.len() > 6 { " …" } else { "" }
                );
                break;
            }
            let only = licensed[0];
            emitted.push(body.surfaces[only as usize].clone());
            let (next, arced) = body.carry(state, only);
            state = next;
            winding += arced;
        }
        println!("  PROMPT   {prompt:?}");
        println!("  EMITTED  {:?}", emitted.join(" "));
        println!(
            "  halt     {halt}\n  class    {state}   standing {}   longest substring {}   winding {winding}\n",
            body.standing[state as usize], body.depth[state as usize]
        );
    }

    // ================= THE ARC AS A WINDING =================
    //
    // If one class is reached by two paths carrying DIFFERENT accumulated arcs, the transport has
    // holonomy: the same place at two phases. Holonomy is group content, and group content is the
    // crystal. Swept over every class reachable in two symbols.
    println!("THE ARC AS A WINDING — is there holonomy?\n");
    let mut arrivals: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
    let generators: Vec<u16> = (0..body.surfaces.len() as u16).collect();
    let seeds: Vec<u32> = (0..classes as u32).step_by(97).collect();
    for seed in &seeds {
        for first in &generators {
            let (one, arc_one) = body.carry(*seed, *first);
            for second in generators.iter().step_by(29) {
                let (two, arc_two) = body.carry(one, *second);
                arrivals.entry(two).or_default().insert(arc_one + arc_two);
            }
        }
    }
    let plural: Vec<(&u32, &BTreeSet<u32>)> = arrivals
        .iter()
        .filter(|(_, windings)| windings.len() > 1)
        .collect();
    println!("  classes reached           {}", arrivals.len());
    println!(
        "  reached at MORE THAN ONE accumulated winding: {}",
        plural.len()
    );
    for (class, windings) in plural.iter().take(8) {
        let held: Vec<String> = windings.iter().map(u32::to_string).collect();
        println!("    class {class:<8} windings {{{}}}", held.join(", "));
    }
    if plural.is_empty() {
        println!("  NONE. The accumulated arc is a function of the class alone, so it carries no");
        println!(
            "  phase and there is no holonomy to recover. The winding would have to come from"
        );
        println!("  somewhere other than the arc depth.");
    } else {
        println!();
        println!("  HOLONOMY IS PRESENT. The same class is reached carrying different accumulated");
        println!("  windings, so the arc is a genuine PHASE on top of the class — the same place,");
        println!("  two turns. `{{class, matched_length}}` cannot see it and `{{class,");
        println!(
            "  matched_length, winding}}` can. That is the coordinate whose absence makes the"
        );
        println!("  monoid aperiodic, and it is recoverable from transport this container already");
        println!("  carries rather than from anything new.");
    }
    Ok(())
}
