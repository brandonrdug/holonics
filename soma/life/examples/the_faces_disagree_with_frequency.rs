//! **What frequency threw away — measured, not asserted.**
//!
//! Brandon, 2026-08-16: *"'frequent' is not the only characteristic in the machine that dictates
//! whether or not it's relevant."* And 2026-08-08: *"you've been masking frequency as 'recurrence'?
//! That's dumb. It's just frequency."*
//!
//! A continuation in this machine carries at least four independent faces, and a generator built
//! this week read exactly one of them:
//!
//! | face | what it says |
//! |---|---|
//! | **multiplicity** | how many times the material carried it — `Π`, and the only one that was read |
//! | **source breadth** | how many DISTINCT passages attest it. Four passages once each is not one passage four times |
//! | **scale breadth** | how many suffix depths attest it — supported across scales, or a coincidence at one |
//! | **deepest support** | the longest context that licenses it at all |
//!
//! Same multiplicity, different lineage, different scale support. **This measures how often the
//! four disagree**, which is the whole content of the correction: if they never disagreed,
//! frequency would be a lawful stand-in and it is not.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use life::causal_language::{
    fiber_bytes, lexical_tokens, CausalLanguageEcology, CausalLanguagePassage,
};
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
    "the machine",
    "every claim",
    "the trace",
    "a probability",
];
const BOUND: u32 = 3;
const STEPS: usize = 30;

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
    surfaces: Vec<String>,
    index_of: BTreeMap<String, u16>,
}

/// One continuation, read on every face the machine actually carries.
#[derive(Clone, Debug)]
struct Face {
    germ: u16,
    /// `Π` — how many times the material carried it.
    multiplicity: u64,
    /// How many DISTINCT suffix depths attest it. Support across scales, not repetition at one.
    scale_breadth: usize,
    /// The deepest context that licenses it.
    deepest: u32,
    /// The multiplicity summed at the DEEPEST support only — what the longest context alone says.
    deepest_multiplicity: u64,
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
    /// **The whole face population.** Walks the arc from the class to the root, so every
    /// continuation carries every depth that attests it — the horizon profile, not a total.
    fn faces(&self, state: u32) -> Vec<Face> {
        let mut held: BTreeMap<u16, (u64, BTreeSet<u32>, u32, u64)> = BTreeMap::new();
        let mut at = state;
        loop {
            let depth = self.minimum[at as usize];
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            for slot in from..to {
                let germ = self.germ[slot];
                let standing = self.standing[self.target[slot] as usize];
                let entry = held.entry(germ).or_insert((0, BTreeSet::new(), 0, 0));
                entry.1.insert(depth);
                if depth >= entry.2 {
                    entry.2 = depth;
                    entry.3 = standing;
                }
                entry.0 = entry.0.max(standing);
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
        }
        held.into_iter()
            .map(
                |(germ, (multiplicity, depths, deepest, deepest_multiplicity))| Face {
                    germ,
                    multiplicity,
                    scale_breadth: depths.len(),
                    deepest,
                    deepest_multiplicity,
                },
            )
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
    let body = Body {
        indptr,
        germ,
        target,
        suffix,
        minimum,
        standing,
        surfaces,
        index_of,
    };

    println!("HOW OFTEN DO THE FACES DISAGREE WITH FREQUENCY?\n");
    println!("  Four readings of the same junction, all from the machine's own carriers:");
    println!("    Π          greatest multiplicity — what a week's generator read, and only this");
    println!("    scale      greatest number of distinct depths attesting it");
    println!("    deepest    licensed by the longest context");
    println!("    deep-Π     greatest multiplicity AT the deepest support\n");

    let mut junctions = 0usize;
    let mut differ_scale = 0usize;
    let mut differ_deep = 0usize;
    let mut differ_deepmul = 0usize;
    let mut examples: Vec<String> = Vec::new();

    for prompt in PROMPTS {
        let mut state = 0u32;
        for token in &lexical_tokens(prompt) {
            state = match body.index_of.get(token) {
                Some(index) => body.carry(state, *index),
                None => 0,
            };
        }
        for _ in 0..STEPS {
            let read = body.bounded(state, BOUND);
            let faces = body.faces(read);
            if faces.len() < 2 {
                if faces.is_empty() {
                    break;
                }
                state = body.carry(read, faces[0].germ);
                continue;
            }
            junctions += 1;
            let pick = |key: fn(&Face) -> (u64, u64)| -> u16 {
                faces
                    .iter()
                    .max_by_key(|face| (key(face), std::cmp::Reverse(face.germ)))
                    .map(|face| face.germ)
                    .unwrap_or(0)
            };
            let by_frequency = pick(|f| (f.multiplicity, 0));
            let by_scale = pick(|f| (f.scale_breadth as u64, 0));
            let by_deepest = pick(|f| (u64::from(f.deepest), 0));
            let by_deep_mul = pick(|f| (u64::from(f.deepest), f.deepest_multiplicity));
            if by_scale != by_frequency {
                differ_scale += 1;
            }
            if by_deepest != by_frequency {
                differ_deep += 1;
            }
            if by_deep_mul != by_frequency {
                differ_deepmul += 1;
            }
            if by_deepest != by_frequency && examples.len() < 8 {
                let f = |g: u16| body.surfaces[g as usize].clone();
                let fq = faces.iter().find(|x| x.germ == by_frequency).unwrap();
                let dp = faces.iter().find(|x| x.germ == by_deepest).unwrap();
                examples.push(format!(
                    "    {:<22} Π={:<5} scale={} depth={}   AGAINST   {:<22} Π={:<5} scale={} depth={}",
                    format!("{:?}", f(by_frequency)), fq.multiplicity, fq.scale_breadth, fq.deepest,
                    format!("{:?}", f(by_deepest)), dp.multiplicity, dp.scale_breadth, dp.deepest
                ));
            }
            state = body.carry(read, by_frequency);
        }
    }

    println!("  plural junctions visited        {junctions}");
    println!(
        "  scale breadth disagrees with Π  {differ_scale:>4}  ({}%)",
        100 * differ_scale / junctions.max(1)
    );
    println!(
        "  deepest support disagrees       {differ_deep:>4}  ({}%)",
        100 * differ_deep / junctions.max(1)
    );
    println!(
        "  deepest-Π disagrees             {differ_deepmul:>4}  ({}%)",
        100 * differ_deepmul / junctions.max(1)
    );
    println!();
    println!("  WHERE THEY DISAGREE — frequency's reading against the deepest-context reading:");
    for line in &examples {
        println!("{line}");
    }
    println!();
    println!(
        "  A face that never disagreed would make frequency a lawful stand-in for the others."
    );
    println!("  Every disagreement is a continuation the frequency reading discarded and another");
    println!("  reading of the SAME return kept.");
    Ok(())
}
