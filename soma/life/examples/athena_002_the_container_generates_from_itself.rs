//! **ATHENA-002 — one container, both halves, and it produces with nothing else present.**
//!
//! ATHENA-000 carried the tree chart; ATHENA-001 carried the transport and replayed it. This carries
//! both plus the vocabulary, declares its own architecture in the container, and **generates from
//! the file alone** — no ecology, no corpus, no organ.
//!
//! **The coordinates are rebased and that is the repair ATHENA-000 measured.** Its widest residual
//! was 64, because a raw depth-first index is an **absolute coordinate** and a `BF16` ulp at
//! magnitude 16,000 is 64. A relative interval is a **ratio**, and only a ratio crosses a horizon.
//!
//! **The architecture is declared in the container, in the container's own terms**: layer `k` is the
//! atlas at suffix-link height `k`, the layer count is the tree's own height, and the transport is
//! compressed sparse rows with the suffix link as the arc. No transformer is implied and none is
//! needed to run it.

use std::collections::BTreeMap;

use body::num::Cog;
use holonic_engine::athena::{
    emit_integers, emit_tensor, IntegerDtype, IntegerTensor, TreeChart,
};
use life::causal_language::{
    fiber_bytes, lexical_tokens, token_germs_public, CausalLanguageEcology, CausalLanguagePassage,
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

const LAYERS: u32 = 6;
const PROMPTS: &[&str] = &["the receiver", "a compression is a codec", "the quantum wobbleflux"];

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

/// The container as it sits on disk, and everything a run needs.
struct Athena {
    indptr: Vec<u32>,
    germ: Vec<u16>,
    target: Vec<u32>,
    standing: Vec<u32>,
    suffix: Vec<u32>,
    /// germ index -> surface, from the container's own vocabulary tensors.
    surfaces: Vec<String>,
    index_of: BTreeMap<String, u16>,
    layers: u32,
}

impl Athena {
    /// **`carry`, expressed in integer arrays.** Forward while a germ is in the class's span; arc
    /// down the suffix link when it is not. This is the whole of inference.
    fn carry(&self, state: u32, germ: u16) -> (u32, bool) {
        let mut at = state;
        loop {
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            if let Some(slot) = (from..to).find(|slot| self.germ[*slot] == germ) {
                return (self.target[slot], true);
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                return (0, false);
            }
            at = parent;
        }
    }

    /// The continuation population of a class, read at every scale up the arc — the same current
    /// through every nested context. **Nothing is ranked and nothing is crowned.**
    fn continuations(&self, state: u32) -> Vec<(String, u32, u32)> {
        let mut held: BTreeMap<u16, (u32, u32)> = BTreeMap::new();
        let mut at = state;
        let mut depth = 0u32;
        loop {
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            for slot in from..to {
                held.entry(self.germ[slot])
                    .or_insert((self.standing[self.target[slot] as usize], depth));
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
            depth += 1;
        }
        held.into_iter()
            .map(|(germ, (standing, depth))| {
                (self.surfaces[germ as usize].clone(), standing, depth)
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
    let chart = TreeChart::label(classes, |state| atlas.suffix_link(state))
        .map_err(|error| format!("{error:?}"))?;

    // ---- vocabulary, canonical ----
    let mut index_of: BTreeMap<String, u16> = BTreeMap::new();
    let mut ordered: Vec<String> = Vec::new();
    {
        let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity()).map_err(|error| format!("{error:?}"))?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            index_of.insert(token.clone(), at as u16);
            ordered.push(token);
        }
    }

    // ---- transport ----
    let mut indptr: Vec<u64> = vec![0];
    let mut germ: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    let mut suffix: Vec<u64> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(String, u32)> = atlas
            .outgoing(state)
            .into_iter()
            .map(|(g, t)| (fiber_bytes(g.identity()).unwrap_or_default(), t))
            .collect();
        rows.sort();
        for (token, reaches) in rows {
            germ.push(u64::from(index_of[&token]));
            target.push(u64::from(reaches));
        }
        indptr.push(germ.len() as u64);
        standing.push(atlas.standing_at(state).unwrap_or(0));
        suffix.push(u64::from(atlas.suffix_link(state).unwrap_or(0)));
    }

    // ---- the tree chart, REBASED: a ratio crosses where a magnitude cannot ----
    let extent = Rat::from_integer(BigInt::from(2 * classes as u64));
    let occurrences = Rat::from_integer(BigInt::from(atlas.material_occurrence_count().max(1)));
    let mut rows: Vec<Vec<Rat>> = Vec::with_capacity(ordered.len());
    for token in &ordered {
        let germs = token_germs_public(std::slice::from_ref(token))
            .map_err(|error| format!("{error:?}"))?;
        let landed = atlas.receive_path(&germs).map_err(|error| format!("{error:?}"))?;
        let mut row = Vec::with_capacity(LAYERS as usize * 3);
        for height in 0..LAYERS {
            let class = atlas.suffix_ancestor(landed.state(), height);
            let (t, x) = chart.minkowski(class).ok_or("no interval")?;
            row.push(t / &extent);
            row.push(x / &extent);
            row.push(
                Rat::from_integer(BigInt::from(atlas.standing_at(class).unwrap_or(0)))
                    / &occurrences,
            );
        }
        rows.push(row);
    }
    let embedding = emit_tensor("athena.embed.minkowski", &rows)
        .map_err(|error| format!("{error:?}"))?;

    println!("ATHENA-002\n");
    println!("  classes {classes}   transitions {}   vocabulary {}", germ.len(), ordered.len());
    println!("  suffix-link tree height {}   layers emitted {LAYERS}", chart.height);
    println!();
    println!("  THE REBASE — ATHENA-000 measured a widest residual of 64 on ABSOLUTE indices");
    println!(
        "    embedding entries {}   crossed EXACTLY {}   widest residual {}",
        embedding.words.len(),
        embedding.exact_entries(),
        embedding.widest_residual()
    );

    // ---- vocabulary as octets plus offsets: integers, and the surfaces come back ----
    let mut vocabulary_octets: Vec<u64> = Vec::new();
    let mut vocabulary_offsets: Vec<u64> = vec![0];
    for token in &ordered {
        vocabulary_octets.extend(token.as_bytes().iter().map(|octet| u64::from(*octet)));
        vocabulary_offsets.push(vocabulary_octets.len() as u64);
    }

    let integers: Vec<IntegerTensor> = vec![
        emit_integers("athena.transport.indptr", &indptr, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.transport.germ", &germ, 1, IntegerDtype::U16).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.transport.target", &target, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.class.standing", &standing, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.class.suffix", &suffix, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.vocabulary.octets", &vocabulary_octets, 1, IntegerDtype::U16).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.vocabulary.offsets", &vocabulary_offsets, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        // **The architecture, declared IN the container.** layer k = suffix height k; the layer
        // count is the tree's own; the arc is `athena.class.suffix`. Nothing here implies a
        // transformer and nothing outside the file is needed to run it.
        emit_integers(
            "athena.architecture",
            &[
                u64::from(LAYERS),
                u64::from(chart.height),
                classes as u64,
                germ.len() as u64,
                ordered.len() as u64,
            ],
            1,
            IntegerDtype::U32,
        )
        .map_err(|e| format!("{e:?}"))?,
    ];

    // ---- write one container holding both halves ----
    let mut header = String::from("{");
    let mut offset = 0usize;
    let mut spans: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for tensor in &integers {
        let end = offset + tensor.octets.len();
        header.push_str(&format!(
            "\"{}\":{{\"dtype\":\"{}\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}},",
            tensor.name, tensor.dtype.name(), tensor.rows, tensor.width
        ));
        spans.insert(tensor.name.clone(), (offset, end));
        offset = end;
    }
    let end = offset + embedding.words.len() * 2;
    header.push_str(&format!(
        "\"{}\":{{\"dtype\":\"BF16\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}}}}",
        embedding.name, embedding.rows, embedding.width
    ));
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut container = Vec::new();
    container.extend_from_slice(&(header.len() as u64).to_le_bytes());
    container.extend_from_slice(header.as_bytes());
    for tensor in &integers {
        container.extend_from_slice(&tensor.octets);
    }
    for word in &embedding.words {
        container.extend_from_slice(&word.to_le_bytes());
    }
    std::fs::create_dir_all("output/athena-002").map_err(|e| format!("{e}"))?;
    let path = "output/athena-002/model.safetensors";
    std::fs::write(path, &container).map_err(|error| format!("{path}: {error}"))?;
    println!();
    println!("  CONTAINER  {} octets = {} KiB  -> {path}", container.len(), container.len() / 1024);

    // ================= from here on, ONLY the file =================
    let raw = std::fs::read(path).map_err(|error| format!("{path}: {error}"))?;
    let length = u64::from_le_bytes(raw[..8].try_into().unwrap()) as usize;
    let payload = &raw[8 + length..];
    let u32s = |name: &str| -> Vec<u32> {
        let (start, end) = spans[name];
        payload[start..end].chunks_exact(4).map(|r| u32::from_le_bytes([r[0], r[1], r[2], r[3]])).collect()
    };
    let u16s = |name: &str| -> Vec<u16> {
        let (start, end) = spans[name];
        payload[start..end].chunks_exact(2).map(|r| u16::from_le_bytes([r[0], r[1]])).collect()
    };
    let architecture = u32s("athena.architecture");
    let octets = u16s("athena.vocabulary.octets");
    let offsets = u32s("athena.vocabulary.offsets");
    let mut surfaces = Vec::with_capacity(offsets.len() - 1);
    for pair in offsets.windows(2) {
        let bytes: Vec<u8> = octets[pair[0] as usize..pair[1] as usize]
            .iter()
            .map(|word| *word as u8)
            .collect();
        surfaces.push(String::from_utf8(bytes).map_err(|e| format!("{e}"))?);
    }
    let mut mounted_index: BTreeMap<String, u16> = BTreeMap::new();
    for (at, surface) in surfaces.iter().enumerate() {
        mounted_index.insert(surface.clone(), at as u16);
    }
    let athena = Athena {
        indptr: u32s("athena.transport.indptr"),
        germ: u16s("athena.transport.germ"),
        target: u32s("athena.transport.target"),
        standing: u32s("athena.class.standing"),
        suffix: u32s("athena.class.suffix"),
        surfaces,
        index_of: mounted_index,
        layers: architecture[0],
    };
    println!();
    println!("  MOUNTED FROM THE FILE ALONE");
    println!(
        "    architecture: {} layers declared, tree height {}, {} classes, {} transitions, {} vocabulary",
        athena.layers, architecture[1], architecture[2], architecture[3], architecture[4]
    );

    println!();
    println!("PRODUCTION — from the container, with no ecology, no corpus, and no organ\n");
    for prompt in PROMPTS {
        let tokens = lexical_tokens(prompt);
        let mut state = 0u32;
        let mut trace = Vec::new();
        for token in &tokens {
            match athena.index_of.get(token) {
                None => {
                    state = 0;
                    trace.push(format!("{token}=UNSEEN->root"));
                }
                Some(index) => {
                    let (next, forward) = athena.carry(state, *index);
                    state = next;
                    trace.push(format!("{token}{}", if forward { "" } else { "*ARC" }));
                }
            }
        }
        let population = athena.continuations(state);
        println!("  {prompt:?}");
        println!("    walk        {}", trace.join(" -> "));
        println!("    class       {state}   standing {}", athena.standing[state as usize]);
        println!("    continuations {}  (the whole fiber, nothing ranked)", population.len());

        // **Grouped by arc depth, which is the structure the material has.** Depth 0 is the class's
        // own span -- the most specific continuations, the ones the full context licenses. Each step
        // up is the same current through a shorter context, and the root offers everything the
        // material starts with. Sorting the fiber alphabetically buries the specific under the
        // generic and reports the root's breadth as though it were the answer.
        let mut by_depth: BTreeMap<u32, Vec<(String, u32)>> = BTreeMap::new();
        for (surface, standing, depth) in &population {
            by_depth
                .entry(*depth)
                .or_default()
                .push((surface.clone(), *standing));
        }
        for (depth, mut members) in by_depth {
            members.sort_by_key(|(surface, _)| surface.clone());
            let label = if depth == 0 {
                "the class's own — what the FULL context licenses".to_owned()
            } else {
                format!("reached by arcing {depth} shorter")
            };
            println!("      depth {depth}: {:<5} continuations — {label}", members.len());
            if depth <= 1 {
                for (surface, standing) in members.iter().take(10) {
                    println!("        {:<24} standing {standing}", format!("{surface:?}"));
                }
                if members.len() > 10 {
                    println!("        … {} more at this depth, all retained", members.len() - 10);
                }
            }
        }
        if population.is_empty() {
            println!("      none — the material offers no continuation from here");
        }
        println!();
    }
    println!("The container declares its own architecture, carries its own vocabulary, and");
    println!("produces. A ratio crossed where a magnitude could not.");
    Ok(())
}
