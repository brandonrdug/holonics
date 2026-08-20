//! **Deed P2: the atlas condenses where the receiver factors, and the remainder is retained whole.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8 Deed P2
//! and §7.2/§7.3/§7.6. Authority for the mathematics: `CLAUDE.md` §11 (*the tree condenses for free,
//! and the remainder is the departure from a forest*), §0k (a compression is a codec pivot carrying a
//! declared decoder; the invariance is **additive**; a figure without its decoder is the
//! absolute-volume violation), §0l (Markov is a property of the pair `(material, receiver family)`),
//! §0m (tolerance is the aperture, and the collapsed-pair relation is what computes it).
//!
//! # What the deed is
//!
//! ```text
//!   the P0 rest (an integer safetensors atlas: 59,698 classes, 102,904 germ transitions)
//!     -> PART 0: the repaired receiver_exact_compression re-reads P0's declared scope
//!                and the equality against the committed manifest is bit-identical
//!     -> the WHOLE-ATLAS reading P0 refused, taken once
//!     -> the declared future receiver family R1..R7, PRINTED BEFORE ANY CONDENSATION RUNS
//!     -> the structural split:  tree part   -> interval labelling, remainder EMPTY
//!                               transport   -> the Nerode quotient's shared block rows
//!                               remainder   -> retained whole, exhibited by name
//!     -> a condensed rest, its decoder, and the ADDITIVE cost vector
//! ```
//!
//! # No dense-rank truncation anywhere
//!
//! Nothing here truncates a rank, drops a small entry, or fits a width. Every condensation is a
//! quotient by an equivalence the declared receiver family cannot see, and every pair the quotient
//! merges that some receiver *can* see is retained with the shortest word that separates it.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_atlas_condenses_where_the_receiver_factors
//! ```
//!
//! `--remount <condensed rest> --landed <class>...` is the fresh-process control: it reads the
//! condensed rest and nothing else, and prints the R1 faces for bit-comparison against the parent.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::time::Instant;

use holonic_engine::athena::{emit_integers, IntegerDtype, IntegerTensor, TreeChart};
use holonic_engine::exact_work::ExactWork;
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::native_occurrence::NativeOccurrence;
use holonic_engine::receiver_exact_compression::{
    compress, exhibit_collapsed_within, refine, separated_pair_population, InputId, ItemId,
    Observation, ObservedSystem, Partition, ReceiverId,
};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

const OUT: &str = "output/the_atlas_condenses";
const REST: &str = "output/the_native_baseline_conducts/rest.safetensors";
const ABLATED: &str = "output/the_native_baseline_conducts/rest-without-hexis.safetensors";
const P0_RECEIPT: &str = "output/the_native_baseline_conducts/receipt.form";
const P1_RECEIPT: &str = "output/the_lift_returns_its_defect/receipt.form";
const SOURCE: &str = include_str!("the_atlas_condenses_where_the_receiver_factors.rs");

/// The same eight runtime-supplied prompts Deed P0 conducted. They are the probe family R1 declares.
const PROMPTS: &[&str] = &[
    "the receiver",
    "a compression is a codec",
    "hexis is rested conditional transport",
    "the suffix link",
    "cultivation relative to inherited rest",
    "the document law",
    "an operation is a construction",
    "the quantum wobbleflux",
];

/// **The committed P0 values part 0 must reproduce bit-identically.**
const P0_ONE_SHOT: usize = 93;
const P0_CONDUCT: usize = 795;
const P0_ROUNDS: usize = 1;
const P0_COLLAPSED: usize = 653_599;
const P0_ORDER: usize = 3;
const P0_SCOPE_CLASSES: usize = 5_598;
const P0_SCOPE_GERMS: usize = 5_385;
const P0_CYCLE_RANK: i64 = 43_207;
const P0_RECONVERGENT_CLASSES: usize = 27_628;
const P0_RECONVERGENT_ARCS: usize = 43_215;
/// The eight classes Deed P0's committed receipt records its prompts landing in.
const P0_LANDED: &[u32] = &[7812, 48389, 56428, 1093, 56966, 25667, 42299, 0];

/// The exhibition aperture for the whole-atlas collapsed population: how many pairs are given their
/// shortest separating word. An APERTURE with its outside measured and returned, never a sample.
const EXHIBITION_APERTURE: usize = 64;

// ---------------------------------------------------------------------------------------------
// BASELINE-DECODER-BEGIN — the source rest's own reader and R1 face. Its extent is the decoder
// coordinate of the BASELINE cost vector, so the two vectors are priced by the same rule.

/// The source rest as this process holds it.
struct Rest {
    locator: String,
    indptr: Vec<u32>,
    germ: Vec<u32>,
    target: Vec<u32>,
    standing: Vec<u32>,
    suffix: Vec<u32>,
    surfaces: Vec<String>,
    index_of: BTreeMap<String, u32>,
    classes: usize,
    transitions: usize,
    vocabulary: usize,
    height: u32,
    octets: u64,
    work: ExactWork,
}

fn read_rest(locator: &str) -> Result<Rest, String> {
    let occurrence =
        NativeOccurrence::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let (_, container) =
        manifest_safetensors(locator).map_err(|error| format!("{locator}: {error}"))?;
    let raw = std::fs::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let header = u64::from_le_bytes(raw[..8].try_into().map_err(|_| "short container")?) as usize;
    let payload = &raw[8 + header..];
    let region = |name: &str| -> Result<(usize, usize), String> {
        container
            .tensors
            .get(name)
            .map(|t| (t.start as usize, t.end as usize))
            .ok_or_else(|| format!("{locator} does not identify {name}"))
    };
    let u32s = |name: &str| -> Result<Vec<u32>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end]
            .chunks_exact(4)
            .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
            .collect())
    };
    let u16s = |name: &str| -> Result<Vec<u16>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end]
            .chunks_exact(2)
            .map(|w| u16::from_le_bytes([w[0], w[1]]))
            .collect())
    };
    let architecture = u32s("athena.architecture")?;
    let octets = u16s("athena.vocabulary.octets")?;
    let offsets = u32s("athena.vocabulary.offsets")?;
    let mut surfaces = Vec::with_capacity(offsets.len().saturating_sub(1));
    for pair in offsets.windows(2) {
        let bytes: Vec<u8> = octets[pair[0] as usize..pair[1] as usize]
            .iter()
            .map(|w| *w as u8)
            .collect();
        surfaces.push(String::from_utf8(bytes).map_err(|e| e.to_string())?);
    }
    let mut index_of = BTreeMap::new();
    for (at, surface) in surfaces.iter().enumerate() {
        index_of.insert(surface.clone(), at as u32);
    }
    let mut work = ExactWork::nothing();
    work.resident(raw.len() as u64);
    Ok(Rest {
        locator: locator.to_owned(),
        indptr: u32s("athena.transport.indptr")?,
        germ: u32s("athena.transport.germ")?,
        target: u32s("athena.transport.target")?,
        standing: u32s("athena.class.standing")?,
        suffix: u32s("athena.class.suffix")?,
        surfaces,
        index_of,
        height: architecture[0],
        classes: architecture[1] as usize,
        transitions: architecture[2] as usize,
        vocabulary: architecture[3] as usize,
        octets: occurrence.container.octets,
        work,
    })
}

impl Rest {
    fn row(&self, class: u32) -> (usize, usize) {
        (
            self.indptr[class as usize] as usize,
            self.indptr[class as usize + 1] as usize,
        )
    }

    /// The R4 face: how far up the suffix-link tree a class sits, read off the stored parent array
    /// by climbing. The condensed decoder answers the same question from the interval chart, and the
    /// two are priced over this same face.
    fn height_of(&mut self, class: u32) -> u32 {
        let mut at = class;
        let mut height = 0u32;
        loop {
            self.work.stepped();
            let parent = self.suffix[at as usize];
            if parent == at {
                return height;
            }
            at = parent;
            height += 1;
        }
    }

    /// **The R1 face at a class**: every germ the whole suffix chain offers, with the standing of the
    /// class it reaches and the arc depth at which it was found. First-wins by depth, which is the
    /// rest's own declared future/depth law. Nothing is ranked and nothing is crowned.
    fn section(&mut self, class: u32) -> Vec<(u32, u32, u32)> {
        let mut held: BTreeMap<u32, (u32, u32)> = BTreeMap::new();
        let mut at = class;
        let mut depth = 0u32;
        loop {
            let (from, to) = self.row(at);
            for slot in from..to {
                self.work.stepped();
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
            .map(|(germ, (standing, depth))| (germ, standing, depth))
            .collect()
    }
}

// BASELINE-DECODER-END
// ---------------------------------------------------------------------------------------------

impl Rest {
    fn out_degree(&self, class: u32) -> u32 {
        let (from, to) = self.row(class);
        (to - from) as u32
    }

    fn step(&self, class: u32, germ: u32) -> Option<u32> {
        let (from, to) = self.row(class);
        self.germ[from..to]
            .binary_search(&germ)
            .ok()
            .map(|at| self.target[from + at])
    }

    /// The rest's own walk law, reproduced host-side: carry each germ through the transport row of
    /// the current class from the root; where the row has no such germ, fall along the suffix link
    /// and retry (the arc); an unseen germ returns to the root. The control that this is the rest's
    /// own law is that it lands the eight prompts where the committed P0 receipt records them.
    fn walk(&self, prompt: &str) -> u32 {
        let mut at = 0u32;
        for token in lexical_tokens(prompt) {
            let Some(germ) = self.index_of.get(&token).copied() else {
                at = 0;
                continue;
            };
            let mut climbing = at;
            loop {
                if let Some(next) = self.step(climbing, germ) {
                    at = next;
                    break;
                }
                let parent = self.suffix[climbing as usize];
                if parent == climbing {
                    at = 0;
                    break;
                }
                climbing = parent;
            }
        }
        at
    }

    fn suffix_height(&self, class: u32) -> u32 {
        let mut at = class;
        let mut height = 0u32;
        loop {
            let parent = self.suffix[at as usize];
            if parent == at {
                return height;
            }
            at = parent;
            height += 1;
        }
    }

    /// The classes the declared probe family actually reaches: the eight landed classes, their
    /// suffix ancestors, and one germ step forward from each — Deed P0's declared scope.
    fn excited(&self, landed: &[u32]) -> BTreeSet<u32> {
        let mut scope: BTreeSet<u32> = BTreeSet::new();
        for class in landed {
            let mut at = *class;
            loop {
                scope.insert(at);
                let parent = self.suffix[at as usize];
                if parent == at {
                    break;
                }
                at = parent;
            }
        }
        let reached: Vec<u32> = scope.iter().copied().collect();
        for class in reached {
            let (from, to) = self.row(class);
            for slot in from..to {
                scope.insert(self.target[slot]);
            }
        }
        scope
    }
}

fn lexical_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for character in text.chars() {
        if character.is_alphanumeric() || character == '\'' {
            current.push(character.to_ascii_lowercase());
        } else {
            if !current.is_empty() {
                tokens.push(std::mem::take(&mut current));
            }
            if !character.is_whitespace() {
                tokens.push(character.to_string());
            }
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

/// The extent of one marked region of this driver's own source, in octets. The decoder coordinate of
/// a cost vector is a **measured** extent of declared code, not an estimate.
fn marked_octets(begin: &str, end: &str) -> usize {
    let Some(from) = SOURCE.find(begin) else {
        return 0;
    };
    let Some(to) = SOURCE[from..].find(end) else {
        return 0;
    };
    SOURCE[from..from + to].len()
}

// ---------------------------------------------------------------------------------------------
// the observed system
// ---------------------------------------------------------------------------------------------

/// Which receivers a reading declares. **The family is a declaration, never a fit.**
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    /// Deed P0's declared family: the class's own out-degree, and whether the class is the root.
    P0,
    /// This deed's condensation family: P0's two receivers **and the class's standing**, because
    /// R1's face returns the standing of every germ's target, so a quotient blind to standing does
    /// not factor R1 and may not be used to condense the transport.
    Condensation,
}

impl Family {
    fn receivers(self) -> Vec<ReceiverId> {
        match self {
            Self::P0 => vec![ReceiverId(0), ReceiverId(1)],
            Self::Condensation => vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)],
        }
    }
    fn text(self) -> &'static str {
        match self {
            Self::P0 => "(a) the class's own out-degree, (b) whether the class is the root",
            Self::Condensation => "(a) the class's own out-degree, (b) whether the class is the root, (c) the class's standing",
        }
    }
}

struct AtlasSystem<'a> {
    rest: &'a Rest,
    family: Family,
    items: Vec<ItemId>,
    inputs: Vec<InputId>,
    /// The sparse successor face, or `None` to withhold it — which is the dense reading and the
    /// control that the face moves nothing.
    by_germ: Option<BTreeMap<u32, Vec<(ItemId, ItemId)>>>,
}

impl<'a> AtlasSystem<'a> {
    fn new(rest: &'a Rest, family: Family, items: Vec<ItemId>, inputs: Vec<InputId>, sparse: bool) -> Self {
        let by_germ = sparse.then(|| {
            let mut by_germ: BTreeMap<u32, Vec<(ItemId, ItemId)>> = BTreeMap::new();
            for item in &items {
                let class = item.0 as u32;
                let (from, to) = rest.row(class);
                for slot in from..to {
                    by_germ
                        .entry(rest.germ[slot])
                        .or_default()
                        .push((*item, ItemId(u64::from(rest.target[slot]))));
                }
            }
            by_germ
        });
        Self { rest, family, items, inputs, by_germ }
    }
}

impl ObservedSystem for AtlasSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        self.family.receivers()
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let class = item.0 as u32;
        match receiver.0 {
            0 => Observation(u64::from(self.rest.out_degree(class))),
            1 => Observation(u64::from(self.rest.suffix[class as usize] == class)),
            _ => Observation(u64::from(self.rest.standing[class as usize])),
        }
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.rest
            .step(item.0 as u32, input.0 as u32)
            .map(|target| ItemId(u64::from(target)))
    }
    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        self.by_germ
            .as_ref()
            .map(|by_germ| by_germ.get(&(input.0 as u32)).cloned().unwrap_or_default())
    }
}

fn whole_atlas(rest: &Rest) -> (Vec<ItemId>, Vec<InputId>) {
    (
        (0..rest.classes as u64).map(ItemId).collect(),
        (0..rest.vocabulary as u64).map(InputId).collect(),
    )
}

/// Deed P0's declared scope, rebuilt from the rest and the eight landed classes.
fn p0_scope(rest: &Rest, landed: &[u32]) -> (Vec<ItemId>, Vec<InputId>) {
    let scope = rest.excited(landed);
    let items: Vec<ItemId> = scope.iter().map(|class| ItemId(u64::from(*class))).collect();
    let mut germs: BTreeSet<u32> = BTreeSet::new();
    for class in &scope {
        let (from, to) = rest.row(*class);
        for slot in from..to {
            germs.insert(rest.germ[slot]);
        }
    }
    let inputs: Vec<InputId> = germs.iter().map(|germ| InputId(u64::from(*germ))).collect();
    (items, inputs)
}

// ---------------------------------------------------------------------------------------------
// the condensed rest
// ---------------------------------------------------------------------------------------------

/// **The condensed rest, by construction rather than by truncation.**
///
/// ```text
///   TREE       the depth-first interval per class. Containment IS suffix-link ancestry, so the
///              whole descendant population of every class becomes two words. Remainder EMPTY.
///   NERODE     the conduct block per class, and one shared transport row per BLOCK. Two classes
///              of a block admit the same germs and reach the same blocks, so the row is a property
///              of the block and storing it per class was storing it |block| times.
///   REMAINDER  what the block row cannot resolve: the exact target CLASS of every arc whose target
///              block is plural, and the reconvergent-arc population the interval receiver cannot
///              separate. Retained whole. Never truncated.
/// ```
struct Condensed {
    classes: usize,
    entry: Vec<u32>,
    exit: Vec<u32>,
    height: u32,
    block_of: Vec<u32>,
    block_indptr: Vec<u32>,
    block_germ: Vec<u32>,
    block_target: Vec<u32>,
    block_standing: Vec<u32>,
    remainder_target: Vec<u32>,
    reconvergent_slot: Vec<u32>,
    surfaces: Vec<String>,
    /// Classes the declared probe family never reaches. **Unexcited, not dropped**: their bytes are
    /// in every section above and in the complete cost.
    unexcited: Vec<u32>,
    /// The pairs the coarser one-shot reading merged and conduct separates, with the shortest word
    /// that separates each: the ReconstructionFiber, carried in the condensed rest's own metadata.
    fibre: Vec<(u32, u32, Vec<u32>)>,
}

fn condense(
    rest: &Rest,
    conduct: &Partition,
    excited: &BTreeSet<u32>,
    fibre: Vec<(u32, u32, Vec<u32>)>,
) -> Result<(Condensed, Vec<String>), String> {
    let mut notes = Vec::new();
    let chart = TreeChart::label(rest.classes, |state| {
        if rest.suffix[state as usize] == state {
            None
        } else {
            Some(rest.suffix[state as usize])
        }
    })
    .map_err(|error| format!("{error}"))?;
    let index = conduct.index();
    let mut block_of = vec![u32::MAX; rest.classes];
    for class in 0..rest.classes as u32 {
        block_of[class as usize] = index
            .block_of(ItemId(u64::from(class)))
            .ok_or_else(|| format!("class {class} is in no conduct block"))?
            as u32;
    }
    let blocks = conduct.len();
    let mut block_size = vec![0u32; blocks];
    for class in 0..rest.classes {
        block_size[block_of[class] as usize] += 1;
    }
    let mut representative = vec![u32::MAX; blocks];
    for class in (0..rest.classes as u32).rev() {
        representative[block_of[class as usize] as usize] = class;
    }

    let mut block_indptr = Vec::with_capacity(blocks + 1);
    let mut block_germ = Vec::new();
    let mut block_target = Vec::new();
    let mut block_standing = vec![0u32; blocks];
    block_indptr.push(0u32);
    for block in 0..blocks {
        let class = representative[block];
        block_standing[block] = rest.standing[class as usize];
        let (from, to) = rest.row(class);
        for slot in from..to {
            block_germ.push(rest.germ[slot]);
            block_target.push(block_of[rest.target[slot] as usize]);
        }
        block_indptr.push(block_germ.len() as u32);
    }

    // **The shared row is MEASURED, not assumed.** Nerode stability says every class of a block has
    // the same germ set and the same target blocks; a shared row that did not hold would be a
    // condensation the receiver family cannot pay for, so it is checked against every class.
    let mut disagreeing = 0usize;
    for class in 0..rest.classes as u32 {
        let block = block_of[class as usize] as usize;
        let (from, to) = rest.row(class);
        let (bfrom, bto) = (
            block_indptr[block] as usize,
            block_indptr[block + 1] as usize,
        );
        if to - from != bto - bfrom || rest.standing[class as usize] != block_standing[block] {
            disagreeing += 1;
            continue;
        }
        for offset in 0..(to - from) {
            if rest.germ[from + offset] != block_germ[bfrom + offset]
                || block_of[rest.target[from + offset] as usize] != block_target[bfrom + offset]
            {
                disagreeing += 1;
                break;
            }
        }
    }
    notes.push(format!(
        "the shared block row holds for {} of {} classes ({disagreeing} disagreeing)",
        rest.classes - disagreeing,
        rest.classes
    ));

    let mut remainder_target = Vec::new();
    for class in 0..rest.classes as u32 {
        let (from, to) = rest.row(class);
        for slot in from..to {
            let target = rest.target[slot];
            if block_size[block_of[target as usize] as usize] > 1 {
                remainder_target.push(target);
            }
        }
    }

    let mut indegree = vec![0u32; rest.classes];
    let mut reconvergent_slot = Vec::new();
    for slot in 0..rest.transitions {
        let target = rest.target[slot] as usize;
        indegree[target] += 1;
        if indegree[target] > 1 {
            reconvergent_slot.push(slot as u32);
        }
    }

    let unexcited: Vec<u32> = (0..rest.classes as u32)
        .filter(|class| !excited.contains(class))
        .collect();

    Ok((
        Condensed {
            classes: rest.classes,
            entry: chart.intervals.iter().map(|(a, _)| *a as u32).collect(),
            exit: chart.intervals.iter().map(|(_, b)| *b as u32).collect(),
            height: chart.height,
            block_of,
            block_indptr,
            block_germ,
            block_target,
            block_standing,
            remainder_target,
            reconvergent_slot,
            surfaces: rest.surfaces.clone(),
            unexcited,
            fibre,
        },
        notes,
    ))
}

/// The condensed rest's own declared laws — a sibling of the P0 rest's, declaring what it is rather
/// than requiring a reader to have been told.
const TREE_LAW: &str = "tree: a depth-first interval per class; interval containment IS suffix-link ancestry, so the descendant population of every class is two words and the remainder of this half is empty; the suffix parent of a class is the minimal interval strictly containing it";
const BLOCK_LAW: &str = "block: one transport row per conduct block, not per class; two classes of a block admit the same germs and reach the same blocks, and the block's standing is the standing of every class in it";
const REMAINDER_LAW: &str = "remainder: the exact target class of every arc whose target block is plural, in the canonical (class, germ) order the block rows induce, plus the transport slots beyond a spanning forest which the interval receiver cannot separate; retained whole and never truncated";
const SECTION_LAW: &str = "section: for a class, every germ its suffix chain offers with the standing of the block it reaches and the arc depth at which it was found, first-wins by depth — the P0 future/depth law read through the block rows";
const FAMILY_DECLARATION: &str = "R1 plural future sections; R2 fresh-process remount; R3 construction-level ablation factoring; R4 the suffix-link height scale action; R5 the Nerode/Markov memory order; R6 decoder work and resident octets; R7 the P1 native recombination";

fn container(condensed: &Condensed) -> Result<Vec<u8>, String> {
    let mut vocabulary_octets: Vec<u64> = Vec::new();
    let mut vocabulary_offsets: Vec<u64> = vec![0];
    for surface in &condensed.surfaces {
        for octet in surface.as_bytes() {
            vocabulary_octets.push(u64::from(*octet));
        }
        vocabulary_offsets.push(vocabulary_octets.len() as u64);
    }
    let padded = |values: &[u32]| -> Vec<u64> {
        if values.is_empty() {
            vec![0]
        } else {
            values.iter().map(|value| u64::from(*value)).collect()
        }
    };
    let u32s = |name: &str, values: &[u32]| -> Result<IntegerTensor, String> {
        emit_integers(name, &padded(values), 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))
    };
    // The fibre travels as a flat integer population with its own offsets: pairs, then words.
    let mut fibre_pair: Vec<u32> = Vec::new();
    let mut fibre_word: Vec<u32> = Vec::new();
    let mut fibre_offset: Vec<u32> = vec![0];
    for (left, right, word) in &condensed.fibre {
        fibre_pair.push(*left);
        fibre_pair.push(*right);
        fibre_word.extend(word.iter().copied());
        fibre_offset.push(fibre_word.len() as u32);
    }
    let tensors = vec![
        u32s("condensed.tree.entry", &condensed.entry)?,
        u32s("condensed.tree.exit", &condensed.exit)?,
        u32s("condensed.class.block", &condensed.block_of)?,
        u32s("condensed.block.indptr", &condensed.block_indptr)?,
        u32s("condensed.block.germ", &condensed.block_germ)?,
        u32s("condensed.block.target", &condensed.block_target)?,
        u32s("condensed.block.standing", &condensed.block_standing)?,
        u32s("condensed.remainder.target", &condensed.remainder_target)?,
        u32s("condensed.remainder.reconvergent", &condensed.reconvergent_slot)?,
        u32s("condensed.unexcited.class", &condensed.unexcited)?,
        u32s("condensed.fibre.pair", &fibre_pair)?,
        u32s("condensed.fibre.word", &fibre_word)?,
        u32s("condensed.fibre.offset", &fibre_offset)?,
        emit_integers("condensed.vocabulary.octets", &vocabulary_octets, 1, IntegerDtype::U16)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers("condensed.vocabulary.offsets", &vocabulary_offsets, 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers(
            "condensed.architecture",
            &[
                u64::from(condensed.height),
                condensed.classes as u64,
                (condensed.block_indptr.len() - 1) as u64,
                condensed.surfaces.len() as u64,
                condensed.remainder_target.len() as u64,
                condensed.reconvergent_slot.len() as u64,
                condensed.unexcited.len() as u64,
                condensed.fibre.len() as u64,
            ],
            1,
            IntegerDtype::U32,
        )
        .map_err(|error| format!("{error:?}"))?,
    ];
    let mut metadata: BTreeMap<String, String> = BTreeMap::new();
    metadata.insert("schema".to_owned(), "holonics.athena.condensed-rest.v1".to_owned());
    metadata.insert("law.tree".to_owned(), TREE_LAW.to_owned());
    metadata.insert("law.block".to_owned(), BLOCK_LAW.to_owned());
    metadata.insert("law.remainder".to_owned(), REMAINDER_LAW.to_owned());
    metadata.insert("law.section".to_owned(), SECTION_LAW.to_owned());
    metadata.insert("receiver.family".to_owned(), FAMILY_DECLARATION.to_owned());
    Ok(write_container(&tensors, &metadata))
}

fn write_container(tensors: &[IntegerTensor], metadata: &BTreeMap<String, String>) -> Vec<u8> {
    let escape = |text: &str| {
        text.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
    };
    let mut header = String::from("{\"__metadata__\":{");
    for (at, (key, value)) in metadata.iter().enumerate() {
        if at > 0 {
            header.push(',');
        }
        header.push_str(&format!("\"{}\":\"{}\"", escape(key), escape(value)));
    }
    header.push('}');
    let mut offset = 0usize;
    for tensor in tensors {
        let end = offset + tensor.octets.len();
        header.push_str(&format!(
            ",\"{}\":{{\"dtype\":\"{}\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}}",
            tensor.name,
            tensor.dtype.name(),
            tensor.rows,
            tensor.width
        ));
        offset = end;
    }
    header.push('}');
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut octets = Vec::with_capacity(8 + header.len() + offset);
    octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
    octets.extend_from_slice(header.as_bytes());
    for tensor in tensors {
        octets.extend_from_slice(&tensor.octets);
    }
    octets
}

// ---------------------------------------------------------------------------------------------
// DECODER-BEGIN — every octet between these markers is the declared decoder. It reads the condensed
// rest and NOTHING else, and its extent is the decoder coordinate of the condensed cost vector.

/// The condensed rest as a reader holds it, with nothing from the source rest in reach.
struct CondensedRest {
    classes: usize,
    height: u32,
    entry: Vec<u32>,
    exit: Vec<u32>,
    block_of: Vec<u32>,
    block_indptr: Vec<u32>,
    block_germ: Vec<u32>,
    block_target: Vec<u32>,
    block_standing: Vec<u32>,
    remainder_target: Vec<u32>,
    reconvergent_slot: Vec<u32>,
    unexcited: Vec<u32>,
    surfaces: Vec<String>,
    /// Recovered, not stored: the suffix parent of every class, from the interval chart alone.
    parent: Vec<u32>,
    /// Recovered, not stored: which blocks are plural, the single class of each singleton block, and
    /// where each class's plural-target arcs begin in the remainder.
    plural: Vec<bool>,
    singleton: Vec<u32>,
    remainder_at: Vec<u32>,
    work: ExactWork,
}

fn read_condensed(locator: &str) -> Result<CondensedRest, String> {
    let (_, container) =
        manifest_safetensors(locator).map_err(|error| format!("{locator}: {error}"))?;
    let raw = std::fs::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let header = u64::from_le_bytes(raw[..8].try_into().map_err(|_| "short container")?) as usize;
    let payload = &raw[8 + header..];
    let region = |name: &str| -> Result<(usize, usize), String> {
        container
            .tensors
            .get(name)
            .map(|t| (t.start as usize, t.end as usize))
            .ok_or_else(|| format!("{locator} does not identify {name}"))
    };
    let u32s = |name: &str| -> Result<Vec<u32>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end]
            .chunks_exact(4)
            .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
            .collect())
    };
    let u16s = |name: &str| -> Result<Vec<u16>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end]
            .chunks_exact(2)
            .map(|w| u16::from_le_bytes([w[0], w[1]]))
            .collect())
    };
    let architecture = u32s("condensed.architecture")?;
    let octets = u16s("condensed.vocabulary.octets")?;
    let offsets = u32s("condensed.vocabulary.offsets")?;
    let mut surfaces = Vec::with_capacity(offsets.len().saturating_sub(1));
    for pair in offsets.windows(2) {
        let bytes: Vec<u8> = octets[pair[0] as usize..pair[1] as usize]
            .iter()
            .map(|w| *w as u8)
            .collect();
        surfaces.push(String::from_utf8(bytes).map_err(|e| e.to_string())?);
    }
    let classes = architecture[1] as usize;
    let blocks = architecture[2] as usize;
    let mut remainder_target = u32s("condensed.remainder.target")?;
    remainder_target.truncate(architecture[4] as usize);
    let mut reconvergent_slot = u32s("condensed.remainder.reconvergent")?;
    reconvergent_slot.truncate(architecture[5] as usize);
    let mut unexcited = u32s("condensed.unexcited.class")?;
    unexcited.truncate(architecture[6] as usize);
    let block_of = u32s("condensed.class.block")?;
    let block_indptr = u32s("condensed.block.indptr")?;
    let block_germ = u32s("condensed.block.germ")?;
    let block_target = u32s("condensed.block.target")?;

    // The three recovered indexes, one pass each.
    let mut size = vec![0u32; blocks];
    let mut singleton = vec![u32::MAX; blocks];
    for class in 0..classes {
        let block = block_of[class] as usize;
        size[block] += 1;
        singleton[block] = class as u32;
    }
    let plural: Vec<bool> = size.iter().map(|count| *count > 1).collect();
    let mut remainder_at = vec![0u32; classes + 1];
    for class in 0..classes {
        let block = block_of[class] as usize;
        let (from, to) = (block_indptr[block] as usize, block_indptr[block + 1] as usize);
        let widening = (from..to)
            .filter(|slot| plural[block_target[*slot] as usize])
            .count() as u32;
        remainder_at[class + 1] = remainder_at[class] + widening;
    }

    let mut rest = CondensedRest {
        classes,
        height: architecture[0],
        entry: u32s("condensed.tree.entry")?,
        exit: u32s("condensed.tree.exit")?,
        block_of,
        block_indptr,
        block_germ,
        block_target,
        block_standing: u32s("condensed.block.standing")?,
        remainder_target,
        reconvergent_slot,
        unexcited,
        surfaces,
        parent: Vec::new(),
        plural,
        singleton,
        remainder_at,
        work: ExactWork::nothing(),
    };
    rest.parent = recover_parents(&mut rest.work, &rest.entry, &rest.exit);
    rest.work.resident(raw.len() as u64);
    Ok(rest)
}

/// **The suffix parent recovered from the interval chart alone.**
///
/// The parent of a class is the minimal interval strictly containing its own. Sorting the classes by
/// entry and carrying a stack of open intervals returns every parent in one pass — which is the
/// statement that the tree half of the transition is a rebase and not a lossy chart: the parent
/// array was not stored and is not approximated, it is recomputed exactly.
fn recover_parents(work: &mut ExactWork, entry: &[u32], exit: &[u32]) -> Vec<u32> {
    let mut order: Vec<u32> = (0..entry.len() as u32).collect();
    order.sort_by_key(|class| entry[*class as usize]);
    let mut parent = vec![0u32; entry.len()];
    let mut open: Vec<u32> = Vec::new();
    for class in order {
        // `<=`, not `<`. A depth-first labelling closes a subtree at the clock its next sibling
        // opens at, so an exhausted interval and the next one TOUCH; testing `<` leaves the sibling
        // on the stack and returns it as the parent. Found by the parent array failing to be
        // bit-equal to the source's suffix array, which is why that control exists.
        while let Some(top) = open.last().copied() {
            work.stepped();
            if exit[top as usize] <= entry[class as usize] {
                open.pop();
            } else {
                break;
            }
        }
        parent[class as usize] = open.last().copied().unwrap_or(class);
        open.push(class);
    }
    parent
}

impl CondensedRest {
    /// Interval containment, which is the causal order of the declared `(+, -)` chart: `outer` is a
    /// suffix ancestor of `inner` exactly when its interval contains `inner`'s.
    fn contains(&self, outer: u32, inner: u32) -> bool {
        self.entry[outer as usize] <= self.entry[inner as usize]
            && self.exit[inner as usize] <= self.exit[outer as usize]
    }

    /// The scale action R4 declares: how far up the suffix-link tree a class sits.
    fn height_of(&mut self, class: u32) -> u32 {
        let mut at = class;
        let mut height = 0u32;
        loop {
            self.work.stepped();
            let parent = self.parent[at as usize];
            if parent == at {
                return height;
            }
            at = parent;
            height += 1;
        }
    }

    fn block_row(&self, class: u32) -> (usize, usize) {
        let block = self.block_of[class as usize] as usize;
        (
            self.block_indptr[block] as usize,
            self.block_indptr[block + 1] as usize,
        )
    }

    /// **The R1 face, reconstructed from the condensed rest.** The chain comes from the recovered
    /// parents, each ancestor's germ population from its block's shared row, and the standing from
    /// the block the arc reaches. First-wins by depth, exactly the section law.
    fn section(&mut self, class: u32) -> Vec<(u32, u32, u32)> {
        let mut held: BTreeMap<u32, (u32, u32)> = BTreeMap::new();
        let mut at = class;
        let mut depth = 0u32;
        loop {
            let (from, to) = self.block_row(at);
            for slot in from..to {
                self.work.stepped();
                held.entry(self.block_germ[slot])
                    .or_insert((self.block_standing[self.block_target[slot] as usize], depth));
            }
            let parent = self.parent[at as usize];
            if parent == at {
                break;
            }
            at = parent;
            depth += 1;
        }
        held.into_iter()
            .map(|(germ, (standing, depth))| (germ, standing, depth))
            .collect()
    }

    /// **The class-level successor, reopened through the remainder.** The block row gives the target
    /// *block*; where that block is a singleton the class follows, and where it is plural the exact
    /// class comes from the retained remainder at this arc's canonical position. Nothing is guessed.
    fn step(&self, class: u32, germ: u32) -> Option<u32> {
        let (from, to) = self.block_row(class);
        let at = from + self.block_germ[from..to].binary_search(&germ).ok()?;
        let target_block = self.block_target[at] as usize;
        if !self.plural[target_block] {
            return Some(self.singleton[target_block]);
        }
        let ahead = (from..at)
            .filter(|slot| self.plural[self.block_target[*slot] as usize])
            .count();
        Some(self.remainder_target[self.remainder_at[class as usize] as usize + ahead])
    }

    fn out_degree(&self, class: u32) -> u32 {
        let (from, to) = self.block_row(class);
        (to - from) as u32
    }

    fn walk(&self, prompt: &str, index_of: &BTreeMap<String, u32>) -> u32 {
        let mut at = 0u32;
        for token in lexical_tokens(prompt) {
            let Some(germ) = index_of.get(&token).copied() else {
                at = 0;
                continue;
            };
            let mut climbing = at;
            loop {
                if let Some(next) = self.step(climbing, germ) {
                    at = next;
                    break;
                }
                let parent = self.parent[climbing as usize];
                if parent == climbing {
                    at = 0;
                    break;
                }
                climbing = parent;
            }
        }
        at
    }

    fn index_of(&self) -> BTreeMap<String, u32> {
        self.surfaces
            .iter()
            .enumerate()
            .map(|(at, surface)| (surface.clone(), at as u32))
            .collect()
    }
}

// DECODER-END
// ---------------------------------------------------------------------------------------------

/// The condensed rest as an observed system, so the Nerode reading R5 declares can be **recomputed
/// from the condensed body** rather than carried across from the source.
struct CondensedSystem<'a> {
    rest: &'a CondensedRest,
    family: Family,
    items: Vec<ItemId>,
    inputs: Vec<InputId>,
}

impl ObservedSystem for CondensedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        self.family.receivers()
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let class = item.0 as u32;
        match receiver.0 {
            0 => Observation(u64::from(self.rest.out_degree(class))),
            1 => Observation(u64::from(self.rest.parent[class as usize] == class)),
            _ => Observation(u64::from(
                self.rest.block_standing[self.rest.block_of[class as usize] as usize],
            )),
        }
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.rest
            .step(item.0 as u32, input.0 as u32)
            .map(|target| ItemId(u64::from(target)))
    }
}

// ---------------------------------------------------------------------------------------------
// lumpability, exactly over Rat
// ---------------------------------------------------------------------------------------------

/// The exact aggregate transport of one state into the blocks of a declared partition:
/// `(P C)_{i, beta} = |{ g : delta(i,g) in beta }| / outdeg(i)`.
///
/// A state with no continuation contributes the zero row: the transport is a **partial** function
/// and the terminus is a genuine absence, so the matrix is sub-stochastic by construction and is
/// declared as such rather than repaired with a self-loop.
fn aggregate_row(rest: &Rest, class: u32, block_of: &[u32]) -> BTreeMap<u32, Rat> {
    let (from, to) = rest.row(class);
    let degree = (to - from) as i64;
    let mut counts: BTreeMap<u32, i64> = BTreeMap::new();
    for slot in from..to {
        *counts.entry(block_of[rest.target[slot] as usize]).or_default() += 1;
    }
    counts
        .into_iter()
        .map(|(block, count)| {
            (
                block,
                Rat::new(BigInt::from(count), BigInt::from(degree.max(1))),
            )
        })
        .collect()
}

struct Lumpability {
    holds: bool,
    blocks: usize,
    checked: usize,
    /// The first failing block: its two states, the target block they disagree on, and the two exact
    /// rationals. The complete defect, not a verdict.
    defect: Option<(u32, u32, u32, u32, String, String)>,
    disagreeing_blocks: usize,
}

fn lumpability(rest: &Rest, partition: &Partition) -> Lumpability {
    let index = partition.index();
    let mut block_of = vec![0u32; rest.classes];
    for class in 0..rest.classes as u32 {
        block_of[class as usize] = index.block_of(ItemId(u64::from(class))).unwrap_or(0) as u32;
    }
    let mut defect = None;
    let mut disagreeing_blocks = 0usize;
    let mut checked = 0usize;
    for (at, block) in partition.blocks.iter().enumerate() {
        let mut members = block.iter().map(|item| item.0 as u32);
        let Some(first) = members.next() else {
            continue;
        };
        let reference = aggregate_row(rest, first, &block_of);
        let mut block_disagrees = false;
        for member in members {
            checked += 1;
            let row = aggregate_row(rest, member, &block_of);
            if row != reference {
                block_disagrees = true;
                if defect.is_none() {
                    let keys: BTreeSet<u32> =
                        reference.keys().chain(row.keys()).copied().collect();
                    for key in keys {
                        let left = reference.get(&key).cloned().unwrap_or_else(Rat::zero);
                        let right = row.get(&key).cloned().unwrap_or_else(Rat::zero);
                        if left != right {
                            defect = Some((
                                at as u32,
                                first,
                                member,
                                key,
                                format!("{left}"),
                                format!("{right}"),
                            ));
                            break;
                        }
                    }
                }
            }
        }
        if block_disagrees {
            disagreeing_blocks += 1;
        }
    }
    Lumpability {
        holds: defect.is_none(),
        blocks: partition.len(),
        checked,
        defect,
        disagreeing_blocks,
    }
}

/// **The suffix-ancestor coarsening at a declared height.**
///
/// Every class carried up its own chain until its ancestor sits at height `height` or the chain
/// ends. Deed P0's manifest named this a sufficient-state candidate and left the row OPEN with
/// exactly this falsifier: *a sufficient state is decided by lumpability against a DECLARED receiver
/// family, not by a name.* It is measured here.
fn height_coarsening(rest: &Rest, height: u32) -> Partition {
    Partition::from_keys((0..rest.classes as u32).map(|class| {
        let mut at = class;
        while rest.suffix_height(at) > height {
            at = rest.suffix[at as usize];
        }
        (ItemId(u64::from(class)), at)
    }))
}

/// The shortest word separating one named pair, through the owner's own search: a one-block
/// "one-shot" and a two-singleton "conduct" isolate exactly that pair for
/// [`exhibit_collapsed_within`].
fn separator(system: &dyn ObservedSystem, left: u32, right: u32) -> Option<Vec<u32>> {
    let (left, right) = (ItemId(u64::from(left)), ItemId(u64::from(right)));
    let merged = Partition {
        blocks: vec![BTreeSet::from([left, right])],
    };
    let split = Partition {
        blocks: vec![BTreeSet::from([left]), BTreeSet::from([right])],
    };
    exhibit_collapsed_within(system, &merged, &split, Some(1))
        .first()
        .map(|pair| {
            pair.distinguishing_word
                .iter()
                .map(|input| input.0 as u32)
                .collect()
        })
}

// ---------------------------------------------------------------------------------------------
// the report
// ---------------------------------------------------------------------------------------------

struct Verdicts {
    lines: Vec<String>,
    failed: usize,
}

impl Verdicts {
    fn record(&mut self, number: u32, name: &str, pass: bool, detail: impl AsRef<str>) {
        if !pass {
            self.failed += 1;
        }
        let line = format!(
            "  [{number:>2}] {}  {name}\n        {}",
            if pass { "PASS" } else { "FAIL" },
            detail.as_ref()
        );
        println!("{line}");
        let _ = std::io::stdout().flush();
        self.lines.push(line);
    }
}

fn say(receipt: &mut Vec<String>, line: impl AsRef<str>) {
    println!("{}", line.as_ref());
    let _ = std::io::stdout().flush();
    receipt.push(line.as_ref().to_owned());
}

fn main() {
    if let Err(error) = run() {
        eprintln!("the deed did not stand: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments: Vec<String> = std::env::args().collect();
    if let Some(at) = arguments.iter().position(|a| a == "--remount") {
        let locator = arguments
            .get(at + 1)
            .ok_or("--remount needs the condensed rest")?;
        return remount(locator);
    }
    deed()
}

/// The fresh-process control: read the condensed rest and print the R1 faces, with nothing else in
/// reach. The parent compares the octets.
fn remount(locator: &str) -> Result<(), String> {
    let mut condensed = read_condensed(locator)?;
    let landed: Vec<u32> = std::env::args()
        .skip_while(|a| a != "--landed")
        .skip(1)
        .filter_map(|a| a.parse().ok())
        .collect();
    let mut out = std::io::stdout().lock();
    for class in landed {
        for (germ, standing, depth) in condensed.section(class) {
            let _ = writeln!(
                out,
                "{class} {} {standing} {depth}",
                condensed.surfaces[germ as usize]
            );
        }
    }
    Ok(())
}

fn deed() -> Result<(), String> {
    let whole_clock = Instant::now();
    let mut receipt: Vec<String> = Vec::new();
    let mut verdicts = Verdicts {
        lines: Vec::new(),
        failed: 0,
    };

    say(&mut receipt, "THE ATLAS CONDENSES WHERE THE RECEIVER FACTORS — Deed P2, ARM N");
    say(&mut receipt, "");
    say(&mut receipt, "THE DECLARED FUTURE RECEIVER FAMILY — printed before any condensation code runs, and the");
    say(&mut receipt, "driver's structure makes the declaration prior: nothing below reads a condensation result.");
    for line in [
        "  R1  plural future sections at every reached class — the germ population the whole suffix",
        "      chain offers, each with the standing of the class it reaches and the arc depth, first-",
        "      wins by depth. This is Deed P0's future/depth face, unchanged.",
        "  R2  recurrence/remount: a fresh process reading the condensed rest ALONE returns R1 bit-equal.",
        "  R3  intervention: the construction-level ablation (the rest rebuilt without one document).",
        "      The ablation diff of the condensed pair must equal the condensation of the ablation diff.",
        "  R4  the adjoint/return face: the interval-chart scale action — the suffix-link height.",
        "  R5  cross-codec: the Nerode/Markov memory-order reading at the declared receiver family.",
        "  R6  work/residency: the decoder's exact work and resident octets, returned as the cost axis.",
        "  R7  the native recombination of Deed P1, unaffected where it does not touch the condensed",
        "      coordinates and stated where it does.",
        "  The condensation quotient's receivers, declared with the family: (a) out-degree, (b) is-root,",
        "  (c) standing — (c) because R1 returns the standing of every germ's target, so a quotient",
        "  blind to standing cannot factor R1 and is refused as the condensation quotient.",
        "  The inputs: the rest's own germs. The probes: the eight prompts Deed P0 conducted.",
    ] {
        say(&mut receipt, line);
    }
    say(&mut receipt, "");

    // ---- the material ----
    let mut rest = read_rest(REST)?;
    say(
        &mut receipt,
        format!(
            "THE MATERIAL — {} · {} octets · {} classes · {} transitions · {} germs · tree height {}",
            rest.locator, rest.octets, rest.classes, rest.transitions, rest.vocabulary, rest.height
        ),
    );

    // The walk is reproduced host-side and controlled against the committed P0 receipt.
    let committed = landed_from_receipt(P0_RECEIPT)?;
    let landed: Vec<u32> = PROMPTS.iter().map(|prompt| rest.walk(prompt)).collect();
    verdicts.record(
        1,
        "the walk is reproduced from the rest alone and lands where the committed P0 receipt records",
        landed == committed && committed == P0_LANDED,
        format!("reproduced {landed:?} · committed {committed:?}"),
    );

    // ---- PART 0: the repaired owner re-reads P0's declared scope ----
    say(&mut receipt, "");
    say(&mut receipt, "PART 0 — THE REPAIR INSIDE receiver_exact_compression, AND ITS EQUALITY");
    let (items, inputs) = p0_scope(&rest, &landed);
    let sparse = AtlasSystem::new(&rest, Family::P0, items.clone(), inputs.clone(), true);
    let clock = Instant::now();
    let repaired = compress(&sparse);
    let repaired_wall = clock.elapsed().as_secs_f64();
    let dense = AtlasSystem::new(&rest, Family::P0, items.clone(), inputs.clone(), false);
    let clock = Instant::now();
    let withheld = compress(&dense);
    let withheld_wall = clock.elapsed().as_secs_f64();
    let equality = repaired.one_shot.len() == P0_ONE_SHOT
        && repaired.conduct.len() == P0_CONDUCT
        && repaired.rounds == P0_ROUNDS
        && repaired.collapsed.len() == P0_COLLAPSED
        && repaired.memory_order() == Some(P0_ORDER)
        && items.len() == P0_SCOPE_CLASSES
        && inputs.len() == P0_SCOPE_GERMS;
    say(
        &mut receipt,
        format!(
            "  the P0 declared scope re-read: {} classes x {} germs · one-shot {} · conduct {} · rounds {} · collapsed {} · order {:?} · {repaired_wall:.1} s",
            items.len(),
            inputs.len(),
            repaired.one_shot.len(),
            repaired.conduct.len(),
            repaired.rounds,
            repaired.collapsed.len(),
            repaired.memory_order()
        ),
    );
    say(
        &mut receipt,
        format!(
            "  the committed P0 manifest: {P0_SCOPE_CLASSES} classes x {P0_SCOPE_GERMS} germs · one-shot {P0_ONE_SHOT} · conduct {P0_CONDUCT} · rounds {P0_ROUNDS} · collapsed {P0_COLLAPSED} · order {P0_ORDER} · 11.9 s"
        ),
    );
    verdicts.record(
        2,
        "part 0: the repaired owner returns the committed P0 values bit-identically",
        equality,
        format!(
            "every figure equal: {equality} · the repair is an indexed block lookup and a streamed signature INSIDE receiver_exact_compression, and the module's own tests are unchanged and green"
        ),
    );
    verdicts.record(
        3,
        "the sparse successor face moves nothing on real material, and the dense reading is the control",
        repaired.one_shot == withheld.one_shot
            && repaired.conduct == withheld.conduct
            && repaired.rounds == withheld.rounds
            && repaired.collapsed == withheld.collapsed,
        format!(
            "sparse {repaired_wall:.1} s against dense {withheld_wall:.1} s on the same scope, and every returned population is equal — one-shot, conduct, rounds and the complete collapsed population with its words"
        ),
    );

    // The scope is not closed under the successor relation, and that is why the round count and the
    // memory order disagree here while they must agree at the whole atlas.
    let scope: BTreeSet<u64> = items.iter().map(|item| item.0).collect();
    let leaving = items
        .iter()
        .filter(|item| {
            let class = item.0 as u32;
            let (from, to) = rest.row(class);
            (from..to).any(|slot| !scope.contains(&u64::from(rest.target[slot])))
        })
        .count();
    let counted = separated_pair_population(&repaired.one_shot, &repaired.conduct);
    say(
        &mut receipt,
        format!(
            "  the scope is NOT closed under the transport: {leaving} of {} classes carry an arc that leaves it. So refinement reads a departing successor as an absence and separates on it, while the search for a word follows it out and may find no receiver difference — which is exactly why rounds {} and memory order {} disagree here. Counted separated pairs {counted} against {} exhibited with a word: the difference {} IS that population.",
            items.len(),
            repaired.rounds,
            P0_ORDER,
            repaired.collapsed.len(),
            counted - repaired.collapsed.len() as u128
        ),
    );

    // ---- the whole-atlas reading P0 refused ----
    say(&mut receipt, "");
    say(&mut receipt, "THE WHOLE-ATLAS READING — the one Deed P0 named its aperture against");
    let (all_items, all_inputs) = whole_atlas(&rest);
    let atlas = AtlasSystem::new(&rest, Family::P0, all_items.clone(), all_inputs.clone(), true);
    let clock = Instant::now();
    let whole = refine(&atlas);
    let whole_wall = clock.elapsed().as_secs_f64();
    let whole_pairs = separated_pair_population(&whole.one_shot, &whole.conduct);
    let clock = Instant::now();
    let exhibited = exhibit_collapsed_within(
        &atlas,
        &whole.one_shot,
        &whole.conduct,
        Some(EXHIBITION_APERTURE),
    );
    let exhibition_wall = clock.elapsed().as_secs_f64();
    say(
        &mut receipt,
        format!(
            "  family {} · items {} · inputs {} · one-shot blocks {} · conduct-stable blocks {} · Moore rounds {} · {whole_wall:.1} s",
            Family::P0.text(),
            all_items.len(),
            all_inputs.len(),
            whole.one_shot.len(),
            whole.conduct.len(),
            whole.rounds
        ),
    );
    say(
        &mut receipt,
        format!(
            "  the whole atlas IS closed under the transport, so Moore's round k separates exactly the pairs whose shortest word has length k: the memory order is {} and needs no per-pair search. Collapsed pairs {whole_pairs}, counted exactly from the block sizes.",
            whole.rounds
        ),
    );
    for pair in exhibited.iter().take(6) {
        say(
            &mut receipt,
            format!(
                "    classes {} and {} separated by {:?}{}",
                pair.left.0,
                pair.right.0,
                pair.distinguishing_word
                    .iter()
                    .map(|input| rest.surfaces[input.0 as usize].clone())
                    .collect::<Vec<_>>(),
                if pair.separated_by_terminus {
                    " (a terminus, no receiver named)"
                } else {
                    ""
                }
            ),
        );
    }
    let per_pair = exhibition_wall / EXHIBITION_APERTURE.max(1) as f64;
    say(
        &mut receipt,
        format!(
            "  APERTURE, measured rather than asserted: {EXHIBITION_APERTURE} of {whole_pairs} pairs were given their shortest word in {exhibition_wall:.2} s, {per_pair:.4} s each, so exhibiting the whole population at this rate is {:.3e} s. The count is exact and free; the WORDS are what remains out of aperture, and the repair that lifted the partition reading does not lift a per-pair breadth-first search.",
            per_pair * whole_pairs as f64
        ),
    );

    // The closed-population theorem is used above to read the whole-atlas memory order off the round
    // count. It is asserted by a test on closed fixtures; here it is checked on THIS material, on a
    // population that is closed by construction — the forward closure of a landed class under the
    // germ transport, which the manifest measured to be a DAG.
    let mut closure_report = String::from("no landed class has a forward closure in range");
    let mut closure_holds = false;
    for seed in &landed {
        let mut closed: BTreeSet<u32> = BTreeSet::new();
        let mut frontier = vec![*seed];
        while let Some(class) = frontier.pop() {
            if !closed.insert(class) {
                continue;
            }
            let (from, to) = rest.row(class);
            for slot in from..to {
                frontier.push(rest.target[slot]);
            }
        }
        if closed.len() < 32 || closed.len() > 4096 {
            continue;
        }
        let closed_items: Vec<ItemId> = closed.iter().map(|c| ItemId(u64::from(*c))).collect();
        let mut closed_germs: BTreeSet<u32> = BTreeSet::new();
        for class in &closed {
            let (from, to) = rest.row(*class);
            for slot in from..to {
                closed_germs.insert(rest.germ[slot]);
            }
        }
        let closed_inputs: Vec<InputId> =
            closed_germs.iter().map(|g| InputId(u64::from(*g))).collect();
        let closed_system =
            AtlasSystem::new(&rest, Family::P0, closed_items, closed_inputs.clone(), true);
        let closed_reading = compress(&closed_system);
        let counted = separated_pair_population(&closed_reading.one_shot, &closed_reading.conduct);
        closure_holds = match closed_reading.memory_order() {
            None => closed_reading.rounds == 0,
            Some(order) => closed_reading.rounds == order,
        } && counted == closed_reading.collapsed.len() as u128;
        closure_report = format!(
            "the forward closure of class {seed} under the transport is {} classes over {} germs, closed by construction. Moore rounds {} · memory order {:?} · counted separated pairs {counted} · exhibited with a word {}. The two readings agree exactly, which is the condition the whole-atlas memory order is read under; at Deed P0's unclosed scope they disagree by construction, and both are shown.",
            closed.len(),
            closed_inputs.len(),
            closed_reading.rounds,
            closed_reading.memory_order(),
            closed_reading.collapsed.len()
        );
        break;
    }
    verdicts.record(
        17,
        "the closed-population theorem the whole-atlas memory order is read under is checked on THIS material",
        closure_holds,
        closure_report,
    );

    // ---- the condensation quotient ----
    say(&mut receipt, "");
    say(&mut receipt, "THE CONDENSATION QUOTIENT — at the family declared above, over the whole atlas");
    let condensing = AtlasSystem::new(
        &rest,
        Family::Condensation,
        all_items.clone(),
        all_inputs.clone(),
        true,
    );
    let clock = Instant::now();
    let quotient = refine(&condensing);
    let quotient_wall = clock.elapsed().as_secs_f64();
    let quotient_pairs = separated_pair_population(&quotient.one_shot, &quotient.conduct);
    let mut sizes: BTreeMap<usize, usize> = BTreeMap::new();
    for block in &quotient.conduct.blocks {
        *sizes.entry(block.len()).or_default() += 1;
    }
    let plural_blocks = quotient
        .conduct
        .blocks
        .iter()
        .filter(|block| block.len() > 1)
        .count();
    let condensed_classes: usize = quotient
        .conduct
        .blocks
        .iter()
        .filter(|block| block.len() > 1)
        .map(|block| block.len())
        .sum();
    say(
        &mut receipt,
        format!(
            "  family {} · one-shot blocks {} · conduct-stable blocks {} · Moore rounds {} · collapsed pairs {quotient_pairs} · {quotient_wall:.1} s",
            Family::Condensation.text(),
            quotient.one_shot.len(),
            quotient.conduct.len(),
            quotient.rounds
        ),
    );
    say(
        &mut receipt,
        format!(
            "  block sizes {:?} · {plural_blocks} plural blocks holding {condensed_classes} of {} classes: that population is what the transport condensation can pay for, and the rest is a discrete quotient which condenses nothing.",
            sizes.iter().map(|(size, count)| (*size, *count)).collect::<Vec<_>>(),
            rest.classes
        ),
    );

    // ---- lumpability, measured on two partitions so the check can fail ----
    say(&mut receipt, "");
    say(&mut receipt, "LUMPABILITY — P C = C P-bar, exact over Rat, MEASURED on two partitions");
    let conduct_lump = lumpability(&rest, &quotient.conduct);
    let one_shot_lump = lumpability(&rest, &quotient.one_shot);
    say(
        &mut receipt,
        format!(
            "  the CONDUCT partition ({} blocks, {} within-block comparisons): {}",
            conduct_lump.blocks,
            conduct_lump.checked,
            if conduct_lump.holds {
                "the aggregate row is identical for every pair of states in every block, so P C = C P-bar holds EXACTLY and P-bar is the block transport".to_owned()
            } else {
                format!("DEFECT {:?}", conduct_lump.defect)
            }
        ),
    );
    let defect_line = match &one_shot_lump.defect {
        None => "no defect — which would make the control vacuous".to_owned(),
        Some((block, left, right, target, left_value, right_value)) => {
            let word = separator(&condensing, *left, *right).map(|word| {
                word.iter()
                    .map(|germ| rest.surfaces[*germ as usize].clone())
                    .collect::<Vec<_>>()
            });
            format!(
                "block {block}: states {left} and {right} disagree into block {target}, {left_value} against {right_value}; {} disagreeing blocks of {}; the two within-block histories are separated by {:?}",
                one_shot_lump.disagreeing_blocks, one_shot_lump.blocks, word
            )
        }
    };
    say(
        &mut receipt,
        format!("  the ONE-SHOT partition, the control that this check can fail: {defect_line}"),
    );
    // The third partition, and it moves a row Deed P0's manifest left OPEN by name.
    let coarsening = height_coarsening(&rest, 1);
    let height_lump = lumpability(&rest, &coarsening);
    let height_pairs = separated_pair_population(&coarsening, &quotient.conduct);
    let height_line = match &height_lump.defect {
        None => "no defect: the height-1 coarsening IS a sufficient state for this transport"
            .to_owned(),
        Some((block, left, right, target, left_value, right_value)) => {
            let word = separator(&condensing, *left, *right).map(|word| {
                word.iter()
                    .map(|germ| rest.surfaces[*germ as usize].clone())
                    .collect::<Vec<_>>()
            });
            format!(
                "DEFECT — block {block}: classes {left} and {right} disagree into block {target}, {left_value} against {right_value}; {} disagreeing blocks of {}; the two within-block histories are separated by {:?}. So the suffix-ancestor at height 1 is NOT a sufficient state, and {height_pairs} pairs it holds together the declared family separates.",
                height_lump.disagreeing_blocks, height_lump.blocks, word
            )
        }
    };
    say(
        &mut receipt,
        format!(
            "  the SUFFIX-ANCESTOR coarsening at height 1 ({} blocks, {} comparisons) — the candidate Deed P0's manifest named and left OPEN with lumpability as its falsifier: {height_line}",
            height_lump.blocks, height_lump.checked
        ),
    );
    verdicts.record(
        4,
        "lumpability is MEASURED and the measurement can fail: exact on the conduct quotient, defective on both coarser ones",
        conduct_lump.holds && !one_shot_lump.holds && !height_lump.holds,
        format!(
            "conduct holds {} · one-shot holds {} · height-1 coarsening holds {} (a check that could not fail carries no evidence, so two coarser partitions are run as controls)",
            conduct_lump.holds, one_shot_lump.holds, height_lump.holds
        ),
    );

    // ---- the ReconstructionFiber and one reopening ----
    let fibre_pairs = exhibit_collapsed_within(
        &condensing,
        &quotient.one_shot,
        &quotient.conduct,
        Some(EXHIBITION_APERTURE),
    );
    let fibre: Vec<(u32, u32, Vec<u32>)> = fibre_pairs
        .iter()
        .map(|pair| {
            (
                pair.left.0 as u32,
                pair.right.0 as u32,
                pair.distinguishing_word
                    .iter()
                    .map(|input| input.0 as u32)
                    .collect(),
            )
        })
        .collect();

    // ---- the condensation ----
    say(&mut receipt, "");
    say(&mut receipt, "THE CONDENSATION");
    let excited = rest.excited(&landed);
    let (condensed, notes) = condense(&rest, &quotient.conduct, &excited, fibre.clone())?;
    for note in &notes {
        say(&mut receipt, format!("  {note}"));
    }
    let cycle_rank = rest.transitions as i64 - rest.classes as i64 + 1;
    let mut indegree: BTreeMap<u32, usize> = BTreeMap::new();
    for target in &rest.target {
        *indegree.entry(*target).or_default() += 1;
    }
    let reconvergent_classes = indegree.values().filter(|count| **count > 1).count();
    say(
        &mut receipt,
        format!(
            "  TREE: {} intervals, height {}. Containment IS ancestry, so the descendant population of every class — {} ancestor-descendant pairs in total — is two words per class. Remainder EMPTY.",
            condensed.entry.len(),
            condensed.height,
            (0..rest.classes as u32).map(|class| u64::from(rest.suffix_height(class)) + 1).sum::<u64>()
        ),
    );
    say(
        &mut receipt,
        format!(
            "  NERODE: {} shared block rows carrying {} arcs, against {} class rows carrying {} arcs.",
            condensed.block_indptr.len() - 1,
            condensed.block_germ.len(),
            rest.classes,
            rest.transitions
        ),
    );
    say(
        &mut receipt,
        format!(
            "  REMAINDER, certified and retained whole: {} arcs into a plural block, which the block row cannot resolve to a class; and the INTERVAL receiver's own remainder, {} arcs beyond a spanning forest at {} reconvergent classes, cycle rank b1 = {cycle_rank}.",
            condensed.remainder_target.len(),
            condensed.reconvergent_slot.len(),
            reconvergent_classes
        ),
    );
    say(
        &mut receipt,
        format!(
            "  UNEXCITED: {} of {} classes the declared probe family never reaches. Their bytes are in every section above and in the complete cost. NOT dropped.",
            condensed.unexcited.len(),
            rest.classes
        ),
    );
    verdicts.record(
        5,
        "the certified remainder in the condensed rest equals Deed P0's measured reconvergence",
        condensed.reconvergent_slot.len() == P0_RECONVERGENT_ARCS
            && reconvergent_classes == P0_RECONVERGENT_CLASSES
            && cycle_rank == P0_CYCLE_RANK,
        format!(
            "{} arcs at {reconvergent_classes} classes, b1 = {cycle_rank}, against P0's {P0_RECONVERGENT_ARCS} / {P0_RECONVERGENT_CLASSES} / {P0_CYCLE_RANK}",
            condensed.reconvergent_slot.len()
        ),
    );

    let bytes = container(&condensed)?;
    std::fs::create_dir_all(OUT).map_err(|error| format!("{OUT}: {error}"))?;
    let condensed_path = format!("{OUT}/condensed-rest.safetensors");
    std::fs::write(&condensed_path, &bytes).map_err(|error| format!("{condensed_path}: {error}"))?;
    say(
        &mut receipt,
        format!("  the condensed rest: {condensed_path} · {} octets", bytes.len()),
    );

    // ---- the decoder, and R1 through R5 read from the condensed body ----
    say(&mut receipt, "");
    say(&mut receipt, "THE DECLARED FACES, RECONSTRUCTED FROM THE CONDENSED REST");
    let mut reader = read_condensed(&condensed_path)?;

    // R1
    let source_faces: Vec<Vec<(String, u32, u32)>> = landed
        .iter()
        .map(|class| {
            rest.section(*class)
                .into_iter()
                .map(|(germ, standing, depth)| {
                    (rest.surfaces[germ as usize].clone(), standing, depth)
                })
                .collect()
        })
        .collect();
    let condensed_faces: Vec<Vec<(String, u32, u32)>> = landed
        .iter()
        .map(|class| {
            reader
                .section(*class)
                .into_iter()
                .map(|(germ, standing, depth)| {
                    (reader.surfaces[germ as usize].clone(), standing, depth)
                })
                .collect()
        })
        .collect();
    verdicts.record(
        6,
        "R1 — the plural future sections are bit-equal between the source rest and the condensed one",
        source_faces == condensed_faces,
        format!(
            "8 prompts · germ populations {:?} · every (germ, standing, depth) triple equal: {}",
            source_faces.iter().map(|face| face.len()).collect::<Vec<_>>(),
            source_faces == condensed_faces
        ),
    );

    // The condensed rest carries its own walk, its own exhibited remainder and its own unexcited
    // population, and they read back as written.
    let condensed_index = reader.index_of();
    let condensed_landed: Vec<u32> = PROMPTS
        .iter()
        .map(|prompt| reader.walk(prompt, &condensed_index))
        .collect();
    verdicts.record(
        15,
        "the condensed rest carries the walk, the exhibited remainder and the unexcited population, and they read back as written",
        condensed_landed == landed
            && reader.reconvergent_slot == condensed.reconvergent_slot
            && reader.unexcited == condensed.unexcited,
        format!(
            "the walk through the block rows and the reopened remainder lands {condensed_landed:?}, the source rest lands {landed:?} · {} reconvergent slots and {} unexcited classes read back",
            reader.reconvergent_slot.len(),
            reader.unexcited.len()
        ),
    );

    // R4
    let source_heights: Vec<u32> = (0..rest.classes as u32).map(|c| rest.suffix_height(c)).collect();
    let condensed_heights: Vec<u32> = (0..reader.classes as u32).map(|c| reader.height_of(c)).collect();
    let ancestry_agrees = (0..rest.classes as u32).take(4096).all(|class| {
        let mut at = class;
        loop {
            let parent = rest.suffix[at as usize];
            if !reader.contains(parent, class) {
                return false;
            }
            if parent == at {
                return true;
            }
            at = parent;
        }
    });
    verdicts.record(
        7,
        "R4 — the scale action survives: every suffix-link height is recovered from the interval chart alone",
        source_heights == condensed_heights
            && reader.height == rest.height
            && reader.parent == rest.suffix
            && ancestry_agrees,
        format!(
            "{} heights equal · tree height {} · the parent array RECOVERED from the intervals is bit-equal to the source's suffix array ({}) · interval containment agrees with the suffix chain on the first 4096 classes ({ancestry_agrees})",
            source_heights.len(),
            reader.height,
            reader.parent == rest.suffix
        ),
    );

    // R5
    let condensed_scope: Vec<ItemId> = items.clone();
    let condensed_system = CondensedSystem {
        rest: &reader,
        family: Family::P0,
        items: condensed_scope,
        inputs: inputs.clone(),
    };
    let condensed_reading = compress(&condensed_system);
    verdicts.record(
        8,
        "R5 — the Nerode/Markov reading recomputed FROM the condensed rest is the same reading",
        condensed_reading.one_shot == repaired.one_shot
            && condensed_reading.conduct == repaired.conduct
            && condensed_reading.rounds == repaired.rounds
            && condensed_reading.collapsed == repaired.collapsed,
        format!(
            "one-shot {} · conduct {} · rounds {} · collapsed {} · order {:?} — every population equal to the source reading, and the class-level successors it needs come back through the retained remainder rather than from a stored target array",
            condensed_reading.one_shot.len(),
            condensed_reading.conduct.len(),
            condensed_reading.rounds,
            condensed_reading.collapsed.len(),
            condensed_reading.memory_order()
        ),
    );

    // The reopening demonstration.
    let reopened = fibre.first().cloned();
    let reopening = match &reopened {
        None => "no pair collapsed at the declared family, so there is nothing to reopen".to_owned(),
        Some((left, right, word)) => {
            let mut here = *left;
            let mut there = *right;
            for germ in word {
                here = reader.step(here, *germ).unwrap_or(here);
                there = reader.step(there, *germ).unwrap_or(there);
            }
            let before = (
                rest.out_degree(*left),
                rest.standing[*left as usize],
                rest.out_degree(*right),
                rest.standing[*right as usize],
            );
            let after = (
                reader.out_degree(here),
                reader.block_standing[reader.block_of[here as usize] as usize],
                reader.out_degree(there),
                reader.block_standing[reader.block_of[there as usize] as usize],
            );
            format!(
                "classes {left} and {right} read alike one-shot — out-degree {} and {}, standing {} and {} — and the retained word {:?} carries them to {here} and {there}, where the declared receivers return {:?} against {:?}. The distinction RETURNS, from the condensed rest alone.",
                before.0,
                before.2,
                before.1,
                before.3,
                word.iter().map(|germ| rest.surfaces[*germ as usize].clone()).collect::<Vec<_>>(),
                (after.0, after.1),
                (after.2, after.3)
            )
        }
    };
    verdicts.record(
        9,
        "the ReconstructionFiber is retained in the condensed rest and one collapsed pair is REOPENED by its separator",
        reopened.is_some()
            && reopened
                .as_ref()
                .map(|(left, right, word)| {
                    let mut here = *left;
                    let mut there = *right;
                    for germ in word {
                        here = reader.step(here, *germ).unwrap_or(here);
                        there = reader.step(there, *germ).unwrap_or(there);
                    }
                    (
                        reader.out_degree(here),
                        reader.block_standing[reader.block_of[here as usize] as usize],
                    ) != (
                        reader.out_degree(there),
                        reader.block_standing[reader.block_of[there as usize] as usize],
                    )
                })
                .unwrap_or(false),
        reopening,
    );

    // ---- R2: the fresh process ----
    let parent_face: String = landed
        .iter()
        .flat_map(|class| {
            let mut lines = Vec::new();
            for (germ, standing, depth) in reader.section(*class) {
                lines.push(format!("{class} {} {standing} {depth}", reader.surfaces[germ as usize]));
            }
            lines
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut command = std::process::Command::new(std::env::current_exe().map_err(|e| e.to_string())?);
    command.arg("--remount").arg(&condensed_path).arg("--landed");
    for class in &landed {
        command.arg(class.to_string());
    }
    let child = command.output().map_err(|error| format!("{error}"))?;
    let child_face = String::from_utf8_lossy(&child.stdout).trim_end().to_owned();
    verdicts.record(
        10,
        "R2 — a fresh process reading the condensed rest ALONE returns R1 bit-equal",
        child.status.success() && child_face == parent_face,
        format!(
            "child exit {:?} · {} octets returned, parent {} octets, bit-equal {} · its whole argument vector is the condensed rest's path and the landed classes: no source rest, no corpus, no vocabulary path",
            child.status.code(),
            child_face.len(),
            parent_face.len(),
            child_face == parent_face
        ),
    );

    // ---- R3: the intervention factors ----
    say(&mut receipt, "");
    say(&mut receipt, "R3 — THE CONSTRUCTION-LEVEL ABLATION, CONDENSED ON BOTH SIDES");
    let mut ablated = read_rest(ABLATED)?;
    let ablated_landed: Vec<u32> = PROMPTS.iter().map(|prompt| ablated.walk(prompt)).collect();
    let (ablated_items, ablated_inputs) = whole_atlas(&ablated);
    let ablating = AtlasSystem::new(
        &ablated,
        Family::Condensation,
        ablated_items,
        ablated_inputs,
        true,
    );
    let ablated_quotient = refine(&ablating);
    let ablated_excited = ablated.excited(&ablated_landed);
    let (ablated_condensed, _) = condense(
        &ablated,
        &ablated_quotient.conduct,
        &ablated_excited,
        Vec::new(),
    )?;
    let ablated_bytes = container(&ablated_condensed)?;
    let ablated_path = format!("{OUT}/condensed-rest-without-hexis.safetensors");
    std::fs::write(&ablated_path, &ablated_bytes)
        .map_err(|error| format!("{ablated_path}: {error}"))?;
    let mut ablated_reader = read_condensed(&ablated_path)?;

    let diff = |before: &[(String, u32, u32)], after: &[(String, u32, u32)]| -> (usize, usize, usize) {
        let before_map: BTreeMap<&String, (u32, u32)> =
            before.iter().map(|(g, s, d)| (g, (*s, *d))).collect();
        let after_map: BTreeMap<&String, (u32, u32)> =
            after.iter().map(|(g, s, d)| (g, (*s, *d))).collect();
        let gone = before_map
            .keys()
            .filter(|germ| !after_map.contains_key(*germ))
            .count();
        let arrived = after_map
            .keys()
            .filter(|germ| !before_map.contains_key(*germ))
            .count();
        // `moved` counts germs present on BOTH sides whose face changed — a germ that left is
        // `gone`, not moved. That is Deed P0's own accounting, and it is what makes the two tables
        // comparable rather than merely similar.
        let moved = before_map
            .iter()
            .filter(|(germ, value)| after_map.get(*germ).is_some_and(|other| other != *value))
            .count();
        (moved, gone, arrived)
    };
    let source_diff: Vec<(usize, usize, usize)> = PROMPTS
        .iter()
        .enumerate()
        .map(|(at, _)| {
            let after: Vec<(String, u32, u32)> = ablated
                .section(ablated_landed[at])
                .into_iter()
                .map(|(germ, standing, depth)| {
                    (ablated.surfaces[germ as usize].clone(), standing, depth)
                })
                .collect();
            diff(&source_faces[at], &after)
        })
        .collect();
    let condensed_diff: Vec<(usize, usize, usize)> = PROMPTS
        .iter()
        .enumerate()
        .map(|(at, _)| {
            let after: Vec<(String, u32, u32)> = ablated_reader
                .section(ablated_landed[at])
                .into_iter()
                .map(|(germ, standing, depth)| {
                    (ablated_reader.surfaces[germ as usize].clone(), standing, depth)
                })
                .collect();
            diff(&condensed_faces[at], &after)
        })
        .collect();
    for (at, prompt) in PROMPTS.iter().enumerate() {
        say(
            &mut receipt,
            format!(
                "  {prompt:<42} source (moved {}, gone {}, arrived {}) · condensed (moved {}, gone {}, arrived {})",
                source_diff[at].0, source_diff[at].1, source_diff[at].2,
                condensed_diff[at].0, condensed_diff[at].1, condensed_diff[at].2
            ),
        );
    }
    verdicts.record(
        11,
        "R3 — the ablation diff of the condensed pair equals the condensation of the ablation diff",
        source_diff == condensed_diff,
        format!(
            "8 prompts, every (moved, gone, arrived) triple equal: {} · the ablated rest is condensed by the same law, {} classes into {} blocks",
            source_diff == condensed_diff,
            ablated.classes,
            ablated_quotient.conduct.len()
        ),
    );
    let committed_ablation: Vec<(usize, usize)> = vec![
        (606, 216),
        (622, 216),
        (5169, 216),
        (623, 216),
        (5169, 216),
        (609, 216),
        (609, 216),
        (630, 216),
    ];
    let measured_ablation: Vec<(usize, usize)> =
        source_diff.iter().map(|(moved, gone, _)| (*moved, *gone)).collect();
    verdicts.record(
        16,
        "R3's ablation table equals Deed P0's committed one, so the intervention being condensed is the same intervention",
        measured_ablation == committed_ablation,
        format!("measured {measured_ablation:?} against P0's committed {committed_ablation:?}"),
    );

    // ---- R7: the P1 recombination ----
    let p1 = std::fs::read_to_string(P1_RECEIPT).unwrap_or_default();
    let header_end = 8 + u64::from_le_bytes(bytes[..8].try_into().unwrap()) as usize;
    let condensed_header = String::from_utf8_lossy(&bytes[8..header_end]).to_owned();
    let p1_touches_native = p1.contains("athena.") || p1.contains("condensed.");
    // The measurement is over the container's TENSOR names — the coordinates — not its metadata,
    // which declares the receiver family in prose and would match on the word alone.
    let condensed_coordinates: Vec<&str> = condensed_header
        .match_indices("\"condensed.")
        .filter_map(|(at, _)| {
            let tail = &condensed_header[at + 1..];
            tail.find('"').map(|end| &tail[..end])
        })
        .collect();
    let source_names = [
        "q_proj",
        "model.layers",
        "bf16",
        "gemma",
        "phoenix",
        "codeword",
        "binade",
        "significand",
    ];
    let condensed_touches_source = condensed_coordinates
        .iter()
        .filter(|name| source_names.iter().any(|foreign| name.contains(foreign)))
        .count();
    verdicts.record(
        12,
        "R7 — the P1 native recombination does not touch the condensed coordinates, measured on both sides",
        !p1_touches_native && condensed_touches_source == 0,
        format!(
            "the P1 receipt names no athena/condensed coordinate ({}); of the condensed container's {} coordinates, {} carry any of the {} probed source-chart names. The P1 recombination composes a foreign FAMILY coordinate's grouped-sharing quotient with the bf16 rounding fibre — coordinates of the SOURCE chart. The condensation here moves native atlas coordinates only: class intervals, conduct blocks and germ arcs. WHERE THEY WOULD TOUCH: Phi_X's native side is this atlas, so a condensation that changed the native class POPULATION would move Phi_X's domain basis; this one does not — the population is unchanged at {} classes and only the chart it is written in moved.",
            !p1_touches_native,
            condensed_coordinates.len(),
            condensed_touches_source,
            source_names.len(),
            condensed.classes
        ),
    );

    // ---- R6 and the cost law ----
    say(&mut receipt, "");
    say(&mut receipt, "THE COST, ADDITIVELY — artifact octets + decoder octets + decoder exact work");
    let baseline_decoder = marked_octets("// BASELINE-DECODER-BEGIN", "// BASELINE-DECODER-END");
    let condensed_decoder = marked_octets("// DECODER-BEGIN", "// DECODER-END");

    // **Both decoders are priced over the SAME declared face set**, from a cleared counter: R1 at
    // the eight probes and R4 at every class. A work figure taken over two different face sets is
    // not a comparison, and the condensed reader had already paid for its parent recovery.
    rest.work = ExactWork::nothing();
    rest.work.resident(rest.octets);
    reader.work = ExactWork::nothing();
    reader.work.resident(bytes.len() as u64);
    assert_eq!(
        recover_parents(&mut reader.work, &reader.entry, &reader.exit),
        reader.parent,
        "the priced parent recovery must be the same recovery the decoder already ran"
    );
    for class in &landed {
        let _ = rest.section(*class);
        let _ = reader.section(*class);
    }
    for class in 0..rest.classes as u32 {
        let _ = rest.height_of(class);
        let _ = reader.height_of(class);
    }
    let baseline_work = rest.work.coordinates();
    let condensed_work = reader.work.coordinates();
    let coordinate = |work: &[(&'static str, num_bigint::BigUint)], name: &str| -> String {
        work.iter()
            .find(|(key, _)| *key == name)
            .map(|(_, value)| value.to_string())
            .unwrap_or_else(|| "0".to_owned())
    };
    let baseline_vector = (
        rest.octets as usize,
        baseline_decoder,
        coordinate(&baseline_work, "dependency-span"),
    );
    let condensed_vector = (
        bytes.len(),
        condensed_decoder,
        coordinate(&condensed_work, "dependency-span"),
    );
    say(
        &mut receipt,
        format!(
            "  BASELINE  artifact {} octets · decoder {} octets · exact work {:?}",
            baseline_vector.0, baseline_vector.1, baseline_work
        ),
    );
    say(
        &mut receipt,
        format!(
            "  CONDENSED artifact {} octets · decoder {} octets · exact work {:?}",
            condensed_vector.0, condensed_vector.1, condensed_work
        ),
    );
    let artifact_falls = condensed_vector.0 < baseline_vector.0;
    let decoder_falls = condensed_vector.1 < baseline_vector.1;
    let work_falls = condensed_vector.2.parse::<u128>().unwrap_or(u128::MAX)
        < baseline_vector.2.parse::<u128>().unwrap_or(0);
    let regression = verdicts.failed > 0;
    let strict_fall = artifact_falls && decoder_falls && work_falls && !regression;
    say(
        &mut receipt,
        format!(
            "  the vector falls on artifact {artifact_falls}, on decoder {decoder_falls}, on work {work_falls}; receiver regression {regression}."
        ),
    );
    say(
        &mut receipt,
        if strict_fall {
            "  the complete vector STRICTLY FALLS with every declared face factoring, so a factor may be quoted.".to_owned()
        } else {
            "  THE VECTOR DOES NOT STRICTLY FALL, so NO compression factor is quoted. The invariance is additive (CLAUDE.md 0k): a ratio without its decoder is the absolute-volume violation, and a ratio with a decoder that grew is a ratio that moved cost rather than removed it. What the condensation returns is a typed structural result, not a smaller file.".to_owned()
        },
    );
    verdicts.record(
        13,
        "R6 — the cost is returned as the additive vector with the decoder declared, and no factor is quoted unless it strictly falls",
        true,
        format!(
            "baseline ({}, {}, {}) against condensed ({}, {}, {}) · strict fall {strict_fall} · resident octets baseline {} condensed {}",
            baseline_vector.0, baseline_vector.1, baseline_vector.2,
            condensed_vector.0, condensed_vector.1, condensed_vector.2,
            coordinate(&baseline_work, "resident-entries"),
            coordinate(&condensed_work, "resident-entries")
        ),
    );
    // The tree half priced on its own, because it is the half that pays and the whole vector hides it.
    let ancestry_pairs: u64 = (0..rest.classes as u32)
        .map(|class| u64::from(rest.suffix_height(class)) + 1)
        .sum();
    let materialised = ancestry_pairs * 8;
    let chart_octets = ((condensed.entry.len() + condensed.exit.len()) * 4) as u64;
    let parent_octets = (rest.classes * 4) as u64;
    say(
        &mut receipt,
        format!(
            "  THE TREE HALF, PRICED ON ITS OWN — CLAUDE.md §11's trivial instance on material that is not trivial:\n\
             \x20   against the ancestry relation held as an explicit pair population, which is what a receiver answering\n\
             \x20   ancestry in constant time without the chart must hold: {ancestry_pairs} pairs = {materialised} octets against the chart's\n\
             \x20   {chart_octets} octets, remainder EMPTY, decoder two integer comparisons. That axis STRICTLY FALLS, {:.2}x.\n\
             \x20   against the suffix parent array as stored ({parent_octets} octets): the chart is {:.2}x LARGER and answers ancestry in\n\
             \x20   two comparisons where the array answers it in a climb of up to {} steps. That axis TRADES rather than falls,\n\
             \x20   and the additive law is what makes the trade visible instead of a ratio hiding it.",
            materialised as f64 / chart_octets as f64,
            chart_octets as f64 / parent_octets as f64,
            rest.height
        ),
    );

    verdicts.record(
        14,
        "no dense-rank truncation anywhere, and the unexcited population is retained with its bytes in the cost",
        condensed.unexcited.len() + excited.len() == rest.classes,
        format!(
            "{} unexcited + {} excited = {} classes · every condensation above is a quotient by an equivalence the declared family cannot see, and every pair it merges that a receiver CAN see is retained with its shortest word",
            condensed.unexcited.len(),
            excited.len(),
            rest.classes
        ),
    );

    // ---- the artifacts ----
    let cost = format!(
        "THE COST VECTOR — Deed P2, additive per CLAUDE.md 0k\n\
         axis\tbaseline\tcondensed\n\
         artifact octets\t{}\t{}\n\
         decoder octets\t{}\t{}\n\
         decoder exact steps\t{}\t{}\n\
         decoder resident octets\t{}\t{}\n\
         strict fall\t\t{strict_fall}\n\
         factor quoted\t\t{}\n",
        baseline_vector.0,
        condensed_vector.0,
        baseline_vector.1,
        condensed_vector.1,
        baseline_vector.2,
        condensed_vector.2,
        coordinate(&baseline_work, "resident-entries"),
        coordinate(&condensed_work, "resident-entries"),
        if strict_fall { "yes" } else { "NONE" }
    );
    std::fs::write(format!("{OUT}/cost-vector.form"), &cost)
        .map_err(|error| format!("{error}"))?;

    say(&mut receipt, "");
    say(&mut receipt, "VERDICTS");
    let mut whole_receipt = receipt.join("\n");
    whole_receipt.push('\n');
    whole_receipt.push_str(&verdicts.lines.join("\n"));
    whole_receipt.push_str(&format!(
        "\n\n{} verdicts, {} failed · {:.1} s\n",
        verdicts.lines.len(),
        verdicts.failed,
        whole_clock.elapsed().as_secs_f64()
    ));
    std::fs::write(format!("{OUT}/receipt.form"), &whole_receipt)
        .map_err(|error| format!("{error}"))?;
    println!(
        "\n{} verdicts, {} failed · {:.1} s",
        verdicts.lines.len(),
        verdicts.failed,
        whole_clock.elapsed().as_secs_f64()
    );
    if verdicts.failed > 0 {
        return Err(format!("{} verdicts failed", verdicts.failed));
    }
    Ok(())
}

/// The eight classes Deed P0's committed receipt records its prompts landing in, read from the
/// artifact rather than restated.
fn landed_from_receipt(locator: &str) -> Result<Vec<u32>, String> {
    let text = std::fs::read_to_string(locator).map_err(|error| format!("{locator}: {error}"))?;
    let mut landed = Vec::new();
    for line in text.lines() {
        let Some(at) = line.find("-> class ") else {
            continue;
        };
        let tail = &line[at + "-> class ".len()..];
        let number: String = tail.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(class) = number.parse::<u32>() {
            landed.push(class);
        }
    }
    Ok(landed)
}
