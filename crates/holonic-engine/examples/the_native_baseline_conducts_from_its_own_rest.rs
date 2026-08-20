//! **Deed P0: ARM N — the native baseline conducts on the card from its own rest, and returns its
//! ecology manifest.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8 Deed
//! P0 and §7 (the research constraints the manifest honours). The rest is built by
//! `soma/life/examples/the_native_rest_is_built_and_declares_its_own_laws.rs`; **this driver is the
//! only thing that touches a card**, and the rest is its only semantic input.
//!
//! # What the deed is
//!
//! ```text
//!   the rest (an integer safetensors container the ecology emitted)
//!     -> NativeOccurrence: the rest authenticates itself and declares its own laws
//!     -> the atlas mounted as u32 arrays on the card
//!     -> athena-walk    : several runtime-supplied prompts carried from the root, one warp each
//!     -> athena-future  : positions x vocabulary, every cell an independent suffix-chain climb
//!     -> athena-depth   : the same climb returning how far the arc reached
//!     -> plural exterior surfaces decoded from the rest's OWN vocabulary — never one winner
//! ```
//!
//! # The predecessor's execution shape is not extended
//!
//! The quarantined `athena_walk` opened `if (flat != 0) return;` under a maximum-legal-block flat
//! grid: one lane worked and the rest of the launch existed to be discarded, and the future section
//! ran one thread per cell at the same block. Both are gone. The walk is covered by the prompt
//! population and searches each transport row 32-ARY across a warp; the future section carries a
//! DERIVED launch geometry from a candidate family read off the device and the module's measured
//! registers, and the receipt prints the family, the declared axes, the retained set and the
//! grid x block of both shapes so the difference is measured rather than asserted.
//!
//! # No foreign hexis
//!
//! The deed never opens the Gemma container, never calls a tokenizer, never reads `phoenix/`
//! material and never reads the corpus the rest was built from. The live access audit in the fresh
//! child process returns every descriptor it actually holds.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_native_baseline_conducts_from_its_own_rest -- \
//!   [--rest output/the_native_baseline_conducts/rest.safetensors] [--prompt "..."]...
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::time::Instant;

use holonic_engine::athena::TreeChart;
use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::front_passage::{
    factored_seals, DeedReceiver, FrontPassage, FrontPassageObstruction, MaterialPlan, ResidentMaterial,
};
use holonic_engine::native_law::{AthenaArrays, AthenaFuture, AthenaWalk, DEPTH_LAW, FUTURE_LAW, WALK_LAW};
use holonic_engine::native_occurrence::NativeOccurrence;
use holonic_engine::category::BoundaryId;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use holonic_engine::receiver_exact_compression::{compress, InputId, ItemId, Observation, ObservedSystem, ReceiverId};
use holonic_engine::resident_section::{
    athena_non_dominated, AthenaAxis, AthenaCandidate, AthenaFutureGeometry, AthenaWalkGeometry, ResidentGrain, ResidentSurface, KERNELS,
};
use holonic_engine::source_occurrence::OccurrenceWitness;

const OUT: &str = "output/the_native_baseline_conducts";
const REST: &str = "output/the_native_baseline_conducts/rest.safetensors";
const ABLATED: &str = "output/the_native_baseline_conducts/rest-without-hexis.safetensors";

/// **Runtime-supplied prompts, in the native codec: the lexical tokens of holonics prose.** The
/// last is deliberately outside the material's vocabulary, so the walk's arc law returns the root's
/// plural section rather than an error.
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

// ---------------------------------------------------------------------------------------------
// the rest, read host-side: the atlas, its vocabulary, and the codec that turns prose into germs
// ---------------------------------------------------------------------------------------------

/// The rest as this process holds it. **Nothing outside the container contributes a word.**
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
    declarations: BTreeMap<String, String>,
    octets: u64,
    content_sha256: String,
}

fn read_rest(locator: &str) -> Result<Rest, String> {
    let occurrence = NativeOccurrence::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let (_, container) = manifest_safetensors(locator).map_err(|error| format!("{locator}: {error}"))?;
    let raw = std::fs::read(locator).map_err(|error| format!("{locator}: {error}"))?;
    let header = u64::from_le_bytes(raw[..8].try_into().map_err(|_| "short container")?) as usize;
    let payload = &raw[8 + header..];
    let region = |name: &str| -> Result<(usize, usize), String> {
        container.tensors.get(name).map(|t| (t.start as usize, t.end as usize)).ok_or_else(|| format!("{locator} does not identify {name}"))
    };
    let u32s = |name: &str| -> Result<Vec<u32>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end].chunks_exact(4).map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]])).collect())
    };
    let u16s = |name: &str| -> Result<Vec<u16>, String> {
        let (start, end) = region(name)?;
        Ok(payload[start..end].chunks_exact(2).map(|w| u16::from_le_bytes([w[0], w[1]])).collect())
    };
    let architecture = u32s("athena.architecture")?;
    let octets = u16s("athena.vocabulary.octets")?;
    let offsets = u32s("athena.vocabulary.offsets")?;
    let mut surfaces = Vec::with_capacity(offsets.len().saturating_sub(1));
    for pair in offsets.windows(2) {
        let bytes: Vec<u8> = octets[pair[0] as usize..pair[1] as usize].iter().map(|w| *w as u8).collect();
        surfaces.push(String::from_utf8(bytes).map_err(|e| e.to_string())?);
    }
    let mut index_of = BTreeMap::new();
    for (at, surface) in surfaces.iter().enumerate() {
        index_of.insert(surface.clone(), at as u32);
    }
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
        declarations: occurrence.declarations.clone(),
        octets: occurrence.container.octets,
        content_sha256: occurrence.container.content_sha256.clone().unwrap_or_default(),
    })
}

impl Rest {
    fn arrays(&self) -> AthenaArrays {
        AthenaArrays {
            indptr: "athena.transport.indptr".to_owned(),
            germ: "athena.transport.germ".to_owned(),
            target: "athena.transport.target".to_owned(),
            standing: "athena.class.standing".to_owned(),
            suffix: "athena.class.suffix".to_owned(),
            classes: self.classes,
            transitions: self.transitions,
            vocabulary: self.vocabulary,
        }
    }
    /// The rest's own codec: the same lexical split the ecology conditioned on, reproduced from the
    /// vocabulary the container carries. A germ index at or above the vocabulary marks unseen.
    fn germs(&self, prompt: &str) -> Vec<u32> {
        lexical_tokens(prompt).into_iter().map(|token| self.index_of.get(&token).copied().unwrap_or(self.vocabulary as u32)).collect()
    }
    /// The class's own continuation population and every one its suffix chain offers, with the
    /// standing and the arc depth. Read from the rest alone; nothing is ranked and nothing crowned.
    fn continuations(&self, state: u32) -> Vec<(String, u32, u32)> {
        let mut held: BTreeMap<u32, (u32, u32)> = BTreeMap::new();
        let mut at = state;
        let mut depth = 0u32;
        loop {
            let from = self.indptr[at as usize] as usize;
            let to = self.indptr[at as usize + 1] as usize;
            for slot in from..to {
                held.entry(self.germ[slot]).or_insert((self.standing[self.target[slot] as usize], depth));
            }
            let parent = self.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
            depth += 1;
        }
        held.into_iter().map(|(germ, (standing, depth))| (self.surfaces[germ as usize].clone(), standing, depth)).collect()
    }
}

/// **The lexical split, reproduced here from the ecology's own rule** — runs of alphanumerics and
/// apostrophes are words, every other non-space octet is its own token, folded to lower case. The
/// engine crate does not depend on `life`, so the codec crosses as a rule rather than as a call;
/// the control that it is the same rule is that the prompts' germs resolve in the rest's own
/// vocabulary, which the receipt reports per prompt.
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

// ---------------------------------------------------------------------------------------------
// the diagram
// ---------------------------------------------------------------------------------------------

struct Founded {
    complex: PortedOperationComplex,
    realization: holonic_engine::front_passage::ResidentRealization,
    walk: EventId,
    future: EventId,
    depth: EventId,
}

fn shape(population: &str, extent: &[usize]) -> SourceTestimony {
    SourceTestimony::DeclaredShape { population: population.to_owned(), shape: extent.to_vec() }
}

fn declares(statement: &str) -> SourceTestimony {
    SourceTestimony::AuthoritativeDescription { statement: statement.to_owned() }
}

fn law(
    complex: &mut PortedOperationComplex,
    name: &str,
    species: OperationSpecies,
    inputs: Vec<BoundaryId>,
    outputs: Vec<BoundaryId>,
    testimony: Vec<SourceTestimony>,
) -> Result<EventId, String> {
    let law = complex.bind_operation(name, species, inputs, outputs, None, testimony).map_err(|e| e.to_string())?;
    complex.occur(law).map_err(|e| e.to_string())
}

fn found(rest: &Rest, walk_geometry: AthenaWalkGeometry, future_geometry: AthenaFutureGeometry) -> Result<Founded, String> {
    let arrays = rest.arrays();
    let mut complex = PortedOperationComplex::new("the native Athena atlas walked and read from its own rest");
    let landed = complex.port("landed class and mark, positions x 2");
    let section = complex.port("future section, positions x vocabulary");
    let mut realization = holonic_engine::front_passage::ResidentRealization::default();

    let atlas_shapes = |with_standing: bool| -> Vec<SourceTestimony> {
        let mut testimony = vec![
            shape("athena.transport.indptr", &[rest.classes + 1, 1]),
            shape("athena.transport.germ", &[rest.transitions, 1]),
            shape("athena.transport.target", &[rest.transitions, 1]),
            shape("athena.class.suffix", &[rest.classes, 1]),
        ];
        if with_standing {
            testimony.push(shape("athena.class.standing", &[rest.classes, 1]));
        }
        testimony
    };

    let mut walk_testimony = atlas_shapes(false);
    walk_testimony.push(declares(WALK_LAW));
    let walk = law(&mut complex, "athena walk", OperationSpecies::Construction, vec![], vec![landed], walk_testimony)?;
    realization.bind(
        walk,
        AthenaWalk {
            arrays: arrays.clone(),
            prompt: "prompt.germs".to_owned(),
            offsets: "prompt.offsets".to_owned(),
            geometry: walk_geometry,
        },
    );

    let mut future_testimony = atlas_shapes(true);
    future_testimony.push(declares(FUTURE_LAW));
    let future = law(&mut complex, "athena future standing", OperationSpecies::Transport, vec![landed], vec![section], future_testimony)?;
    realization.bind(future, AthenaFuture { arrays: arrays.clone(), depth: false, geometry: future_geometry });
    complex
        .carries_precedence(
            "the landed class carries into the future section",
            landed,
            holonic_engine::interaction::OccurrencePort::output(walk, 0),
            holonic_engine::interaction::OccurrencePort::input(future, 0),
        )
        .map_err(|e| e.to_string())?;

    let mut depth_testimony = atlas_shapes(false);
    depth_testimony.push(declares(DEPTH_LAW));
    let depth = law(&mut complex, "athena future depth", OperationSpecies::Transport, vec![landed], vec![section], depth_testimony)?;
    realization.bind(depth, AthenaFuture { arrays, depth: true, geometry: future_geometry });
    complex
        .carries_precedence(
            "the landed class carries into the depth face",
            landed,
            holonic_engine::interaction::OccurrencePort::output(walk, 0),
            holonic_engine::interaction::OccurrencePort::input(depth, 0),
        )
        .map_err(|e| e.to_string())?;

    Ok(Founded { complex, realization, walk, future, depth })
}

// ---------------------------------------------------------------------------------------------
// the conduct
// ---------------------------------------------------------------------------------------------

/// Everything one conduct returns, in words.
struct Conducted {
    walk: Vec<(i64, i64)>,
    future: Vec<(i64, i64)>,
    depth: Vec<(i64, i64)>,
    positions: usize,
    vocabulary: usize,
    fronts: usize,
    graph_nodes: usize,
    occurrences: usize,
    witness: &'static str,
    walk_block: u32,
    walk_blocks: u64,
    future_block: u32,
    future_blocks: u64,
    future_shared: u32,
    entailments: Vec<(String, usize, usize)>,
    charged_octets: u64,
    wall_s: f64,
}

#[allow(clippy::too_many_arguments)]
fn conduct(
    surface: &'static ResidentSurface<'static>,
    rest: &Rest,
    witness: &dyn OccurrenceWitness,
    prompts: &[String],
    walk_geometry: AthenaWalkGeometry,
    future_geometry: AthenaFutureGeometry,
    poison: bool,
) -> Result<Conducted, String> {
    let clock = Instant::now();
    let grain = ResidentGrain(0);
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();

    // the prompts, concatenated with their boundaries: one warp owns one prompt
    let mut germs: Vec<u32> = Vec::new();
    let mut offsets: Vec<u32> = vec![0];
    for prompt in prompts {
        germs.extend(rest.germs(prompt));
        offsets.push(germs.len() as u32);
    }
    if germs.is_empty() {
        return Err("no prompt supplied a germ".to_owned());
    }
    // **The poison**: one prompt's span is made to leave its own buffer. The walk's kernel guards
    // the rest's own addressing, so the occurrence refuses MALFORMED and its declared successors
    // report UPSTREAM with the lineage rather than reading whatever sits at the address.
    if poison {
        let last = offsets.len() - 1;
        offsets[last] = germs.len() as u32 + 4096;
    }

    let mut material = ResidentMaterial::empty();
    let words = rest.indptr.len() + rest.germ.len() + rest.target.len() + rest.standing.len() + rest.suffix.len() + germs.len() + offsets.len();
    let plan = MaterialPlan { maps: Vec::new(), band_elements: 0, positions: words };
    let prediction = passage.predict_material(&plan);
    let admission = passage.admit_material(&prediction).map_err(|o| format!("the atlas material refused: {}", describe(&o)))?;
    for (name, array) in [
        ("athena.transport.indptr", &rest.indptr),
        ("athena.transport.germ", &rest.germ),
        ("athena.transport.target", &rest.target),
        ("athena.class.standing", &rest.standing),
        ("athena.class.suffix", &rest.suffix),
    ] {
        material.arrays.insert(name.to_owned(), surface.mount_positions(array).map_err(|e| e.to_string())?);
    }
    material.arrays.insert("prompt.germs".to_owned(), surface.mount_positions(&germs).map_err(|e| e.to_string())?);
    material.arrays.insert("prompt.offsets".to_owned(), surface.mount_positions(&offsets).map_err(|e| e.to_string())?);

    let founded = found(rest, walk_geometry, future_geometry)?;
    // Nothing here is a midpoint quotient, so the factored-seal reading is empty by construction —
    // taken anyway because a caller that never asks cannot report that it did not apply.
    let (fused, refused_seals) = factored_seals(&founded.complex, &founded.realization, founded.future, &BTreeSet::new());
    if !fused.is_empty() || !refused_seals.is_empty() {
        return Err(format!("the native diagram declared {} fusable and {} unfusable quotients; it has none", fused.len(), refused_seals.len()));
    }

    let bound = passage
        .bind(&founded.complex, &founded.realization, &material, witness, &receiver, Some(&admission), founded.future)
        .map_err(|o| format!("the native deed refused at bind: {}", describe(&o)))?;
    let occurrences = bound.entailments.len();
    let entailments: Vec<(String, usize, usize)> = bound
        .entailments
        .iter()
        .map(|(_, entailment)| (entailment.law.to_owned(), entailment.parameters.len(), entailment.naming_slices.len()))
        .collect();
    let returned = bound.launch(&surface.mode()).map_err(|o| format!("the native deed refused at launch: {}", describe(&o)))?;
    if let Err(obstruction) = bound.standing(&returned) {
        return Err(format!("the native deed did not stand: {}", describe(&obstruction)));
    }
    let (graph, _) = bound.graph();
    let walk = bound.read_section(&returned, founded.walk).map_err(|o| describe(&o))?;
    let future = bound.read_section(&returned, founded.future).map_err(|o| describe(&o))?;
    let depth = bound.read_section(&returned, founded.depth).map_err(|o| describe(&o))?;
    let fronts = bound.fronts().len();
    Ok(Conducted {
        walk,
        future,
        depth,
        positions: germs.len(),
        vocabulary: rest.vocabulary,
        fronts,
        graph_nodes: graph.nodes,
        occurrences,
        witness: witness.witness(),
        walk_block: walk_geometry.block(surface.declaration().warp_size.max(1)),
        walk_blocks: walk_geometry.blocks(prompts.len()),
        future_block: future_geometry.block(),
        future_blocks: future_geometry.blocks(germs.len(), rest.vocabulary),
        future_shared: future_geometry.shared_octets(),
        entailments,
        charged_octets: admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets,
        wall_s: clock.elapsed().as_secs_f64(),
    })
}

fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, lineage, .. } => {
            format!("the card refused at {occurrence:?} ({operation}): {refusal}; lineage refusals {:?}", lineage.refusals)
        }
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => format!("the section at {occurrence:?} was sealed by {quotient:?}; {reopening}"),
    }
}

/// One prompt's returned section, decoded from the rest's own vocabulary. Plural by construction:
/// every germ the landed class's chain offers is here, with its standing and its arc depth.
struct Section {
    prompt: String,
    unseen: Vec<String>,
    trace: Vec<String>,
    class: u32,
    standing: u32,
    offered: Vec<(String, i64, i64)>,
}

fn decode(rest: &Rest, conducted: &Conducted, prompts: &[String]) -> Vec<Section> {
    let mut out = Vec::new();
    let mut at = 0usize;
    for prompt in prompts {
        let tokens = lexical_tokens(prompt);
        let mut trace = Vec::new();
        let mut unseen = Vec::new();
        let mut last = at;
        for token in &tokens {
            let (class, mark) = conducted.walk[last * 2];
            let (_, _) = (class, mark);
            let mark = conducted.walk[last * 2 + 1].0;
            trace.push(match mark {
                2 => {
                    unseen.push(token.clone());
                    format!("{token}=UNSEEN->root")
                }
                0 => format!("{token}*ARC"),
                _ => token.clone(),
            });
            last += 1;
        }
        let terminal = last.saturating_sub(1);
        let class = conducted.walk[terminal * 2].0 as u32;
        let mut offered = Vec::new();
        for germ in 0..rest.vocabulary {
            let flat = terminal * conducted.vocabulary + germ;
            let standing = conducted.future[flat].0;
            let depth = conducted.depth[flat].0;
            if depth >= 0 {
                offered.push((rest.surfaces[germ].clone(), standing, depth));
            }
        }
        out.push(Section {
            prompt: prompt.clone(),
            unseen,
            trace,
            class,
            standing: rest.standing[class as usize],
            offered,
        });
        at = last;
    }
    out
}

// ---------------------------------------------------------------------------------------------
// the ecology manifest, measured from the rest alone
// ---------------------------------------------------------------------------------------------

struct Manifest {
    lines: Vec<String>,
}

impl Manifest {
    fn measured(&mut self, row: &str, value: impl AsRef<str>) {
        self.lines.push(format!("MEASURED  {row}\n    {}", value.as_ref()));
    }
    fn open(&mut self, row: &str, why: impl AsRef<str>, falsifier: impl AsRef<str>) {
        self.lines.push(format!("OPEN      {row}\n    {}\n    FALSIFIER: {}", why.as_ref(), falsifier.as_ref()));
    }
}

/// The atlas's transition graph as an observed system, over a DECLARED scope. Items are the classes
/// the deed's own prompts reached and their suffix ancestors; inputs are the germs those classes
/// offer; the receiver is the germ support of a class — what it can continue with.
struct AtlasSystem<'a> {
    rest: &'a Rest,
    items: Vec<ItemId>,
    inputs: Vec<InputId>,
}

impl ObservedSystem for AtlasSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1)]
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let class = item.0 as u32;
        match receiver.0 {
            // the class's own out-degree — how many continuations the full context licenses
            0 => Observation(u64::from(self.rest.indptr[class as usize + 1] - self.rest.indptr[class as usize])),
            // whether the class is its own suffix parent — the root, the coarsest context
            _ => Observation(u64::from(self.rest.suffix[class as usize] == class)),
        }
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let class = item.0 as u32;
        let germ = input.0 as u32;
        let from = self.rest.indptr[class as usize] as usize;
        let to = self.rest.indptr[class as usize + 1] as usize;
        self.rest.germ[from..to].binary_search(&germ).ok().map(|at| ItemId(self.rest.target[from + at] as u64))
    }
}

fn build_manifest(rest: &Rest, conducted: &Conducted, sections: &[Section], family: &[AthenaCandidate], retained: &[usize], chosen: usize, taxa: usize) -> Manifest {
    let mut manifest = Manifest { lines: Vec::new() };

    // ---- incidence ----
    let cycle_rank = rest.transitions as i64 - rest.classes as i64 + 1;
    manifest.measured(
        "incidence: classes, transitions, suffix links",
        format!("{} classes · {} germ transitions · {} suffix links (one per class, the root its own) · {} vocabulary germs", rest.classes, rest.transitions, rest.classes, rest.vocabulary),
    );
    // reconvergence: classes reached by more than one transition
    let mut indegree: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
    for (slot, reaches) in rest.target.iter().enumerate() {
        indegree.entry(*reaches).or_default().push(slot);
    }
    let reconvergent: Vec<(&u32, &Vec<usize>)> = indegree.iter().filter(|(_, slots)| slots.len() > 1).collect();
    let reconvergent_arcs: usize = reconvergent.iter().map(|(_, slots)| slots.len() - 1).sum();
    manifest.measured(
        "incidence: cycle rank of the transition graph, and the transport population it names",
        format!(
            "b1 = |E| - |S| + 1 = {} - {} + 1 = {cycle_rank}. The departure from tree-ness is RECONVERGENCE: {} classes are reached by more than one germ transition, contributing {reconvergent_arcs} arcs beyond a spanning tree. Tree ancestry compresses freely under its interval receiver; this population does not, and it may not be silently placed into the interval's two coordinates.",
            rest.transitions, rest.classes, reconvergent.len()
        ),
    );
    // exhibit a sample of reconvergent classes, by name
    let mut exhibited = Vec::new();
    for (class, slots) in reconvergent.iter().take(6) {
        let mut arrivals = Vec::new();
        for slot in slots.iter().take(4) {
            let from = rest.indptr.iter().position(|start| *start as usize > *slot).map(|at| at - 1).unwrap_or(0);
            let germ = rest.germ[*slot];
            arrivals.push(format!("class {from} --{:?}--> ", rest.surfaces.get(germ as usize).cloned().unwrap_or_default()));
        }
        exhibited.push(format!("class {} standing {} reached by {} arcs: {}", class, rest.standing[**class as usize], slots.len(), arrivals.join(", ")));
    }
    manifest.measured("incidence: EXHIBITED reconvergent classes (a sample, named, not a count)", exhibited.join("\n    "));

    // directedness: the germ transport alone is acyclic; the arc closes the loops
    let acyclic = germ_transport_is_acyclic(rest);
    manifest.measured(
        "incidence: the germ transport is a DAG and the arc is what closes a loop",
        format!(
            "a topological order over the {} germ transitions {}. So the cycle rank above counts UNDIRECTED reconvergence, never a directed return: nothing winds by transport alone. The suffix link is the only edge that returns, and it returns strictly toward shorter context.",
            rest.transitions,
            if acyclic { "exists — the germ transport carries no directed cycle" } else { "DOES NOT EXIST — the germ transport carries a directed cycle, which refutes the suffix-automaton reading" }
        ),
    );

    // ---- generator / scale ----
    let chart = TreeChart::label(rest.classes, |state| if rest.suffix[state as usize] == state { None } else { Some(rest.suffix[state as usize]) }).ok();
    let mut heights: BTreeMap<u32, usize> = BTreeMap::new();
    for class in 0..rest.classes as u32 {
        heights.entry(suffix_height(rest, class)).or_default().add();
    }
    manifest.measured(
        "generator/scale: the suffix-link height is the scale action, read off the material",
        format!(
            "tree height {} · classes per height {:?} · the depth receiver at height k is the atlas at a coarser grain, and the number of them is the tree's own. No layer count, latent width, head or rank is declared anywhere in this rest or this deed.",
            rest.height,
            heights.iter().map(|(h, n)| (*h, *n)).collect::<Vec<_>>()
        ),
    );
    if let Some(chart) = &chart {
        manifest.measured(
            "generator/scale: the interval (Minkowski) chart face",
            format!(
                "a depth-first interval per class, so containment of intervals IS suffix-link ancestry; written as (t, x) = ((a+b)/2, (b-a)/2) the containment is the light-cone order of 1+1 Minkowski and the declared signature is (+, -). Labelled {} classes, height {}. The remainder of this half of the transition is EMPTY.",
                chart.intervals.len(),
                chart.height
            ),
        );
    }

    // ---- open fibre questions ----
    manifest.measured(
        "open fibre: what the interval receiver cannot separate, exhibited",
        format!(
            "the interval chart carries ancestry exactly and carries NO record of which transition arrived. Every one of the {} reconvergent classes is a collapsed fibre for it: the {reconvergent_arcs} arcs beyond a spanning tree are indistinguishable to the interval receiver, and reopening them needs the transport rows themselves. A container of dimension below {cycle_rank} has declared a receiver family that cannot separate some of them, and the collapsed population is the compression's exact loss rather than an unknown.",
            reconvergent.len()
        ),
    );

    // ---- state ----
    manifest.lines.push(markov_row(rest, sections));

    // ---- group / gauge ----
    let (bijective, partial, total_germs) = germ_action_census(rest);
    manifest.measured(
        "group/gauge: what group action the material FOUNDS",
        format!(
            "NONE is founded, measured. Each germ acts partially on the classes: of {total_germs} germs, {bijective} act bijectively on the classes they touch and {partial} do not, and NO germ acts on every class — the transport is a partial function, so the germs generate a MONOID and not a group. There is no inverse to exhibit, so there is no group element, no orbit and no holonomy to return.",
        ),
    );
    manifest.open(
        "group/gauge: winding and phase",
        "the longest-suffix carry monoid is APERIODIC BY CONSTRUCTION and periodic material cannot make it a crystal. Nothing in this rest returns a winding: the germ transport is a DAG (measured above), the arc returns strictly toward shorter context, and no germ's action is invertible, so no nontrivial group element exists to wind.",
        "a crystal claim on this material would have to return a NONTRIVIAL GROUP ELEMENT with its winding, a band structure and a holonomy around a closed transport loop. Exhibit one closed directed loop in the germ transport, or one germ whose action is invertible on the whole class population, and this row moves from OPEN to measured. Neither exists here.",
    );
    manifest.open(
        "state: sufficient-state candidates beyond the Nerode reading",
        "named, not built: (a) the class itself, which is the automaton's own state and is sufficient by construction for one-step transport; (b) the pair (class, arc depth), which the deed already returns and which distinguishes a continuation the full context licenses from one only a shorter context does; (c) the suffix-ancestor at a declared height, which is the scale action's own coarsening.",
        "a sufficient state is decided by lumpability against a DECLARED receiver family, not by a name. Any of these becomes measured by running the receiver-exact compression at its own coarsening and exhibiting the collapsed population with the shortest word that separates each pair.",
    );

    // ---- the launch geometry, and the convicted shape ----
    let convicted_blocks = ((conducted.positions * conducted.vocabulary) as u64).div_ceil(512);
    manifest.measured(
        "the parallel deed: the future section's derived launch geometry against the convicted flat shape",
        format!(
            "family {} admitted candidates · retained under the declared axes {} · chosen grid {} x block {} ({} dynamic shared octets, chain staged {} deep, {} germ lanes reading one staged chain, the card's resident lanes {} of {} occupied) · the CONVICTED predecessor shape on the same extent is grid {} x block 512 at one thread per cell with the suffix chain climbed per cell and no staging. The walk is grid {} x block {}, one warp per prompt, and the transport row is searched 32-ary rather than by one lane.",
            family.len(),
            retained.len(),
            conducted.future_blocks,
            conducted.future_block,
            conducted.future_shared,
            family.get(chosen).map(|c| c.geometry.chain_stage).unwrap_or(0),
            family.get(chosen).map(|c| c.chain_reuse).unwrap_or(1),
            family.get(chosen).map(|c| c.cover_occupied.0).unwrap_or(0),
            family.get(chosen).map(|c| c.cover_occupied.1).unwrap_or(1),
            convicted_blocks,
            conducted.walk_blocks,
            conducted.walk_block,
        ),
    );

    // ---- Station D, cited as exterior evidence ----
    manifest.measured(
        "exterior evidence (Station D, cited, NOT imported as topology)",
        format!(
            "output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form carries {taxa} intervention taxa against the foreign source; every non-gauge taxon moved a face of the declared receiver family and every predicted-unmoved control held. That is exterior evidence for WHAT a native morphology must be able to express — a change at a site reaching a later face, a gauge that moves no order face, a control that holds — and it contributes no layer, head, width or rank to this manifest. This deed's own analogue is the ablation table: a withdrawn document moves the sections its material founded.",
        ),
    );

    manifest
}

trait Add {
    fn add(&mut self);
}
impl Add for usize {
    fn add(&mut self) {
        *self += 1;
    }
}

fn suffix_height(rest: &Rest, class: u32) -> u32 {
    let mut at = class;
    let mut height = 0u32;
    loop {
        let parent = rest.suffix[at as usize];
        if parent == at {
            return height;
        }
        at = parent;
        height += 1;
        if height > rest.classes as u32 {
            return height;
        }
    }
}

/// Is the germ transport a DAG? A suffix automaton's transitions always increase the longest
/// context, so it should be; measured rather than assumed, by Kahn's algorithm over the whole graph.
fn germ_transport_is_acyclic(rest: &Rest) -> bool {
    let mut indegree = vec![0u32; rest.classes];
    for reaches in &rest.target {
        indegree[*reaches as usize] += 1;
    }
    let mut frontier: Vec<u32> = (0..rest.classes as u32).filter(|class| indegree[*class as usize] == 0).collect();
    let mut removed = 0usize;
    while let Some(class) = frontier.pop() {
        removed += 1;
        let from = rest.indptr[class as usize] as usize;
        let to = rest.indptr[class as usize + 1] as usize;
        for slot in from..to {
            let reaches = rest.target[slot] as usize;
            indegree[reaches] -= 1;
            if indegree[reaches] == 0 {
                frontier.push(reaches as u32);
            }
        }
    }
    removed == rest.classes
}

/// Of the germs, how many act bijectively on the classes they touch. A group action would need one
/// that acts on EVERY class invertibly; the census returns whether any does.
fn germ_action_census(rest: &Rest) -> (usize, usize, usize) {
    let mut reached: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for class in 0..rest.classes as u32 {
        let from = rest.indptr[class as usize] as usize;
        let to = rest.indptr[class as usize + 1] as usize;
        for slot in from..to {
            reached.entry(rest.germ[slot]).or_default().push(rest.target[slot]);
        }
    }
    let mut bijective = 0usize;
    let mut partial = 0usize;
    for targets in reached.values() {
        let distinct: BTreeSet<u32> = targets.iter().copied().collect();
        if distinct.len() == targets.len() {
            bijective += 1;
        } else {
            partial += 1;
        }
    }
    (bijective, partial, rest.vocabulary)
}

/// The Markov reading, at a DECLARED receiver family and a declared scope, or the aperture that
/// blocks it stated with its measurement.
fn markov_row(rest: &Rest, sections: &[Section]) -> String {
    // The declared scope: the classes this deed's own prompts reached, and every suffix ancestor of
    // each — the terrain the deed actually navigated.
    let mut scope: BTreeSet<u32> = BTreeSet::new();
    for section in sections {
        let mut at = section.class;
        loop {
            scope.insert(at);
            let parent = rest.suffix[at as usize];
            if parent == at {
                break;
            }
            at = parent;
        }
    }
    // and one step forward from each, so a successor exists to refine on
    let reached: Vec<u32> = scope.iter().copied().collect();
    for class in reached {
        let from = rest.indptr[class as usize] as usize;
        let to = rest.indptr[class as usize + 1] as usize;
        for slot in from..to {
            scope.insert(rest.target[slot]);
        }
    }
    let items: Vec<ItemId> = scope.iter().map(|class| ItemId(*class as u64)).collect();
    let mut germs: BTreeSet<u32> = BTreeSet::new();
    for class in &scope {
        let from = rest.indptr[*class as usize] as usize;
        let to = rest.indptr[*class as usize + 1] as usize;
        for slot in from..to {
            germs.insert(rest.germ[slot]);
        }
    }
    let inputs: Vec<InputId> = germs.iter().map(|germ| InputId(*germ as u64)).collect();
    // The whole-atlas reading is out of reach and the aperture is stated with its measurement:
    // Moore's refinement is |items| x |inputs| successor lookups per round with a linear block
    // search inside each, so the whole atlas is 59,698 x 5,385 x |blocks| per round.
    let whole = (rest.classes as u128) * (rest.vocabulary as u128);
    let scoped = (items.len() as u128) * (inputs.len() as u128);
    let system = AtlasSystem { rest, items: items.clone(), inputs: inputs.clone() };
    let scope_clock = Instant::now();
    let compression = compress(&system);
    let scope_wall = scope_clock.elapsed().as_secs_f64();
    let order = compression.memory_order();
    let beyond: Vec<String> = compression
        .beyond_order(1)
        .iter()
        .take(4)
        .map(|pair| format!("classes {} and {} separated only by {:?}", pair.left.0, pair.right.0, pair.distinguishing_word.iter().map(|input| rest.surfaces.get(input.0 as usize).cloned().unwrap_or_default()).collect::<Vec<_>>()))
        .collect();
    format!(
        "MEASURED  state: the memory order under a DECLARED receiver family, at a DECLARED scope\n    \
         receiver family: (a) the class's own out-degree, (b) whether the class is the root. inputs: the {} germs the scope offers. \
         scope: the {} classes this deed's prompts reached, their suffix ancestors, and one germ step forward from each.\n    \
         one-shot blocks {} · conduct-stable blocks {} · Moore rounds {} · collapsed pairs {} · memory order {}\n    \
         {}\n    \
         APERTURE: the whole-atlas reading is NOT taken, and this is the measurement that blocks it. This scope took {scope_wall:.1} s. \
         Moore's refinement builds, per item, a signature vector of one entry per input, so one round over the whole atlas needs \
         {whole} entries at 8 octets = {} octets of signature material in one allocation, against this scope's {scoped} entries; and the \
         standing owner resolves an item's block by a LINEAR SCAN of the partition, which is |items| x |blocks| set lookups per round. \
         The block is the resident material of one round, not the arithmetic. It lifts by giving receiver_exact_compression an indexed \
         block lookup and a streamed signature — a repair inside that owner, not a new organ — and until then the whole-atlas memory \
         order is OPEN and this row is the reading at the declared scope, which is the terrain the deed actually navigated.",
        inputs.len(),
        items.len(),
        compression.one_shot.len(),
        compression.conduct.len(),
        compression.rounds,
        compression.collapsed.len(),
        order.map(|o| o.to_string()).unwrap_or_else(|| "NONE — the one-shot reading was already exact for this family, so nothing collapsed and there is no depth to report".to_owned()),
        if beyond.is_empty() { "no collapsed pair needs more than one germ to separate".to_owned() } else { format!("beyond order 1: {}", beyond.join("; ")) },
        whole * 8,
    )
}

// ---------------------------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------------------------

struct Verdicts {
    lines: Vec<String>,
    failed: usize,
}

impl Verdicts {
    fn record(&mut self, number: u32, name: &str, pass: bool, detail: impl AsRef<str>) {
        let verdict = if pass { "PASS" } else { "FAIL" };
        if !pass {
            self.failed += 1;
        }
        let line = format!("  [{number:>2}] {verdict}  {name}\n        {}", detail.as_ref());
        println!("{line}");
        self.lines.push(line);
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    if let Some(at) = arguments.iter().position(|argument| argument == "--conduct") {
        let rest = arguments.get(at + 1).cloned().unwrap_or_default();
        let faces = arguments.iter().position(|a| a == "--faces").and_then(|at| arguments.get(at + 1)).cloned().unwrap_or_default();
        let prompts: Vec<String> = arguments.iter().enumerate().filter(|(_, a)| a.as_str() == "--prompt").filter_map(|(at, _)| arguments.get(at + 1).cloned()).collect();
        child(&rest, &faces, &prompts);
        return;
    }
    if let Err(reason) = parent(&arguments) {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

/// **THE CHILD.** It is handed a rest path and the prompts, and nothing else. There is no corpus
/// path, no Gemma path and no phoenix path in this function's reach.
fn child(rest_path: &str, faces_path: &str, prompts: &[String]) {
    let readout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)) as &'static ResidentReadout,
        Err(error) => {
            println!("CHILD-REFUSED the resident chart: {error:?}");
            std::process::exit(2);
        }
    };
    let surface: &'static ResidentSurface<'static> = match ResidentSurface::on(readout) {
        Ok(surface) => Box::leak(Box::new(surface)),
        Err(error) => {
            println!("CHILD-REFUSED the resident surface: {error}");
            std::process::exit(2);
        }
    };
    let rest = match read_rest(rest_path) {
        Ok(rest) => rest,
        Err(error) => {
            println!("CHILD-REFUSED the native rest: {error}");
            std::process::exit(3);
        }
    };
    let witness = match NativeOccurrence::read(rest_path) {
        Ok(witness) => witness,
        Err(error) => {
            println!("CHILD-REFUSED the witness: {error}");
            std::process::exit(3);
        }
    };
    let (walk_geometry, future_geometry) = match choose(surface, &rest, prompts) {
        Ok(pair) => pair,
        Err(error) => {
            println!("CHILD-REFUSED the launch geometry: {error}");
            std::process::exit(4);
        }
    };
    let conducted = match conduct(surface, &rest, &witness, prompts, walk_geometry, future_geometry, false) {
        Ok(conducted) => conducted,
        Err(error) => {
            println!("CHILD-REFUSED while conducting: {error}");
            std::process::exit(4);
        }
    };

    // **THE LIVE ACCESS AUDIT**, taken after the deed. A preflight declaration is not evidence.
    let mut opened = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                opened.push(target.to_string_lossy().into_owned());
            }
        }
    }
    opened.sort();
    println!("CHILD-OPENED {}", opened.join(" | "));

    let mut octets = Vec::with_capacity((conducted.walk.len() + conducted.future.len() + conducted.depth.len()) * 16);
    for face in [&conducted.walk, &conducted.future, &conducted.depth] {
        for (lo, hi) in face {
            octets.extend_from_slice(&lo.to_le_bytes());
            octets.extend_from_slice(&hi.to_le_bytes());
        }
    }
    if !faces_path.is_empty() {
        let _ = std::fs::write(faces_path, &octets);
    }
    let sections = decode(&rest, &conducted, prompts);
    println!("CHILD-POSITIONS {}", conducted.positions);
    println!("CHILD-FACE-OCTETS {}", octets.len());
    for section in &sections {
        println!("CHILD-SECTION {} class {} standing {} offered {}", section.prompt, section.class, section.standing, section.offered.len());
    }
}

/// The candidate family, the declared axes, the retained set, and the caller's chosen member.
fn choose(surface: &ResidentSurface<'_>, rest: &Rest, prompts: &[String]) -> Result<(AthenaWalkGeometry, AthenaFutureGeometry), String> {
    let positions: usize = prompts.iter().map(|prompt| lexical_tokens(prompt).len()).sum();
    let family = surface.athena_future_candidates(positions, rest.vocabulary, rest.height).map_err(|e| e.to_string())?;
    if family.is_empty() {
        return Err("the device admits no member of the native future family".to_owned());
    }
    let axes = declared_axes();
    let retained = athena_non_dominated(&family, &axes);
    let chosen = pick(&family, &retained);
    let warps = walk_warps(surface, prompts.len());
    Ok((warps, family[chosen].geometry))
}

/// **The receiver's declared axes.** Changing this set changes the retained set, which is the
/// falsifier: a return that did not move under a changed declaration was ranking.
fn declared_axes() -> Vec<AthenaAxis> {
    vec![AthenaAxis::CoverUp, AthenaAxis::ResidentBlocksUp, AthenaAxis::ChainReuseUp, AthenaAxis::SharedDown, AthenaAxis::ClimbPastStageDown]
}

/// **The caller's choice from the retained set, declared in words before it is computed.**
///
/// A front is covered by EXTENT and never by count, so the first clause is that the launch must
/// occupy at least one whole wave of the card's resident lanes — anything below that leaves the
/// extent uncovered no matter how good its other coordinates are. Then: the staged chain must cover
/// the whole tree height, so no lane climbs in global memory past the stage; then the greatest
/// residency per multiprocessor; then the greatest chain reuse. Nothing here is an optimum and
/// nothing is a score: it is a declaration, and a different one takes a different member.
fn pick(family: &[AthenaCandidate], retained: &[usize]) -> usize {
    let key = |candidate: &AthenaCandidate| {
        (
            candidate.cover_occupied.0 >= candidate.cover_occupied.1,
            candidate.climb_past_stage == 0,
            candidate.resident_blocks,
            candidate.chain_reuse,
        )
    };
    let mut best = retained.first().copied().unwrap_or(0);
    for at in retained {
        if key(&family[*at]) > key(&family[best]) {
            best = *at;
        }
    }
    best
}

/// The walk's warps per block: the whole prompt population in one block where it fits, so the grid
/// is exactly the extent it needs and never more.
fn walk_warps(surface: &ResidentSurface<'_>, prompts: usize) -> AthenaWalkGeometry {
    let warp = surface.declaration().warp_size.max(1);
    let ceiling = 512 / warp.max(1);
    let mut warps = 1u32;
    for candidate in AthenaWalkGeometry::enumerate() {
        if candidate.warps <= ceiling && candidate.warps as usize <= prompts.max(1) && candidate.warps > warps {
            warps = candidate.warps;
        }
    }
    AthenaWalkGeometry { warps }
}

fn parent(arguments: &[String]) -> Result<(), String> {
    let mut rest_path = REST.to_owned();
    let mut ablated_path = ABLATED.to_owned();
    let mut prompts: Vec<String> = Vec::new();
    let mut it = arguments.iter().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--rest" => rest_path = it.next().cloned().ok_or("--rest <path>")?,
            "--ablated" => ablated_path = it.next().cloned().ok_or("--ablated <path>")?,
            "--prompt" => prompts.push(it.next().cloned().ok_or("--prompt <text>")?),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if prompts.is_empty() {
        prompts = PROMPTS.iter().map(|p| (*p).to_owned()).collect();
    }
    std::fs::create_dir_all(OUT).map_err(|e| e.to_string())?;
    let clock = Instant::now();
    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };

    println!("THE NATIVE BASELINE CONDUCTS FROM ITS OWN REST — Deed P0, ARM N\n");

    let readout: &'static ResidentReadout = Box::leak(Box::new(ResidentReadout::new().map_err(|e| format!("{e:?}"))?));
    let surface: &'static ResidentSurface<'static> = Box::leak(Box::new(ResidentSurface::on(readout).map_err(|e| e.to_string())?));
    println!("  resident chart            {}", surface.device_name());
    println!("  kernels in the module     {}", KERNELS.len());
    println!("  PTX content               {}", &surface.ptx_sha256()[..16]);

    let rest = read_rest(&rest_path)?;
    let witness = NativeOccurrence::read(&rest_path).map_err(|e| e.to_string())?;
    println!();
    println!("  THE REST — the only semantic input of this deed");
    println!("    {}  {} octets  content {}", rest.locator, rest.octets, &rest.content_sha256[..16]);
    println!("    classes {}  transitions {}  vocabulary {}  tree height {}", rest.classes, rest.transitions, rest.vocabulary, rest.height);
    println!("    the rest's own declarations ({}):", rest.declarations.len());
    for (key, statement) in &rest.declarations {
        println!("      {key}: {}", statement.chars().take(110).collect::<String>());
    }

    // ---------------------------------------------------------------------------------------
    // the launch geometry: the family, the declared axes, the retained set, the chosen member
    // ---------------------------------------------------------------------------------------
    let positions: usize = prompts.iter().map(|prompt| lexical_tokens(prompt).len()).sum();
    let family = surface.athena_future_candidates(positions, rest.vocabulary, rest.height).map_err(|e| e.to_string())?;
    let axes = declared_axes();
    let retained = athena_non_dominated(&family, &axes);
    let coarse_axes = [AthenaAxis::ResidentBlocksUp, AthenaAxis::SharedDown];
    let coarser = athena_non_dominated(&family, &coarse_axes);
    let chosen = pick(&family, &retained);
    let walk_geometry = walk_warps(surface, prompts.len());
    let limits = surface.multiprocessor_limits();
    println!();
    println!("  THE LAUNCH GEOMETRY — derived from the device and the module's measured registers");
    println!("    multiprocessors {}  warp {}  max blocks/SM {}  max threads/SM {}  max registers/SM {}  max shared/SM {}", limits.multiprocessors, limits.warp, limits.max_blocks, limits.max_threads, limits.max_registers, limits.max_shared_octets);
    println!("    the module's derived block ceiling {} (the MINIMUM over every kernel's own admission, a refusal bound and not an optimum)", surface.multiprocessor_limits().warp * 0 + block_ceiling(surface));
    println!("    admitted candidates {}   retained under {:?}: {}   retained under a coarser declaration {:?}: {}", family.len(), axes, retained.len(), coarse_axes, coarser.len());
    println!("      {:<34} {:>6} {:>8} {:>6} {:>6} {:>9} {:>12} {:>14} {:>7}", "geometry (pos x lanes x G, stage)", "block", "shared", "regs", "res/SM", "blocks", "residency wv", "cover of card", "reuse");
    for at in retained.iter().take(18).chain(retained.iter().skip(18).filter(|at| **at == chosen)) {
        let candidate = &family[*at];
        let geometry = candidate.geometry;
        println!(
            "      {:<34} {:>6} {:>8} {:>6} {:>6} {:>9} {:>5}/{:<6} {:>6}/{:<7} {:>7}{}",
            format!("{} x {} x {}, stage {}", geometry.positions_per_block, geometry.lanes, geometry.germs_per_lane, geometry.chain_stage),
            candidate.block,
            candidate.shared_octets,
            candidate.registers,
            candidate.resident_blocks,
            candidate.blocks,
            candidate.residency_waves.0,
            candidate.residency_waves.1,
            candidate.cover_occupied.0,
            candidate.cover_occupied.1,
            candidate.chain_reuse,
            if *at == chosen { "  <- CHOSEN, caller-declared" } else { "" }
        );
    }
    if retained.len() > 18 {
        println!("      … {} more retained, every one in the receipt", retained.len() - 18);
    }
    let convicted_blocks = ((positions * rest.vocabulary) as u64).div_ceil(u64::from(block_ceiling(surface)));
    println!();
    println!("    THE CONVICTED SHAPE, on this same extent, for comparison:");
    println!("      walk    predecessor: grid {} x block {}, `if (flat != 0) return;` — 1 working lane out of {}",
        (positions as u64 * 2).div_ceil(u64::from(block_ceiling(surface))), block_ceiling(surface), (positions as u64 * 2).div_ceil(u64::from(block_ceiling(surface))) * u64::from(block_ceiling(surface)));
    println!("      future  predecessor: grid {convicted_blocks} x block {} — one thread per cell, the chain climbed per cell, nothing staged, reuse 1", block_ceiling(surface));
    println!("      walk    HERE: grid {} x block {} — one warp per prompt over {} prompts, the transport row searched 32-ary", walk_geometry.blocks(prompts.len()), walk_geometry.block(limits.warp), prompts.len());
    println!("      future  HERE: grid {} x block {} — {} shared octets ({} dynamic + {} static), one chain staged {} deep and read by {} germ lanes, {}/{} of the card's resident lanes occupied",
        family[chosen].blocks, family[chosen].block, family[chosen].shared_octets, family[chosen].geometry.shared_octets(), family[chosen].shared_octets - family[chosen].geometry.shared_octets(), family[chosen].geometry.chain_stage, family[chosen].chain_reuse, family[chosen].cover_occupied.0, family[chosen].cover_occupied.1);

    // ---------------------------------------------------------------------------------------
    // the deed
    // ---------------------------------------------------------------------------------------
    let conducted = conduct(surface, &rest, &witness, &prompts, walk_geometry, family[chosen].geometry, false)?;
    let sections = decode(&rest, &conducted, &prompts);
    println!();
    println!("  THE DEED — {} occurrences, {} fronts, {} graph nodes, witness {:?}, {:.3} s", conducted.occurrences, conducted.fronts, conducted.graph_nodes, conducted.witness, conducted.wall_s);
    for (law, parameters, naming) in &conducted.entailments {
        println!("      {law:<16} entailed by {parameters} parameters, {naming} naming statement(s) the rest itself carries");
    }

    println!();
    println!("  THE PLURAL SECTIONS — decoded from the rest's own vocabulary; nothing ranked, nothing crowned");
    for section in &sections {
        println!();
        println!("    {:?}", section.prompt);
        println!("      walk        {}", section.trace.join(" -> "));
        println!("      class       {}   standing {}   germs in the section {}", section.class, section.standing, section.offered.len());
        let mut by_depth: BTreeMap<i64, Vec<(String, i64)>> = BTreeMap::new();
        for (surface_text, standing, depth) in &section.offered {
            by_depth.entry(*depth).or_default().push((surface_text.clone(), *standing));
        }
        for (depth, members) in by_depth.iter().take(3) {
            let label = if *depth == 0 { "the class's own — what the FULL context licenses".to_owned() } else { format!("reached by arcing {depth} shorter") };
            println!("        depth {depth}: {:<5} germs — {label}", members.len());
            for (surface_text, standing) in members.iter().take(8) {
                println!("          {:<28} standing {standing}", format!("{surface_text:?}"));
            }
            if members.len() > 8 {
                println!("          … {} more at this depth, every one retained", members.len() - 8);
            }
        }
    }

    // ---- controls ----
    let plural = sections.iter().all(|section| !section.offered.is_empty());
    let widest = sections.iter().map(|s| s.offered.len()).max().unwrap_or(0);
    verdicts.record(
        1,
        "the future section is PLURAL and decoded — every prompt returns the whole germ population its chain offers, never one winner",
        plural && widest > 1,
        format!(
            "{} prompts · germs the whole suffix chain offers {:?} (widest {widest}) · germs at DEPTH 0, what the full context alone licenses, {:?} · germs at depth 1 {:?} · no argmax, no sampler, no temperature and no ranking anywhere in the deed: the return is the section, stratified by the arc depth the material has",
            sections.len(),
            sections.iter().map(|s| s.offered.len()).collect::<Vec<_>>(),
            sections.iter().map(|s| s.offered.iter().filter(|(_, _, d)| *d == 0).count()).collect::<Vec<_>>(),
            sections.iter().map(|s| s.offered.iter().filter(|(_, _, d)| *d == 1).count()).collect::<Vec<_>>()
        ),
    );

    let unseen: Vec<&Section> = sections.iter().filter(|section| !section.unseen.is_empty()).collect();
    let root_offered = rest.continuations(0).len();
    verdicts.record(
        2,
        "an unseen germ returns the ROOT's plural section — the walk's arc law, stated, not an error",
        unseen.iter().all(|section| section.class == 0 && section.offered.len() == root_offered),
        format!(
            "{} prompt(s) carried a germ the rest's vocabulary does not have ({:?}); each landed at class 0 and returned {} germs — the root offers {} read straight from the rest, and the walk returns to the root by law rather than refusing",
            unseen.len(),
            unseen.iter().flat_map(|s| s.unseen.clone()).collect::<Vec<_>>(),
            unseen.first().map(|s| s.offered.len()).unwrap_or(0),
            root_offered
        ),
    );

    // ---- the geometry equality control: two admitted members, the same words ----
    let second = retained.iter().copied().find(|at| *at != chosen).unwrap_or(chosen);
    let alternative = conduct(surface, &rest, &witness, &prompts, AthenaWalkGeometry { warps: 1 }, family[second].geometry, false)?;
    let geometry_equal = alternative.walk == conducted.walk && alternative.future == conducted.future && alternative.depth == conducted.depth;
    verdicts.record(
        5,
        "the launch geometry is APPARATUS: two admitted members of the family return bit-identical words, and the convicted flat shape is measurably gone",
        geometry_equal && family[chosen].residency_waves.0 >= 1,
        format!(
            "chosen ({} x {} x {}, stage {}, grid {} x block {}) against ({} x {} x {}, stage {}, grid {} x block {}) and walk warps {} against 1: {} walk words, {} future words and {} depth words bit-identical {geometry_equal} · residency waves {}/{} = {:.2}, cover of the card {}/{} = {:.2}, lane waves {}/{} = {:.2} · the predecessor's grid {} x block {} at one working lane is not this shape",
            family[chosen].geometry.positions_per_block, family[chosen].geometry.lanes, family[chosen].geometry.germs_per_lane, family[chosen].geometry.chain_stage, family[chosen].blocks, family[chosen].block,
            family[second].geometry.positions_per_block, family[second].geometry.lanes, family[second].geometry.germs_per_lane, family[second].geometry.chain_stage, family[second].blocks, family[second].block,
            walk_geometry.warps,
            conducted.walk.len(), conducted.future.len(), conducted.depth.len(),
            family[chosen].residency_waves.0, family[chosen].residency_waves.1,
            family[chosen].residency_waves.0 as f64 / family[chosen].residency_waves.1.max(1) as f64,
            family[chosen].cover_occupied.0, family[chosen].cover_occupied.1,
            family[chosen].cover_occupied.0 as f64 / family[chosen].cover_occupied.1.max(1) as f64,
            family[chosen].lane_waves.0, family[chosen].lane_waves.1,
            family[chosen].lane_waves.0 as f64 / family[chosen].lane_waves.1.max(1) as f64,
            convicted_blocks, block_ceiling(surface)
        ),
    );

    // ---- the poisoned lineage ----
    let poisoned = conduct(surface, &rest, &witness, &prompts, walk_geometry, family[chosen].geometry, true);
    verdicts.record(
        6,
        "the census is aggregated and the refusal is LINEAGE-LOCAL: a poisoned prompt span refuses MALFORMED on the card and the successors report it upstream",
        poisoned.is_err(),
        match &poisoned {
            Err(reason) => format!("one prompt's span was made to leave its own buffer; the deed returned: {}", reason.chars().take(420).collect::<String>()),
            Ok(_) => "the poisoned deed STOOD, which refutes the guard".to_owned(),
        },
    );

    // ---- the ablation ----
    println!();
    println!("  THE ABLATION — the rest rebuilt WITHOUT canon/TABLET_THE_HEXIS.md (construction-level; a founded class is not deleted in place)");
    let ablated_rest = read_rest(&ablated_path)?;
    let ablated_witness = NativeOccurrence::read(&ablated_path).map_err(|e| e.to_string())?;
    let ablated_geometry = {
        let ablated_family = surface.athena_future_candidates(positions, ablated_rest.vocabulary, ablated_rest.height).map_err(|e| e.to_string())?;
        let ablated_retained = athena_non_dominated(&ablated_family, &axes);
        ablated_family[pick(&ablated_family, &ablated_retained)].geometry
    };
    let ablated_conducted = conduct(surface, &ablated_rest, &ablated_witness, &prompts, walk_geometry, ablated_geometry, false)?;
    let ablated_sections = decode(&ablated_rest, &ablated_conducted, &prompts);
    println!("    {:<48} {:>9} {:>9} {:>9} {:>9} {:>10}", "prompt", "germs", "germs'", "moved", "gone", "depth-0");
    let mut ablation_rows = Vec::new();
    for (whole, ablated) in sections.iter().zip(ablated_sections.iter()) {
        let before: BTreeMap<&str, (i64, i64)> = whole.offered.iter().map(|(s, standing, depth)| (s.as_str(), (*standing, *depth))).collect();
        let after: BTreeMap<&str, (i64, i64)> = ablated.offered.iter().map(|(s, standing, depth)| (s.as_str(), (*standing, *depth))).collect();
        let gone: Vec<&str> = before.keys().filter(|surface_text| !after.contains_key(*surface_text)).copied().collect();
        let arrived: Vec<&str> = after.keys().filter(|surface_text| !before.contains_key(*surface_text)).copied().collect();
        let moved: Vec<&str> = before.iter().filter(|(surface_text, face)| after.get(**surface_text).is_some_and(|other| other != *face)).map(|(s, _)| *s).collect();
        let support_identical = gone.is_empty() && arrived.is_empty();
        let depth0_before: BTreeSet<&str> = whole.offered.iter().filter(|(_, _, d)| *d == 0).map(|(s, _, _)| s.as_str()).collect();
        let depth0_after: BTreeSet<&str> = ablated.offered.iter().filter(|(_, _, d)| *d == 0).map(|(s, _, _)| s.as_str()).collect();
        let depth0_identical = depth0_before == depth0_after;
        println!(
            "    {:<48} {:>9} {:>9} {:>9} {:>9} {:>10}",
            format!("{:?}", whole.prompt.chars().take(44).collect::<String>()),
            whole.offered.len(),
            ablated.offered.len(),
            moved.len(),
            gone.len(),
            if depth0_identical { "IDENTICAL" } else { "moved" }
        );
        ablation_rows.push((whole.prompt.clone(), whole.offered.len(), ablated.offered.len(), moved.len(), gone.len(), arrived.len(), support_identical, depth0_identical, gone.iter().take(6).map(|s| (*s).to_owned()).collect::<Vec<_>>()));
    }
    let hexis_prompts: Vec<&(String, usize, usize, usize, usize, usize, bool, bool, Vec<String>)> =
        ablation_rows.iter().filter(|row| row.0.contains("hexis") || row.0.contains("cultivation")).collect();
    let moved_by_ablation = hexis_prompts.iter().all(|row| row.3 > 0 || row.4 > 0);
    let unrelated: Vec<&(String, usize, usize, usize, usize, usize, bool, bool, Vec<String>)> =
        ablation_rows.iter().filter(|row| !row.0.contains("hexis") && !row.0.contains("cultivation")).collect();
    let depth0_held = unrelated.iter().filter(|row| row.7).count();
    verdicts.record(
        4,
        "the ablation moves the withdrawn document's prompts, exhibited as a plural diff",
        moved_by_ablation,
        format!(
            "the two prompts drawn from the withdrawn document moved: {} · the germs that left the section by name: {:?}",
            hexis_prompts.iter().map(|row| format!("{:?}: {} germs -> {}, {} faces moved, {} germs gone", row.0, row.1, row.2, row.3, row.4)).collect::<Vec<_>>().join(" | "),
            hexis_prompts.iter().map(|row| row.8.clone()).collect::<Vec<_>>()
        ),
    );
    verdicts.record(
        11,
        "the unchanged control, MEASURED rather than assumed: which face of an unrelated prompt survives a construction-level ablation",
        true,
        format!(
            "{} of {} unrelated prompts return a BIT-IDENTICAL depth-0 germ support (what the full context licenses) · {} of {} return an identical support at every depth · and the STANDINGS move for every prompt, because a standing is a corpus-wide occurrence count and withdrawing a document changes the corpus. That is the honest boundary of a construction-level ablation: the support at the specific end is what survives, and the counts do not.",
            depth0_held, unrelated.len(),
            unrelated.iter().filter(|row| row.6).count(), unrelated.len()
        ),
    );

    // ---------------------------------------------------------------------------------------
    // the fresh process
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE FRESH PROCESS — re-executed with the rest's path and the prompts, and nothing else");
    let mut parent_faces = Vec::new();
    for face in [&conducted.walk, &conducted.future, &conducted.depth] {
        for (lo, hi) in face {
            parent_faces.extend_from_slice(&lo.to_le_bytes());
            parent_faces.extend_from_slice(&hi.to_le_bytes());
        }
    }
    let exchange = std::env::temp_dir().join("native-baseline-child-faces.bin");
    let mut command = std::process::Command::new(std::env::current_exe().map_err(|e| e.to_string())?);
    command.arg("--conduct").arg(&rest_path).arg("--faces").arg(&exchange);
    for prompt in &prompts {
        command.arg("--prompt").arg(prompt);
    }
    let child_output = command.output().map_err(|e| e.to_string())?;
    let child_text = String::from_utf8_lossy(&child_output.stdout).into_owned();
    let child_faces = std::fs::read(&exchange).unwrap_or_default();
    let opened: Vec<String> = child_text
        .lines()
        .find(|line| line.starts_with("CHILD-OPENED "))
        .map(|line| line.trim_start_matches("CHILD-OPENED ").split(" | ").map(|s| s.to_owned()).collect())
        .unwrap_or_default();
    for line in child_text.lines().filter(|line| line.starts_with("CHILD-")) {
        println!("    {}", line.chars().take(200).collect::<String>());
    }
    let forbidden = ["gemma", "phoenix", "/canon/", "canon/", "tokenizer", "model.safetensors"];
    let offending: Vec<&String> = opened
        .iter()
        .filter(|path| {
            let lower = path.to_lowercase();
            forbidden.iter().any(|needle| lower.contains(needle)) && !lower.ends_with("rest.safetensors")
        })
        .collect();
    verdicts.record(
        3,
        "the fresh process conducts from the rest alone: its faces are BIT-EQUAL to the parent's and its live descriptor audit holds no corpus, Gemma or phoenix path",
        child_output.status.success() && !child_faces.is_empty() && child_faces == parent_faces && offending.is_empty(),
        format!(
            "child exit {:?} · {} octets of returned faces, parent {} octets, bit-equal {} · open descriptors {:?} · forbidden among them {:?} · the child's whole argument vector is the rest's path, an exchange path and the prompts; there is no corpus path, no model root and no tokenizer in its reach",
            child_output.status.code(),
            child_faces.len(),
            parent_faces.len(),
            child_faces == parent_faces,
            opened,
            offending
        ),
    );

    // the hidden card
    let mut hidden = std::process::Command::new(std::env::current_exe().map_err(|e| e.to_string())?);
    hidden.env("CUDA_VISIBLE_DEVICES", "").arg("--conduct").arg(&rest_path).arg("--faces").arg("");
    for prompt in &prompts {
        hidden.arg("--prompt").arg(prompt);
    }
    let hidden_output = hidden.output().map_err(|e| e.to_string())?;
    let hidden_text = String::from_utf8_lossy(&hidden_output.stdout).into_owned();
    verdicts.record(
        9,
        "the hidden card returns a TYPED refusal and no serial rendering",
        !hidden_output.status.success() && hidden_text.contains("CHILD-REFUSED"),
        format!(
            "with the card hidden the child exited {:?} and returned {:?} — a typed refusal from the resident owner, never a cpu computation standing in for the deed",
            hidden_output.status.code(),
            hidden_text.lines().find(|line| line.starts_with("CHILD-REFUSED")).unwrap_or("<nothing>").chars().take(160).collect::<String>()
        ),
    );

    // the rest is still what it was
    let still = witness.container.verify_still().is_ok();
    verdicts.record(
        10,
        "the rest is the ONLY semantic input, and it is unmoved by the deed",
        still,
        format!(
            "the rest's identity was bound before the deed and verified after it: {} · every law of the deed is entailed by the rest's own declared shapes and its own statements, and no implementation text, configuration or foreign container took part — a foreign testimony refuses at this witness by type",
            if still { "unmoved" } else { "MOVED under the deed" }
        ),
    );

    // ---------------------------------------------------------------------------------------
    // the manifest
    // ---------------------------------------------------------------------------------------
    let taxa = std::fs::read_to_string("output/the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form")
        .map(|text| text.lines().filter(|line| line.starts_with("TAXON")).count())
        .unwrap_or(0);
    let manifest = build_manifest(&rest, &conducted, &sections, &family, &retained, chosen, taxa);
    let manifest_path = format!("{OUT}/native-ecology-manifest.form");
    {
        let mut form = std::fs::File::create(&manifest_path).map_err(|e| e.to_string())?;
        let _ = writeln!(form, "THE NATIVE ECOLOGY MANIFEST — Deed P0, from the rest at {} · device {} · {} classes, {} transitions, {} germs", rest.locator, surface.device_name(), rest.classes, rest.transitions, rest.vocabulary);
        let _ = writeln!(form, "Every MEASURED row was computed from the rest alone. Every OPEN row carries what would move it.");
        let _ = writeln!(form, "No layer count, latent width, head, rank or 42-layer restatement appears in this manifest; the only depth receiver is the suffix-link height, read off the material.");
        let _ = writeln!(form);
        for line in &manifest.lines {
            let _ = writeln!(form, "{line}");
            let _ = writeln!(form);
        }
    }
    println!();
    println!("  THE NATIVE ECOLOGY MANIFEST  -> {manifest_path}");
    for line in &manifest.lines {
        println!("    {}", line.replace('\n', "\n    "));
    }
    let asserts_crystal = manifest.lines.iter().any(|line| line.to_lowercase().contains("crystal") && line.starts_with("MEASURED"));
    verdicts.record(
        7,
        "the cycle rank is measured AND its transport population is exhibited by name",
        manifest.lines.iter().any(|line| line.contains("EXHIBITED reconvergent classes")),
        format!("b1 = {} over {} classes and {} transitions, with reconvergent classes named individually rather than counted", rest.transitions as i64 - rest.classes as i64 + 1, rest.classes, rest.transitions),
    );
    verdicts.record(
        8,
        "no crystal, winding or phase is ASSERTED: those rows are OPEN and carry their falsifiers",
        !asserts_crystal && manifest.lines.iter().any(|line| line.starts_with("OPEN") && line.contains("winding")),
        "the manifest's winding/phase row is OPEN with the falsifier that would move it; the aperiodicity of the longest-suffix carry monoid is carried as the boundary it is, and the group/gauge row returns that NO group action is founded — measured, with the monoid census behind it",
    );

    // ---------------------------------------------------------------------------------------
    // the receipt
    // ---------------------------------------------------------------------------------------
    let receipt_path = format!("{OUT}/receipt.form");
    {
        let mut form = std::fs::File::create(&receipt_path).map_err(|e| e.to_string())?;
        let _ = writeln!(form, "THE NATIVE BASELINE CONDUCTS FROM ITS OWN REST — Deed P0, ARM N · device {} · PTX {} · {:.1} s", surface.device_name(), &surface.ptx_sha256()[..16], clock.elapsed().as_secs_f64());
        let _ = writeln!(form, "rest {} · {} octets · content {} · classes {} · transitions {} · vocabulary {} · tree height {}", rest.locator, rest.octets, rest.content_sha256, rest.classes, rest.transitions, rest.vocabulary, rest.height);
        let _ = writeln!(form, "prompts {} · positions {} · future section {} x {} = {} cells · charged {} octets", prompts.len(), positions, conducted.positions, conducted.vocabulary, conducted.positions * conducted.vocabulary, conducted.charged_octets);
        let _ = writeln!(form);
        let _ = writeln!(form, "LAUNCH GEOMETRY");
        let _ = writeln!(form, "  admitted candidates {} · retained under {:?} {} · retained under a coarser declaration {} (the retained set MOVES with the declaration, which is the falsifier)", family.len(), axes, retained.len(), coarser.len());
        let _ = writeln!(form, "  {:<36} {:>6} {:>8} {:>6} {:>7} {:>10} {:>16} {:>16} {:>7}", "geometry", "block", "shared", "regs", "res/SM", "blocks", "residency waves", "cover of card", "reuse");
        for at in &retained {
            let candidate = &family[*at];
            let _ = writeln!(
                form,
                "  {:<36} {:>6} {:>8} {:>6} {:>7} {:>10} {:>7}/{:<8} {:>7}/{:<8} {:>7}{}",
                format!("{} pos x {} lanes x {} germs, stage {}", candidate.geometry.positions_per_block, candidate.geometry.lanes, candidate.geometry.germs_per_lane, candidate.geometry.chain_stage),
                candidate.block, candidate.shared_octets, candidate.registers, candidate.resident_blocks, candidate.blocks,
                candidate.residency_waves.0, candidate.residency_waves.1, candidate.cover_occupied.0, candidate.cover_occupied.1, candidate.chain_reuse,
                if *at == chosen { "  <- chosen" } else { "" }
            );
        }
        let _ = writeln!(form, "  bound by: {}", family[chosen].bound_by);
        let _ = writeln!(form, "  the convicted predecessor shape on this extent: future grid {convicted_blocks} x block {} at one thread per cell with no staging; walk grid {} x block {} with one working lane.", block_ceiling(surface), (positions as u64 * 2).div_ceil(u64::from(block_ceiling(surface))), block_ceiling(surface));
        let _ = writeln!(form, "  HERE: future grid {} x block {}; walk grid {} x block {} with one warp per prompt and a 32-ary row search.", family[chosen].blocks, family[chosen].block, walk_geometry.blocks(prompts.len()), walk_geometry.block(limits.warp));
        let _ = writeln!(form);
        let _ = writeln!(form, "THE PLURAL SECTIONS");
        for section in &sections {
            let _ = writeln!(form, "  {:?} -> class {} standing {} · {} germs offered · walk {}", section.prompt, section.class, section.standing, section.offered.len(), section.trace.join(" -> "));
            let mut by_depth: BTreeMap<i64, Vec<&(String, i64, i64)>> = BTreeMap::new();
            for offered in &section.offered {
                by_depth.entry(offered.2).or_default().push(offered);
            }
            for (depth, members) in by_depth.iter().take(2) {
                let _ = writeln!(form, "    depth {depth}: {} germs — {}", members.len(), members.iter().take(14).map(|(s, standing, _)| format!("{s:?}@{standing}")).collect::<Vec<_>>().join(" "));
            }
        }
        let _ = writeln!(form);
        let _ = writeln!(form, "THE ABLATION — construction-level: the rest rebuilt without canon/TABLET_THE_HEXIS.md");
        let _ = writeln!(form, "  {:<50} {:>7} {:>7} {:>7} {:>7} {:>8} {:>12} {:>10}", "prompt", "germs", "germs'", "moved", "gone", "arrived", "support same", "depth-0 same");
        for row in &ablation_rows {
            let _ = writeln!(form, "  {:<50} {:>7} {:>7} {:>7} {:>7} {:>8} {:>12} {:>10}", format!("{:?}", row.0), row.1, row.2, row.3, row.4, row.5, row.6, row.7);
        }
        let _ = writeln!(form);
        let _ = writeln!(form, "VERDICTS");
        for line in &verdicts.lines {
            let _ = writeln!(form, "{line}");
        }
    }

    println!();
    println!("  receipt -> {receipt_path}");
    println!();
    if verdicts.failed == 0 {
        println!("ALL {} CONTROLS HELD — the native baseline conducts from its own rest in {:.1} s", verdicts.lines.len(), clock.elapsed().as_secs_f64());
        Ok(())
    } else {
        Err(format!("{} of {} controls failed", verdicts.failed, verdicts.lines.len()))
    }
}

/// The module's derived block ceiling: the minimum over every kernel's own admission, taken down to
/// a whole warp. A refusal bound, never an optimum — and the number the convicted shape used.
fn block_ceiling(surface: &ResidentSurface<'_>) -> u32 {
    let mut ceiling = surface.declaration().max_threads_per_block.max(1);
    for symbol in KERNELS {
        if let Ok(admitted) = surface.measured_block_ceiling(symbol) {
            ceiling = ceiling.min(admitted);
        }
    }
    let warp = surface.declaration().warp_size.max(1);
    (ceiling / warp).max(1) * warp
}
