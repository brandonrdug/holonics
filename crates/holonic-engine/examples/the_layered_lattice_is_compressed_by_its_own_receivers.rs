//! **The layered lattice a transformer forbids itself to leave, put through the compression organ —
//! and what comes back is the exact object superposition is the lossy analogue of.**
//!
//! ```text
//! cargo run --release --example the_layered_lattice_is_compressed_by_its_own_receivers
//! ```
//!
//! **Station five of
//! [`archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md`](../../../archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md).**
//!
//! # The lattice, stated exactly
//!
//! Sites `(i, ℓ)` — position and depth. Admitted edges: attention `(j,ℓ) → (i,ℓ+1)` iff `j ≤ i`;
//! residual and MLP `(i,ℓ) → (i,ℓ+1)`. Their transitive closure is
//!
//! ```text
//!     (j,ℓ) ⇝ (i,ℓ')   ⟺   j ≤ i  ∧  ℓ ≤ ℓ'
//! ```
//!
//! — the product order on a grid, a discrete light cone monotone on both axes. **A chain of `k`
//! dependencies in the material's causal order costs `k` layers**, because there is no same-depth
//! lateral edge; and this repository has measured that constraint on its own material, at
//! `derivation_atlas.rs:617-620`, where a one-hop-only orientation made theorem chaining impossible
//! to form at all.
//!
//! # What is asked of it, and why the answer is not available inside the network
//!
//! `receiver_exact_compression` computes the **coarsest** partition for which conduct is determined
//! by the block — the causal-state construction, the Nerode congruence of a declared receiver family
//! — and returns the **collapsed population**: every pair the one-shot reading merged that the
//! lattice separates, each carrying the **shortest word that separates it**. The longest such word
//! is the memory order: how far the reading had to look.
//!
//! Read on this lattice, an input word is a **descent through layers**, so the memory order is
//! literally *how many layers of depth are required before two sites become distinguishable*.
//! That question has a name in the industry vocabulary and no exact answer there.
//!
//! # The receivers are declared BEFORE the run, and they are faces of the material
//!
//! `CLAUDE.md`'s authored-partition rule governs: *"which declared input, if varied across two
//! members of one returned block, would move them apart? If the answer is the one I set equal for
//! both, the class is authored."* Every receiver below is a **codec face of the octets at the
//! site** — its dense identity, its first octet, its octet count, its adjacent-bit-transition
//! winding. None is a coordinate of the lattice, none is a field this driver assigns per site, and
//! varying the corpus moves every block. The anti-vacuity arm at the end varies exactly that and
//! exhibits the movement.
//!
//! # The surface
//!
//! **The card, and it is already the law.** `receiver_exact_compression::compress_on_device` enacts
//! the same quotient through the resident refinement shell, with `quotient_on_cpu` standing beside
//! it as the exact reference rather than as the implementation — `cuda_refine.rs` quoting Brandon,
//! 2026-08-10: *"the card's integration is so fucking important and you can't just keep punting
//! it… It's GPU first."* Both carriers run here and their partitions are asserted equal, which is a
//! two-frame check rather than one computation trusted.
//!
//! **And the aperture is measured rather than assumed.** The refinement scales; the *exhibition* of
//! the collapsed population does not, because it walks every pair inside a one-shot block. The run
//! reports where that boundary actually sits, on both carriers, instead of choosing a size quietly.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::cuda_refine::{CudaRefineExecutor, quotient_on_cpu};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression, ReceiverId, compress,
    compress_on_device,
};

/// The declared depth of the lattice. A caller declaration about how deep a stack it is asking
/// about, exhibited in the return.
const LAYERS: usize = 8;

/// How many attention offsets the run admits, past the residual. The excluded population is
/// **reported**, never dropped: `CLAUDE.md`'s no-silent-caps rule.
const OFFSET_APERTURE: usize = 6;

/// The four declared receivers, named before anything is read.
const RECEIVER_IDENTITY: ReceiverId = ReceiverId(0);
const RECEIVER_FIRST_OCTET: ReceiverId = ReceiverId(1);
const RECEIVER_OCTET_COUNT: ReceiverId = ReceiverId(2);
const RECEIVER_OCTET_WINDING: ReceiverId = ReceiverId(3);

/// The corpus files this run reads. The declared corpus of `CLAUDE.md` §0e includes this codebase;
/// these are its own governing documents.
const CORPUS: [&str; 2] = [
    "docs/canon/THE_HOLOBROCHOS_SPINE.md",
    "docs/canon/THE_INFORMATION_ENGINE.md",
];

/// One position of the material: its octets and the four faces read off them.
#[derive(Clone, Debug)]
struct Position {
    surface: String,
    identity: u64,
    first_octet: u64,
    octet_count: u64,
    octet_winding: u64,
}

/// §III's winding: adjacent bit transitions across the octet stream. The tree's own reading, and a
/// winding rather than a magnitude, so it crosses a frame boundary.
fn octet_winding(octets: &[u8]) -> u64 {
    let mut winding = 0u64;
    let mut previous: Option<bool> = None;
    for octet in octets {
        for bit in (0..8).rev() {
            let here = octet >> bit & 1 == 1;
            if let Some(there) = previous
                && here != there
            {
                winding += 1;
            }
            previous = Some(here);
        }
    }
    winding
}

/// **The lattice as an observed system.** Nothing about a transformer is imported except its own
/// admitted transports; the material is the corpus.
struct LayeredLattice {
    positions: Vec<Position>,
    layers: usize,
    /// The attention offsets this run admits, derived from the material's own recurrence gaps.
    offsets: Vec<usize>,
}

impl LayeredLattice {
    fn site(&self, item: ItemId) -> (usize, usize) {
        let at = item.0 as usize;
        (at % self.positions.len(), at / self.positions.len())
    }

    fn item_of(&self, position: usize, layer: usize) -> ItemId {
        ItemId((layer * self.positions.len() + position) as u64)
    }
}

impl ObservedSystem for LayeredLattice {
    fn items(&self) -> Vec<ItemId> {
        (0..(self.positions.len() * self.layers) as u64)
            .map(ItemId)
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![
            RECEIVER_IDENTITY,
            RECEIVER_FIRST_OCTET,
            RECEIVER_OCTET_COUNT,
            RECEIVER_OCTET_WINDING,
        ]
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.offsets.len() as u64).map(InputId).collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let (position, _) = self.site(item);
        let here = &self.positions[position];
        Observation(match receiver {
            RECEIVER_IDENTITY => here.identity,
            RECEIVER_FIRST_OCTET => here.first_octet,
            RECEIVER_OCTET_COUNT => here.octet_count,
            RECEIVER_OCTET_WINDING => here.octet_winding,
            _ => 0,
        })
    }

    /// **The admitted transport.** One layer down, and forward by the declared offset — the causal
    /// mask read in the direction current actually moves. `None` is a terminus: the bottom of the
    /// stack, or past the end of the sequence. A terminus is a distinction, not a gap.
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let (position, layer) = self.site(item);
        if layer + 1 >= self.layers {
            return None;
        }
        let offset = self.offsets[input.0 as usize];
        let target = position.checked_add(offset)?;
        if target >= self.positions.len() {
            return None;
        }
        Some(self.item_of(target, layer + 1))
    }
}

/// Read the corpus into positions, with dense identities assigned canonically over the sorted
/// distinct surfaces — exact and collision-free, never a hash.
fn read_corpus(limit: usize) -> Result<Vec<Position>, String> {
    let mut surfaces: Vec<String> = Vec::new();
    for path in CORPUS {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        for word in text.split_whitespace() {
            surfaces.push(word.to_owned());
            if surfaces.len() >= limit {
                break;
            }
        }
        if surfaces.len() >= limit {
            break;
        }
    }
    if surfaces.is_empty() {
        return Err("the corpus is empty".into());
    }
    let distinct: BTreeSet<&str> = surfaces.iter().map(String::as_str).collect();
    let identities: BTreeMap<&str, u64> = distinct
        .iter()
        .enumerate()
        .map(|(at, surface)| (*surface, at as u64 + 1))
        .collect();
    Ok(surfaces
        .iter()
        .map(|surface| {
            let octets = surface.as_bytes();
            Position {
                identity: identities[surface.as_str()],
                first_octet: u64::from(octets[0]),
                octet_count: octets.len() as u64,
                octet_winding: octet_winding(octets),
                surface: surface.clone(),
            }
        })
        .collect())
}

/// **The offsets, derived from the material.** The distinct gaps at which a surface recurs — the
/// transport distances the corpus itself exhibits — with the residual (`0`) always admitted because
/// it is a structural edge and not a recurrence.
fn offsets_from(positions: &[Position], aperture: usize) -> (Vec<usize>, usize) {
    let mut last: BTreeMap<u64, usize> = BTreeMap::new();
    let mut gaps: BTreeMap<usize, usize> = BTreeMap::new();
    for (at, position) in positions.iter().enumerate() {
        if let Some(previous) = last.insert(position.identity, at) {
            *gaps.entry(at - previous).or_insert(0) += 1;
        }
    }
    let mut ranked: Vec<(usize, usize)> = gaps.into_iter().collect();
    ranked.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
    let complete = ranked.len();
    let mut admitted: Vec<usize> = vec![0];
    for (gap, _) in ranked.into_iter().take(aperture.saturating_sub(1)) {
        admitted.push(gap);
    }
    admitted.sort_unstable();
    admitted.dedup();
    (admitted, complete)
}

fn report(label: &str, reading: &ReceiverExactCompression, lattice: &LayeredLattice) {
    println!("  {label}");
    println!(
        "    one-shot blocks {} · conduct blocks {} · refinement rounds {}",
        reading.one_shot.len(),
        reading.conduct.len(),
        reading.rounds
    );
    println!(
        "    collapsed pairs {} · memory order {:?} · exact {}",
        reading.collapsed.len(),
        reading.memory_order(),
        reading.is_exact()
    );
    let by_terminus = reading
        .collapsed
        .iter()
        .filter(|pair| pair.separated_by_terminus)
        .count();
    println!(
        "    separated by a terminus {} · by a receiver {}",
        by_terminus,
        reading.collapsed.len() - by_terminus
    );
    // THE TWO SPECIES MUST NOT SHARE A CENSUS, and the first run of this driver showed why: the
    // headline memory order came back as exactly LAYERS - 1, which is the declared depth and not a
    // fact about the corpus. A pair of sites carrying the SAME material at two depths is separated
    // only because one reaches the bottom of the stack sooner, and its word length is forced to
    // `LAYERS - 1 - max(layer)` by the declaration. That is `CLAUDE.md`'s tautology rule: a receipt
    // that could not have come out otherwise carries no evidence. The receiver-separated half is
    // where the material speaks.
    let mut terminus_depths: BTreeMap<usize, usize> = BTreeMap::new();
    let mut receiver_depths: BTreeMap<usize, usize> = BTreeMap::new();
    for pair in &reading.collapsed {
        let census = if pair.separated_by_terminus {
            &mut terminus_depths
        } else {
            &mut receiver_depths
        };
        *census.entry(pair.distinguishing_word.len()).or_insert(0) += 1;
    }
    print!("    word lengths, TERMINUS-separated (a depth artifact):");
    for (length, count) in &terminus_depths {
        print!("  {length}→{count}");
    }
    println!();
    print!("    word lengths, RECEIVER-separated (about the material):");
    for (length, count) in &receiver_depths {
        print!("  {length}→{count}");
    }
    println!();
    println!(
        "    the material's memory order is {:?}; the {:?} above is the declared depth minus one",
        receiver_depths.keys().max(),
        reading.memory_order()
    );
    println!("    two of each species, exhibited:");
    let mut shown_terminus = 0usize;
    let mut shown_receiver = 0usize;
    for pair in &reading.collapsed {
        let quota = if pair.separated_by_terminus {
            &mut shown_terminus
        } else {
            &mut shown_receiver
        };
        if *quota >= 2 {
            continue;
        }
        *quota += 1;
        let (left_position, left_layer) = lattice.site(pair.left);
        let (right_position, right_layer) = lattice.site(pair.right);
        println!(
            "      ({:?} @ layer {left_layer}) vs ({:?} @ layer {right_layer}) — word of {} layer(s){}",
            lattice.positions[left_position].surface,
            lattice.positions[right_position].surface,
            pair.distinguishing_word.len(),
            match &pair.witness {
                Some((receiver, here, there)) => format!(
                    ", receiver {} saw {} against {}",
                    receiver.0, here.0, there.0
                ),
                None => ", separated by a terminus".to_string(),
            }
        );
        if shown_terminus >= 2 && shown_receiver >= 2 {
            break;
        }
    }

    // AND THE OBJECT AT THE END: what the lattice genuinely cannot tell apart.
    let survivors: Vec<&BTreeSet<ItemId>> = reading
        .conduct
        .blocks
        .iter()
        .filter(|block| block.len() > 1)
        .collect();
    let merged: usize = survivors.iter().map(|block| block.len()).sum();
    println!(
        "    conduct blocks with more than one member: {} holding {} sites — the population the",
        survivors.len(),
        merged
    );
    println!("    WHOLE lattice cannot separate, which is the object rather than any count above:");
    // WHERE they sit is the finding. Measured, not asserted.
    let mut by_layer: BTreeMap<usize, usize> = BTreeMap::new();
    for block in &survivors {
        for item in *block {
            *by_layer.entry(lattice.site(*item).1).or_insert(0) += 1;
        }
    }
    print!("    their layers:");
    for (layer, count) in &by_layer {
        print!("  {layer}→{count}");
    }
    println!();
    if by_layer.len() == 1 && by_layer.contains_key(&(lattice.layers - 1)) {
        println!(
            "    >> EVERY ONE IS AT THE TERMINAL LAYER. Depth is what separates, and at layer {} there",
            lattice.layers - 1
        );
        println!(
            "    >> is none left: a site with no successor has no future to be distinguished by,"
        );
        println!("    >> so the last layer's quotient is exactly the one-shot reading's own. The");
        println!("    >> lattice ALONE cannot tell two occurrences of one surface apart there.");
    }
    for block in survivors.iter().take(3) {
        let named: Vec<String> = block
            .iter()
            .map(|item| {
                let (position, layer) = lattice.site(*item);
                format!("{:?}@{layer}", lattice.positions[position].surface)
            })
            .collect();
        println!("      {{ {} }}", named.join(", "));
    }
}

#[allow(clippy::too_many_lines)]
fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    println!("{}", "=".repeat(100));
    println!("THE LAYERED LATTICE IS COMPRESSED BY ITS OWN RECEIVERS");
    println!("{}", "=".repeat(100));
    println!();
    println!("  Sites (i, l). Admitted edges: attention (j,l) -> (i,l+1) iff j <= i; residual and");
    println!("  MLP (i,l) -> (i,l+1). Their closure is the PRODUCT ORDER on a grid:");
    println!();
    println!("      (j,l) ~> (i,l')   <=>   j <= i  AND  l <= l'");
    println!();
    println!(
        "  a discrete light cone monotone on both axes, with NO same-depth lateral edge. So a"
    );
    println!(
        "  chain of k dependencies in the material's causal order costs k LAYERS, and an input"
    );
    println!("  word in the compression below is literally a descent through depth.");

    // ---------------------------------------------------------------- the material
    let positions = read_corpus(320)?;
    let (offsets, complete_gaps) = offsets_from(&positions, OFFSET_APERTURE);
    let lattice = LayeredLattice {
        positions,
        layers: LAYERS,
        offsets: offsets.clone(),
    };
    let distinct: BTreeSet<u64> = lattice
        .positions
        .iter()
        .map(|position| position.identity)
        .collect();

    println!();
    println!("{}", "=".repeat(100));
    println!("THE MATERIAL, AND THE APERTURE IT DECLARES");
    println!("{}", "=".repeat(100));
    println!();
    println!("  corpus: {}", CORPUS.join(", "));
    println!(
        "  {} positions, {} distinct surfaces, {} layers -> {} sites",
        lattice.positions.len(),
        distinct.len(),
        lattice.layers,
        lattice.positions.len() * lattice.layers
    );
    println!();
    println!(
        "  THE OFFSETS ARE DERIVED, not chosen: the distinct gaps at which a surface recurs in"
    );
    println!("  this corpus, ranked by how often they occur, plus the residual 0 which is a");
    println!("  structural edge rather than a recurrence.");
    println!("    admitted: {offsets:?}");
    println!(
        "    the aperture excluded {} of {complete_gaps} distinct recurrence gaps, reported rather than dropped",
        complete_gaps.saturating_sub(offsets.len() - 1)
    );
    println!();
    println!("  THE RECEIVERS, DECLARED BEFORE THE RUN. Each is a codec face of the octets AT the");
    println!("  site; none is a coordinate of the lattice and none is assigned per site by this");
    println!("  driver:");
    println!(
        "    {}  the dense identity, canonical over the sorted distinct surfaces",
        RECEIVER_IDENTITY.0
    );
    println!("    {}  the first octet", RECEIVER_FIRST_OCTET.0);
    println!("    {}  the octet count", RECEIVER_OCTET_COUNT.0);
    println!(
        "    {}  the adjacent-bit-transition winding of the octet stream",
        RECEIVER_OCTET_WINDING.0
    );

    // ---------------------------------------------------------------- the two carriers
    println!();
    println!("{}", "=".repeat(100));
    println!("THE COMPRESSION, ON BOTH CARRIERS");
    println!("{}", "=".repeat(100));
    println!();
    let serial = compress(&lattice);
    report("the serial path", &serial, &lattice);

    println!();
    let mut executor = match CudaRefineExecutor::new() {
        Ok(executor) => executor,
        Err(error) => {
            return Err(format!(
                "the card refused and this station is a card deed: {error}"
            ));
        }
    };
    println!("  the card: {}", executor.device_name());
    println!(
        "    block {} threads, warp {}",
        executor.block_threads(),
        executor.warp_size()
    );
    let launches_before = executor.launches();
    let resident = compress_on_device(&lattice, &mut executor)
        .map_err(|error| format!("the device refinement refused: {error}"))?;
    println!(
        "    {} launches for this deed",
        executor.launches() - launches_before
    );
    println!();
    report("the card", &resident, &lattice);

    println!();
    println!(
        "  THE TWO-FRAME CHECK. The partitions must agree exactly; the device claims identities"
    );
    println!(
        "  in whatever order its lanes reach them, so NUMBERING is a realization coordinate and"
    );
    println!("  is not compared.");
    let agree = serial.one_shot == resident.one_shot && serial.conduct == resident.conduct;
    println!("    one-shot and conduct partitions agree: {agree}");
    if !agree {
        return Err(
            "the two carriers disagree; one of them is wrong and neither is trusted".into(),
        );
    }
    println!(
        "    collapsed populations agree: {}",
        serial.collapsed == resident.collapsed
    );

    // ---------------------------------------------------------------- where the aperture is
    println!();
    println!("{}", "=".repeat(100));
    println!("WHERE THE APERTURE ACTUALLY SITS  --  measured, not assumed");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  The REFINEMENT scales: it is one quotient per receiver and one per input per round,"
    );
    println!(
        "  and the card's table is sized from the material with no load factor. The EXHIBITION"
    );
    println!(
        "  does not: it walks every pair inside a one-shot block, which is quadratic in block"
    );
    println!("  size. So the boundary is not where it looks.");
    println!();
    println!(
        "  {:>10} {:>10} {:>14} {:>16} {:>14}",
        "positions", "sites", "one-shot blocks", "pairs in blocks", "collapsed"
    );
    for limit in [80usize, 160, 320, 640] {
        let positions = read_corpus(limit)?;
        let (offsets, _) = offsets_from(&positions, OFFSET_APERTURE);
        let smaller = LayeredLattice {
            positions,
            layers: LAYERS,
            offsets,
        };
        let reading = compress(&smaller);
        let pairs: usize = reading
            .one_shot
            .blocks
            .iter()
            .map(|block| block.len() * block.len().saturating_sub(1) / 2)
            .sum();
        println!(
            "  {:>10} {:>10} {:>14} {:>16} {:>14}",
            smaller.positions.len(),
            smaller.positions.len() * smaller.layers,
            reading.one_shot.len(),
            pairs,
            reading.collapsed.len()
        );
    }
    println!();
    println!("  THE REFINEMENT ALONE, past where the exhibition reaches. The card's quotient is");
    println!("  driven directly and cross-checked against the serial reference at each step, with");
    println!("  no collapsed population exhibited:");
    println!();
    println!(
        "  {:>10} {:>10} {:>12} {:>16} {:>12}",
        "positions", "sites", "receivers", "conduct blocks", "agree"
    );
    for limit in [640usize, 2560, 10_240] {
        let positions = read_corpus(limit)?;
        let (offsets, _) = offsets_from(&positions, OFFSET_APERTURE);
        let wide = LayeredLattice {
            positions,
            layers: LAYERS,
            offsets,
        };
        let items = wide.items();
        let mut classes = vec![1u32; items.len()];
        let mut reference = vec![1u32; items.len()];
        let mut agree = true;
        for receiver in wide.receivers() {
            let keys: Vec<u64> = items
                .iter()
                .map(|item| wide.observation(*item, receiver).0)
                .collect();
            let device = executor
                .quotient_on_device(&classes, &keys)
                .map_err(|error| format!("device quotient: {error}"))?;
            let serial_step = quotient_on_cpu(&reference, &keys);
            agree &= device.same_partition_as(&serial_step);
            classes = device.cell_class;
            reference = serial_step.cell_class;
        }
        let locations: BTreeMap<ItemId, usize> = items
            .iter()
            .copied()
            .enumerate()
            .map(|(at, item)| (item, at))
            .collect();
        loop {
            let before: BTreeSet<u32> = classes.iter().copied().collect();
            for input in wide.inputs() {
                let keys: Vec<u64> = items
                    .iter()
                    .map(|item| {
                        wide.successor(*item, input)
                            .and_then(|successor| locations.get(&successor).copied())
                            .and_then(|at| classes.get(at).copied())
                            .map_or(0, u64::from)
                    })
                    .collect();
                let device = executor
                    .quotient_on_device(&classes, &keys)
                    .map_err(|error| format!("device quotient: {error}"))?;
                let serial_step = quotient_on_cpu(&reference, &keys);
                agree &= device.same_partition_as(&serial_step);
                classes = device.cell_class;
                reference = serial_step.cell_class;
            }
            let after: BTreeSet<u32> = classes.iter().copied().collect();
            if after.len() == before.len() {
                break;
            }
        }
        let blocks: BTreeSet<u32> = classes.iter().copied().collect();
        println!(
            "  {:>10} {:>10} {:>12} {:>16} {:>12}",
            wide.positions.len(),
            wide.positions.len() * wide.layers,
            wide.receivers().len(),
            blocks.len(),
            agree
        );
        if !agree {
            return Err("the carriers disagreed at scale".into());
        }
    }

    // ---------------------------------------------------------------- the anti-vacuity arm
    println!();
    println!("{}", "=".repeat(100));
    println!("THE AUTHORED-PARTITION FALSIFIER");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  \"Which declared input, if varied across two members of one returned block, would move"
    );
    println!(
        "  them apart? If the answer is the one I set equal for both, the class is authored.\""
    );
    println!();
    println!(
        "  The answer here is THE MATERIAL AT THE POSITION, and the corpus owns it. Varying the"
    );
    println!(
        "  corpus must move the partition, or the receivers were reading the lattice rather than"
    );
    println!("  reading the material. Two disjoint slices of the same corpus, same lattice shape:");
    println!();
    let whole = read_corpus(640)?;
    println!(
        "  {:<14} {:>12} {:>16} {:>14} {:>14}",
        "slice", "distinct", "one-shot blocks", "conduct blocks", "collapsed"
    );
    let mut signatures: Vec<Vec<usize>> = Vec::new();
    for (name, slice) in [("first 320", &whole[..320]), ("last 320", &whole[320..])] {
        let (offsets, _) = offsets_from(slice, OFFSET_APERTURE);
        let piece = LayeredLattice {
            positions: slice.to_vec(),
            layers: LAYERS,
            offsets,
        };
        let reading = compress(&piece);
        let distinct: BTreeSet<u64> = piece
            .positions
            .iter()
            .map(|position| position.identity)
            .collect();
        println!(
            "  {:<14} {:>12} {:>16} {:>14} {:>14}",
            name,
            distinct.len(),
            reading.one_shot.len(),
            reading.conduct.len(),
            reading.collapsed.len()
        );
        signatures.push(vec![
            reading.one_shot.len(),
            reading.conduct.len(),
            reading.collapsed.len(),
            reading.memory_order().unwrap_or(0),
        ]);
    }
    let moved = signatures[0] != signatures[1];
    println!();
    println!("  the partition moved with the material: {moved}");
    if !moved {
        return Err(
            "the partition did not move with the material; the receivers read the lattice, not the corpus"
                .into(),
        );
    }

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!("  It does not claim to have compressed a transformer. It compresses THE LATTICE a");
    println!(
        "  transformer's admitted transports define, over a declared receiver family and real"
    );
    println!("  material, and returns the collapsed population that lattice forces. No weight is");
    println!("  read here; station six is where a real head enters.");
    println!();
    println!(
        "  The memory order is the memory order of the PAIR (material, receiver family), never"
    );
    println!(
        "  of the material. A finer family un-collapses pairs this one merged, and the figure"
    );
    println!("  above speaks about the receivers as much as about the corpus.");
    println!();
    println!(
        "  Nothing here is a compression ratio. The invariance is additive and a ratio is the"
    );
    println!(
        "  frame-dependent quantity; what is returned is the POPULATION, each pair carrying the"
    );
    println!("  shortest word that separates it.");
    Ok(())
}
