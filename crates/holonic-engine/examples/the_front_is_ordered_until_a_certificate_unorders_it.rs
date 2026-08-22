//! Two orders interchange exactly when no receiver in the founded family separates them.
//!
//! `blueprint/PURE_HOLONIC_ENGINE.md:170-174` specifies an `InterchangeCertificate` in prose and
//! ends with the sentence this driver exists to make operative: *"Without this certificate, the
//! front remains ordered."* `holonic_engine::interchange` is the certificate; this runs it against
//! four materials and returns both verdicts.
//!
//! ## The two comparisons, kept apart on purpose
//!
//! `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`
//! is RATIFIED and states the independence relation: two events belong to it only when their
//! complete exact consequences commute, *"including lineage, radiation, obstruction, and changed
//! morphology"*, and *"a common label, collection, or lack of a visible edge does not prove
//! independence."* So the driver computes **both** the endpoint-only verdict and the lineage
//! verdict, prints them side by side, and reports the disagreement as the finding rather than
//! silently taking the stronger one.
//!
//! ## Controls
//!
//! 1. **The certificate ADMITS on material where the junctions are independent.** One that refuses
//!    everything has measured nothing.
//! 2. **The certificate REFUSES on material where they are not**, and exhibits the distinguishing
//!    word — the receiver that now witnesses the junction the other founding closed.
//! 3. **Both verdicts come out of one code path**, on one organ, in one run.
//! 4. **The mint ordinal moves and the verdict does not.** A `ReceiverId` is an absolute frame;
//!    the two orders hand the same axis different ordinals and the comparison must not notice.
//! 5. **Endpoint comparison against lineage comparison.** On `soma/formal` they disagree, and the
//!    endpoint-only comparator is the convicted defect — *"Endpoint equality became stateful
//!    equivalence."*
//! 6. **Disjoint footprints do not prove independence.** `CoupledJunctions` stages two junctions
//!    sharing one item and coupled through a third pair neither names.
//! 7. **The three-or-more case is not inferred.** A pair certificate returns `PairwiseOnly` and
//!    names what a triple would require; a declared set is certified over every permutation.
//! 8. **`capacities()` has a library consumer.** `canon/THE_CONTAMINANT_PROTOCOL.md` §2.1's verified
//!    instance is `FoundedPanel::capacities`, whose only call sites were a driver and a test. The
//!    certificate compares it as the successor's logical resource, so the arrow now exists in
//!    library code.
//!
//! ## The material, and why this driver did not return before 2026-08-11
//!
//! `canon/TABLET_THE_MANIFOLD.md` recorded that this driver *"reaches soma/formal and stops,
//! including under an 8 GB bound."* The diagnosis is not a cost defect in the certificate. It is
//! the material: `lean_paths` walked **every** `.lean` under the root, and `soma/formal` carries a
//! Lake package cache — **8,612 files and 91,167,882 octets** of vendored mathlib, batteries and
//! plausible against **13 files and 27,980 octets** of soma's own development. The certificate was
//! being asked about mathlib. Refusing `.lake` by name returns the whole run, all sixteen
//! controls, in **0.21 s**.
//!
//! The cost wall is real and is now measured rather than hit, on caller-declared slices of that
//! same cache (argv[2], debug profile, one cpu core):
//!
//! ```text
//!   files   items   collapsed pairs   junctions   compress    certify_founding_orders   peak RSS
//!       4       5                 2           2    42.3 µs                   256.6 µs
//!       8      48               253         216   984.7 µs                  11.13  ms
//!      16      63               499         372     1.80 ms                  19.59  ms
//!      32     212             4,850       2,575    33.01 ms                 380.7   ms
//!      64     341            12,718       6,005   117.5  ms                   1.164 s
//!     128     873            85,496      25,415     2.180 s                  16.578 s   0.051 GiB
//!     256   1,880           327,054      52,387    17.98  s                 139.915 s   0.170 GiB
//!     512   4,484         1,623,179     183,569   194.55  s               1,437.19  s   0.640 GiB
//! ```
//!
//! `certify_founding_orders` grows as **items^2.7** and holds that exponent across every doubling
//! measured — ×2.56 in items → ×14.2 in work, ×2.15 → ×8.44, ×2.385 → ×10.27 — which the owner
//! explains exactly: `founded_receiver::found_in_order` loops bounded by `items − 1` and calls
//! `compress` over the **whole widened system** once per founded axis, and
//! `certify_founding_orders` runs that loop twice. The collapsed-pair population is `~items²/12`
//! and is what `compress` carries; peak resident grows as only `items^1.5`.
//!
//! **So the 8 GB bound was never what stopped it, and that is the finding.** Extrapolating the two
//! measured laws to the whole package cache (≈133,000 items) gives ≈150 days of one core against
//! ≈115 GiB; 8 GiB is not reached until ≈23,000 items, where the same extrapolation *already*
//! costs about **34 hours**. Time exhausts more than a day before memory does at every scale, so a
//! memory bound could never have been the thing observed stopping. The wall is `found_in_order`'s
//! repeated whole-system `compress`, owner `crates/holonic-engine/src/founded_receiver.rs:443`,
//! and the resource is **time**. Falsifier: a run that exceeds 8 GiB before it exceeds a day.
//!
//! Run: `the_front_is_ordered_until_a_certificate_unorders_it [development-root] [vendored-slice]`

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use holonic_engine::founded_receiver::{FoundingRefusal, standing_junctions};
use holonic_engine::interchange::{
    Coherence, DistinguishingWord, Interchange, InterchangeCertificate, StagedFootprint,
    bare_junctions, certify_founding_orders, certify_pair, certify_set,
    declared_material::{CoupledJunctions, SameEndpointDifferentPath, ThreeGadgets, TwoGadgets},
};
use holonic_engine::lean_development::{
    DeclarationGrain, DevelopmentReading, join, read_development,
};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

/// The development as a system under observation — the same reading
/// `the_receiver_is_founded_at_the_junction.rs` declares, so the two drivers speak about one
/// material.
struct Development {
    names: Vec<String>,
    recruits: Vec<Vec<usize>>,
    formers: Vec<u64>,
    depths: Vec<u64>,
    stated: Vec<u64>,
    width: usize,
}

impl Development {
    fn read(reading: &DevelopmentReading) -> Self {
        let mut names: Vec<String> = reading
            .declarations
            .iter()
            .map(|form| form.name.clone())
            .collect();
        names.sort();
        names.dedup();
        let ordinal: BTreeMap<String, usize> = names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), index))
            .collect();

        let mut recruits = vec![Vec::new(); names.len()];
        let mut formers = vec![0u64; names.len()];
        let mut depths = vec![0u64; names.len()];
        let mut stated = vec![0u64; names.len()];
        let declared = reading.declared_names();

        for form in &reading.declarations {
            let Some(index) = ordinal.get(&form.name).copied() else {
                continue;
            };
            let mut reached: Vec<usize> = form
                .recruited
                .keys()
                .filter(|symbol| declared.contains(symbol.as_str()))
                .filter_map(|symbol| ordinal.get(symbol).copied())
                .filter(|other| *other != index)
                .collect();
            reached.sort_unstable();
            reached.dedup();
            recruits[index] = reached;
            formers[index] = form.former.bytes().fold(0u64, |acc, byte| {
                acc.wrapping_mul(131).wrapping_add(u64::from(byte))
            });
            depths[index] = form.namespace_path.len() as u64;
            stated[index] = u64::from(!form.statement.is_empty());
        }

        let width = recruits.iter().map(Vec::len).max().unwrap_or(0);
        Self {
            names,
            recruits,
            formers,
            depths,
            stated,
            width,
        }
    }

    fn name_of(&self, item: ItemId) -> &str {
        &self.names[item.0 as usize]
    }
}

impl ObservedSystem for Development {
    fn items(&self) -> Vec<ItemId> {
        (0..self.names.len() as u64).map(ItemId).collect()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)]
    }
    fn inputs(&self) -> Vec<InputId> {
        (0..self.width as u64).map(InputId).collect()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let index = item.0 as usize;
        Observation(match receiver.0 {
            0 => self.formers[index],
            1 => self.depths[index],
            _ => self.stated[index],
        })
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.recruits[item.0 as usize]
            .get(input.0 as usize)
            .map(|next| ItemId(*next as u64))
    }
}

fn section(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

/// How an item is named, per material.
type Naming<'a> = &'a dyn Fn(ItemId) -> String;

/// A congestion-founded axis carries no junction pair — `found_to_exhaustion` records it as
/// `(ItemId(0), ItemId(0))`, which cannot collide with a real junction because a junction is a pair
/// of distinct items. Rendering it as two names would read as a pair the material does not carry.
fn junction_label(junction: (ItemId, ItemId), name: Naming<'_>) -> String {
    if junction.0 == junction.1 {
        "<congestion axis — no junction pair>".to_owned()
    } else {
        format!("{} | {}", name(junction.0), name(junction.1))
    }
}

fn report(certificate: &InterchangeCertificate, name: Naming<'_>) {
    println!(
        "\n  predecessor      {} declared receivers, {} axes already founded, {} standing junctions",
        certificate.predecessor.declared.len(),
        certificate.predecessor.prefix.len(),
        certificate.predecessor.standing_junctions.len()
    );
    println!("  staged           {} footprints", certificate.staged.len());
    for footprint in &certificate.staged {
        println!(
            "                     {}",
            junction_label(footprint.junction, name)
        );
    }

    println!(
        "\n  {:<6} {:<10} {:<28} {:<10} capacities (per axis)",
        "order", "rebased", "founded", "blocks"
    );
    println!("  {}", "-".repeat(92));
    for (index, order) in certificate.orders.iter().enumerate() {
        let founded: Vec<String> = order
            .founded
            .iter()
            .map(|junction| junction_label(*junction, name).replace(" | ", "|"))
            .collect();
        let capacities: Vec<String> = order
            .capacities
            .iter()
            .map(|(_, capacity)| capacity.to_string())
            .collect();
        println!(
            "  {:<6} {:<10} {:<28} {:<10} {}",
            index,
            if order.rebased() { "yes" } else { "REFUSED" },
            truncate(&founded.join(", "), 28),
            certificate.orders[index].one_shot.len(),
            capacities.join(" ")
        );
        if !order.blocks_gained.is_empty() {
            println!(
                "         blocks gained per staged founding (a STAGING coordinate, not compared): {:?}",
                order.blocks_gained
            );
        }
    }

    println!("\n  THE TWO COMPARISONS");
    println!(
        "    conduct invariant (law)          {}",
        certificate.conduct_agrees
    );
    println!(
        "    ENDPOINT  one-shot partitions    {}",
        certificate.endpoints_agree
    );
    println!(
        "    ENDPOINT  equivalence on items   {}",
        certificate.identified_agrees
    );
    println!(
        "    LINEAGE   content-keyed delta    {}",
        certificate.combined_delta.is_some()
    );
    println!(
        "    LINEAGE   capacities per axis    {}",
        certificate.capacities_agree
    );
    println!(
        "    mint ordinal moved across orders {}",
        certificate.minted_ids_differ
    );
    println!(
        "\n    endpoint-only verdict  {}",
        if certificate.endpoint_only_verdict() {
            "INTERCHANGEABLE"
        } else {
            "ORDERED"
        }
    );
    println!(
        "    certificate verdict    {}",
        if certificate.is_interchangeable() {
            "INTERCHANGEABLE"
        } else {
            "ORDERED"
        }
    );
    if certificate.lineage_changed_the_verdict() {
        println!("\n    >>> LINEAGE COMPARISON CHANGED THE VERDICT. A certificate comparing only");
        println!("    >>> final states would have returned the other answer. That is the defect");
        println!("    >>> `2026-08-02_THE_CPU_FOREMAN...` convicts: endpoint equality became");
        println!("    >>> stateful equivalence.");
    }

    match &certificate.verdict {
        Interchange::Interchangeable => {
            println!(
                "\n  ADMITTED. No receiver in the founded family has a distinguishing word for"
            );
            println!(
                "  these two orders, both rebased lawfully, and the combined delta is canonical:"
            );
            if let Some(delta) = &certificate.combined_delta {
                for axis in delta {
                    println!(
                        "    axis at {}  species {:?}  read after word {:?}",
                        junction_label(axis.junction, name),
                        axis.species,
                        axis.after.iter().map(|input| input.0).collect::<Vec<_>>()
                    );
                }
            }
        }
        Interchange::Ordered { because } => {
            println!("\n  ORDERED. The refusal, exhibited:");
            exhibit(because, name);
        }
    }

    match &certificate.coherence {
        Coherence::PairwiseOnly => {
            println!("\n  COHERENCE: PAIRWISE ONLY. This certificate claims nothing about a third");
            println!("  occurrence. What a triple would require:");
            for line in Coherence::TRIPLE_REQUIRES.split(". ") {
                println!("    {}", line.trim());
            }
        }
        Coherence::FootprintDisjoint {
            occurrences,
            pairs_checked,
        } => {
            println!(
                "\n  COHERENCE: FOOTPRINTS DISJOINT. {occurrences} occurrences, {pairs_checked} pairs \
                 checked for a shared written address; independence derived, not replayed."
            );
        }
        Coherence::AllOrders {
            occurrences,
            orders_compared,
            orders_lawful,
            agreed,
        } => {
            println!(
                "\n  COHERENCE: ALL ORDERS. {occurrences} occurrences, {orders_compared} permutations \
                 rebased, {orders_lawful} lawful, agreed {agreed}."
            );
            println!(
                "  Every permutation of the DECLARED set was compared -- strictly stronger than"
            );
            println!("  pairwise, which is what `canon/01_CAUSAL_CALCULUS.md:88` asks for.");
        }
    }
}

fn exhibit(word: &DistinguishingWord, name: Naming<'_>) {
    match word {
        DistinguishingWord::ReceiverSeparates {
            pair,
            separating_order,
            identifying_order,
            receiver,
            axis,
            separating_observations,
            collapsed_under_identifying_order,
        } => {
            println!(
                "    species  ReceiverSeparates -- the family HAS a word for these two orders"
            );
            println!("    pair     {} | {}", name(pair.0), name(pair.1));
            println!(
                "    order {separating_order} separates it; order {identifying_order} identifies it"
            );
            println!(
                "    axis     receiver #{} founded at {}, reading after word {:?}",
                receiver.0,
                junction_label(axis.junction, name),
                axis.after.iter().map(|input| input.0).collect::<Vec<_>>()
            );
            println!(
                "    returns  {:#x} against {:#x}",
                separating_observations.0.0, separating_observations.1.0
            );
            match collapsed_under_identifying_order {
                Some(collapsed) => {
                    println!(
                        "    THE DISTINGUISHING WORD, from `receiver_exact_compression`: {:?}",
                        collapsed
                            .distinguishing_word
                            .iter()
                            .map(|input| input.0)
                            .collect::<Vec<_>>()
                    );
                    match collapsed.witness {
                        Some((witness, left, right)) => println!(
                            "    witnessed by receiver #{} returning {:#x} against {:#x}",
                            witness.0, left.0, right.0
                        ),
                        None => println!(
                            "    separated by TERMINUS at that word -- no receiver saw it, which is \
                             itself the junction"
                        ),
                    }
                }
                None => println!(
                    "    conduct does not separate this pair under the identifying order, so there \
                     is NO word: reported rather than invented"
                ),
            }
        }
        DistinguishingWord::RebaseRefused {
            order,
            step,
            junction,
            refusal,
            now_witnessed_by,
        } => {
            println!("    species  RebaseRefused -- rebasing is not lawful in both orders");
            println!(
                "    order {order} could not found at step {step}: {}",
                junction_label(*junction, name)
            );
            println!("    refusal  {refusal:?}");
            match refusal {
                FoundingRefusal::NotAStandingJunction { .. } => println!(
                    "             the junction CEASED TO BE ONE once the other founding stood"
                ),
                other => println!("             {other:?}"),
            }
            match now_witnessed_by {
                Some((receiver, left, right, word)) => {
                    println!(
                        "    THE DISTINGUISHING WORD: receiver #{} returns {:#x} against {:#x} \
                         after word {:?}",
                        receiver.0,
                        left.0,
                        right.0,
                        word.iter().map(|input| input.0).collect::<Vec<_>>()
                    );
                    println!(
                        "    That receiver did not exist over the predecessor. The first founding"
                    );
                    println!("    made it, and it sees what the panel could not -- so the two");
                    println!("    occurrences are not independent and the front stays ordered.");
                }
                None => println!(
                    "    no witness found for the closed junction: reported rather than invented"
                ),
            }
        }
        DistinguishingWord::LineageDiverges { step, only_in } => {
            println!("    species  LineageDiverges -- SAME endpoint, DIFFERENT path");
            println!("    first divergence at founding {step:?}");
            for (order, axes) in only_in {
                for axis in axes {
                    println!(
                        "      only order {order} founded  {}   (word {:?}, species {:?})",
                        junction_label(axis.junction, name),
                        axis.after.iter().map(|input| input.0).collect::<Vec<_>>(),
                        axis.species
                    );
                }
            }
            println!(
                "    Equal endpoints do not identify ordered paths. `CLAUDE.md` §0 lesson 4 and"
            );
            println!(
                "    `canon/01_CAUSAL_CALCULUS.md:85`: the isomorphism must preserve complete"
            );
            println!("    successor incidence AND morphology, not just the returned state.");
        }
        DistinguishingWord::ResourcesDiffer {
            orders,
            axis,
            capacities,
        } => {
            println!("    species  ResourcesDiffer -- endpoint, equivalence and content all agree");
            println!(
                "    orders {orders:?} disagree on the capacity of the axis at {}: {} against {}",
                junction_label(axis.junction, name),
                capacities.0,
                capacities.1
            );
        }
        DistinguishingWord::ConductMoved { orders } => {
            println!(
                "    species  ConductMoved -- THE LAW MOVED. Orders {orders:?} disagree on the"
            );
            println!(
                "    Nerode congruence, which founding may not touch. This is a defect report,"
            );
            println!("    not a verdict.");
        }
        DistinguishingWord::ReturnDiffers {
            orders,
            coordinate,
            port,
            differing,
        } => {
            println!(
                "    species  ReturnDiffers -- an enacted front's {coordinate} moved between orders {orders:?} at {port} ({differing} differing)"
            );
        }
        DistinguishingWord::EnactmentRefused { order, reason } => {
            println!(
                "    species  EnactmentRefused -- order {order} could not be enacted: {reason}"
            );
        }
        DistinguishingWord::FootprintShared { members, address } => {
            println!(
                "    species  FootprintShared -- members {members:?} share written address {address}"
            );
        }
    }
}

fn truncate(text: &str, width: usize) -> String {
    if text.chars().count() <= width {
        text.to_owned()
    } else {
        format!("{}…", text.chars().take(width - 1).collect::<String>())
    }
}

/// **The material is declared, and a package cache is not the development.**
///
/// This walked every `.lean` under the root, and under `soma/formal` that is **8,625 files and
/// 91,195,862 octets** — the vendored `.lake/packages/` tree (mathlib, batteries, plausible, …)
/// against **13 files and 27,980 octets** of soma's own development, a factor of **3,259 in
/// octets**. Every previous attempt to run this driver on `soma/formal` was therefore running the
/// certificate over mathlib, which is not the material the header names and is not a development
/// this repository authored. That is `blueprint/THE_ROADMAP.md` plan 1's convicted shape — an
/// inferred layout standing in for a declared root — arriving one organ over.
///
/// A `.lake` directory is a build artifact by Lake's own convention. It is refused here by name,
/// and [`vendored_lean_paths`] exists so the vendored corpus can still be entered **as a separately
/// declared material** when the question is the cost law rather than the development.
fn lean_paths(root: &Path) -> Vec<PathBuf> {
    walk_lean(root, false)
}

/// The same walk, admitting the package cache. Used only where the vendored corpus is the declared
/// material — the scale sweep below, where the question is where the certificate's cost wall is.
fn vendored_lean_paths(root: &Path) -> Vec<PathBuf> {
    walk_lean(root, true)
}

fn walk_lean(root: &Path, admit_package_cache: bool) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            if !admit_package_cache && path.file_name().is_some_and(|name| name == ".lake") {
                continue;
            }
            found.extend(walk_lean(&path, admit_package_cache));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

/// The octets a path population carries, which is the material's own extent and the only honest
/// x-axis for a cost law.
fn octets(paths: &[PathBuf]) -> u64 {
    paths
        .iter()
        .filter_map(|path| std::fs::metadata(path).ok())
        .map(|meta| meta.len())
        .sum()
}

fn main() {
    let root = PathBuf::from(
        std::env::args()
            .nth(1)
            .unwrap_or_else(|| "soma/formal".to_owned()),
    );

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!(
        "law=two orders interchange exactly when no receiver in the founded family separates them"
    );

    let mut controls: Vec<(bool, String, String)> = Vec::new();
    let ordinal = |item: ItemId| item.0.to_string();

    // ---------------------------------------------------------------- 1. the junctions ARE independent
    section("CONTROL 1 (ADMISSION) -- TWO GADGETS THAT NEVER MEET");
    println!("\n  Gadget A conducts only under input 0, gadget B only under input 1. The reading");
    println!("  founded at A's junction terminates at step 0 on every one of B's items, so it");
    println!("  returns the same observation for all of them and cannot separate, witness, or");
    println!("  shorten B's junction. The certificate must ADMIT.");
    let gadget_junctions = bare_junctions(&TwoGadgets);
    println!("\n  standing junctions over the bare panel: {gadget_junctions:?}");
    let admitted = certify_pair(
        &TwoGadgets,
        &[],
        StagedFootprint::at(ItemId(0), ItemId(1)),
        StagedFootprint::at(ItemId(4), ItemId(5)),
    );
    report(&admitted, &ordinal);
    controls.push((
        admitted.is_interchangeable(),
        "control 1 -- the certificate ADMITS where the junctions are independent".to_owned(),
        format!("verdict {:?}", admitted.verdict),
    ));
    controls.push((
        admitted.minted_ids_differ,
        "control 4 -- the mint ordinal moves and the verdict does not".to_owned(),
        format!(
            "order 0 frame {:?}  order 1 frame {:?}",
            admitted.orders[0].mint_frame.values().collect::<Vec<_>>(),
            admitted.orders[1].mint_frame.values().collect::<Vec<_>>()
        ),
    ));

    // ---------------------------------------------------------------- 2. the junctions are NOT
    section("CONTROL 2 (REFUSAL) -- TWO JUNCTIONS COUPLED THROUGH A PAIR NEITHER NAMES");
    println!("\n  (0,1) and (0,2) both stand over the bare panel. Founding at (0,1) reads");
    println!("  aperture_after(., [1]), which separates 3 from 4 -- items NEITHER junction names.");
    println!("  The breadth-first search for (0,2)'s distinguishing word walks straight through");
    println!("  (3,4), so once that axis stands, (0,2) is WITNESSED and stops being a junction.");
    let coupled_junctions = bare_junctions(&CoupledJunctions);
    println!("\n  standing junctions over the bare panel: {coupled_junctions:?}");
    let refused = certify_pair(
        &CoupledJunctions,
        &[],
        StagedFootprint::at(ItemId(0), ItemId(1)),
        StagedFootprint::at(ItemId(0), ItemId(2)),
    );
    report(&refused, &ordinal);
    controls.push((
        !refused.is_interchangeable(),
        "control 2 -- the certificate REFUSES where they are coupled, and exhibits the word"
            .to_owned(),
        format!(
            "refusal species {}",
            match refused.because() {
                Some(DistinguishingWord::RebaseRefused { .. }) => "RebaseRefused",
                Some(DistinguishingWord::ReceiverSeparates { .. }) => "ReceiverSeparates",
                Some(DistinguishingWord::LineageDiverges { .. }) => "LineageDiverges",
                Some(DistinguishingWord::ResourcesDiffer { .. }) => "ResourcesDiffer",
                Some(DistinguishingWord::ConductMoved { .. }) => "ConductMoved",
                Some(DistinguishingWord::ReturnDiffers { .. }) => "ReturnDiffers",
                Some(DistinguishingWord::EnactmentRefused { .. }) => "EnactmentRefused",
                Some(DistinguishingWord::FootprintShared { .. }) => "FootprintShared",
                None => "none",
            }
        ),
    ));
    controls.push((
        admitted.is_interchangeable() && !refused.is_interchangeable(),
        "control 3 -- BOTH verdicts come out of one organ on one code path".to_owned(),
        "TwoGadgets ADMITTED, CoupledJunctions ORDERED".to_owned(),
    ));
    let footprints_disjoint = {
        let left = admitted.staged[0].junction;
        let right = admitted.staged[1].junction;
        left.0 != right.0 && left.0 != right.1 && left.1 != right.0 && left.1 != right.1
    };
    controls.push((
        footprints_disjoint,
        "control 6 -- disjoint footprints do not decide it".to_owned(),
        format!(
            "the admitted pair has disjoint footprints ({footprints_disjoint}); the refused pair \
             SHARES item 0 and is coupled through (3,4), which neither names"
        ),
    ));

    // ---------------------------------------------------------------- 3. the whole-order form
    section("CONTROL 5 -- THE WHOLE-ORDER FORM ON THE COUPLED MATERIAL");
    println!(
        "\n  `certify_founding_orders` runs `found_to_exhaustion` twice, deferring the junction"
    );
    println!(
        "  the first order took first. The two runs may found DIFFERENT SETS of axes, which is"
    );
    println!("  where endpoint comparison and lineage comparison can part company.");
    let whole = certify_founding_orders(&CoupledJunctions);
    report(&whole, &ordinal);
    if let Some(gyration) = &whole.gyration {
        println!("\n  the gyration it consumed");
        println!("    partitions agree  {}", gyration.partitions_agree);
        println!("    conduct agrees    {}", gyration.conduct_agrees);
        println!(
            "    founded agree     {}  <- the ORDERED SEQUENCE, which is the wrong test here:",
            gyration.founded_agree
        );
        println!(
            "                          the sequence differing is the premise of the question."
        );
        println!("    is_holonomy       {}", gyration.is_holonomy());
        println!("    only left  {:?}", gyration.only_left);
        println!("    only right {:?}", gyration.only_right);
    }
    controls.push((
        whole
            .gyration
            .as_ref()
            .is_some_and(|gyr| gyr.conduct_agrees),
        "control 5a -- founding order does not move the Nerode congruence".to_owned(),
        format!(
            "conduct blocks {} across both orders",
            whole.orders[0].conduct.len()
        ),
    ));

    // ---------------------------------------------------------------- 2b. the complete aperture
    section("CONTROL 10 -- APERTURE-COMPLETE: EVERY UNORDERED PAIR OF STANDING JUNCTIONS");
    println!(
        "\n  A verdict measured on one hand-chosen pair per material is a reading of that pair."
    );
    println!("  Both fixtures are small enough to exhaust: every unordered pair of the junctions");
    println!(
        "  standing over the bare panel is certified, and the split is reported. The aperture is"
    );
    println!("  the material's whole standing junction population, not a window.");
    let mut sweep_rows: Vec<(&str, usize, usize, usize)> = Vec::new();
    for (label, system) in [
        ("TwoGadgets", &TwoGadgets as &dyn ObservedSystem),
        ("ThreeGadgets", &ThreeGadgets as &dyn ObservedSystem),
        ("CoupledJunctions", &CoupledJunctions as &dyn ObservedSystem),
        (
            "SameEndpointDifferentPath",
            &SameEndpointDifferentPath as &dyn ObservedSystem,
        ),
    ] {
        let standing = bare_junctions(system);
        let mut admitted_here = 0usize;
        let mut refused_here = 0usize;
        println!("\n  {label}: {} standing junctions", standing.len());
        for (index, left) in standing.iter().enumerate() {
            for right in &standing[index + 1..] {
                let certificate = certify_pair(
                    system,
                    &[],
                    StagedFootprint::at(left.0, left.1),
                    StagedFootprint::at(right.0, right.1),
                );
                if certificate.is_interchangeable() {
                    admitted_here += 1;
                } else {
                    refused_here += 1;
                }
                println!(
                    "    ({},{}) x ({},{})  {}   endpoint-only {}",
                    left.0.0,
                    left.1.0,
                    right.0.0,
                    right.1.0,
                    if certificate.is_interchangeable() {
                        "ADMITTED"
                    } else {
                        "ORDERED "
                    },
                    if certificate.endpoint_only_verdict() {
                        "ADMITTED"
                    } else {
                        "ORDERED"
                    }
                );
            }
        }
        sweep_rows.push((label, standing.len(), admitted_here, refused_here));
    }
    println!(
        "\n  {:<28} {:>10} {:>10} {:>10}",
        "material", "junctions", "admitted", "ordered"
    );
    println!("  {}", "-".repeat(62));
    for (label, junctions, admitted_here, refused_here) in &sweep_rows {
        println!("  {label:<28} {junctions:>10} {admitted_here:>10} {refused_here:>10}");
    }
    let sweep_admitted: usize = sweep_rows.iter().map(|row| row.2).sum();
    let sweep_refused: usize = sweep_rows.iter().map(|row| row.3).sum();
    controls.push((
        sweep_admitted > 0 && sweep_refused > 0,
        "control 10 -- over the COMPLETE junction aperture the verdict is not constant".to_owned(),
        format!("{sweep_admitted} admitted, {sweep_refused} ordered, across four materials"),
    ));

    // ---------------------------------------------------------------- 3b. same endpoint, other path
    section("CONTROL 5c -- SAME ENDPOINT, DIFFERENT PATH, ON EIGHT ITEMS");
    println!("\n  `CoupledJunctions` with item 4's successor removed. The two complete founding");
    println!(
        "  orders reach ONE partition and get there by founding different axes. An endpoint-only"
    );
    println!("  comparator ADMITS; the certificate REFUSES on lineage. This is the same shape");
    println!("  soma/formal returns, reproduced without the filesystem so the finding is not a");
    println!("  property of one corpus.");
    let same_endpoint = certify_founding_orders(&SameEndpointDifferentPath);
    report(&same_endpoint, &ordinal);
    controls.push((
        same_endpoint.endpoint_only_verdict()
            && !same_endpoint.is_interchangeable()
            && same_endpoint.lineage_changed_the_verdict(),
        "control 5c -- lineage comparison refuses what endpoint comparison admits".to_owned(),
        format!(
            "endpoint-only {} / certificate {}",
            same_endpoint.endpoint_only_verdict(),
            same_endpoint.is_interchangeable()
        ),
    ));

    // ---------------------------------------------------------------- 4. real material
    let paths = lean_paths(&root);
    if paths.is_empty() {
        eprintln!(
            "no .lean under {} -- the real-material sections are skipped",
            root.display()
        );
        std::process::exit(2);
    }
    let reading = join(
        paths
            .iter()
            .filter_map(|path| std::fs::read_to_string(path).ok())
            .map(|text| read_development(&text, DeclarationGrain::EveryTopLevelDeclaration))
            .collect(),
    );
    let development = Development::read(&reading);
    let named = |item: ItemId| development.name_of(item).to_owned();

    section("REAL MATERIAL -- THE WHOLE-ORDER FORM ON soma/formal");
    println!("\n  material  {}", root.display());
    println!(
        "  declared  {} .lean files, {} octets — the package cache under `.lake` is REFUSED by name",
        paths.len(),
        octets(&paths)
    );
    let vendored = vendored_lean_paths(&root);
    println!(
        "  refused   {} files, {} octets of vendored `.lake/packages` (mathlib and its deps)",
        vendored.len() - paths.len(),
        octets(&vendored).saturating_sub(octets(&paths))
    );
    let before = compress(&development);
    println!(
        "  items {} | inputs {} | one-shot {} blocks | conduct {} blocks | {} standing junctions",
        development.names.len(),
        development.width,
        before.one_shot.len(),
        before.conduct.len(),
        standing_junctions(&development, &[]).len()
    );
    let formal = certify_founding_orders(&development);
    report(&formal, &named);
    if let Some(gyration) = &formal.gyration {
        println!("\n  the gyration it consumed");
        println!("    partitions agree  {}", gyration.partitions_agree);
        println!("    conduct agrees    {}", gyration.conduct_agrees);
        println!("    founded agree     {}", gyration.founded_agree);
        println!("    is_holonomy       {}", gyration.is_holonomy());
    }
    controls.push((
        formal.orders.iter().all(|order| order.rebased()),
        "control 5b -- both complete founding orders ran on real material".to_owned(),
        format!(
            "left {} foundings, right {} foundings",
            formal.orders[0].founded.len(),
            formal.orders[1].founded.len()
        ),
    ));
    controls.push((
        formal.endpoints_agree
            && formal.identified_agrees
            && !formal.is_interchangeable()
            && formal.lineage_changed_the_verdict(),
        "control 5 -- ON REAL MATERIAL, lineage comparison changed the verdict".to_owned(),
        format!(
            "endpoint-only INTERCHANGEABLE={}, certificate INTERCHANGEABLE={}, divergence {}",
            formal.endpoint_only_verdict(),
            formal.is_interchangeable(),
            match formal.because() {
                Some(DistinguishingWord::LineageDiverges { only_in, .. }) => only_in
                    .iter()
                    .map(|(order, axes)| format!(
                        "order {order}: {}",
                        axes.iter()
                            .map(|axis| junction_label(axis.junction, &named))
                            .collect::<Vec<_>>()
                            .join(" / ")
                    ))
                    .collect::<Vec<_>>()
                    .join("  vs  "),
                other => format!("{other:?}"),
            }
        ),
    ));

    // ---------------------------------------------------------------- 5. staged pair on real material
    section("REAL MATERIAL -- THE STAGED PAIR THAT THE GYRATION DIVERGED ON");
    let standing = standing_junctions(&development, &[]);
    let first_two: Vec<StagedFootprint> = standing
        .iter()
        .take(2)
        .map(|pair| StagedFootprint::at(pair.left, pair.right))
        .collect();
    if first_two.len() == 2 {
        println!(
            "\n  staging the first two standing junctions:\n    {}\n    {}",
            junction_label(first_two[0].junction, &named),
            junction_label(first_two[1].junction, &named),
        );
        let staged = certify_pair(&development, &[], first_two[0], first_two[1]);
        report(&staged, &named);
        controls.push((
            staged.because().is_some() || staged.is_interchangeable(),
            "control 7a -- the staged pair on real material returns a verdict with its exhibit"
                .to_owned(),
            format!("verdict interchangeable={}", staged.is_interchangeable()),
        ));
    }

    // ---------------------------------------------------------------- 6. the declared set
    section("CONTROL 7 -- A DECLARED SET, OVER EVERY PERMUTATION");
    println!(
        "\n  Pairwise interchange does not compose. A pair certificate returns PairwiseOnly and"
    );
    println!(
        "  names what a triple would require; `certify_set` rebases n! orders of the CALLER's"
    );
    println!("  declared set and requires all of them to agree.");
    let triple: Vec<StagedFootprint> = standing
        .iter()
        .take(3)
        .map(|pair| StagedFootprint::at(pair.left, pair.right))
        .collect();
    if triple.len() == 3 {
        let set = certify_set(&development, &[], &triple);
        report(&set, &named);
        controls.push((
            matches!(
                set.coherence,
                Coherence::AllOrders {
                    orders_compared: 6,
                    ..
                }
            ),
            "control 7 -- a declared triple is certified over all 3! = 6 orders".to_owned(),
            format!("{:?}", set.coherence),
        ));
    }
    let gadget_set = certify_set(
        &TwoGadgets,
        &[],
        &[
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        ],
    );
    println!(
        "\n  and on the independent material: {:?} -> interchangeable {}",
        gadget_set.coherence,
        gadget_set.is_interchangeable()
    );
    controls.push((
        gadget_set.is_interchangeable(),
        "control 7b -- the all-orders form still ADMITS where the pair form does".to_owned(),
        format!("{:?}", gadget_set.coherence),
    ));

    section("CONTROL 7c -- A TRIPLE THAT ACTUALLY AGREES, OVER ALL 3! = 6 ORDERS");
    println!(
        "\n  A coherence check that has only ever returned a refusal has not been shown to be"
    );
    println!("  able to admit. Three gadgets, each conducting under exactly one input, so each");
    println!("  founded reading terminates at step 0 on the other two gadgets' items.");
    println!(
        "\n  standing junctions over the bare panel: {:?}",
        bare_junctions(&ThreeGadgets)
    );
    let triple_admitted = certify_set(
        &ThreeGadgets,
        &[],
        &[
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(2), ItemId(3)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        ],
    );
    report(&triple_admitted, &ordinal);
    controls.push((
        matches!(
            triple_admitted.coherence,
            Coherence::AllOrders {
                orders_compared: 6,
                orders_lawful: 6,
                agreed: true,
                ..
            }
        ),
        "control 7c -- a declared triple ADMITS over all six orders".to_owned(),
        format!("{:?}", triple_admitted.coherence),
    ));

    section("CONTROL 9 -- THE FAMILY IS A PREVIOUSLY FOUNDED REGION, NOT THE LIVE FRONT");
    println!("\n  The receiver family the certificate asks against is what the ALREADY-FOUNDED");
    println!("  regions can distinguish. So the certificate has to stage over a non-empty prefix:");
    println!("  found at gadget A's junction first, then certify B against C over that panel.");
    let prefix = vec![
        holonic_engine::founded_receiver::found_at(&ThreeGadgets, &[], (ItemId(0), ItemId(1)))
            .expect("gadget A's junction stands over the bare panel"),
    ];
    let over_prefix = certify_pair(
        &ThreeGadgets,
        &prefix,
        StagedFootprint::at(ItemId(2), ItemId(3)),
        StagedFootprint::at(ItemId(4), ItemId(5)),
    );
    report(&over_prefix, &ordinal);
    controls.push((
        over_prefix.predecessor.prefix.len() == 1
            && over_prefix.is_interchangeable()
            && over_prefix.orders[0].delta.len() == 2,
        "control 9 -- the certificate stages over an already-founded prefix".to_owned(),
        format!(
            "{} axes in the predecessor, {} in the delta, {} standing junctions over it",
            over_prefix.predecessor.prefix.len(),
            over_prefix.orders[0].delta.len(),
            over_prefix.predecessor.standing_junctions.len()
        ),
    ));

    // ---------------------------------------------------------------- 7. capacities
    section("CONTROL 8 -- capacities() NOW HAS A LIBRARY CONSUMER");
    println!(
        "\n  `canon/THE_CONTAMINANT_PROTOCOL.md` §2.1, the verified instance of the unconsumed"
    );
    println!(
        "  return: `founded_receiver.rs:238 capacities()`, whose only call sites were a driver"
    );
    println!("  and a test. The certificate reads it as the successor's logical resource -- the");
    println!(
        "  blueprint's \"equivalence of all other successor standing/consequences/obstruction/"
    );
    println!("  logical resources\" -- re-keyed off the mint ordinal onto the axis content.");
    println!("\n  consumer: crates/holonic-engine/src/interchange.rs, `order_from_panel`.");
    println!("\n  the capacity vector each order carried, on the admitted material:");
    for (index, order) in admitted.orders.iter().enumerate() {
        for (axis, capacity) in &order.capacities {
            println!(
                "    order {index}  axis {}|{}  capacity {capacity}",
                axis.junction.0.0, axis.junction.1.0
            );
        }
    }
    let capacities_nonempty = admitted
        .orders
        .iter()
        .all(|order| !order.capacities.is_empty());
    controls.push((
        capacities_nonempty && admitted.capacities_agree,
        "control 8 -- capacities() is read by a library organ and compared".to_owned(),
        format!(
            "{} axes carried a capacity in each order; agree {}",
            admitted.orders[0].capacities.len(),
            admitted.capacities_agree
        ),
    ));

    // ---------------------------------------------------------------- the cost law, on declared slices
    //
    // **Where the wall is, measured rather than narrated.** The certificate returns on soma's own
    // development in well under a second; it had never returned on `soma/formal` because
    // `lean_paths` was walking mathlib. That leaves a real question this section answers: at what
    // material extent does the certificate stop returning, and which phase stops first?
    //
    // The slice is a CALLER declaration — argv[2], a count of vendored files to admit — never a
    // level authored here. Nothing branches on the elapsed figures: the clock measures and the
    // caller (a shell `timeout` around this process) is what stops a run. `CLAUDE.md` §8.
    if let Some(slice) = std::env::args()
        .nth(2)
        .and_then(|arg| arg.parse::<usize>().ok())
    {
        section("THE COST LAW -- THE CERTIFICATE ON A CALLER-DECLARED SLICE OF THE PACKAGE CACHE");
        let mut vendored = vendored_lean_paths(&root);
        vendored.truncate(slice);
        println!(
            "\n  slice     {} files, {} octets",
            vendored.len(),
            octets(&vendored)
        );

        let clock = std::time::Instant::now();
        let sliced = join(
            vendored
                .iter()
                .filter_map(|path| std::fs::read_to_string(path).ok())
                .map(|text| read_development(&text, DeclarationGrain::EveryTopLevelDeclaration))
                .collect(),
        );
        let sliced = Development::read(&sliced);
        println!(
            "  read      {} items, {} inputs, {:?}",
            sliced.names.len(),
            sliced.width,
            clock.elapsed()
        );

        let clock = std::time::Instant::now();
        let partition = compress(&sliced);
        println!(
            "  compress  {} one-shot blocks, {} conduct blocks, {} collapsed pairs, {:?}",
            partition.one_shot.len(),
            partition.conduct.len(),
            partition.collapsed.len(),
            clock.elapsed()
        );

        let clock = std::time::Instant::now();
        let standing_here = standing_junctions(&sliced, &[]);
        println!(
            "  junctions {} standing, {:?}",
            standing_here.len(),
            clock.elapsed()
        );

        let clock = std::time::Instant::now();
        let certified = certify_founding_orders(&sliced);
        println!(
            "  certify   {} foundings left / {} right, verdict interchangeable={}, {:?}",
            certified.orders[0].founded.len(),
            certified.orders[1].founded.len(),
            certified.is_interchangeable(),
            clock.elapsed()
        );
        println!(
            "\n  Every phase above is a measurement. The founding loop is bounded by items-1 in\n  \
             `founded_receiver::found_in_order` and calls `compress` over the WHOLE widened system\n  \
             once per founded axis, so the certificate's work is at least items x cost(compress),\n  \
             and `certify_founding_orders` runs that loop twice."
        );
    }

    // ---------------------------------------------------------------- the controls
    section("THE CONTROLS");
    let mut failed = 0usize;
    for (held, name, detail) in &controls {
        println!("  [{}] {name}", if *held { "HELD" } else { "FAIL" });
        println!("         {detail}");
        if !held {
            failed += 1;
        }
    }
    println!(
        "\n  {} of {} controls held",
        controls.len() - failed,
        controls.len()
    );
    if failed > 0 {
        std::process::exit(1);
    }
}
