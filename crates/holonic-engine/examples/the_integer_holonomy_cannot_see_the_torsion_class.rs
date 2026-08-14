//! The tree's holonomy instrument was blind to the class the tree's invariant instrument found,
//! and the modulus the caller declares is what opens its eye.
//!
//! ## The defect this drives
//!
//! `canon/TABLET_THE_FLOW.md` §6 states it as a theorem rather than a complaint:
//!
//! > `Hom(Z/n, Z) = 0`. **A `Z`-valued holonomy is a homomorphism out of `H_1` and kills every
//! > torsion class by construction.** The tree's holonomy instrument is provably blind to the class
//! > the tree's invariant instrument just found, and they are in the same crate.
//!
//! `rebase_invariants` computes integral homology **with** torsion and returns `Z/2` on a face wound
//! twice about its rim. `running_integral::found_potential` hard-wired all three arms of its chord
//! obstruction to `BigInt` until 2026-08-10, so no cochain it ever tested could report that class.
//! `found_potential_in` now takes the coefficient group as an argument, and this driver is the
//! falsifier: **the same material, the same cochain, three declared groups, three different
//! returns.**
//!
//! ## What the chord population actually is
//!
//! A chord closes exactly one fundamental cycle, and the residual `declared - implied` is the
//! pairing of the cochain with that cycle. So the population `found_potential` returns **is** the
//! homomorphism `H_1(1-skeleton) -> G` written in the fundamental-cycle basis, split into its
//! kernel (agreeing) and its complement (retained). Which `G` decides what it can see:
//!
//! ```text
//!   Hom(Z/2, Z)   = 0        an integer holonomy annihilates the class
//!   Hom(Z/2, Z/3) = 0        gcd(2,3) = 1: a coprime modulus is exactly as blind
//!   Hom(Z/2, Z/2) = Z/2      the class is visible, and a witness exists
//! ```
//!
//! The third line is the one this driver has to *exhibit*, because the first two are refusals and a
//! refusal alone is not evidence that anything was there to refuse.
//!
//! ## Where the modulus comes from
//!
//! `CLAUDE.md` §8: *"A level is either read off the material or declared by the caller — never
//! authored inside the organ."* The organ authors nothing: `found_potential` is still `Z` and
//! `found_potential_in` takes the group. **This driver reads `2` off `rebase_invariants`'
//! `total_torsion()` and declares it**, and it also declares `Z/3` — a modulus the material does
//! *not* name — precisely so the reading cannot be mistaken for a knob that always weakens the
//! test. `Z/3` refuses exactly where `Z` refuses.
//!
//! ## The two materials
//!
//! - **the wound circuit**, the shape `examples/grown_circuit_invariants.rs` grows under
//!   `Closure::Wound`: a recursive cell divided into a tree, the frontier closed into a rim, and one
//!   2-cell attached to `2 x (the rim cycle)`. Every wire is a tree cell and every rim arc is a
//!   chord, which is `CLAUDE.md` §11's *"the tree condenses for free; the remainder is the departure
//!   from a forest"* with the departure named.
//! - **the staggered attachment**, `rebase_invariants.rs`'s own gauge fixture: three parallel arcs
//!   and one face attached as `4 e1 - 6 e2 + 2 e3`. Its torsion is the same `Z/2` reached a
//!   different way — by a gcd rather than by a uniform doubling — and it is where
//!   `TABLET_THE_FLOW.md`'s recorded prototype detector lands: *"solving over `F_2` for a cocycle
//!   pairing to 1 with the torsion class returned a support of size one, the single arc appearing in
//!   one face boundary with coefficient 2."*
//!
//! ## The declared controls
//!
//! Every one of them can fail, and three of them fail against the code as it stood yesterday:
//!
//! - the `Z` and `Z/2` chord populations must DIFFER on a declared cochain (fails if the group is
//!   ignored);
//! - they must AGREE on another (fails if the reduction is unconditional rather than declared);
//! - `Z/3` must not agree with `Z/2` (fails if the modulus is read as a boolean);
//! - the torsion pairing must be forced to zero over `Z` **and** reachable over `Z/2` (fails either
//!   way round);
//! - the unwound control material must carry no torsion at all, so the material is shown capable of
//!   returning nothing.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::rebase_invariants::{PivotRule, rebase_invariants};
use holonic_engine::running_integral::{
    Cochain, CoefficientGroup, PotentialSearch, coboundary, found_potential, found_potential_in,
};

// ---------------------------------------------------------------------------------------------
// the material

/// A wound circuit: a tree grown from one root, its frontier closed into a rim, and one 2-cell
/// attached to the rim cycle TWICE.
///
/// The doubling is the whole of it. `d F = 2 R` is a boundary the rationals cannot tell from zero
/// and the integers can, so `[R]` has order exactly two in `H_1`.
struct Wound {
    complex: GradedCausalComplex,
    root: CausalCellId,
    wires: Vec<CausalCellId>,
    rim: Vec<CausalCellId>,
    face: Option<CausalCellId>,
}

fn event(counter: &mut u64) -> BTreeSet<EventId> {
    *counter += 1;
    BTreeSet::from([EventId(*counter)])
}

fn grow(depth: u32, split: u32, wind: bool) -> Wound {
    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;
    let mut wires = Vec::new();
    let root = complex
        .found_cell("root", event(&mut counter), 0, CausalChain::default())
        .expect("the root vertex has no boundary");

    let mut pending = VecDeque::from([(root, "root".to_owned(), depth)]);
    let mut frontier: Vec<(CausalCellId, String)> = Vec::new();
    while let Some((vertex, label, aperture)) = pending.pop_front() {
        if aperture == 0 {
            frontier.push((vertex, label));
            continue;
        }
        for child in 0..split {
            let name = format!("{label}.{child}");
            let landed = complex
                .found_cell(name.clone(), event(&mut counter), 0, CausalChain::default())
                .expect("a vertex has no boundary");
            let mut boundary = CausalChain::default();
            boundary.add_term(landed, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
            wires.push(
                complex
                    .found_cell(
                        format!("wire:{label}->{name}"),
                        event(&mut counter),
                        1,
                        boundary,
                    )
                    .expect("an edge between two founded vertices closes"),
            );
            pending.push_back((landed, name, aperture - 1));
        }
    }

    let mut rim = Vec::new();
    for index in 0..frontier.len() {
        let (from, from_label) = &frontier[index];
        let (to, to_label) = &frontier[(index + 1) % frontier.len()];
        let mut boundary = CausalChain::default();
        boundary.add_term(*to, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(*from, ComparativeMultiplicity::negative(1u32));
        rim.push(
            complex
                .found_cell(
                    format!("rim:{from_label}->{to_label}"),
                    event(&mut counter),
                    1,
                    boundary,
                )
                .expect("a rim edge closes"),
        );
    }

    let face = wind.then(|| {
        let mut boundary = CausalChain::default();
        for edge in &rim {
            boundary.add_term(*edge, ComparativeMultiplicity::positive(2u32));
        }
        complex
            .found_cell("wound-face", event(&mut counter), 2, boundary)
            .expect("the doubled rim is a cycle, so the face closes")
    });

    Wound {
        complex,
        root,
        wires,
        rim,
        face,
    }
}

/// `rebase_invariants.rs`'s own gauge fixture, rebuilt here: three parallel arcs `a -> b` and one
/// face attached as `4 e1 - 6 e2 + 2 e3`. `gcd(4, 6, 2) = 2`, so the reduction settles a `Z/2`.
struct Staggered {
    complex: GradedCausalComplex,
    a: CausalCellId,
    arcs: Vec<CausalCellId>,
    face: CausalCellId,
}

fn staggered() -> Staggered {
    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;
    let a = complex
        .found_cell("a", event(&mut counter), 0, CausalChain::default())
        .expect("a vertex has no boundary");
    let b = complex
        .found_cell("b", event(&mut counter), 0, CausalChain::default())
        .expect("a vertex has no boundary");
    let mut arcs = Vec::new();
    for name in ["e1", "e2", "e3"] {
        let mut boundary = CausalChain::default();
        boundary.add_term(b, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        arcs.push(
            complex
                .found_cell(name, event(&mut counter), 1, boundary)
                .expect("a parallel arc closes"),
        );
    }
    let mut boundary = CausalChain::default();
    boundary.add_term(arcs[0], ComparativeMultiplicity::positive(4u32));
    boundary.add_term(arcs[1], ComparativeMultiplicity::negative(6u32));
    boundary.add_term(arcs[2], ComparativeMultiplicity::positive(2u32));
    let face = complex
        .found_cell("staggered-face", event(&mut counter), 2, boundary)
        .expect("the coefficients sum to zero, so the face closes");
    Staggered {
        complex,
        a,
        arcs,
        face,
    }
}

// ---------------------------------------------------------------------------------------------
// readings

fn name_of(complex: &GradedCausalComplex, cell: CausalCellId) -> String {
    complex
        .cell(cell)
        .map(|body| body.name.clone())
        .unwrap_or_else(|_| format!("{cell:?}"))
}

fn chain_of(cells: &[CausalCellId], coefficient: u32) -> CausalChain {
    let mut chain = CausalChain::default();
    for cell in cells {
        chain.add_term(*cell, ComparativeMultiplicity::positive(coefficient));
    }
    chain
}

fn cochain_on(cells: &[CausalCellId], values: &[i64]) -> Cochain {
    Cochain::from_values(
        1,
        cells
            .iter()
            .zip(values.iter())
            .map(|(cell, value)| (*cell, BigInt::from(*value))),
    )
}

/// The arm each chord landed in, by name, for one search.
fn population(complex: &GradedCausalComplex, search: &PotentialSearch) -> String {
    let mut rendered = String::new();
    for cell in &search.agreeing_chords {
        rendered.push_str(&format!("      agreeing    {}\n", name_of(complex, *cell)));
    }
    for chord in &search.retained_obstructions {
        rendered.push_str(&format!(
            "      OBSTRUCTION {}   residual {} in Z, {} in the declared group\n",
            name_of(complex, chord.cell),
            chord.residual,
            chord.residual_in(&search.group)
        ));
    }
    rendered
}

fn group_name(group: &CoefficientGroup) -> String {
    match group.modulus() {
        None => "Z".to_owned(),
        Some(modulus) => format!("Z/{modulus}"),
    }
}

/// The retained chords' addresses, which is the population two groups are compared on.
fn retained(search: &PotentialSearch) -> BTreeSet<CausalCellId> {
    search
        .retained_obstructions
        .iter()
        .map(|chord| chord.cell)
        .collect()
}

fn main() {
    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    println!("THE INTEGER HOLONOMY CANNOT SEE THE TORSION CLASS");
    println!("=================================================\n");

    // -- 1. the material states its own torsion, and the caller reads the modulus off it -------

    let wound = grow(2, 2, true);
    let control = grow(2, 2, false);
    let wound_invariants =
        rebase_invariants(&wound.complex, PivotRule::FirstNonzero).expect("an exact reduction");
    let control_invariants =
        rebase_invariants(&control.complex, PivotRule::FirstNonzero).expect("an exact reduction");

    println!("1. THE MATERIAL, AND WHERE THE MODULUS COMES FROM");
    println!("-------------------------------------------------");
    println!(
        "  wound circuit   {} wires, {} rim arcs, 1 face attached to 2 x (the rim cycle)",
        wound.wires.len(),
        wound.rim.len()
    );
    println!(
        "    betti {:?}   torsion {:?}",
        wound_invariants.betti_vector(),
        wound_invariants.total_torsion()
    );
    println!(
        "  CONTROL the same circuit UNWOUND (no face at all)\n    betti {:?}   torsion {:?}",
        control_invariants.betti_vector(),
        control_invariants.total_torsion()
    );

    let torsion = wound_invariants.total_torsion();
    holds.push((
        "CONTROL the unwound circuit carries NO torsion, so the torsion column can return nothing",
        control_invariants.total_torsion().is_empty(),
        format!("unwound torsion {:?}", control_invariants.total_torsion()),
    ));
    holds.push((
        "CONTROL winding the face twice DEPOSITS torsion, so the column can also be nonzero",
        torsion.len() == 1 && torsion[0] == BigInt::from(2),
        format!("wound torsion {torsion:?}"),
    ));

    let declared_modulus = torsion
        .first()
        .cloned()
        .expect("the invariant instrument named a torsion coefficient");
    let integers = CoefficientGroup::Integers;
    let cyclic = CoefficientGroup::cyclic(declared_modulus.clone()).expect("a positive modulus");
    let coprime = CoefficientGroup::cyclic(BigInt::from(3)).expect("a positive modulus");
    println!(
        "\n  THE MODULUS IS READ OFF THE MATERIAL AND DECLARED BY THIS DRIVER: total_torsion()"
    );
    println!(
        "  returned {declared_modulus}, so the declared groups are Z, Z/{declared_modulus}, and"
    );
    println!("  Z/3 — the last one a modulus the material does NOT name, declared on purpose.\n");

    // -- 2. the torsion cycle, exhibited ------------------------------------------------------

    let rim_cycle = chain_of(&wound.rim, 1);
    let doubled = chain_of(&wound.rim, 2);
    let face = wound.face.expect("the wound circuit carries its face");
    let face_boundary = wound
        .complex
        .cell(face)
        .expect("the face was founded")
        .boundary
        .clone();
    let rim_is_closed = wound
        .complex
        .boundary_of_chain(&rim_cycle)
        .expect("the rim is a chain")
        .difference_is_zero();

    println!("2. THE TORSION CYCLE");
    println!("--------------------");
    println!("  R  = {} rim arcs, each once", wound.rim.len());
    println!("  dR = 0                     {rim_is_closed}");
    println!("  dF = 2R                    {}", face_boundary == doubled);
    println!("  so [R] has order two in H_1: 2R bounds and R does not.\n");
    holds.push((
        "the rim cycle closes and the face bounds exactly twice it",
        rim_is_closed && face_boundary == doubled,
        format!("dF == 2R is {}", face_boundary == doubled),
    ));

    // -- 3. Hom(Z/2, Z) = 0, measured over a declared family ----------------------------------
    //
    // The pairing of a cochain with [R] is read two independent ways: from the incidence, by
    // evaluating the cochain against the chain R; and from the chord population, by summing the
    // retained and agreeing residuals over the rim chords. They must agree, because R is the sum of
    // the fundamental cycles the rim chords close and the tree paths telescope away.

    println!("3. THE PAIRING WITH [R], READ TWO WAYS, OVER A DECLARED FAMILY");
    println!("--------------------------------------------------------------");

    let mut wire_frames: Vec<(&str, Vec<i64>)> = Vec::new();
    wire_frames.push(("wires at rest", vec![0; wound.wires.len()]));
    wire_frames.push((
        "wires under a second frame",
        (0..wound.wires.len())
            .map(|index| index as i64 - 2)
            .collect(),
    ));

    let mut closed_over_z = 0usize;
    let mut closed_over_z_pairing_nonzero = 0usize;
    let mut open_over_z = 0usize;
    let mut open_over_z_pairing_nonzero = 0usize;
    let mut readings_disagreed = 0usize;
    let mut mod_two_closed = 0usize;
    let mut mod_two_pairing_one = 0usize;
    let mut individual_residuals: BTreeSet<Vec<BigInt>> = BTreeSet::new();
    let mut pairings_per_rim: BTreeMap<Vec<i64>, BTreeSet<BigInt>> = BTreeMap::new();
    let mut family = 0usize;

    let arity = wound.rim.len();
    let alphabet: [i64; 3] = [-1, 0, 1];
    let mut word = vec![0usize; arity];
    loop {
        let rim_values: Vec<i64> = word.iter().map(|index| alphabet[*index]).collect();
        for (_, wire_values) in &wire_frames {
            let mut cochain = cochain_on(&wound.wires, wire_values);
            for (cell, value) in wound.rim.iter().zip(rim_values.iter()) {
                cochain.set(*cell, BigInt::from(*value));
            }
            family += 1;

            let from_incidence = cochain
                .evaluate(&wound.complex, &rim_cycle)
                .expect("R is a 1-chain");
            let search = found_potential(&wound.complex, &cochain, wound.root)
                .expect("the root is a vertex");
            let from_chords: BigInt = search
                .retained_obstructions
                .iter()
                .map(|chord| chord.residual.clone())
                .sum();
            if from_incidence != from_chords {
                readings_disagreed += 1;
            }
            individual_residuals.insert(search.standing_residuals());
            pairings_per_rim
                .entry(rim_values.clone())
                .or_default()
                .insert(from_incidence.clone());

            let d = coboundary(&wound.complex, &cochain).expect("the coboundary is total");
            if d.is_zero() {
                closed_over_z += 1;
                if !from_incidence.is_zero() {
                    closed_over_z_pairing_nonzero += 1;
                }
            } else {
                open_over_z += 1;
                if !from_incidence.is_zero() {
                    open_over_z_pairing_nonzero += 1;
                }
            }
            if d.values().values().all(|value| cyclic.vanishes(value)) {
                mod_two_closed += 1;
                if !cyclic.vanishes(&from_incidence) {
                    mod_two_pairing_one += 1;
                }
            }
        }

        let mut at = 0usize;
        loop {
            if at == arity {
                break;
            }
            word[at] += 1;
            if word[at] < alphabet.len() {
                break;
            }
            word[at] = 0;
            at += 1;
        }
        if at == arity {
            break;
        }
    }

    println!("  declared family: rim values in {{-1, 0, 1}}^{arity}, under two wire frames");
    println!("  readings taken: {family}");
    println!(
        "  the two readings of <w, R> — from the incidence and from the chord residuals — \
         disagreed on {readings_disagreed}"
    );
    println!(
        "  distinct residual VECTORS returned: {}   (the individual residuals move with the frame)",
        individual_residuals.len()
    );
    let pairing_is_frame_free = pairings_per_rim
        .values()
        .all(|pairings| pairings.len() == 1);
    println!(
        "  <w, R> per rim word, across both wire frames: {} value each   {pairing_is_frame_free}",
        if pairing_is_frame_free {
            "one"
        } else {
            "MORE THAN one"
        }
    );
    println!();
    println!(
        "  over Z    closed cochains {closed_over_z:>4}, of which <w,R> != 0 : {closed_over_z_pairing_nonzero}"
    );
    println!(
        "            open   cochains {open_over_z:>4}, of which <w,R> != 0 : {open_over_z_pairing_nonzero}"
    );
    println!(
        "  over Z/2  closed cochains {mod_two_closed:>4}, of which <w,R> != 0 : {mod_two_pairing_one}"
    );
    println!();
    println!(
        "  Every Z-cocycle is forced to pair to ZERO with [R], because 2<w,R> = <w,dF> = 0 in"
    );
    println!(
        "  a group with no 2-torsion. Mod 2 the face imposes NO condition at all — dF = 2R is"
    );
    println!(
        "  identically zero there — so the whole family is closed and the pairing runs free.\n"
    );

    holds.push((
        "Hom(Z/2, Z) = 0 MEASURED: no Z-cocycle in the declared family pairs nonzero with [R]",
        closed_over_z > 0 && closed_over_z_pairing_nonzero == 0,
        format!(
            "{closed_over_z} Z-cocycles, {closed_over_z_pairing_nonzero} with a nonzero pairing"
        ),
    ));
    holds.push((
        "CONTROL the pairing is NOT identically zero on the family, so the line above is not vacuous",
        open_over_z_pairing_nonzero > 0,
        format!("{open_over_z_pairing_nonzero} of {open_over_z} non-cocycles pair nonzero"),
    ));
    holds.push((
        "Hom(Z/2, Z/2) = Z/2 MEASURED: mod 2 the whole family is closed and the pairing is reached",
        mod_two_closed == family && mod_two_pairing_one > 0,
        format!("{mod_two_closed} of {family} closed mod 2, {mod_two_pairing_one} pair to 1"),
    ));
    holds.push((
        "the incidence reading and the chord-population reading of <w, R> never disagreed",
        readings_disagreed == 0,
        format!("{readings_disagreed} disagreements over {family} readings"),
    ));
    holds.push((
        "CONTROL the individual residuals MOVE with the wire frame while <w, R> does not",
        individual_residuals.len() > pairings_per_rim.len() && pairing_is_frame_free,
        format!(
            "{} distinct residual vectors over {} rim words, each with one pairing",
            individual_residuals.len(),
            pairings_per_rim.len()
        ),
    ));

    // -- 4. the witness, and its support ------------------------------------------------------

    let witness = {
        let mut cochain = cochain_on(&wound.wires, &vec![0; wound.wires.len()]);
        cochain.set(wound.rim[0], BigInt::one());
        cochain
    };
    let witness_pairing = witness
        .evaluate(&wound.complex, &rim_cycle)
        .expect("R is a 1-chain");
    let witness_d = coboundary(&wound.complex, &witness).expect("the coboundary is total");
    println!("4. THE WITNESS OVER Z/2, AND WHAT IT COSTS OVER Z");
    println!("--------------------------------------------------");
    println!(
        "  w* = 1 on {} and nothing else       support {}",
        name_of(&wound.complex, wound.rim[0]),
        witness.support().len()
    );
    println!("  <w*, R> = {witness_pairing}   -> the torsion generator is sent to 1 in Z/2");
    println!(
        "  d w* on the face = {}   -> w* is NOT a Z-cocycle, and no Z-cocycle can do this",
        witness_d.value(face)
    );
    holds.push((
        "the mod-2 witness has support of size ONE and pairs to 1 with the torsion class",
        witness.support().len() == 1 && cyclic.reduce(&witness_pairing) == BigInt::one(),
        format!(
            "support {}, pairing {witness_pairing} = {} in Z/2",
            witness.support().len(),
            cyclic.reduce(&witness_pairing)
        ),
    ));
    holds.push((
        "CONTROL and it is not a Z-cocycle, which is exactly why Z cannot carry it",
        !witness_d.is_zero() && cyclic.vanishes(&witness_d.value(face)),
        format!(
            "d w* on the face = {} — zero mod 2, nonzero in Z",
            witness_d.value(face)
        ),
    ));

    // -- 5. THE ORBIT: one cochain, three declared groups, three chord populations ------------

    println!("\n5. THE ORBIT — one complex, one cochain, three declared groups");
    println!("---------------------------------------------------------------");
    let doubled_witness = {
        let mut cochain = cochain_on(&wound.wires, &vec![0; wound.wires.len()]);
        cochain.set(wound.rim[0], BigInt::from(2));
        cochain
    };
    println!(
        "  w = 2 on {} and nothing else.\n",
        name_of(&wound.complex, wound.rim[0])
    );
    let mut orbit: Vec<(String, PotentialSearch)> = Vec::new();
    for group in [integers.clone(), cyclic.clone(), coprime.clone()] {
        let search =
            found_potential_in(&wound.complex, &doubled_witness, wound.root, group.clone())
                .expect("the root is a vertex");
        println!(
            "  declared {}:  {} tree cells, {} chords, {} retained, admits a potential {}",
            group_name(&group),
            search.tree_cells.len(),
            search.cycle_rank(),
            search.retained_obstructions.len(),
            search.admits_a_potential()
        );
        print!("{}", population(&wound.complex, &search));
        orbit.push((group_name(&group), search));
    }
    println!();

    let over_z = &orbit[0].1;
    let over_two = &orbit[1].1;
    let over_three = &orbit[2].1;
    let moved: BTreeSet<CausalCellId> = retained(over_z)
        .difference(&retained(over_two))
        .copied()
        .collect();
    println!("  THE CHORD THAT MOVED, BY NAME:");
    for cell in &moved {
        println!(
            "    {}   OBSTRUCTION over Z (residual 2)  ->  agreeing over Z/2",
            name_of(&wound.complex, *cell)
        );
    }
    println!(
        "  and over Z/3 it is an obstruction again: gcd(2, 3) = 1, so Z/3 is as blind as Z.\n"
    );

    holds.push((
        "THE FALSIFIER: the Z and Z/2 chord populations DIFFER on this declared cochain",
        retained(over_z) != retained(over_two) && !moved.is_empty(),
        format!(
            "Z retained {}, Z/2 retained {}, moved {:?}",
            over_z.retained_obstructions.len(),
            over_two.retained_obstructions.len(),
            moved
                .iter()
                .map(|cell| name_of(&wound.complex, *cell))
                .collect::<Vec<_>>()
        ),
    ));
    holds.push((
        "CONTROL Z/3 does NOT agree with Z/2, so the modulus is consulted rather than a boolean",
        retained(over_three) != retained(over_two) && retained(over_three) == retained(over_z),
        format!(
            "Z/3 retained {}, Z/2 retained {}, Z retained {}",
            over_three.retained_obstructions.len(),
            over_two.retained_obstructions.len(),
            over_z.retained_obstructions.len()
        ),
    ));
    holds.push((
        "CONTROL the tree, the reached set and the exact Z potential do not move with the group",
        over_z.tree_cells == over_two.tree_cells
            && over_z.reached == over_two.reached
            && over_z.potential == over_two.potential
            && over_z.cycle_rank() == over_two.cycle_rank(),
        format!(
            "{} tree cells and {} chords under every declared group",
            over_z.tree_cells.len(),
            over_z.cycle_rank()
        ),
    ));
    holds.push((
        "CONTROL Z/2 closed over a LIVE cycle population, not over an empty one",
        over_two.closes_over_a_live_cycle_population(),
        format!("{} chords tested, 0 retained", over_two.cycle_rank()),
    ));

    // the second half of the anti-tautology control: a cochain on which the groups AGREE.
    let mut agreeing_case: Vec<(String, BTreeSet<CausalCellId>)> = Vec::new();
    for group in [integers.clone(), cyclic.clone()] {
        let search = found_potential_in(&wound.complex, &witness, wound.root, group.clone())
            .expect("the root is a vertex");
        agreeing_case.push((group_name(&group), retained(&search)));
    }
    println!(
        "  CONTROL on w* (value 1, not 2) the two groups return the SAME population: {} and {}",
        agreeing_case[0].1.len(),
        agreeing_case[1].1.len()
    );
    holds.push((
        "CONTROL a declared cochain on which Z and Z/2 AGREE, so the difference above is not \
         automatic",
        agreeing_case[0].1 == agreeing_case[1].1 && !agreeing_case[0].1.is_empty(),
        format!(
            "w* retained {:?} under both groups",
            agreeing_case[0]
                .1
                .iter()
                .map(|cell| name_of(&wound.complex, *cell))
                .collect::<Vec<_>>()
        ),
    ));

    // -- 6. the second material, and the recorded prototype reproduced ------------------------

    println!("\n6. THE SECOND MATERIAL — 4 e1 - 6 e2 + 2 e3, and the recorded prototype");
    println!("------------------------------------------------------------------------");
    let stagger = staggered();
    let stagger_invariants =
        rebase_invariants(&stagger.complex, PivotRule::FirstNonzero).expect("an exact reduction");
    println!(
        "  betti {:?}   torsion {:?}",
        stagger_invariants.betti_vector(),
        stagger_invariants.total_torsion()
    );

    // The torsion class: z = 2 e1 - 3 e2 + e3, with 2z = dF exactly.
    let mut torsion_cycle = CausalChain::default();
    torsion_cycle.add_term(stagger.arcs[0], ComparativeMultiplicity::positive(2u32));
    torsion_cycle.add_term(stagger.arcs[1], ComparativeMultiplicity::negative(3u32));
    torsion_cycle.add_term(stagger.arcs[2], ComparativeMultiplicity::positive(1u32));
    let mut doubled_cycle = CausalChain::default();
    doubled_cycle.add_term(stagger.arcs[0], ComparativeMultiplicity::positive(4u32));
    doubled_cycle.add_term(stagger.arcs[1], ComparativeMultiplicity::negative(6u32));
    doubled_cycle.add_term(stagger.arcs[2], ComparativeMultiplicity::positive(2u32));
    let stagger_face_boundary = stagger
        .complex
        .cell(stagger.face)
        .expect("the face was founded")
        .boundary
        .clone();
    let z_closes = stagger
        .complex
        .boundary_of_chain(&torsion_cycle)
        .expect("z is a chain")
        .difference_is_zero();
    println!("  z  = 2 e1 - 3 e2 + e3      dz = 0  {z_closes}");
    println!(
        "  2z = dF                    {}",
        stagger_face_boundary == doubled_cycle
    );
    holds.push((
        "the staggered torsion class closes and doubles exactly onto the face boundary",
        z_closes && stagger_face_boundary == doubled_cycle,
        format!("2z == dF is {}", stagger_face_boundary == doubled_cycle),
    ));

    // enumerate every cochain in a declared box and split it by group
    let mut stagger_z_cocycles = 0usize;
    let mut stagger_z_sighted = 0usize;
    let mut stagger_two_cocycles = 0usize;
    let mut stagger_two_sighted = 0usize;
    // Which single arcs carry a mod-2 cocycle that pairs to 1 with the torsion class. The recorded
    // prototype returned ONE such arc; whether it is the only one is a question about the material
    // and is answered here rather than assumed.
    let mut support_one_arcs: BTreeSet<String> = BTreeSet::new();
    for first in -3i64..=3 {
        for second in -3i64..=3 {
            for third in -3i64..=3 {
                let values = vec![first, second, third];
                let cochain = cochain_on(&stagger.arcs, &values);
                let pairing = cochain
                    .evaluate(&stagger.complex, &torsion_cycle)
                    .expect("z is a 1-chain");
                let d = coboundary(&stagger.complex, &cochain).expect("the coboundary is total");
                if d.is_zero() {
                    stagger_z_cocycles += 1;
                    if !pairing.is_zero() {
                        stagger_z_sighted += 1;
                    }
                }
                if d.values().values().all(|value| cyclic.vanishes(value)) {
                    stagger_two_cocycles += 1;
                    if !cyclic.vanishes(&pairing) {
                        stagger_two_sighted += 1;
                        let mut carried = stagger
                            .arcs
                            .iter()
                            .zip(values.iter())
                            .filter(|(_, value)| **value != 0)
                            .map(|(cell, _)| name_of(&stagger.complex, *cell));
                        if let (Some(only), None) = (carried.next(), carried.next()) {
                            support_one_arcs.insert(only);
                        }
                    }
                }
            }
        }
    }
    println!("\n  declared family: all cochains with values in [-3, 3]^3 — 343 readings");
    println!(
        "  over Z    cocycles {stagger_z_cocycles:>4}, of which <w, z> != 0 : {stagger_z_sighted}"
    );
    println!(
        "  over Z/2  cocycles {stagger_two_cocycles:>4}, of which <w, z> != 0 : {stagger_two_sighted}"
    );

    let coefficient_of = |arc: CausalCellId| {
        stagger_face_boundary
            .coefficients()
            .get(&arc)
            .map(ComparativeMultiplicity::difference)
            .unwrap_or_else(BigInt::zero)
    };
    let coefficient_two_arc = name_of(&stagger.complex, stagger.arcs[2]);
    println!("\n  every single arc carrying a mod-2 cocycle that pairs to 1 with [z]:");
    for arc in &support_one_arcs {
        let cell = stagger
            .arcs
            .iter()
            .find(|candidate| name_of(&stagger.complex, **candidate) == *arc)
            .copied()
            .expect("the arc came from this population");
        println!(
            "    {arc}   face coefficient {}   support 1",
            coefficient_of(cell)
        );
    }
    println!(
        "\n  TABLET_THE_FLOW.md recorded the prototype's return as *\"a support of size one, the"
    );
    println!("  single arc appearing in one face boundary with coefficient 2\"*. The support-one");
    println!(
        "  shape reproduces, and {coefficient_two_arc} — the arc whose face coefficient IS 2 —"
    );
    println!(
        "  is one of the carriers. It is NOT the only one, and that refines the record: mod 2"
    );
    println!(
        "  every face coefficient here (4, -6, 2) is zero, so the face constrains nothing and"
    );
    println!("  <w, z> = w2 + w3 is reached by either arc. The clause \"with coefficient 2\" is a");
    println!("  fact about which arc that run happened to return, not about the mechanism.");

    holds.push((
        "Hom(Z/2, Z) = 0 on the staggered material too: no Z-cocycle in the box sees the class",
        stagger_z_cocycles > 0 && stagger_z_sighted == 0,
        format!("{stagger_z_cocycles} Z-cocycles, {stagger_z_sighted} sighted"),
    ));
    holds.push((
        "and over Z/2 the class IS seen, by a cocycle of support ONE, the arc whose face \
         coefficient is 2 among the carriers",
        stagger_two_sighted > 0
            && !support_one_arcs.is_empty()
            && support_one_arcs.contains(&coefficient_two_arc)
            && coefficient_of(stagger.arcs[2]) == BigInt::from(2),
        format!(
            "support-one carriers {support_one_arcs:?}, {coefficient_two_arc} has face \
             coefficient {}, {stagger_two_sighted} sighted of {stagger_two_cocycles}",
            coefficient_of(stagger.arcs[2])
        ),
    ));
    holds.push((
        "REFINEMENT the support-one witness is NOT unique on this material, so the recorded \
         \"coefficient 2\" clause is a coincidence of presentation rather than the mechanism",
        support_one_arcs.len() > 1,
        format!(
            "{} arcs carry one: {support_one_arcs:?}",
            support_one_arcs.len()
        ),
    ));

    // the chord population on the staggered material, all three groups, on the coefficient-2 arc
    let witness_values = vec![0i64, 0, 1];
    println!("\n  the chord population under each declared group, on w = {witness_values:?}:");
    let stagger_witness = cochain_on(&stagger.arcs, &witness_values);
    let mut stagger_orbit: Vec<(String, BTreeSet<CausalCellId>)> = Vec::new();
    for group in [integers.clone(), cyclic.clone(), coprime.clone()] {
        let search =
            found_potential_in(&stagger.complex, &stagger_witness, stagger.a, group.clone())
                .expect("a is a vertex");
        println!(
            "    declared {:>4}: {} chords, {} retained",
            group_name(&group),
            search.cycle_rank(),
            search.retained_obstructions.len()
        );
        print!("{}", population(&stagger.complex, &search));
        stagger_orbit.push((group_name(&group), retained(&search)));
    }

    // -- report --------------------------------------------------------------------------------

    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0usize;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }

    println!();
    if failed == 0 {
        println!("HELD — {} declared controls, 0 failed", holds.len());
    } else {
        println!(
            "FAILED — {failed} of {} declared controls did not hold",
            holds.len()
        );
        std::process::exit(1);
    }
}
