//! **A lattice gauge configuration over `structure_group`: representation, plaquette holonomy,
//! Wilson action, and one transfer operator whose spectrum is exact.**
//!
//! ```text
//! cargo run --release --example the_plaquette_carries_a_group_element
//! ```
//!
//! `canon/THE_MILLENNIUM_FRAME.md`'s Yang–Mills row was corrected on 2026-08-11: the discrete
//! `a ∧ a` already exists at `structure_group.rs:511`, and what the Yang–Mills-facing line lacks is
//! *a representation, a Wilson plaquette action, a transfer operator*. Each of those is a **receiver
//! on a connection**, not a new geometry, so [`holonic_engine::lattice_gauge`] is a mouth around
//! [`holonic_engine::structure_group`] rather than an organ beside it. Every group operation printed
//! below is `structure_group`'s.
//!
//! # No gap claim, and the reason is not caution
//!
//! **The words "mass gap" appear nowhere as a claim here.** A finite matrix having a gap is nearly
//! automatic, and the Yang–Mills problem is about a *family* carrying lattice spacing, volume, and
//! correlation-length scaling. This construction carries none of the three: one lattice, a spacing
//! that is not a parameter at all, no volume sequence. What is returned is the spectrum, its
//! multiplicities, and the exact intervals between consecutive eigenvalues — measurements of this
//! operator on this configuration, and evidence about nothing else.
//!
//! # The three controls
//!
//! 1. A **gauge-equivalent** pair returns the identical action and the identical spectrum — and the
//!    pair is checked to actually differ on some link first, or the agreement is one configuration
//!    compared with itself (`CLAUDE.md` §8's vacuous gauge).
//! 2. A **deliberately altered** link moves both.
//! 3. An **abelian control** — the same lattice with the connection restricted to the cyclic
//!    subgroup `⟨i⟩ ≅ ℤ/4` — erases the commutator contribution while the action and the spectrum
//!    stay non-trivial, so what is erased is the commutator and not the reading.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Zero;
use relational_geometry::Rat;

use holonic_engine::lattice_gauge::{
    ExactSpectrum, GaugeConfiguration, IntegralRepresentation, Lattice, Link, Plaquette,
};
use holonic_engine::structure_group::{GroupElement, OrientedEdge, StructureGroup};

// -------------------------------------------------------------------------------------------------
// the material
// -------------------------------------------------------------------------------------------------

/// The `extent × extent` periodic lattice. The extent is a **declared fixture level**: one number,
/// stated here where the material is declared, and never inside the organ.
fn torus(extent: u64) -> Lattice {
    let vertex = move |row: u64, column: u64| extent * (row % extent) + (column % extent);
    let x_link = move |row: u64, column: u64| 100 + vertex(row, column);
    let y_link = move |row: u64, column: u64| 200 + vertex(row, column);
    let mut links = Vec::new();
    let mut plaquettes = Vec::new();
    for row in 0..extent {
        for column in 0..extent {
            links.push(Link {
                id: x_link(row, column),
                tail: vertex(row, column),
                head: vertex(row, column + 1),
            });
            links.push(Link {
                id: y_link(row, column),
                tail: vertex(row, column),
                head: vertex(row + 1, column),
            });
            plaquettes.push(Plaquette {
                id: vertex(row, column),
                walk: vec![
                    OrientedEdge::forward(x_link(row, column)),
                    OrientedEdge::forward(y_link(row, column + 1)),
                    OrientedEdge::backward(x_link(row + 1, column)),
                    OrientedEdge::backward(y_link(row, column)),
                ],
            });
        }
    }
    Lattice::declare(links, plaquettes).expect("the torus closes")
}

fn quaternion(coefficients: [i8; 4]) -> GroupElement {
    GroupElement::Quaternion(coefficients)
}

fn configuration(group: StructureGroup, carried: &[(u64, GroupElement)]) -> GaugeConfiguration {
    let lattice = torus(3);
    let identity = group.identity().clone();
    let assignment: Vec<(u64, GroupElement)> = lattice
        .links()
        .map(|link| {
            let element = carried
                .iter()
                .find(|(id, _)| *id == link.id)
                .map_or_else(|| identity.clone(), |(_, element)| element.clone());
            (link.id, element)
        })
        .collect();
    GaugeConfiguration::declare(lattice, group, assignment).expect("every link carries")
}

fn written(element: &GroupElement) -> String {
    let GroupElement::Quaternion([a, b, c, d]) = element else {
        return format!("{element:?}");
    };
    let names = [("", *a), ("i", *b), ("j", *c), ("k", *d)];
    let mut out = String::new();
    for (name, value) in names {
        if value == 0 {
            continue;
        }
        if value < 0 {
            out.push('-');
        } else if !out.is_empty() {
            out.push('+');
        }
        if name.is_empty() || value.abs() != 1 {
            out.push_str(&value.abs().to_string());
        }
        out.push_str(name);
    }
    if out.is_empty() {
        out.push('0');
    }
    out
}

fn print_spectrum(label: &str, spectrum: &ExactSpectrum) {
    let placed: Vec<String> = spectrum
        .rational_eigenvalues
        .iter()
        .map(|(value, multiplicity)| format!("{value}^{multiplicity}"))
        .collect();
    let intervals: Vec<String> = spectrum.intervals.iter().map(ToString::to_string).collect();
    println!(
        "  {label:<24} extent {}  eigenvalues [{}]  accounted {}",
        spectrum.extent,
        placed.join(", "),
        spectrum.accounted()
    );
    println!(
        "  {:<24} intervals between consecutive eigenvalues [{}]  completely rational {}",
        "",
        intervals.join(", "),
        spectrum.is_completely_rational()
    );
}

// -------------------------------------------------------------------------------------------------

fn main() {
    println!("== a lattice gauge configuration, read through structure_group ==");

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the group and its exact integral representation --");
    let group = StructureGroup::close(
        [quaternion([0, 1, 0, 0]), quaternion([0, 0, 1, 0])],
        8,
    )
    .expect("Q8 closes at order eight");
    println!(
        "  <i, j> closes at order {}, abelian {}",
        group.order(),
        group.is_abelian()
    );
    let derived = group.commutator_subgroup().expect("the group closes");
    let named: Vec<String> = derived.iter().map(written).collect();
    println!("  the derived subgroup [G, G] = {{{}}}", named.join(", "));

    let representation = IntegralRepresentation::natural(&group).expect("the law holds");
    println!(
        "  the natural representation: dimension {}, faithful {}, {} distinct character values",
        representation.dimension(),
        representation.is_faithful(),
        representation.distinct_character_values()
    );
    println!("  the homomorphism law was checked over all {} pairs at construction", group.order() * group.order());
    let mut seen = BTreeSet::new();
    for element in group.elements() {
        let class = group.conjugacy_class(element).expect("the class exists");
        if !seen.insert(class.clone()) {
            continue;
        }
        println!(
            "    class {:<6} chi = {:<4} Wilson weight 1 - chi/dim = {}",
            written(&class),
            representation.character(element).expect("the character exists"),
            representation
                .plaquette_weight(element)
                .expect("the weight exists")
        );
    }

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the configuration --");
    let twisted = configuration(
        group.clone(),
        &[
            (100, quaternion([0, 1, 0, 0])),
            (201, quaternion([0, 0, 1, 0])),
            (104, quaternion([-1, 0, 0, 0])),
        ],
    );
    println!(
        "  a 3x3 torus: {} vertices, {} links, {} plaquettes",
        twisted.lattice().vertices().len(),
        twisted.lattice().links().count(),
        twisted.lattice().plaquettes().len()
    );
    let holonomies = twisted.plaquette_holonomies().expect("the walks close");
    let classes = twisted.plaquette_classes().expect("the walks close");
    let written_holonomies: Vec<String> = holonomies.iter().map(written).collect();
    let written_classes: Vec<String> = classes.iter().map(written).collect();
    println!("  plaquette holonomies (frame-relative) [{}]", written_holonomies.join(", "));
    println!("  their conjugacy classes (the invariant) [{}]", written_classes.join(", "));
    let action = twisted.wilson_action(&representation).expect("the weights exist");
    println!("  the Wilson action S = sum_p (1 - chi(U_p)/dim) = {action}");

    let contribution = twisted.commutator_contribution().expect("the group closes");
    println!(
        "  the commutator contribution: {} of {} plaquette pairs do not commute",
        contribution.nonidentity.len(),
        contribution.pairs_read
    );
    for (left, right, commutator) in contribution.nonidentity.iter().take(4) {
        println!(
            "    [F(p{left}), F(p{right})] = {}   -- the discrete a ^ a, as an element",
            written(commutator)
        );
    }
    println!(
        "  and {} pair(s) the abelianization identifies and the group separates:",
        contribution.separated.len()
    );
    for pair in &contribution.separated {
        println!(
            "    p{} and p{} share {} in G/[G,G] and split into {} against {}",
            pair.left,
            pair.right,
            written(&pair.shared_abelianized),
            written(&pair.left_class),
            written(&pair.right_class)
        );
    }

    let distribution = twisted.class_distribution().expect("the walks close");
    let shares: Vec<String> = distribution
        .iter()
        .map(|(class, share)| format!("{} {share}", written(class)))
        .collect();
    println!("  the empirical class distribution: {}", shares.join(", "));
    let spectrum = twisted.transfer_spectrum().expect("the operator diagonalizes");
    print_spectrum("the configuration", &spectrum);
    println!(
        "  NOT a gap claim: one lattice, no spacing parameter, no volume family, no correlation \
         scaling."
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 1: a gauge-equivalent pair --");
    let turns = [
        quaternion([1, 0, 0, 0]),
        quaternion([0, 1, 0, 0]),
        quaternion([0, 0, 1, 0]),
        quaternion([0, 0, 0, 1]),
        quaternion([-1, 0, 0, 0]),
    ];
    let gauge: BTreeMap<u64, GroupElement> = twisted
        .lattice()
        .vertices()
        .into_iter()
        .map(|vertex| (vertex, turns[vertex as usize % turns.len()].clone()))
        .collect();
    let moved = twisted.gauge_transformed(&gauge).expect("every vertex is named");
    let differing: Vec<u64> = twisted
        .lattice()
        .links()
        .filter(|link| twisted.carried(link.id).ok() != moved.carried(link.id).ok())
        .map(|link| link.id)
        .collect();
    println!(
        "  the transformation moved {} of {} links (a transformation that moved none proves \
         nothing)",
        differing.len(),
        twisted.lattice().links().count()
    );
    let moved_holonomies: Vec<String> = moved
        .plaquette_holonomies()
        .expect("the walks close")
        .iter()
        .map(written)
        .collect();
    println!("  the holonomies themselves moved: [{}]", moved_holonomies.join(", "));
    println!(
        "  the classes did not: {}",
        moved.plaquette_classes().expect("the walks close") == classes
    );
    let moved_action = moved.wilson_action(&representation).expect("the weights exist");
    let moved_spectrum = moved.transfer_spectrum().expect("the operator diagonalizes");
    println!("  action {action} against {moved_action}   equal {}", action == moved_action);
    println!(
        "  spectrum equal {}",
        spectrum == moved_spectrum
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 2: a deliberately altered link --");
    let altered = twisted
        .with_link(200, quaternion([0, 1, 0, 0]))
        .expect("i is in Q8");
    let altered_action = altered.wilson_action(&representation).expect("the weights exist");
    let altered_spectrum = altered.transfer_spectrum().expect("the operator diagonalizes");
    let altered_holonomies: Vec<String> = altered
        .plaquette_holonomies()
        .expect("the walks close")
        .iter()
        .map(written)
        .collect();
    println!("  link 200 set to i; holonomies [{}]", altered_holonomies.join(", "));
    println!(
        "  action {action} -> {altered_action}   moved {}",
        action != altered_action
    );
    print_spectrum("after the alteration", &altered_spectrum);
    println!("  spectrum moved {}", spectrum != altered_spectrum);

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- control 3: the abelian restriction --");
    let cyclic = StructureGroup::close([quaternion([0, 1, 0, 0])], 4).expect("<i> closes");
    println!(
        "  <i> closes at order {}, abelian {}",
        cyclic.order(),
        cyclic.is_abelian()
    );
    let abelian = configuration(
        cyclic,
        &[
            (100, quaternion([0, 1, 0, 0])),
            (104, quaternion([-1, 0, 0, 0])),
        ],
    );
    let abelian_holonomies: Vec<String> = abelian
        .plaquette_holonomies()
        .expect("the walks close")
        .iter()
        .map(written)
        .collect();
    println!("  holonomies [{}]", abelian_holonomies.join(", "));
    let erased = abelian.commutator_contribution().expect("the group closes");
    println!(
        "  {} of {} pairs do not commute; separating pairs {}; the contribution is empty {}",
        erased.nonidentity.len(),
        erased.pairs_read,
        erased.separated.len(),
        erased.is_empty()
    );
    let abelian_representation =
        IntegralRepresentation::natural(abelian.connection().group()).expect("the law holds");
    let abelian_action = abelian
        .wilson_action(&abelian_representation)
        .expect("the weights exist");
    println!(
        "  and the reading is not erased with it: S = {abelian_action}, non-zero {}",
        !abelian_action.is_zero()
    );
    print_spectrum("the abelian control", &abelian.transfer_spectrum().expect("it diagonalizes"));

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the refusals the organ owes --");
    let partial = BTreeMap::from([(0u64, quaternion([0, 1, 0, 0]))]);
    println!(
        "  a gauge transformation missing a vertex: {:?}",
        twisted.gauge_transformed(&partial).err()
    );
    let open = Lattice::declare(
        [Link { id: 1, tail: 0, head: 1 }, Link { id: 2, tail: 1, head: 2 }],
        [Plaquette {
            id: 7,
            walk: vec![OrientedEdge::forward(1), OrientedEdge::forward(2)],
        }],
    );
    println!("  a plaquette that does not close: {:?}", open.err());
    println!(
        "  a link the configuration never assigned: {:?}",
        GaugeConfiguration::declare(
            torus(3),
            StructureGroup::close([quaternion([0, 1, 0, 0])], 4).expect("<i> closes"),
            vec![(100u64, quaternion([0, 1, 0, 0]))],
        )
        .err()
    );

    // ---------------------------------------------------------------------------------------
    println!();
    println!("-- the transfer operator itself --");
    let (order, operator) = twisted.transfer_operator().expect("the operator builds");
    let names: Vec<String> = order.iter().map(written).collect();
    println!("  rows and columns in the group's own order: [{}]", names.join(", "));
    for row in 0..operator.rows() {
        let entries: Vec<String> = operator
            .row(row)
            .expect("the row exists")
            .iter()
            .map(ToString::to_string)
            .collect();
        println!("    {:<4} [{}]", names[row], entries.join(", "));
    }
    let mut totals = BTreeSet::new();
    for row in 0..operator.rows() {
        totals.insert(
            operator
                .row(row)
                .expect("the row exists")
                .iter()
                .fold(Rat::zero(), |sum, entry| sum + entry),
        );
    }
    let written_totals: Vec<String> = totals.iter().map(ToString::to_string).collect();
    println!(
        "  every row carries the same total: {} ({})",
        totals.len() == 1,
        written_totals.join(", ")
    );
    let characteristic: Vec<String> = spectrum
        .characteristic
        .coefficients()
        .iter()
        .map(ToString::to_string)
        .collect();
    println!(
        "  the characteristic polynomial, ascending: [{}]",
        characteristic.join(", ")
    );
}
