//! `skein -> substitution_realizers -> placement`, driven end to end through step 1's organ.
//!
//! `blueprint/THE_ASSEMBLY.md` steps 1 and 2 in one run, on one carrier:
//!
//! ```text
//!   GradedCausalComplex  --ComplexSystem-->  ObservedSystem   (step 1: dilated sections as
//!                                                              receivers, conduct across 1-cells)
//!   skein::Substitution  --read_and_realize-->  SubstitutionRealizers   (step 2: a declared move
//!                                                              is a realizer; its landings are
//!                                                              what it added)
//!   SubstitutionRealizers --place_substitutions--> SubstitutionPlacement
//! ```
//!
//! Until this driver existed the chain ran only inside `#[cfg(test)]`, and step 2 reached step 1
//! through two `const fn` newtype rewraps and nothing else. `CLAUDE.md` §9b: *work that joins
//! partials outranks work that perfects one organ.*
//!
//! The material is the hollow tetrahedron — four vertices, six edges, and four candidate triangles
//! that are cells of the complex but are **not** in every declared subcomplex. That is what makes a
//! substitution here a real move: filling `012` is a choice, swapping it for `013` is another, and
//! filling both at once deposits two cells the receiver family cannot tell apart.
//!
//! What is printed is the population, never a total: every declared move with its landings, every
//! conduct class with its member cells by name, every standing class with the declared moves that
//! paid for it, every OPEN class with its obstruction, the exact per-context remainders, the
//! realizer-against-class incidence, and the resting form of the deposit.
//!
//! Run with `PATH=/opt/cuda/bin:$PATH cargo run -p holonic-engine --example
//! substitution_realizer_placement`.

use std::collections::BTreeSet;

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::complex_system::{cell as cell_of_item, AddressReading, ComplexSystem};
use holonic_engine::dilation::{dilate, Horizon, WalkOrder};
use holonic_engine::placement::{discharge, Discharge, Placement};
use holonic_engine::rebase_invariants::PivotRule;
use holonic_engine::receiver_exact_compression::ReceiverId;
use holonic_engine::skein::Substitution;
use holonic_engine::substitution_realizers::{
    discharge_substitutions, place_substitutions, read_and_realize, RealizerAdmission,
    SubstitutionDischarge, SubstitutionPlacement, SubstitutionRealizers,
};
use holonic_engine::supported_realizers::{incidence, positive_form};

// ---------------------------------------------------------------------------------------------
// the material

struct Tetrahedron {
    complex: GradedCausalComplex,
    vertices: Vec<CausalCellId>,
    edges: Vec<CausalCellId>,
    faces: Vec<CausalCellId>,
}

fn source() -> BTreeSet<EventId> {
    BTreeSet::from([EventId(1)])
}

/// Four vertices, six edges, four triangles. `found_cell` refuses any boundary whose own boundary
/// is nonzero, so `e_ij + e_jk - e_ik` is checked rather than asserted.
fn tetrahedron() -> Tetrahedron {
    let mut complex = GradedCausalComplex::default();
    let vertices: Vec<CausalCellId> = (0..4)
        .map(|index| {
            complex
                .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                .expect("a vertex has no boundary")
        })
        .collect();

    let pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
    let edges: Vec<CausalCellId> = pairs
        .iter()
        .map(|(tail, head)| {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[*head], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertices[*tail], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{tail}{head}"), source(), 1, boundary)
                .expect("an edge closes")
        })
        .collect();
    let edge_of = |left: usize, right: usize| {
        edges[pairs
            .iter()
            .position(|pair| *pair == (left, right))
            .expect("the pair is one of the six")]
    };

    let faces: Vec<CausalCellId> = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
        .iter()
        .map(|(low, mid, high)| {
            let mut boundary = CausalChain::default();
            boundary.add_term(edge_of(*low, *mid), ComparativeMultiplicity::positive(1u32));
            boundary.add_term(edge_of(*mid, *high), ComparativeMultiplicity::positive(1u32));
            boundary.add_term(edge_of(*low, *high), ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("f{low}{mid}{high}"), source(), 2, boundary)
                .expect("e_lm + e_mh - e_lh is a cycle")
        })
        .collect();

    Tetrahedron {
        complex,
        vertices,
        edges,
        faces,
    }
}

impl Tetrahedron {
    fn skeleton(&self) -> BTreeSet<CausalCellId> {
        self.vertices.iter().chain(self.edges.iter()).copied().collect()
    }

    fn edge(&self, left: usize, right: usize) -> CausalCellId {
        let pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
        self.edges[pairs
            .iter()
            .position(|pair| *pair == (left, right))
            .expect("the pair is one of the six")]
    }

    /// The closed subcomplex carrying one triangle and everything it is attached to.
    fn disc(&self, face: usize, corners: [usize; 3], sides: [(usize, usize); 3]) -> BTreeSet<CausalCellId> {
        let mut support: BTreeSet<CausalCellId> =
            corners.iter().map(|corner| self.vertices[*corner]).collect();
        for (left, right) in sides {
            support.insert(self.edge(left, right));
        }
        support.insert(self.faces[face]);
        support
    }

    fn rim(&self, corners: [usize; 3], sides: [(usize, usize); 3]) -> BTreeSet<CausalCellId> {
        let mut support: BTreeSet<CausalCellId> =
            corners.iter().map(|corner| self.vertices[*corner]).collect();
        for (left, right) in sides {
            support.insert(self.edge(left, right));
        }
        support
    }
}

fn name(complex: &GradedCausalComplex, cell: CausalCellId) -> String {
    complex
        .cell(cell)
        .map_or_else(|_| format!("{cell:?}"), |body| body.name.clone())
}

fn names(
    complex: &GradedCausalComplex,
    cells: impl IntoIterator<Item = CausalCellId>,
) -> String {
    let listed: Vec<String> = cells.into_iter().map(|cell| name(complex, cell)).collect();
    if listed.is_empty() {
        "-".to_owned()
    } else {
        listed.join(" ")
    }
}

// ---------------------------------------------------------------------------------------------
// the declared moves

/// Every move, in declared order. The swap is first so that a one-move family read at `EveryRead`
/// and the whole family read at `Invisible` hand `place` the same realizer — which is how the two
/// frames below come out bit-identical as placements.
fn declared(world: &Tetrahedron) -> Vec<(&'static str, Substitution)> {
    let skeleton = world.skeleton();
    let disc_012 = world.disc(0, [0, 1, 2], [(0, 1), (1, 2), (0, 2)]);
    let disc_013 = world.disc(1, [0, 1, 3], [(0, 1), (1, 3), (0, 3)]);
    let rim_012 = world.rim([0, 1, 2], [(0, 1), (1, 2), (0, 2)]);
    let rim_023 = world.rim([0, 2, 3], [(0, 2), (2, 3), (0, 3)]);

    let mut both_faces = skeleton.clone();
    both_faces.insert(world.faces[0]);
    both_faces.insert(world.faces[1]);

    let mut three_faces = skeleton.clone();
    for face in 0..3 {
        three_faces.insert(world.faces[face]);
    }
    let mut sphere = three_faces.clone();
    sphere.insert(world.faces[3]);

    let mut filled_012 = rim_012.clone();
    filled_012.insert(world.faces[0]);
    let mut filled_023 = rim_023.clone();
    filled_023.insert(world.faces[2]);

    let ends_23 = BTreeSet::from([world.vertices[2], world.vertices[3]]);
    let mut with_e23 = ends_23.clone();
    with_e23.insert(world.edge(2, 3));

    vec![
        (
            "swap the disc on 012 for the disc on 013",
            Substitution {
                boundary: BTreeSet::from([world.vertices[0], world.vertices[1], world.edge(0, 1)]),
                before: disc_012,
                after: disc_013,
            },
        ),
        (
            "fill the rim 012 with its triangle",
            Substitution {
                boundary: rim_012.clone(),
                before: rim_012,
                after: filled_012,
            },
        ),
        (
            "fill the rim 023 with its triangle",
            Substitution {
                boundary: rim_023.clone(),
                before: rim_023,
                after: filled_023,
            },
        ),
        (
            "fill the skeleton with BOTH 012 and 013 at once",
            Substitution {
                boundary: skeleton.clone(),
                before: skeleton.clone(),
                after: both_faces,
            },
        ),
        (
            "close the sphere: the fourth triangle onto three",
            Substitution {
                boundary: skeleton,
                before: three_faces,
                after: sphere,
            },
        ),
        (
            "grow the edge e23 between two loose vertices",
            Substitution {
                boundary: ends_23.clone(),
                before: ends_23,
                after: with_e23,
            },
        ),
        (
            "REFUSED: a triangle without the edges it hangs from",
            Substitution {
                boundary: BTreeSet::from([world.vertices[0], world.vertices[1]]),
                before: BTreeSet::from([world.vertices[0], world.vertices[1]]),
                after: BTreeSet::from([world.vertices[0], world.vertices[1], world.faces[0]]),
            },
        ),
    ]
}

/// Three contexts that are three different readings.
///
/// `v0 v2 v3 e02 e03` is an arc: depositing `e23` against it **closes a cycle**, while against four
/// loose vertices the same deposit **joins two components**. One move, two different exact
/// remainders, and the whole 1-skeleton blind to it because it already holds the edge.
fn narrow_contexts(world: &Tetrahedron) -> Vec<BTreeSet<CausalCellId>> {
    vec![
        world.vertices.iter().copied().collect(),
        BTreeSet::from([
            world.vertices[0],
            world.vertices[2],
            world.vertices[3],
            world.edge(0, 2),
            world.edge(0, 3),
        ]),
        world.skeleton(),
    ]
}

/// The same three, plus a context that already holds one of the swap's two fillings. Nothing about
/// the moves changed; what changed is who is looking.
fn wide_contexts(world: &Tetrahedron) -> Vec<BTreeSet<CausalCellId>> {
    let mut family = narrow_contexts(world);
    let mut with_face = world.skeleton();
    with_face.insert(world.faces[0]);
    family.push(with_face);
    family
}

// ---------------------------------------------------------------------------------------------
// the printing — the population, never a total

fn print_conduct(complex: &GradedCausalComplex, placement: &Placement) {
    println!(
        "conduct classes ({} of them, over {} receivers):",
        placement.class_extent, placement.receiver_extent
    );
    for (class, members) in placement.compression.conduct.blocks.iter().enumerate() {
        println!(
            "  class {class:2}  {}",
            names(complex, members.iter().copied().map(cell_of_item))
        );
    }
    if placement.compression.collapsed.is_empty() {
        println!("  conduct is exact on this material: nothing the one-shot reading merged survived it");
    } else {
        println!("  cells the receivers merged and conduct then separated, each with the word that did it:");
        for pair in &placement.compression.collapsed {
            println!(
                "    {} ~ {}   word {:?}   by-terminus {}",
                name(complex, cell_of_item(pair.left)),
                name(complex, cell_of_item(pair.right)),
                pair.distinguishing_word,
                pair.separated_by_terminus
            );
        }
    }
}

fn print_population(
    complex: &GradedCausalComplex,
    labels: &[&str],
    founded: &SubstitutionRealizers,
) {
    println!("the declared population, read against {} contexts:", founded.contexts.len());
    for realizer in &founded.realizers {
        println!(
            "  [{}] {}",
            realizer.declared, labels[realizer.declared]
        );
        println!(
            "        realizer {:?}   deposits {}   withdraws {}",
            realizer.realizer,
            names(complex, realizer.landings.iter().copied()),
            names(complex, realizer.withdrawn.iter().copied())
        );
        let admitted: Vec<&str> = [
            (RealizerAdmission::EveryRead, "every-read"),
            (RealizerAdmission::Invisible, "invisible"),
            (RealizerAdmission::Visible, "visible"),
        ]
        .iter()
        .filter(|(admission, _)| realizer.admitted_under(*admission))
        .map(|(_, label)| *label)
        .collect();
        println!("        admitted at: {}", admitted.join(" "));
        let reading = realizer.reading.as_ref().expect("read against a complex");
        for verdict in &reading.verdicts {
            if verdict.remainder.is_empty() {
                println!(
                    "        context {}: invariant   betti {:?}",
                    verdict.context,
                    verdict.before.betti_vector()
                );
                continue;
            }
            for moved in &verdict.remainder {
                println!(
                    "        context {}: grade {} betti {:+}  torsion +{:?} -{:?}   betti {:?} -> {:?}",
                    verdict.context,
                    moved.grade,
                    moved.betti_change,
                    moved.torsion_gained,
                    moved.torsion_lost,
                    verdict.before.betti_vector(),
                    verdict.after.betti_vector()
                );
            }
        }
    }
    for refused in &founded.refused {
        println!(
            "  [{}] {}\n        REFUSED {:?}\n        the move is still in the deposit: before {} after {}",
            refused.declared,
            labels[refused.declared],
            refused.refusal,
            names(complex, refused.substitution.before.iter().copied()),
            names(complex, refused.substitution.after.iter().copied()),
        );
    }
}

fn print_placement(
    complex: &GradedCausalComplex,
    labels: &[&str],
    founded: &SubstitutionRealizers,
    placed: &SubstitutionPlacement,
) {
    let placement = &placed.placement;
    println!(
        "placement at aperture {:?}: {} declared, {:?} admitted",
        placed.admission,
        placed.declared.len(),
        placed.admitted
    );
    for standing in &placement.standing {
        println!(
            "  STANDING class {:2}  {}",
            standing.class,
            names(complex, standing.members.iter().copied().map(cell_of_item)),
        );
        for realizer in &standing.realizers {
            // Read the realizer id back through the DEPOSIT rather than through the caller's own
            // array. A `Placement` carries only `RealizerId`s, so this is the whole link from a
            // standing class to the move that paid for it, and the deposited move is what closes it.
            let position = realizer.0 as usize;
            let deposited = founded
                .declared_at(position)
                .unwrap_or_else(|| panic!("declared position {position} is not in the deposit"));
            println!(
                "              paid for by [{position}] {}\n                          deposited move adds {}",
                labels[position],
                names(
                    complex,
                    deposited.after.difference(&deposited.before).copied()
                )
            );
        }
    }
    for open in &placement.open {
        let obstruction = match &open.reached_only_in_multiple {
            None => "nothing reached it".to_owned(),
            Some(factor) => format!("reached only as {factor}·c — rational, not integral"),
        };
        println!(
            "  OPEN     class {:2}  {}\n              {obstruction}",
            open.class,
            names(complex, open.members.iter().copied().map(cell_of_item))
        );
    }
    println!(
        "  support: rank {}  invariant factors {:?}  free obstruction {}  torsion obstruction {:?}",
        placement.support.supported_rank,
        placement.support.invariant_factors,
        placement.support.free_obstruction(),
        placement.support.torsion_obstruction()
    );
}

fn print_incidence(
    labels: &[&str],
    founded: &SubstitutionRealizers,
    placed: &SubstitutionPlacement,
) {
    let realizations = founded.realizations_under(
        placed.admission,
        &placed.placement.compression.conduct,
    );
    let matrix = incidence(&realizations, placed.placement.class_extent);
    let form = positive_form(&matrix);
    println!("the realizer-against-class incidence, exact:");
    for (row, realization) in realizations.iter().enumerate() {
        let landings: Vec<String> = (0..matrix.columns())
            .filter(|class| !matrix.at(row, *class).to_string().eq("0"))
            .map(|class| format!("class {class}: {}", matrix.at(row, class)))
            .collect();
        println!(
            "  {:?} [{}] {:<48}  {}",
            realization.realizer,
            realization.realizer.0,
            labels[realization.realizer.0 as usize],
            landings.join("  ")
        );
    }
    let diagonal: Vec<String> = (0..form.columns())
        .filter(|class| !form.at(*class, *class).to_string().eq("0"))
        .map(|class| format!("({class}) {}", form.at(class, class)))
        .collect();
    println!(
        "  the positive form M^T M, nonzero diagonal — |M e_c|^2 per class: {}",
        diagonal.join("  ")
    );
}

// ---------------------------------------------------------------------------------------------

fn main() {
    let world = tetrahedron();
    let complex = &world.complex;

    println!("================ the material ================");
    for body in complex.cells().values() {
        println!(
            "  {:>5}  grade {}  boundary {}",
            body.name,
            body.grade,
            names(complex, body.boundary.support())
        );
    }

    // ------------------------------------------------------------------ step 1: the receivers
    let receivers = vec![
        dilate(complex, world.vertices[0], Horizon::Unbounded, WalkOrder::Breadth)
            .expect("v0 is a cell"),
        dilate(complex, world.vertices[1], Horizon::Unbounded, WalkOrder::Breadth)
            .expect("v1 is a cell"),
    ];
    println!("\n================ step 1: the receivers ================");
    for (index, section) in receivers.iter().enumerate() {
        println!(
            "  receiver {index}  focus {}  horizon {:?}  order {:?}  holds {} cells  covering {}",
            name(complex, section.lineage.focus),
            section.lineage.horizon,
            section.lineage.order,
            section.support.len(),
            section.lineage.is_covering()
        );
    }
    let system = ComplexSystem::declare(
        complex,
        AddressReading::Metric,
        receivers,
        ComplexSystem::every_one_cell(complex),
    )
    .expect("the sections were measured on this complex and the inputs are its own 1-cells");
    println!(
        "  conduct steps across {} declared 1-cells: {}",
        system.inputs.len(),
        names(complex, system.inputs.iter().copied())
    );
    for receiver in 0..system.receivers.len() {
        let addresses = system.addresses(ReceiverId(receiver as u64));
        let spelled: Vec<String> = addresses
            .iter()
            .map(|(cell, address)| format!("{}:{}", name(complex, *cell), address.0))
            .collect();
        println!("  receiver {receiver} addresses: {}", spelled.join(" "));
    }

    // ------------------------------------------------------------------ step 2: the moves
    let moves = declared(&world);
    let labels: Vec<&str> = moves.iter().map(|(label, _)| *label).collect();
    let substitutions: Vec<Substitution> =
        moves.iter().map(|(_, move_made)| move_made.clone()).collect();

    let narrow = read_and_realize(
        complex,
        &substitutions,
        &narrow_contexts(&world),
        PivotRule::FirstNonzero,
    );

    println!("\n================ step 2: the declared population ================");
    for (index, context) in narrow.contexts.iter().enumerate() {
        println!("  context {index}: {}", names(complex, context.iter().copied()));
    }
    print_population(complex, &labels, &narrow);

    // `close the sphere` carries three non-boundary cells across itself, so on this material
    // `added()` and `after - boundary` are different sets and the move must be charged for the one
    // cell it deposited. Stated here because the driver is where the real material is.
    let closing = narrow
        .realizers
        .iter()
        .find(|realizer| realizer.declared == 4)
        .expect("the sphere-closing move was read");
    println!(
        "  the separator on this material: [4] deposits {} while `after - boundary` is {}",
        names(complex, closing.landings.iter().copied()),
        names(
            complex,
            closing
                .substitution
                .after
                .difference(&closing.substitution.boundary)
                .copied()
        )
    );
    assert_eq!(closing.landings, BTreeSet::from([world.faces[3]]));
    assert_eq!(
        closing
            .substitution
            .after
            .difference(&closing.substitution.boundary)
            .count(),
        4,
        "four cells sit outside this move's boundary and it deposited exactly one of them"
    );

    let wide_open = place_substitutions(&system, &narrow, RealizerAdmission::EveryRead);
    println!("\n================ the conduct the moves are placed against ================");
    print_conduct(complex, &wide_open.placement);

    println!("\n================ placement ================");
    print_placement(complex, &labels, &narrow, &wide_open);
    println!();
    print_incidence(&labels, &narrow, &wide_open);

    let withheld = place_substitutions(&system, &narrow, RealizerAdmission::Invisible);
    println!();
    print_placement(complex, &labels, &narrow, &withheld);

    // ------------------------------------------------------------------ the integral question
    let doubled = read_and_realize(
        complex,
        &substitutions[3..4],
        &narrow_contexts(&world),
        PivotRule::FirstNonzero,
    );
    let doubled_placed = place_substitutions(&system, &doubled, RealizerAdmission::EveryRead);
    println!("\n================ the integral-versus-rational split, alone ================");
    println!(
        "one move, depositing two cells the receiver family cannot tell apart: {}",
        names(complex, doubled.realizers[0].landings.iter().copied())
    );
    print_placement(complex, &labels[3..4], &doubled, &doubled_placed);

    // ------------------------------------------------------------------ the apertures
    let one_move = read_and_realize(
        complex,
        &substitutions[..1],
        &narrow_contexts(&world),
        PivotRule::FirstNonzero,
    );
    let a_before = place_substitutions(&system, &one_move, RealizerAdmission::EveryRead);
    let a_after = place_substitutions(&system, &narrow, RealizerAdmission::EveryRead);
    let b_before = place_substitutions(&system, &narrow, RealizerAdmission::Invisible);
    let b_after = place_substitutions(&system, &narrow, RealizerAdmission::EveryRead);

    println!("\n================ two frames placement alone cannot tell apart ================");
    println!(
        "  FRAME A  declared 1 move  -> declared {} moves, both at every-read",
        a_after.declared.len()
    );
    println!(
        "  FRAME B  the same {} moves, at invisible -> at every-read",
        b_after.declared.len()
    );
    println!(
        "  the two BEFORE placements are bit-identical: {}",
        a_before.placement == b_before.placement
    );
    println!(
        "  the two AFTER  placements are bit-identical: {}",
        a_after.placement == b_after.placement
    );
    println!(
        "  placement::discharge          A {:?}   B {:?}   <- the same answer for both",
        discharge(&a_before.placement, &a_after.placement),
        discharge(&b_before.placement, &b_after.placement)
    );
    println!(
        "  discharge_substitutions       A {:?}   B {:?}   <- the realizer aperture, carried",
        discharge_substitutions(&a_before, &a_after),
        discharge_substitutions(&b_before, &b_after)
    );

    // A third route to the same non-production: the declared family and the filter both held
    // fixed, and a CONTEXT withdrawn. Nothing was produced; a move became legible.
    let looked_harder = read_and_realize(
        complex,
        &substitutions,
        &wide_contexts(&world),
        PivotRule::FirstNonzero,
    );
    let c_before = place_substitutions(&system, &looked_harder, RealizerAdmission::Invisible);
    let c_after = place_substitutions(&system, &narrow, RealizerAdmission::Invisible);
    println!(
        "\n  FRAME C  one family, one filter, {} contexts -> {} contexts",
        c_before.contexts.len(),
        c_after.contexts.len()
    );
    println!(
        "  the swap compresses under the {}-context family and is visible to the {}-context one, so \
         withdrawing a context ADMITS it — with nothing declared and the filter untouched",
        c_after.contexts.len(),
        c_before.contexts.len()
    );
    println!("  admitted {:?} -> {:?}", c_before.admitted, c_after.admitted);
    println!(
        "  placement::discharge          C {:?}",
        discharge(&c_before.placement, &c_after.placement)
    );
    println!(
        "  discharge_substitutions       C {:?}",
        discharge_substitutions(&c_before, &c_after)
    );

    // The driver is falsifiable, not decorative: if the composition regresses, this exits nonzero.
    assert_eq!(a_before.placement, b_before.placement);
    assert_eq!(a_after.placement, b_after.placement);
    assert_eq!(discharge(&a_before.placement, &a_after.placement), Discharge::Founded);
    assert_eq!(discharge(&b_before.placement, &b_after.placement), Discharge::Founded);
    assert_eq!(discharge(&c_before.placement, &c_after.placement), Discharge::Founded);
    assert_eq!(
        discharge_substitutions(&a_before, &a_after),
        SubstitutionDischarge::Founded
    );
    assert_eq!(
        discharge_substitutions(&b_before, &b_after),
        SubstitutionDischarge::Widened
    );
    assert_eq!(
        discharge_substitutions(&c_before, &c_after),
        SubstitutionDischarge::Widened
    );
    assert_eq!(
        doubled_placed.placement.support.torsion_obstruction(),
        vec![num_bigint::BigInt::from(2)],
        "two indistinguishable cells deposited at once is a Z/2 and must stay one"
    );

    // ------------------------------------------------------------------ the deposit
    println!("\n================ the deposit, at rest ================");
    let rested = ron::to_string(&narrow).expect("the population rests");
    let remounted: SubstitutionRealizers =
        ron::from_str(&rested).expect("and remounts from its own octets");
    let exact = remounted == narrow;
    let places_the_same = [
        RealizerAdmission::EveryRead,
        RealizerAdmission::Invisible,
        RealizerAdmission::Visible,
    ]
    .iter()
    .all(|admission| {
        place_substitutions(&system, &remounted, *admission)
            == place_substitutions(&system, &narrow, *admission)
    });
    println!("  round trip exact: {exact}   octets: {}", rested.len());
    println!("  the remounted deposit places identically at every aperture: {places_the_same}");
    assert!(exact && places_the_same);
    println!("\n{rested}");
}
