//! `substitution_realizers -> incidence -> positive_form -> inertia`, on a real realizer population.
//!
//! `CLAUDE.md` §2 states the chain this closes, and it is the project's own construction-selection
//! principle:
//!
//! ```text
//!   an ample divisor class (a supported realizer that PAID)
//!     -> a polarization
//!     -> the Rosati involution, POSITIVE
//!     -> positivity of the trace form
//!     -> |alpha| = q^(1/2)          placement, as a RETURN
//! ```
//!
//! *"Do not build modal placement and supported lifting as two organs. **Derive placement from
//! realization.**"* `supported_realizers::induced_placement` is that derivation in code — it takes an
//! incidence, forms `MᵀM`, and hands it to `inertia::inertia`. Until this driver it had **no caller
//! anywhere**, and its two tests both hand it a matrix typed out by hand. `blueprint/THE_ROADMAP.md`:
//! *"the assertion moved out of `#[cfg(test)]`; the conduct did not."*
//!
//! Here the incidence comes from `skein::Substitution` moves read against a real
//! `GradedCausalComplex`, placed against conduct classes a real `ComplexSystem` returns. Nothing in
//! this file types out a matrix.
//!
//! ## What a null direction is, and the space it lives in
//!
//! `incidence()` builds `M` with **rows = realizers, columns = classes**. So `MᵀM` is indexed by
//! **classes**, and its null space is `{x ∈ ℚ^C : Mx = 0}` — a **class** combination that every
//! declared move pairs to zero with. The realizer combinations that land on nothing are the null
//! space of the *other* Gram matrix, `MMᵀ`, which is `induced_placement` applied to `Mᵀ`.
//!
//! Both are computed and both are named, because they answer different questions and the module's
//! own docstring conflated them until 2026-08-10:
//!
//! ```text
//!   ker(MᵀM)   class space      a combination of classes NO declared move can separate
//!                               nullity = |C| − rank = the FREE OBSTRUCTION
//!   ker(MMᵀ)   realizer space   a combination of moves that lands on NOTHING
//!                               nullity = |R| − rank = the dependencies among the moves
//! ```
//!
//! ## The controls, and what would make each fail
//!
//! ```text
//!   1  split == (rank, 0, nullity), with rank from the SMITH NORMAL FORM over ℤ and the split from
//!      a symmetric elimination over ℚ. Two algorithms over two rings. FAILS if the incidence is
//!      built wrong — and the driver exhibits that failure rather than asserting it away, by feeding
//!      the TRANSPOSED incidence to the same call and showing the nullity it returns is not the
//!      corank of the class family.
//!   2  the hand flips and the split does not. `−(MᵀM)` must return (0, nullity, rank). This is what
//!      makes `negative == 0` above evidence about the material rather than about an elimination
//!      that can only ever count upward. `CLAUDE.md` §2b: state the SPLIT and the HAND separately.
//!   3  every returned null vector is verified: `Mx = 0` componentwise AND `xᵀ(MᵀM)x = 0`, and the
//!      count of independent null vectors must equal the nullity the elimination returned.
//!   4  a law that returns zero proves nothing about itself: the form must be NONZERO on a class a
//!      move actually paid for, and zero on one nothing reached.
//!   5  the aperture is a gauge and the material must move under it: `EveryRead` and `Visible` hand
//!      `place` different realizer populations and must return different splits. A gauge whose
//!      group acts trivially on the declared material is not a gauge.
//!   6  the four pivot orders must agree on the inertia AND walk different schedules. Four identical
//!      schedules are one computation compared with itself four times.
//! ```
//!
//! Run with `PATH=/opt/cuda/bin:$PATH cargo run -p holonic-engine --example
//! the_realizer_places_itself`.

use std::collections::BTreeSet;

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::complex_system::{cell as cell_of_item, AddressReading, ComplexSystem};
use holonic_engine::dilation::{dilate, Horizon, WalkOrder};
use holonic_engine::inertia::{inertia, inertia_with_schedule, Inertia, PivotOrder, SymmetricForm};
use holonic_engine::placement::Placement;
use holonic_engine::rebase_invariants::{smith_normal_form, IntegerMatrix, PivotRule};
use holonic_engine::skein::Substitution;
use holonic_engine::substitution_realizers::{
    place_substitutions, read_and_realize, RealizerAdmission, SubstitutionRealizers,
};
use holonic_engine::supported_realizers::{
    incidence, induced_placement, positive_form, quadratic_value, Realization,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

// ---------------------------------------------------------------------------------------------
// the material: the hollow tetrahedron
//
// Four vertices, six edges, four candidate triangles. The triangles are cells of the complex but
// are NOT in every declared subcomplex, which is what makes filling one a real move rather than a
// relabelling. This is the same material `CLAUDE.md` §11 records the supported-realizer organ
// running on.

struct Tetrahedron {
    complex: GradedCausalComplex,
    vertices: Vec<CausalCellId>,
    edges: Vec<CausalCellId>,
    faces: Vec<CausalCellId>,
}

const PAIRS: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
const TRIPLES: [(usize, usize, usize); 4] = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)];

fn source() -> BTreeSet<EventId> {
    BTreeSet::from([EventId(1)])
}

/// `found_cell` refuses any boundary whose own boundary is nonzero, so `e_lm + e_mh − e_lh` is
/// checked by the complex rather than asserted here.
fn tetrahedron() -> Tetrahedron {
    let mut complex = GradedCausalComplex::default();
    let vertices: Vec<CausalCellId> = (0..4)
        .map(|index| {
            complex
                .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                .expect("a vertex has no boundary")
        })
        .collect();

    let edges: Vec<CausalCellId> = PAIRS
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
        edges[PAIRS
            .iter()
            .position(|pair| *pair == (left, right))
            .expect("the pair is one of the six")]
    };

    let faces: Vec<CausalCellId> = TRIPLES
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
    fn edge(&self, left: usize, right: usize) -> CausalCellId {
        self.edges[PAIRS
            .iter()
            .position(|pair| *pair == (left, right))
            .expect("the pair is one of the six")]
    }

    fn skeleton(&self) -> BTreeSet<CausalCellId> {
        self.vertices
            .iter()
            .chain(self.edges.iter())
            .copied()
            .collect()
    }

    /// The closed rim of one triangle: its three corners and its three sides, without the triangle.
    fn rim(&self, corners: [usize; 3], sides: [(usize, usize); 3]) -> BTreeSet<CausalCellId> {
        let mut support: BTreeSet<CausalCellId> =
            corners.iter().map(|corner| self.vertices[*corner]).collect();
        for (left, right) in sides {
            support.insert(self.edge(left, right));
        }
        support
    }

    fn filled(&self, face: usize, corners: [usize; 3], sides: [(usize, usize); 3]) -> BTreeSet<CausalCellId> {
        let mut support = self.rim(corners, sides);
        support.insert(self.faces[face]);
        support
    }
}

fn name(complex: &GradedCausalComplex, cell: CausalCellId) -> String {
    complex
        .cell(cell)
        .map_or_else(|_| format!("{cell:?}"), |body| body.name.clone())
}

fn names(complex: &GradedCausalComplex, cells: impl IntoIterator<Item = CausalCellId>) -> String {
    let listed: Vec<String> = cells.into_iter().map(|cell| name(complex, cell)).collect();
    if listed.is_empty() {
        "-".to_owned()
    } else {
        listed.join(" ")
    }
}

// ---------------------------------------------------------------------------------------------
// the declared moves
//
// Chosen so the population has BOTH kinds of dependency, and neither is manufactured by a matrix
// literal:
//
//   * two moves that deposit cells the receiver family cannot tell apart -> their difference is a
//     realizer combination landing on nothing;
//   * one move that deposits both of those cells at once -> it is the SUM of the other two;
//   * one move that deposits nothing at all (a pure withdrawal) -> a zero row;
//   * one move that deposits two cells the receivers CAN tell apart, and is the only move that
//     reaches either -> the two classes are locked in a fixed ratio, which is a class-space null
//     direction that is not a unit vector;
//   * one move NO declared context can see -> it is the only realizer the `Invisible` aperture
//     admits and the only one `Visible` withholds, so the three apertures hand `place` three
//     genuinely different populations rather than two.

fn declared(world: &Tetrahedron) -> Vec<(&'static str, Substitution)> {
    let rim_012 = world.rim([0, 1, 2], [(0, 1), (1, 2), (0, 2)]);
    let rim_013 = world.rim([0, 1, 3], [(0, 1), (1, 3), (0, 3)]);
    let filled_012 = world.filled(0, [0, 1, 2], [(0, 1), (1, 2), (0, 2)]);
    let filled_013 = world.filled(1, [0, 1, 3], [(0, 1), (1, 3), (0, 3)]);
    let filled_012_again = filled_012.clone();
    let filled_013_again = filled_013.clone();

    let skeleton = world.skeleton();
    let mut two_faces = skeleton.clone();
    two_faces.insert(world.faces[0]);
    two_faces.insert(world.faces[1]);
    let mut sphere = two_faces.clone();
    sphere.insert(world.faces[2]);
    sphere.insert(world.faces[3]);

    let ends_23 = BTreeSet::from([world.vertices[2], world.vertices[3]]);
    let mut with_e23 = ends_23.clone();
    with_e23.insert(world.edge(2, 3));

    vec![
        (
            "fill the rim 012 with its triangle",
            Substitution {
                boundary: rim_012.clone(),
                before: rim_012.clone(),
                after: filled_012.clone(),
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
        (
            "fill the rim 013 with its triangle",
            Substitution {
                boundary: rim_013.clone(),
                before: rim_013,
                after: filled_013,
            },
        ),
        (
            "fill the skeleton with BOTH 012 and 013 at once",
            Substitution {
                boundary: skeleton.clone(),
                before: skeleton,
                after: two_faces.clone(),
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
            "unfill 012: withdraw the triangle again",
            Substitution {
                boundary: rim_012.clone(),
                before: filled_012,
                after: rim_012,
            },
        ),
        (
            "close the sphere: 023 and 123 onto the two-face body",
            Substitution {
                boundary: two_faces.clone(),
                before: two_faces,
                after: sphere,
            },
        ),
        (
            "swap the disc on 012 for the disc on 013",
            Substitution {
                boundary: BTreeSet::from([world.vertices[0], world.vertices[1], world.edge(0, 1)]),
                before: filled_012_again,
                after: filled_013_again,
            },
        ),
    ]
}

/// Three contexts that are three different readings. Depositing `e23` against four loose vertices
/// joins two components; against the arc `v0 v2 v3 e02 e03` it closes a cycle; the whole 1-skeleton
/// is blind to it because it already holds the edge.
fn contexts(world: &Tetrahedron) -> Vec<BTreeSet<CausalCellId>> {
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

// ---------------------------------------------------------------------------------------------
// exact linear algebra, in the driver, over ℚ
//
// `matroid_chow::null_space` is private and there is no public exact null-space owner, so this
// driver carries its own. `Rat` is `BigRational`: no float, no tolerance, no pivot heuristic that
// reads a magnitude as a decision.

fn gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.abs();
    let mut b = right.abs();
    while !b.is_zero() {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    a
}

/// Clear an exact rational vector to a primitive integer vector, oriented so its first nonzero
/// entry is positive. The span is the invariant; the representative is a receiver coordinate.
fn primitive(vector: &[Rat]) -> Vec<BigInt> {
    let mut multiplier = BigInt::one();
    for entry in vector {
        let denominator = entry.denom().clone();
        let divisor = gcd(&multiplier, &denominator);
        multiplier = (&multiplier / &divisor) * &denominator;
    }
    let mut cleared: Vec<BigInt> = vector
        .iter()
        .map(|entry| entry.numer() * (&multiplier / entry.denom()))
        .collect();
    let mut common = BigInt::zero();
    for entry in &cleared {
        common = gcd(&common, entry);
    }
    if !common.is_zero() {
        for entry in cleared.iter_mut() {
            *entry /= &common;
        }
    }
    if cleared
        .iter()
        .find(|entry| !entry.is_zero())
        .is_some_and(BigInt::is_negative)
    {
        for entry in cleared.iter_mut() {
            *entry = -entry.clone();
        }
    }
    cleared
}

/// A basis for `{x ∈ ℚ^columns : M x = 0}`, each vector cleared to primitive integers.
fn null_space(matrix: &IntegerMatrix) -> Vec<Vec<BigInt>> {
    let rows = matrix.rows();
    let columns = matrix.columns();
    let mut work: Vec<Vec<Rat>> = (0..rows)
        .map(|row| {
            (0..columns)
                .map(|column| Rat::from(matrix.at(row, column).clone()))
                .collect()
        })
        .collect();

    let mut pivot_column: Vec<usize> = Vec::new();
    let mut settled = 0usize;
    for column in 0..columns {
        if settled == rows {
            break;
        }
        let Some(found) = (settled..rows).find(|candidate| !work[*candidate][column].is_zero())
        else {
            continue;
        };
        work.swap(settled, found);
        let lead = work[settled][column].clone();
        for entry in work[settled].iter_mut() {
            *entry = entry.clone() / lead.clone();
        }
        let pivot_row = work[settled].clone();
        for other in 0..rows {
            if other == settled {
                continue;
            }
            let factor = work[other][column].clone();
            if factor.is_zero() {
                continue;
            }
            for index in 0..columns {
                let term = factor.clone() * pivot_row[index].clone();
                work[other][index] = work[other][index].clone() - term;
            }
        }
        pivot_column.push(column);
        settled += 1;
    }

    let pivots: BTreeSet<usize> = pivot_column.iter().copied().collect();
    (0..columns)
        .filter(|column| !pivots.contains(column))
        .map(|free| {
            let mut vector = vec![Rat::zero(); columns];
            vector[free] = Rat::one();
            for (row, pivot) in pivot_column.iter().enumerate() {
                vector[*pivot] = -work[row][free].clone();
            }
            primitive(&vector)
        })
        .collect()
}

fn apply(matrix: &IntegerMatrix, vector: &[BigInt]) -> Vec<BigInt> {
    (0..matrix.rows())
        .map(|row| {
            let mut total = BigInt::zero();
            for column in 0..matrix.columns() {
                total += matrix.at(row, column) * &vector[column];
            }
            total
        })
        .collect()
}

fn transposed(matrix: &IntegerMatrix) -> IntegerMatrix {
    let mut turned = IntegerMatrix::zeros(matrix.columns(), matrix.rows());
    for row in 0..matrix.rows() {
        for column in 0..matrix.columns() {
            turned.set(column, row, matrix.at(row, column).clone());
        }
    }
    turned
}

// ---------------------------------------------------------------------------------------------
// printing: the population, never a total

fn class_name(complex: &GradedCausalComplex, placement: &Placement, class: usize) -> String {
    let members = &placement.compression.conduct.blocks[class];
    format!(
        "class {class:2} [{}]",
        names(complex, members.iter().copied().map(cell_of_item))
    )
}

fn print_conduct(complex: &GradedCausalComplex, placement: &Placement) {
    println!(
        "  {} conduct classes over {} receivers, from {} cells:",
        placement.class_extent,
        placement.receiver_extent,
        complex.cells().len()
    );
    for class in 0..placement.class_extent {
        println!("    {}", class_name(complex, placement, class));
    }
    if placement.compression.collapsed.is_empty() {
        println!("    nothing the one-shot reading merged survived conduct");
    } else {
        for pair in &placement.compression.collapsed {
            println!(
                "    the reading merged {} ~ {} and conduct separated them, word {:?}",
                name(complex, cell_of_item(pair.left)),
                name(complex, cell_of_item(pair.right)),
                pair.distinguishing_word
            );
        }
    }
}

fn print_incidence(
    complex: &GradedCausalComplex,
    labels: &[&str],
    placement: &Placement,
    realizations: &[Realization],
    matrix: &IntegerMatrix,
) {
    println!(
        "  M is {} realizers x {} classes, exact over ℤ:",
        matrix.rows(),
        matrix.columns()
    );
    for (row, realization) in realizations.iter().enumerate() {
        let declared = realization.realizer.0 as usize;
        let landings: Vec<String> = (0..matrix.columns())
            .filter(|class| !matrix.at(row, *class).is_zero())
            .map(|class| {
                format!(
                    "{}x {}",
                    matrix.at(row, class),
                    class_name(complex, placement, class)
                )
            })
            .collect();
        println!(
            "    row {row}  realizer {declared}  {:<52}  {}",
            labels[declared],
            if landings.is_empty() {
                "lands nowhere".to_owned()
            } else {
                landings.join("   ")
            }
        );
    }
}

fn print_split(what: &str, split: Inertia) {
    println!(
        "  {what:<34} positive {}  zero {}  negative {}   (rank {}, extent {})",
        split.positive,
        split.zero,
        split.negative,
        split.rank(),
        split.extent()
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

    // ------------------------------------------------------------------ the receivers
    let receivers = vec![
        dilate(complex, world.vertices[0], Horizon::Unbounded, WalkOrder::Breadth)
            .expect("v0 is a cell"),
        dilate(complex, world.vertices[1], Horizon::Unbounded, WalkOrder::Breadth)
            .expect("v1 is a cell"),
    ];
    let system = ComplexSystem::declare(
        complex,
        AddressReading::Metric,
        receivers,
        ComplexSystem::every_one_cell(complex),
    )
    .expect("the sections were measured on this complex and the inputs are its own 1-cells");

    // ------------------------------------------------------------------ the moves
    let moves = declared(&world);
    let labels: Vec<&str> = moves.iter().map(|(label, _)| *label).collect();
    let substitutions: Vec<Substitution> =
        moves.iter().map(|(_, made)| made.clone()).collect();
    let founded: SubstitutionRealizers = read_and_realize(
        complex,
        &substitutions,
        &contexts(&world),
        PivotRule::SmallestMagnitude,
    );

    println!("\n================ the declared population ================");
    println!(
        "  {} declared, {} read, {} refused, against {} contexts",
        founded.declared_extent(),
        founded.realizers.len(),
        founded.refused.len(),
        founded.contexts.len()
    );
    for realizer in &founded.realizers {
        println!(
            "  [{}] {:<52}  deposits {}   withdraws {}",
            realizer.declared,
            labels[realizer.declared],
            names(complex, realizer.landings.iter().copied()),
            names(complex, realizer.withdrawn.iter().copied())
        );
    }
    for refused in &founded.refused {
        println!(
            "  [{}] {:<52}  REFUSED {:?}",
            refused.declared, labels[refused.declared], refused.refusal
        );
    }

    // ------------------------------------------------------------------ the placement
    let admission = RealizerAdmission::EveryRead;
    let placed = place_substitutions(&system, &founded, admission);
    let placement = &placed.placement;

    println!("\n================ the conduct the moves are placed against ================");
    print_conduct(complex, placement);

    let realizations = founded.realizations_under(admission, &placement.compression.conduct);
    let matrix = incidence(&realizations, placement.class_extent);

    println!("\n================ the incidence, off the moves themselves ================");
    print_incidence(complex, &labels, placement, &realizations, &matrix);

    // ------------------------------------------------------------------ THE JOIN
    let split = induced_placement(&matrix).expect("a Gram matrix is symmetric, so the form founds");
    let form = positive_form(&matrix);
    let rank_over_integers = smith_normal_form(&matrix, PivotRule::SmallestMagnitude).rank();

    println!("\n================ induced_placement: the split ================");
    println!("  CLAUDE.md §2: placement is DERIVED from realization, not computed beside it.");
    print_split("MᵀM over the classes", split);
    println!(
        "  cross-frame: rank from the Smith normal form over ℤ is {rank_over_integers}, and \
         `placement.support.supported_rank` is {}",
        placement.support.supported_rank
    );
    println!(
        "  the free obstruction the support reading returns is {}, and the nullity the elimination \
         returned is {}",
        placement.support.free_obstruction(),
        split.zero
    );

    // control 1: the split against two independent computations. This can fail.
    assert_eq!(
        split.negative, 0,
        "MᵀM is positive semi-definite; a negative direction means the elimination is wrong"
    );
    assert_eq!(
        split.positive, rank_over_integers,
        "the positive count must be the incidence's rank, computed by a different algorithm"
    );
    assert_eq!(
        split.positive, placement.support.supported_rank,
        "and the rank placement already returned"
    );
    assert_eq!(
        split.zero,
        placement.class_extent - rank_over_integers,
        "the nullity must be the corank of the class family"
    );
    assert_eq!(split.zero, placement.support.free_obstruction());

    // ------------------------------------------------------------------ the nullity, NAMED
    println!("\n================ the nullity, named ================");
    println!("  ker(MᵀM) — CLASS combinations no declared move can separate:");
    let class_null = null_space(&matrix);
    for (index, vector) in class_null.iter().enumerate() {
        let terms: Vec<String> = (0..placement.class_extent)
            .filter(|class| !vector[*class].is_zero())
            .map(|class| {
                format!(
                    "{:+}·{}",
                    vector[class],
                    class_name(complex, placement, class)
                )
            })
            .collect();
        println!("    {:2}  {}", index + 1, terms.join("   "));
        // control 3: every returned null vector is verified, twice.
        assert!(
            apply(&matrix, vector).iter().all(BigInt::is_zero),
            "M x must be zero componentwise"
        );
        assert!(
            quadratic_value(&form, vector).is_zero(),
            "and xᵀ(MᵀM)x must be zero"
        );
    }
    assert_eq!(
        class_null.len(),
        split.zero,
        "the independent null directions found must be the nullity the elimination returned"
    );

    let turned = transposed(&matrix);
    let realizer_split =
        induced_placement(&turned).expect("the other Gram matrix is symmetric too");
    let realizer_form = positive_form(&turned);
    let realizer_null = null_space(&turned);
    println!(
        "\n  ker(MMᵀ) — REALIZER combinations that land on nothing (nullity {}):",
        realizer_split.zero
    );
    for (index, vector) in realizer_null.iter().enumerate() {
        let terms: Vec<String> = (0..matrix.rows())
            .filter(|row| !vector[*row].is_zero())
            .map(|row| {
                let declared = realizations[row].realizer.0 as usize;
                format!("{:+}·[{declared}] {}", vector[row], labels[declared])
            })
            .collect();
        println!("    {:2}  {}", index + 1, terms.join("   "));
        assert!(
            apply(&turned, vector).iter().all(BigInt::is_zero),
            "xᵀM must be zero componentwise"
        );
        assert!(quadratic_value(&realizer_form, vector).is_zero());
    }
    assert_eq!(realizer_null.len(), realizer_split.zero);
    print_split("MMᵀ over the realizers", realizer_split);
    assert_eq!(
        realizer_split.positive, rank_over_integers,
        "the two Gram matrices share one rank; only the space they are indexed by differs"
    );

    // ------------------------------------------------------------------ control 1, exhibited
    println!("\n================ control: the transposed incidence, which is the way this is built wrong ================");
    println!(
        "  handing `induced_placement` the transposed incidence returns a split of extent {} rather \
         than {}, and a nullity of {} where the corank of the class family is {}.",
        realizer_split.extent(),
        placement.class_extent,
        realizer_split.zero,
        split.zero
    );
    assert_ne!(
        realizer_split, split,
        "if these agreed, the rank/nullity control could not catch a transposed incidence"
    );
    assert_ne!(
        realizer_split.zero,
        placement.class_extent - rank_over_integers,
        "which is exactly the assertion above that would have fired"
    );
    println!("  the `negative == 0` check does NOT catch it: both are Gram matrices and both return");
    println!(
        "  negative {} — which is why positivity is not the evidence and the SPLIT is.",
        realizer_split.negative
    );

    // ------------------------------------------------------------------ control 2: the hand flips
    let symmetric =
        SymmetricForm::from_integer_matrix(&form).expect("a Gram matrix is symmetric");
    let flipped = inertia(&symmetric.negated());
    println!("\n================ control: the hand flips, the split does not ================");
    print_split("MᵀM", split);
    print_split("−(MᵀM)", flipped);
    assert_eq!(flipped.positive, split.negative);
    assert_eq!(flipped.negative, split.positive);
    assert_eq!(flipped.zero, split.zero, "the split is what no frame touches");
    assert!(
        flipped.negative > 0,
        "the elimination must be able to return negatives, or `negative == 0` above is vacuous"
    );

    // ------------------------------------------------------------------ control 4: nonzero return
    println!("\n================ control: the form is nonzero where a move paid ================");
    let paid = placement
        .standing
        .first()
        .expect("at least one class was paid for")
        .class;
    let unreached = placement
        .open
        .iter()
        .find(|open| open.reached_only_in_multiple.is_none())
        .expect("at least one class nothing reached")
        .class;
    let unit = |class: usize| {
        let mut probe = vec![BigInt::zero(); placement.class_extent];
        probe[class] = BigInt::one();
        probe
    };
    let paid_value = quadratic_value(&form, &unit(paid));
    let unreached_value = quadratic_value(&form, &unit(unreached));
    println!(
        "  |M e_c|² on {}  = {paid_value}",
        class_name(complex, placement, paid)
    );
    println!(
        "  |M e_c|² on {}  = {unreached_value}",
        class_name(complex, placement, unreached)
    );
    assert!(
        paid_value > BigInt::zero(),
        "a law that returns zero proves nothing about itself"
    );
    assert!(unreached_value.is_zero());

    // ------------------------------------------------------------------ control 5: the aperture moves the material
    println!("\n================ control: the aperture is a gauge and it acts ================");
    let mut seen: Vec<(RealizerAdmission, usize, Inertia)> = Vec::new();
    for aperture in [
        RealizerAdmission::EveryRead,
        RealizerAdmission::Visible,
        RealizerAdmission::Invisible,
    ] {
        let elsewhere = place_substitutions(&system, &founded, aperture);
        let their_realizations = founded
            .realizations_under(aperture, &elsewhere.placement.compression.conduct);
        let their_matrix = incidence(&their_realizations, elsewhere.placement.class_extent);
        let their_split =
            induced_placement(&their_matrix).expect("a Gram matrix is symmetric");
        println!(
            "  {aperture:?}: {} admitted   {}",
            elsewhere.admitted.len(),
            format_args!(
                "positive {} zero {} negative {}",
                their_split.positive, their_split.zero, their_split.negative
            )
        );
        assert_eq!(
            their_split.positive,
            smith_normal_form(&their_matrix, PivotRule::SmallestMagnitude).rank(),
            "the cross-frame rank check holds at every aperture, not only the widest"
        );
        seen.push((aperture, elsewhere.admitted.len(), their_split));
    }
    let distinct: BTreeSet<(usize, usize, usize)> = seen
        .iter()
        .map(|(_, _, split)| (split.positive, split.zero, split.negative))
        .collect();
    println!(
        "  {} distinct splits over {} declared apertures",
        distinct.len(),
        seen.len()
    );
    assert_eq!(
        distinct.len(),
        seen.len(),
        "a gauge whose group acts trivially on the declared material is not a gauge. The declared \
         family carries a move no context can see and six that at least one can, precisely so all \
         three apertures hand `place` different populations; if this ever collapses, the aperture \
         reading below is bookkeeping and not evidence."
    );

    // ------------------------------------------------------------------ control 6: the pivot order
    println!("\n================ control: four pivot orders, one inertia ================");
    let mut schedules = BTreeSet::new();
    for order in PivotOrder::ALL {
        let (reading, schedule) = inertia_with_schedule(&symmetric, order);
        println!(
            "  {order:?}: positive {} zero {} negative {}   {} steps   zero-diagonal branch {}",
            reading.positive,
            reading.zero,
            reading.negative,
            schedule.steps.len(),
            schedule.used_zero_diagonal_branch()
        );
        assert_eq!(reading, split, "Sylvester's law: the order cannot matter");
        schedules.insert(format!("{:?}", schedule.steps));
    }
    println!(
        "  {} distinct schedules over {} declared orders",
        schedules.len(),
        PivotOrder::ALL.len()
    );
    if schedules.len() == 1 {
        println!(
            "  BOOKKEEPING: the four orders walked ONE schedule on this material, so their agreement \
             is one computation compared with itself four times and is not evidence."
        );
    }

    // ------------------------------------------------------------------ what the split CANNOT see
    //
    // Found by driving it. The inertia of `MᵀM` is a reading over ℚ, and `supported_realizers`'
    // headline content — a class reached only as `2·c`, supported rationally and not integrally — is
    // an invariant of the incidence over ℤ. So the split is BLIND to it, and two populations with
    // genuinely different integral support return the same placement. That is a bound on this join
    // and it is exhibited rather than stated.
    println!("\n================ the bound: the split is rational and the obstruction is integral ================");
    let alone = |family: &[Substitution]| {
        let read = read_and_realize(complex, family, &contexts(&world), PivotRule::SmallestMagnitude);
        let placed_alone = place_substitutions(&system, &read, RealizerAdmission::EveryRead);
        let their_realizations = read.realizations_under(
            RealizerAdmission::EveryRead,
            &placed_alone.placement.compression.conduct,
        );
        let their_matrix = incidence(&their_realizations, placed_alone.placement.class_extent);
        let their_split = induced_placement(&their_matrix).expect("a Gram matrix is symmetric");
        (placed_alone, their_split)
    };
    let (single, single_split) = alone(&substitutions[0..1]);
    let (doubled, doubled_split) = alone(&substitutions[3..4]);
    for (label, placed_alone, their_split) in [
        ("fill the rim 012 once", &single, single_split),
        ("fill the skeleton with BOTH at once", &doubled, doubled_split),
    ] {
        println!(
            "  {label:<38}  split (positive {}, zero {}, negative {})   invariant factors {:?}   \
             torsion obstruction {:?}",
            their_split.positive,
            their_split.zero,
            their_split.negative,
            placed_alone.placement.support.invariant_factors,
            placed_alone.placement.support.torsion_obstruction()
        );
    }
    assert_eq!(
        doubled.placement.support.torsion_obstruction(),
        vec![BigInt::from(2)],
        "one move depositing two indistinguishable cells is a Z/2 and must stay one"
    );
    assert!(
        single.placement.support.torsion_obstruction().is_empty(),
        "and a single deposit is not a doubled one"
    );
    assert_eq!(
        single_split, doubled_split,
        "the bound: two populations whose integral support genuinely differs place identically"
    );
    println!(
        "  the two families differ over ℤ — invariant factors [2] against [1] — and their splits are \
         IDENTICAL. `induced_placement` cannot see the integral obstruction; only \
         `RealizerSupport::torsion_obstruction` can, and it is a different return."
    );

    println!("\n================ what this run returned ================");
    println!(
        "  realization paid for {} of {} classes; {} classes are a free obstruction and {} realizer \
         combinations land on nothing.",
        split.positive, placement.class_extent, split.zero, realizer_split.zero
    );
    println!(
        "  placement is the RETURN: (rank {}, hand +, nullity {}) — derived from which moves reached \
         which classes, and from nothing else.",
        split.positive, split.zero
    );
}
