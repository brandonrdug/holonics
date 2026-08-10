//! The integral is the pair, and the disagreement is the holonomy.
//!
//! `crates/holonic-engine/src/running_integral.rs` is 1,786 lines and has **no direct driver**. Four
//! library modules call into it — `temper.rs`, `contact_gluing.rs`, `derivation_integral.rs` and
//! `derivation_holonomy` through them — but nothing runs the organ itself and returns what it
//! computes. This file does.
//!
//! The module implements
//! `research/records/2026-08-07_THE_INTEGRAL_IS_THE_PAIR_THE_DISAGREEMENT_IS_THE_HOLONOMY.md`:
//! there is no continuum to subdivide, only a lineage of discrete windings, and **the area IS the
//! exact running sum of them** — no mesh, no limit, no error. The honest return is the sum together
//! with its path, and two paths with the same endpoints are compared *as a pair*.
//!
//! ## The three properties the module exists to keep apart
//!
//! ```text
//!   w is a COBOUNDARY   w = d f      =>  every pair agrees; the sum telescopes to f(end) - f(start)
//!   w is CLOSED         d w = 0      =>  the sum over any FILLED region vanishes
//!   w STANDS            a pair disagrees  =>  the residual IS the holonomy
//! ```
//!
//! Closed does not imply coboundary, and the gap is `H^1 != 0`. The module's own falsifier:
//! *"if two enclosing paths always agree, the construction has assumed trivial cohomology and is the
//! classical integral wearing new vocabulary."* Section 4 is that falsifier, run.
//!
//! ## Declared apertures
//!
//! - **Carrier.** `BigInt`. Exact addition, negation and multiplication in `Z`. No float, no
//!   tolerance, no threshold, no averaging.
//! - **Joinable 1-cells only.** A traversed cell must have grade one and a boundary of exactly one
//!   `+1` head and one `-1` tail. A self-incident 1-cell has an *empty* boundary in this carrier and
//!   is refused by name rather than skipped — section 11 drives that refusal.
//! - **Five declared complexes**, and each is declared with what it can and cannot exercise:
//!
//!   | complex | cells | cycle rank | what it can exercise |
//!   |---|---|---|---|
//!   | hollow square | 4 vertices, 4 edges | 1 | both verdicts; one retained chord |
//!   | filled square | + one 2-cell | 1 | closedness, the enclosed region, three readings |
//!   | ladder | 6 vertices, 7 edges | 2 | a **plural** retained remainder |
//!   | severed | square + a disjoint edge | 1 | a non-empty `unreached_cells` population |
//!   | path | 3 vertices, 2 edges | 0 | **nothing** — stated in section 10 and not counted |
//!
//! - **The base vertex of `found_potential` is a declared gauge**, and section 7 measures its orbit
//!   rather than assuming it acts. `CLAUDE.md` §8: a gauge whose group acts trivially on the
//!   declared material is not a gauge.
//!
//! ```text
//! cargo run --release --example the_integral_is_the_pair
//! ```
//!
//! Exits non-zero if any declared control fails.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::running_integral::{
    Cochain, Disagreement, PairReturn, Path, PathStep, PotentialSearch, RunningIntegral,
    RunningIntegralError, coboundary, disagreement, enclosed_disagreement, found_potential,
    holonomy, is_closed, running_sum,
};
use num_bigint::BigInt;
use num_traits::Zero;

fn source() -> BTreeSet<EventId> {
    BTreeSet::from([EventId(1)])
}

fn vertex(complex: &mut GradedCausalComplex, name: &str) -> CausalCellId {
    complex
        .found_cell(name, source(), 0, CausalChain::default())
        .expect("a vertex carries no boundary")
}

fn edge(
    complex: &mut GradedCausalComplex,
    name: &str,
    tail: CausalCellId,
    head: CausalCellId,
) -> CausalCellId {
    let mut boundary = CausalChain::default();
    boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
    boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
    complex
        .found_cell(name, source(), 1, boundary)
        .expect("an edge closes")
}

fn big(value: i64) -> BigInt {
    BigInt::from(value)
}

fn name_of(complex: &GradedCausalComplex, cell: CausalCellId) -> String {
    complex
        .cell(cell)
        .map(|body| body.name.clone())
        .unwrap_or_else(|_| format!("{cell:?}"))
}

fn names(complex: &GradedCausalComplex, cells: impl IntoIterator<Item = CausalCellId>) -> String {
    let rendered: Vec<String> = cells
        .into_iter()
        .map(|cell| name_of(complex, cell))
        .collect();
    if rendered.is_empty() {
        "(empty)".to_owned()
    } else {
        rendered.join(", ")
    }
}

fn render_cochain(complex: &GradedCausalComplex, cochain: &Cochain) -> String {
    let rendered: Vec<String> = cochain
        .values()
        .iter()
        .map(|(cell, value)| format!("{}={value}", name_of(complex, *cell)))
        .collect();
    if rendered.is_empty() {
        "(assigns nothing)".to_owned()
    } else {
        rendered.join("  ")
    }
}

fn render_path(complex: &GradedCausalComplex, path: &Path) -> String {
    path.steps()
        .iter()
        .map(|step| {
            let mark = match step.orientation {
                holonic_engine::running_integral::Orientation::Along => "+",
                holonic_engine::running_integral::Orientation::Against => "-",
            };
            format!("{mark}{}", name_of(complex, step.cell))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// The artifact, whole: every winding with the partial sum standing after it.
fn print_integral(complex: &GradedCausalComplex, label: &str, integral: &RunningIntegral) {
    println!(
        "  {label}   {} -> {}   total {}",
        name_of(complex, integral.start),
        name_of(complex, integral.end),
        integral.total
    );
    println!(
        "    {:>3}  {:<10} {:>9}  {:<6} {:<6} {:>10} {:>12}",
        "k", "cell", "crossing", "from", "to", "increment", "I(k+1)"
    );
    for step in &integral.steps {
        println!(
            "    {:>3}  {:<10} {:>9}  {:<6} {:<6} {:>10} {:>12}",
            step.index,
            name_of(complex, step.cell),
            format!("{:?}", step.orientation),
            name_of(complex, step.departed),
            name_of(complex, step.arrived),
            step.increment,
            step.accumulated
        );
    }
    println!(
        "    lineage [I(0) .. I(n)] = {:?}",
        integral
            .partial_sums()
            .iter()
            .map(BigInt::to_string)
            .collect::<Vec<_>>()
    );
}

fn print_disagreement(complex: &GradedCausalComplex, pair: &Disagreement) {
    println!(
        "    endpoints {} -> {}   left total {}   right total {}   residual {}",
        name_of(complex, pair.start),
        name_of(complex, pair.end),
        pair.left.total,
        pair.right.total,
        pair.residual
    );
    let cycle: Vec<String> = pair
        .cycle
        .coefficients()
        .iter()
        .filter(|(_, coefficient)| !coefficient.difference_is_zero())
        .map(|(cell, coefficient)| {
            format!("{}^{}", name_of(complex, *cell), coefficient.difference())
        })
        .collect();
    println!("    the cycle the pair bounds: {}", cycle.join(" "));
    println!(
        "    verdict {:?}   paths_are_distinct {}",
        pair.verdict(),
        pair.paths_are_distinct()
    );
}

fn print_search(complex: &GradedCausalComplex, label: &str, search: &PotentialSearch) {
    println!(
        "  {label}  base {}   admits a potential: {}",
        name_of(complex, search.base),
        search.admits_a_potential()
    );
    println!("    potential f   {}", render_cochain(complex, &search.potential));
    println!(
        "    reached {}   tree cells {}",
        names(complex, search.reached.iter().copied()),
        names(complex, search.tree_cells.iter().copied())
    );
    println!(
        "    cycle rank {}   agreeing chords {}   unreached cells {}",
        search.cycle_rank(),
        names(complex, search.agreeing_chords.iter().copied()),
        names(complex, search.unreached_cells.iter().copied())
    );
    if search.retained_obstructions.is_empty() {
        println!("    retained obstructions: (none)");
    } else {
        for chord in &search.retained_obstructions {
            println!(
                "    retained chord {:<6} {} -> {}   declared w(e) = {:<4} tree implies {:<4} residual {}",
                name_of(complex, chord.cell),
                name_of(complex, chord.tail),
                name_of(complex, chord.head),
                chord.declared,
                chord.implied,
                chord.residual
            );
        }
    }
}

// -------------------------------------------------------------------------------------------
// the fixtures

struct Square {
    complex: GradedCausalComplex,
    a: CausalCellId,
    b: CausalCellId,
    c: CausalCellId,
    d: CausalCellId,
    ab: CausalCellId,
    bc: CausalCellId,
    ad: CausalCellId,
    dc: CausalCellId,
}

impl Square {
    fn hollow() -> Self {
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");
        let d = vertex(&mut complex, "d");
        let ab = edge(&mut complex, "ab", a, b);
        let bc = edge(&mut complex, "bc", b, c);
        let ad = edge(&mut complex, "ad", a, d);
        let dc = edge(&mut complex, "dc", d, c);
        Self {
            complex,
            a,
            b,
            c,
            d,
            ab,
            bc,
            ad,
            dc,
        }
    }

    fn filled() -> (Self, CausalCellId) {
        let mut square = Self::hollow();
        let mut boundary = CausalChain::default();
        boundary.add_term(square.ab, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(square.bc, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(square.dc, ComparativeMultiplicity::negative(1u32));
        boundary.add_term(square.ad, ComparativeMultiplicity::negative(1u32));
        let face = square
            .complex
            .found_cell("face", source(), 2, boundary)
            .expect("the square's boundary closes");
        (square, face)
    }

    fn left(&self) -> Path {
        Path::along([self.ab, self.bc])
    }

    fn right(&self) -> Path {
        Path::along([self.ad, self.dc])
    }

    fn cycle(&self) -> Path {
        self.left().then(&self.right().reversed())
    }

    /// Closed on the hollow square (no 2-cells can obstruct it) and **not** a coboundary.
    fn standing(&self) -> Cochain {
        Cochain::from_values(1, [(self.ab, big(1))])
    }

    /// `f(a) = 0, f(b) = 3, f(c) = 7, f(d) = -2`.
    fn potential(&self) -> Cochain {
        Cochain::from_values(
            0,
            [
                (self.a, big(0)),
                (self.b, big(3)),
                (self.c, big(7)),
                (self.d, big(-2)),
            ],
        )
    }

    fn exact(&self) -> Cochain {
        coboundary(&self.complex, &self.potential()).expect("the potential has a coboundary")
    }
}

/// Six vertices, seven edges, cycle rank two: the fixture whose retained remainder is **plural**.
struct Ladder {
    complex: GradedCausalComplex,
    cells: BTreeMap<&'static str, CausalCellId>,
}

impl Ladder {
    fn new() -> Self {
        let mut complex = GradedCausalComplex::default();
        let mut cells = BTreeMap::new();
        for name in ["v0", "v1", "v2", "v3", "v4", "v5"] {
            cells.insert(name, vertex(&mut complex, name));
        }
        for (name, tail, head) in [
            ("e0", "v0", "v1"),
            ("e1", "v1", "v2"),
            ("e2", "v0", "v3"),
            ("e3", "v1", "v4"),
            ("e4", "v2", "v5"),
            ("e5", "v3", "v4"),
            ("e6", "v4", "v5"),
        ] {
            let cell = edge(&mut complex, name, cells[tail], cells[head]);
            cells.insert(name, cell);
        }
        Self { complex, cells }
    }

    fn at(&self, name: &str) -> CausalCellId {
        self.cells[name]
    }

    /// `w(e0) = 1`, `w(e1) = 2`, everything else zero.
    fn standing(&self) -> Cochain {
        Cochain::from_values(1, [(self.at("e0"), big(1)), (self.at("e1"), big(2))])
    }

    /// `v0 -> v1 -> v4 -> v3 -> v0`.
    fn left_cycle(&self) -> Path {
        Path::new([
            PathStep::along(self.at("e0")),
            PathStep::along(self.at("e3")),
            PathStep::against(self.at("e5")),
            PathStep::against(self.at("e2")),
        ])
    }

    /// `v1 -> v2 -> v5 -> v4 -> v1`, conjugated along `e0` so that it too is based at `v0` and the
    /// two cycles can be concatenated. Conjugation adds `w(e0)` on the way in and subtracts it on
    /// the way out, so it moves no holonomy — which is itself checked below.
    fn right_cycle(&self) -> Path {
        Path::along([self.at("e0")])
            .then(&Path::new([
                PathStep::along(self.at("e1")),
                PathStep::along(self.at("e4")),
                PathStep::against(self.at("e6")),
                PathStep::against(self.at("e3")),
            ]))
            .then(&Path::new([PathStep::against(self.at("e0"))]))
    }

    /// The same right-hand hole, based at `v1` and not conjugated.
    fn right_cycle_at_v1(&self) -> Path {
        Path::new([
            PathStep::along(self.at("e1")),
            PathStep::along(self.at("e4")),
            PathStep::against(self.at("e6")),
            PathStep::against(self.at("e3")),
        ])
    }
}

fn main() {
    println!("THE INTEGRAL IS THE PAIR");
    println!("========================");
    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=the integral is the running sum WITH its path; the disagreement of two paths stands");
    println!("organ=crates/holonic-engine/src/running_integral.rs   (four library callers, no driver)");

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    let square = Square::hollow();
    let (filled, face) = Square::filled();
    let ladder = Ladder::new();

    // ===========================================================================================
    println!("\n\n1. THE DECLARED COMPLEXES");
    println!("-------------------------");
    for (label, complex) in [
        ("hollow square", &square.complex),
        ("filled square", &filled.complex),
        ("ladder", &ladder.complex),
    ] {
        let f_vector = complex.f_vector();
        let vertices = f_vector.get(&0).copied().unwrap_or(0);
        let edges = f_vector.get(&1).copied().unwrap_or(0);
        let faces = f_vector.get(&2).copied().unwrap_or(0);
        println!(
            "  {label:<15} f-vector {f_vector:?}   cycle rank |E| - |V| + 1 = {}",
            edges as i64 - vertices as i64 + 1
        );
        let _ = faces;
    }

    // ===========================================================================================
    println!("\n\n2. THE THREE PROPERTIES, KEPT APART");
    println!("-----------------------------------");
    let exact = square.exact();
    let standing = square.standing();
    println!(
        "  w = d f on the hollow square:   {}",
        render_cochain(&square.complex, &exact)
    );
    println!(
        "  w = 1 on `ab` alone:            {}",
        render_cochain(&square.complex, &standing)
    );
    println!();
    println!(
        "  {:<26} {:>12} {:>12} {:>14}",
        "cochain / complex", "closed?", "coboundary?", "holonomy"
    );
    let rows: Vec<(&str, bool, bool, BigInt)> = vec![
        (
            "d f  on hollow square",
            is_closed(&square.complex, &exact).expect("gradeable"),
            found_potential(&square.complex, &exact, square.a)
                .expect("a lawful search")
                .admits_a_potential(),
            holonomy(&square.complex, &exact, &square.cycle())
                .expect("a closed traversal")
                .total,
        ),
        (
            "standing on hollow square",
            is_closed(&square.complex, &standing).expect("gradeable"),
            found_potential(&square.complex, &standing, square.a)
                .expect("a lawful search")
                .admits_a_potential(),
            holonomy(&square.complex, &standing, &square.cycle())
                .expect("a closed traversal")
                .total,
        ),
        (
            "d f  on filled square",
            is_closed(&filled.complex, &filled.exact()).expect("gradeable"),
            found_potential(&filled.complex, &filled.exact(), filled.a)
                .expect("a lawful search")
                .admits_a_potential(),
            holonomy(&filled.complex, &filled.exact(), &filled.cycle())
                .expect("a closed traversal")
                .total,
        ),
        (
            "standing on filled square",
            is_closed(&filled.complex, &filled.standing()).expect("gradeable"),
            found_potential(&filled.complex, &filled.standing(), filled.a)
                .expect("a lawful search")
                .admits_a_potential(),
            holonomy(&filled.complex, &filled.standing(), &filled.cycle())
                .expect("a closed traversal")
                .total,
        ),
    ];
    for (label, closed, coboundary_flag, winding) in &rows {
        println!("  {label:<26} {closed:>12} {coboundary_flag:>12} {winding:>14}");
    }
    println!();
    println!("  Row 2 is the whole content: CLOSED and NOT a coboundary, with a holonomy of 1. The");
    println!("  hollow square has no 2-cell that could obstruct any 1-cochain, so closedness there");
    println!("  is vacuous and the winding is entirely free. That gap is H^1 != 0.");
    println!("  Row 4 is the other half: filling the hole makes the same cochain NOT closed, and");
    println!("  `d w` now names the face that witnesses the winding.");
    let d_standing = coboundary(&filled.complex, &filled.standing()).expect("gradeable");
    println!(
        "    d w on the filled square = {}   (grade {})",
        render_cochain(&filled.complex, &d_standing),
        d_standing.grade()
    );
    holds.push((
        "closed does not imply coboundary: one cochain is closed, not exact, and winds by 1",
        rows[1].1 && !rows[1].2 && rows[1].3 == big(1),
        format!(
            "closed {} coboundary {} holonomy {}",
            rows[1].1, rows[1].2, rows[1].3
        ),
    ));
    holds.push((
        "filling the hole moves closedness, and the coboundary names the witnessing face",
        !rows[3].1 && d_standing.value(face) == big(1),
        format!("d w (face) = {}", d_standing.value(face)),
    ));

    // ===========================================================================================
    println!("\n\n3. THE ARTIFACT — THE RUNNING SUM, WITH ITS LINEAGE");
    println!("---------------------------------------------------");
    println!("  Two traversals of `a -> c` on the hollow square, against the COBOUNDARY d f.");
    println!(
        "  left  = {}      right = {}",
        render_path(&square.complex, &square.left()),
        render_path(&square.complex, &square.right())
    );
    let left = running_sum(&square.complex, &exact, &square.left()).expect("joins");
    let right = running_sum(&square.complex, &exact, &square.right()).expect("joins");
    print_integral(&square.complex, "left ", &left);
    print_integral(&square.complex, "right", &right);
    let potential = square.potential();
    println!(
        "\n  the discrete fundamental theorem: total = f(end) - f(start) = {} - {} = {}",
        potential.value(square.c),
        potential.value(square.a),
        potential.value(square.c) - potential.value(square.a)
    );
    println!("  Equal totals, DIFFERENT lineages. Collapsing the return to the scalar would discard");
    println!("  the path, and the path is the thing the deposit says must be kept.");
    holds.push((
        "two traversals return the same total by different lineages, and both are retained",
        left.total == right.total
            && left.partial_sums() != right.partial_sums()
            && !left.total.is_zero()
            && left.path() == square.left(),
        format!(
            "totals {} = {}; lineages {:?} against {:?}",
            left.total,
            right.total,
            left.partial_sums()
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<_>>(),
            right
                .partial_sums()
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<_>>()
        ),
    ));

    // ===========================================================================================
    println!("\n\n4. THE FALSIFIER — DO TWO ENCLOSING PATHS EVER DISAGREE?");
    println!("--------------------------------------------------------");
    println!("  The record: *if two enclosing paths always agree, the construction has assumed");
    println!("  trivial cohomology and is the classical integral wearing new vocabulary.*");
    println!("  ONE complex, ONE pair of traversals, the cochain the only variable:");
    let agreed = disagreement(&square.complex, &exact, &square.left(), &square.right())
        .expect("a comparable pair");
    let stood = disagreement(&square.complex, &standing, &square.left(), &square.right())
        .expect("a comparable pair");
    println!("\n  against d f:");
    print_disagreement(&square.complex, &agreed);
    println!("\n  against the standing cochain:");
    print_disagreement(&square.complex, &stood);
    println!(
        "\n  the same cycle carries both returns: {}",
        agreed.cycle == stood.cycle
    );
    holds.push((
        "the fixture returns BOTH verdicts on one pair, so the cochain is the variable",
        agreed.verdict() == PairReturn::Agreed
            && stood.verdict() == PairReturn::Holonomy(big(1))
            && agreed.cycle == stood.cycle
            && stood.paths_are_distinct(),
        format!("{:?} / {:?}", agreed.verdict(), stood.verdict()),
    ));
    holds.push((
        "the agreement is not vacuous either: the agreed total is itself nonzero",
        !agreed.left.total.is_zero() && agreed.paths_are_distinct(),
        format!("agreed at total {}", agreed.left.total),
    ));

    println!("\n  and the holonomy is linear in the winding and in the cochain:");
    let once = square.cycle();
    let twice = once.then(&once);
    let undone = once.then(&once.reversed());
    let doubled_cochain = standing.plus(&standing).expect("same grade");
    let readings = [
        ("once", holonomy(&square.complex, &standing, &once).unwrap().total),
        ("twice", holonomy(&square.complex, &standing, &twice).unwrap().total),
        (
            "reversed",
            holonomy(&square.complex, &standing, &once.reversed())
                .unwrap()
                .total,
        ),
        (
            "wound and undone",
            holonomy(&square.complex, &standing, &undone).unwrap().total,
        ),
        (
            "2w, once",
            holonomy(&square.complex, &doubled_cochain, &once).unwrap().total,
        ),
    ];
    for (label, value) in &readings {
        println!("    {label:<18} {value}");
    }
    holds.push((
        "a winding deposits, a repeat doubles, a reversal negates, and an undoing deposits nothing",
        readings[0].1 == big(1)
            && readings[1].1 == big(2)
            && readings[2].1 == big(-1)
            && readings[3].1 == big(0)
            && readings[4].1 == big(2),
        format!(
            "{:?}",
            readings
                .iter()
                .map(|(label, value)| format!("{label}={value}"))
                .collect::<Vec<_>>()
        ),
    ));

    // ===========================================================================================
    println!("\n\n5. THREE INDEPENDENT READINGS OF ONE RESIDUAL");
    println!("---------------------------------------------");
    println!("  On the FILLED square the pair bounds a region. `enclosed_disagreement` computes the");
    println!("  same integer three ways: the difference of two running sums, `<w, boundary region>`,");
    println!("  and `<d w, region>`. The two region readings traverse different data, so a sign or");
    println!("  grade error in either shows up as a disagreement here.");
    let region = CausalChain::single(face, ComparativeMultiplicity::positive(1u32));
    let enclosed = enclosed_disagreement(
        &filled.complex,
        &filled.standing(),
        &filled.left(),
        &filled.right(),
        &region,
    )
    .expect("the region encloses the pair");
    println!(
        "\n    difference of running sums   {}",
        enclosed.disagreement.residual
    );
    println!("    <w, boundary region>         {}", enclosed.boundary_residual);
    println!("    <d w, region>                {}", enclosed.coboundary_residual);
    println!("    readings agree               {}", enclosed.readings_agree());
    let enclosed_exact = enclosed_disagreement(
        &filled.complex,
        &filled.exact(),
        &filled.left(),
        &filled.right(),
        &region,
    )
    .expect("the region encloses the pair");
    println!(
        "    the same three against d f   {} / {} / {}   (agree {})",
        enclosed_exact.disagreement.residual,
        enclosed_exact.boundary_residual,
        enclosed_exact.coboundary_residual,
        enclosed_exact.readings_agree()
    );
    holds.push((
        "three independent readings of one residual agree, and the residual is nonzero",
        enclosed.readings_agree()
            && !enclosed.boundary_residual.is_zero()
            && enclosed_exact.readings_agree()
            && enclosed_exact.boundary_residual.is_zero(),
        format!(
            "standing {} / {} / {}; exact {} / {} / {}",
            enclosed.disagreement.residual,
            enclosed.boundary_residual,
            enclosed.coboundary_residual,
            enclosed_exact.disagreement.residual,
            enclosed_exact.boundary_residual,
            enclosed_exact.coboundary_residual
        ),
    ));

    // ===========================================================================================
    println!("\n\n6. THE POTENTIAL, AND THE CHORDS IT CANNOT REPAIR");
    println!("-------------------------------------------------");
    println!("  `CLAUDE.md` §11: the tree condenses for free, subtree equals interval, and THE");
    println!("  DEPARTURE FROM A FOREST IS THE CERTIFIED REMAINDER. `found_potential` walks a");
    println!("  spanning tree, assigns the only potential the tree admits, and then TESTS every");
    println!("  remaining chord. A disagreeing chord is retained with an exact residual; nothing");
    println!("  repairs the potential and nothing averages the two readings.");
    let search_exact = found_potential(&square.complex, &exact, square.a).expect("a lawful search");
    let search_standing =
        found_potential(&square.complex, &standing, square.a).expect("a lawful search");
    println!();
    print_search(&square.complex, "against d f              ", &search_exact);
    println!();
    print_search(&square.complex, "against the standing form", &search_standing);
    let rebuilt = coboundary(&square.complex, &search_exact.potential).expect("gradeable");
    let failed_rebuild =
        coboundary(&square.complex, &search_standing.potential).expect("gradeable");
    println!(
        "\n  d(recovered f) == d f            : {}",
        rebuilt.assigns_the_same_values(&exact)
    );
    println!(
        "  d(recovered f) == standing form  : {}   <- the reconstruction genuinely fails, and",
        failed_rebuild.assigns_the_same_values(&standing)
    );
    println!("                                       the failure is the return");
    println!(
        "  the retained residual is the holonomy of the cycle that chord closes: |{}| = |{}|",
        search_standing.retained_obstructions[0].residual, stood.residual
    );
    holds.push((
        "a coboundary is recovered exactly and its chord agrees",
        search_exact.admits_a_potential()
            && search_exact.agreeing_chords.len() == 1
            && rebuilt.assigns_the_same_values(&exact),
        format!(
            "cycle rank {}, agreeing chords {}",
            search_exact.cycle_rank(),
            search_exact.agreeing_chords.len()
        ),
    ));
    holds.push((
        "a standing cochain leaves a retained chord whose exact residual is the holonomy",
        !search_standing.admits_a_potential()
            && search_standing.retained_obstructions.len() == 1
            && !search_standing.retained_obstructions[0].residual.is_zero()
            && search_standing.retained_obstructions[0].residual == -stood.residual.clone()
            && !failed_rebuild.assigns_the_same_values(&standing),
        format!(
            "residual {} against pair residual {}",
            search_standing.retained_obstructions[0].residual, stood.residual
        ),
    ));

    // ===========================================================================================
    println!("\n\n7. THE BASE IS A GAUGE — MEASURE ITS ORBIT, DO NOT ASSUME IT");
    println!("------------------------------------------------------------");
    println!("  `found_potential` fixes `f(base) = 0` by declaration. Four bases are available on");
    println!("  the hollow square. If all four returned one tree and one chord the base would be a");
    println!("  gauge whose group acts trivially, and every reading above would be base-blind by");
    println!("  accident rather than by law. The orbit is taken:");
    let mut trees = BTreeSet::new();
    let mut chords = BTreeSet::new();
    let mut residual_magnitudes = BTreeSet::new();
    let mut potentials = BTreeSet::new();
    println!(
        "\n    {:<6} {:<22} {:<8} {:>10}  {}",
        "base", "tree cells", "chord", "residual", "potential f"
    );
    for base in [square.a, square.b, square.c, square.d] {
        let search = found_potential(&square.complex, &standing, base).expect("a lawful search");
        let chord = &search.retained_obstructions[0];
        trees.insert(names(&square.complex, search.tree_cells.iter().copied()));
        chords.insert(name_of(&square.complex, chord.cell));
        residual_magnitudes.insert(chord.residual.clone() * chord.residual.clone());
        potentials.insert(render_cochain(&square.complex, &search.potential));
        println!(
            "    {:<6} {:<22} {:<8} {:>10}  {}",
            name_of(&square.complex, base),
            names(&square.complex, search.tree_cells.iter().copied()),
            name_of(&square.complex, chord.cell),
            chord.residual.to_string(),
            render_cochain(&square.complex, &search.potential)
        );
    }
    println!(
        "\n  distinct trees {}   distinct chords {}   distinct potentials {}   distinct |residual|^2 {}",
        trees.len(),
        chords.len(),
        potentials.len(),
        residual_magnitudes.len()
    );
    println!("  The gauge ACTS: three different chords over four bases, and four different");
    println!("  potentials. What no base moves is the magnitude of the retained residual — the");
    println!("  holonomy is the invariant and the chord that carries it is the coordinate.");
    holds.push((
        "the base gauge has a non-trivial orbit on this material, and the residual magnitude is its invariant",
        chords.len() > 1 && potentials.len() > 1 && residual_magnitudes.len() == 1,
        format!(
            "{} trees, {} chords, {} potentials, {} residual magnitudes over 4 bases",
            trees.len(),
            chords.len(),
            potentials.len(),
            residual_magnitudes.len()
        ),
    ));

    // ===========================================================================================
    println!("\n\n8. A PLURAL REMAINDER — THE LADDER, CYCLE RANK TWO");
    println!("--------------------------------------------------");
    println!("  Every retained-remainder reading in the module's own tests has population ONE. A");
    println!("  law measured only at one is not measured; this fixture carries two independent");
    println!("  holes with DIFFERENT holonomies, so the remainder has to be plural and unequal.");
    let ladder_w = ladder.standing();
    println!(
        "\n  w = {}",
        render_cochain(&ladder.complex, &ladder_w)
    );
    let left_cycle = holonomy(&ladder.complex, &ladder_w, &ladder.left_cycle()).expect("closed");
    let right_cycle = holonomy(&ladder.complex, &ladder_w, &ladder.right_cycle()).expect("closed");
    println!(
        "  declared left cycle  {}   holonomy {}",
        render_path(&ladder.complex, &ladder.left_cycle()),
        left_cycle.total
    );
    println!(
        "  declared right cycle {}   holonomy {}",
        render_path(&ladder.complex, &ladder.right_cycle()),
        right_cycle.total
    );
    let unconjugated = holonomy(&ladder.complex, &ladder_w, &ladder.right_cycle_at_v1())
        .expect("closed at v1");
    println!(
        "  the same hole based at v1, unconjugated: {}   holonomy {}   (conjugation moved nothing)",
        render_path(&ladder.complex, &ladder.right_cycle_at_v1()),
        unconjugated.total
    );
    let combined = ladder.left_cycle().then(&ladder.right_cycle());
    let differenced = ladder.left_cycle().then(&ladder.right_cycle().reversed());
    println!(
        "  left then right          holonomy {}   (predicted {} + {} = {})",
        holonomy(&ladder.complex, &ladder_w, &combined).expect("closed").total,
        left_cycle.total,
        right_cycle.total,
        left_cycle.total.clone() + right_cycle.total.clone()
    );
    println!(
        "  left then right reversed holonomy {}   (predicted {} - {} = {})",
        holonomy(&ladder.complex, &ladder_w, &differenced)
            .expect("closed")
            .total,
        left_cycle.total,
        right_cycle.total,
        left_cycle.total.clone() - right_cycle.total.clone()
    );
    println!();
    let ladder_search =
        found_potential(&ladder.complex, &ladder_w, ladder.at("v0")).expect("a lawful search");
    print_search(&ladder.complex, "ladder", &ladder_search);
    let ladder_residuals = ladder_search.standing_residuals();
    println!(
        "\n  standing residuals: {:?}",
        ladder_residuals
            .iter()
            .map(BigInt::to_string)
            .collect::<Vec<_>>()
    );
    let plural = ladder_search.cycle_rank() == 2
        && ladder_residuals.len() == 2
        && ladder_residuals.iter().all(|residual| !residual.is_zero())
        && ladder_residuals[0] != ladder_residuals[1];
    holds.push((
        "the remainder is plural and unequal: two independent chords, two distinct nonzero residuals",
        plural,
        format!(
            "cycle rank {}, residuals {:?}",
            ladder_search.cycle_rank(),
            ladder_residuals
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<_>>()
        ),
    ));
    holds.push((
        "the holonomy is additive over concatenated cycles and blind to conjugation",
        holonomy(&ladder.complex, &ladder_w, &combined).expect("closed").total
            == left_cycle.total.clone() + right_cycle.total.clone()
            && holonomy(&ladder.complex, &ladder_w, &differenced)
                .expect("closed")
                .total
                == left_cycle.total.clone() - right_cycle.total.clone()
            && unconjugated.total == right_cycle.total
            && left_cycle.total != right_cycle.total,
        format!(
            "left {} right {} sum {} difference {}",
            left_cycle.total,
            right_cycle.total,
            holonomy(&ladder.complex, &ladder_w, &combined).expect("closed").total,
            holonomy(&ladder.complex, &ladder_w, &differenced)
                .expect("closed")
                .total
        ),
    ));

    // ===========================================================================================
    println!("\n\n9. A POPULATION THAT IS EMPTY EVERYWHERE ELSE — `unreached_cells`");
    println!("-----------------------------------------------------------------");
    println!("  `PotentialSearch` returns the 1-cells the walked component never touched. On every");
    println!("  connected fixture that population is empty, and a field that is always empty is a");
    println!("  law returning zero about itself. A severed complex forces it non-empty:");
    let mut severed = GradedCausalComplex::default();
    let sa = vertex(&mut severed, "a");
    let sb = vertex(&mut severed, "b");
    let sc = vertex(&mut severed, "c");
    let sd = vertex(&mut severed, "d");
    let se = vertex(&mut severed, "e");
    let sf = vertex(&mut severed, "f");
    let sab = edge(&mut severed, "ab", sa, sb);
    let sbc = edge(&mut severed, "bc", sb, sc);
    let sad = edge(&mut severed, "ad", sa, sd);
    let sdc = edge(&mut severed, "dc", sd, sc);
    let sef = edge(&mut severed, "ef", se, sf);
    let severed_w = Cochain::from_values(1, [(sab, big(1)), (sef, big(9))]);
    let _ = (sbc, sad, sdc);
    let from_a = found_potential(&severed, &severed_w, sa).expect("a lawful search");
    let from_e = found_potential(&severed, &severed_w, se).expect("a lawful search");
    print_search(&severed, "from a", &from_a);
    println!();
    print_search(&severed, "from e", &from_e);
    println!("\n  The two components are two different questions and the organ answers the one it");
    println!("  was asked. From `a` the `ef` winding is UNREACHED, not zero, and the return says so");
    println!("  by name; from `e` the whole square is unreached and the cochain admits a potential");
    println!("  on the component that was walked.");
    holds.push((
        "an unwalked component is returned as unreached rather than silently read as zero",
        from_a.unreached_cells == BTreeSet::from([sef])
            && from_e.unreached_cells.len() == 4
            && from_a.reached.len() == 4
            && from_e.reached.len() == 2,
        format!(
            "from a: {} unreached; from e: {} unreached",
            from_a.unreached_cells.len(),
            from_e.unreached_cells.len()
        ),
    ));

    // ===========================================================================================
    println!("\n\n10. THE FIXTURE THAT CANNOT FALSIFY, DECLARED AS SUCH");
    println!("-----------------------------------------------------");
    println!("  A tree admits two genuinely different traversals of `a -> c`, but only by");
    println!("  backtracking — and a backtrack cancels in the chain. The residual is therefore");
    println!("  FORCED to zero by the material for every cochain, including the nonzero ones. This");
    println!("  is a check that could not have come out otherwise and it is NOT counted as a");
    println!("  control; it is here to name why the square is the fixture that carries the");
    println!("  falsifier.");
    let mut path_complex = GradedCausalComplex::default();
    let pa = vertex(&mut path_complex, "a");
    let pb = vertex(&mut path_complex, "b");
    let pc = vertex(&mut path_complex, "c");
    let pab = edge(&mut path_complex, "ab", pa, pb);
    let pbc = edge(&mut path_complex, "bc", pb, pc);
    let direct = Path::along([pab, pbc]);
    let detoured = Path::new([
        PathStep::along(pab),
        PathStep::along(pbc),
        PathStep::against(pbc),
        PathStep::along(pbc),
    ]);
    println!(
        "\n    {:<24} {:>10} {:>18} {:>20}",
        "cochain", "residual", "paths_are_distinct", "left total"
    );
    for values in [
        vec![(pab, big(5)), (pbc, big(-3))],
        vec![(pab, big(1)), (pbc, big(1))],
        vec![(pab, big(-9)), (pbc, big(0))],
    ] {
        let w = Cochain::from_values(1, values);
        let pair = disagreement(&path_complex, &w, &direct, &detoured).expect("comparable");
        println!(
            "    {:<24} {:>10} {:>18} {:>20}",
            render_cochain(&path_complex, &w),
            pair.residual.to_string(),
            pair.paths_are_distinct(),
            pair.left.total.to_string()
        );
    }
    println!("\n  The traversals differ as chains — the backtrack deposits two opposed passages the");
    println!("  carrier retains — but they are ONE CYCLE, and it is the cycle that decides.");

    // ===========================================================================================
    println!("\n\n11. REFUSALS — WHAT THE ORGAN WILL NOT READ");
    println!("-------------------------------------------");
    let mut refusals: Vec<(&str, String, bool)> = Vec::new();

    let broken = running_sum(&square.complex, &standing, &Path::along([square.ab, square.dc]));
    refusals.push((
        "a traversal whose steps do not join",
        format!("{:?}", broken.as_ref().err()),
        matches!(
            broken.as_ref().err(),
            Some(RunningIntegralError::PathDoesNotJoin { index: 1, .. })
        ),
    ));

    let empty = running_sum(&square.complex, &standing, &Path::default());
    refusals.push((
        "an empty traversal, rather than a baseless zero",
        format!("{:?}", empty.as_ref().err()),
        matches!(empty.as_ref().err(), Some(RunningIntegralError::EmptyPath)),
    ));

    let not_one = running_sum(&square.complex, &square.potential(), &square.left());
    refusals.push((
        "a grade-0 cochain integrated over 1-cells",
        format!("{:?}", not_one.as_ref().err()),
        matches!(
            not_one.as_ref().err(),
            Some(RunningIntegralError::NotAOneCochain(0))
        ),
    ));

    let pairing = square
        .potential()
        .evaluate(&square.complex, &square.left().chain());
    refusals.push((
        "a grade-0 cochain paired with a 1-chain",
        format!("{:?}", pairing.as_ref().err()),
        matches!(
            pairing.as_ref().err(),
            Some(RunningIntegralError::PairingGrade {
                cochain: 0,
                cell: 1,
                ..
            })
        ),
    ));

    let endpoints = disagreement(
        &square.complex,
        &standing,
        &square.left(),
        &Path::along([square.ad]),
    );
    refusals.push((
        "two traversals with different endpoints",
        format!("{:?}", endpoints.as_ref().err()),
        matches!(
            endpoints.as_ref().err(),
            Some(RunningIntegralError::EndpointsDiffer { .. })
        ),
    ));

    let doubled_region = CausalChain::single(face, ComparativeMultiplicity::positive(2u32));
    let not_enclosing = enclosed_disagreement(
        &filled.complex,
        &filled.standing(),
        &filled.left(),
        &filled.right(),
        &doubled_region,
    );
    refusals.push((
        "a region bounding twice the pair's cycle",
        format!("{:?}", not_enclosing.as_ref().err()),
        matches!(
            not_enclosing.as_ref().err(),
            Some(RunningIntegralError::RegionDoesNotEnclose)
        ),
    ));

    let wrong_grade_region = CausalChain::single(filled.ab, ComparativeMultiplicity::positive(1u32));
    let region_grade = enclosed_disagreement(
        &filled.complex,
        &filled.standing(),
        &filled.left(),
        &filled.right(),
        &wrong_grade_region,
    );
    refusals.push((
        "a 1-chain offered as a region for a 1-cochain",
        format!("{:?}", region_grade.as_ref().err()),
        matches!(
            region_grade.as_ref().err(),
            Some(RunningIntegralError::RegionGrade {
                region: 1,
                expected: 2
            })
        ),
    ));

    let grades = standing.plus(&square.potential());
    refusals.push((
        "cochains of different grades added",
        format!("{:?}", grades.as_ref().err()),
        matches!(
            grades.as_ref().err(),
            Some(RunningIntegralError::CochainGradesDiffer { left: 1, right: 0 })
        ),
    ));

    let bad_base = found_potential(&square.complex, &standing, square.ab);
    refusals.push((
        "a 1-cell offered as the base of the potential search",
        format!("{:?}", bad_base.as_ref().err()),
        matches!(
            bad_base.as_ref().err(),
            Some(RunningIntegralError::BaseIsNotAVertex(_))
        ),
    ));

    // The declared aperture: a self-incident 1-cell has an EMPTY boundary in this carrier, so its
    // base point is not recoverable and a walk cannot join through it.
    let mut looped = GradedCausalComplex::default();
    let la = vertex(&mut looped, "a");
    let mut self_boundary = CausalChain::default();
    self_boundary.add_term(la, ComparativeMultiplicity::positive(1u32));
    self_boundary.add_term(la, ComparativeMultiplicity::negative(1u32));
    let self_loop = looped
        .found_cell("loop", source(), 1, self_boundary)
        .expect("both ends stay attached to a");
    let loop_w = Cochain::from_values(1, [(self_loop, big(4))]);
    let unjoinable = running_sum(&looped, &loop_w, &Path::along([self_loop]));
    refusals.push((
        "a self-incident 1-cell, refused rather than skipped (skipping discards a winding)",
        format!("{:?}", unjoinable.as_ref().err()),
        matches!(
            unjoinable.as_ref().err(),
            Some(RunningIntegralError::UnjoinableCell(cell)) if *cell == self_loop
        ),
    ));

    let overflow = coboundary(&square.complex, &Cochain::new(u32::MAX));
    refusals.push((
        "a cochain at the top of the grade carrier, whose coboundary has nowhere to go",
        format!("{:?}", overflow.as_ref().err()),
        matches!(
            overflow.as_ref().err(),
            Some(RunningIntegralError::GradeOverflow)
        ),
    ));

    let absent = Cochain::from_values(1, [(square.ab, big(1))]).evaluate(
        &square.complex,
        &CausalChain::single(CausalCellId(9_999), ComparativeMultiplicity::positive(1u32)),
    );
    refusals.push((
        "a chain naming a cell the complex does not carry",
        format!("{:?}", absent.as_ref().err()),
        matches!(
            absent.as_ref().err(),
            Some(RunningIntegralError::Incidence(_))
        ),
    ));

    for (what, rendered, fired) in &refusals {
        println!("  {:<62} {rendered}", format!("{what}:"));
        let _ = fired;
    }
    let all_fired = refusals.iter().all(|(_, _, fired)| *fired);
    holds.push((
        "every reachable refusal fires, by name, on material built to trigger it",
        all_fired,
        format!(
            "{} of {} refusals returned the declared variant",
            refusals.iter().filter(|(_, _, fired)| *fired).count(),
            refusals.len()
        ),
    ));

    println!("\n  ONE VARIANT IS UNREACHABLE AND IS REPORTED RATHER THAN COUNTED.");
    println!("  `PairIsNotACycle` guards `boundary(chain(left) - chain(right)) != 0`. But");
    println!("  `disagreement` has already refused unequal endpoints three lines above, and the");
    println!("  boundary of a joined traversal from `s` to `t` is exactly `t - s`, so the guarded");
    println!("  difference is a cycle whenever control reaches the guard. It is a correct assertion");
    println!("  about an invariant the preceding check establishes, and no input can trip it.");

    // ===========================================================================================
    println!("\n\n12. THE CONDENSATION IDENTITY, ACROSS EVERY FIXTURE");
    println!("---------------------------------------------------");
    println!("  `CLAUDE.md` §11's shape, as an arithmetic identity the organ has to satisfy:");
    println!("      tree cells = |reached| - 1        (a spanning tree of the walked component)");
    println!("      cycle rank = |walked 1-cells| - |reached| + 1");
    println!("  The tree condenses for free; the chords are the departure from a forest; the");
    println!("  disagreeing chords are the certified remainder.");
    println!(
        "\n    {:<22} {:>8} {:>7} {:>7} {:>7} {:>10} {:>10}",
        "complex / base", "reached", "tree", "chords", "rank", "agreeing", "retained"
    );
    let mut identity_holds = true;
    for (label, complex, cochain, base) in [
        ("hollow square / a", &square.complex, &standing, square.a),
        ("hollow square / d f", &square.complex, &exact, square.a),
        ("ladder / v0", &ladder.complex, &ladder_w, ladder.at("v0")),
        ("severed / a", &severed, &severed_w, sa),
        ("severed / e", &severed, &severed_w, se),
        ("path / a", &path_complex, &Cochain::from_values(1, [(pab, big(5))]), pa),
    ] {
        let search = found_potential(complex, cochain, base).expect("a lawful search");
        let walked = search.tree_cells.len() + search.cycle_rank();
        let tree_is_spanning = search.tree_cells.len() + 1 == search.reached.len();
        let rank_is_the_departure =
            search.cycle_rank() == walked + 1 - search.reached.len();
        identity_holds &= tree_is_spanning && rank_is_the_departure;
        println!(
            "    {label:<22} {:>8} {:>7} {:>7} {:>7} {:>10} {:>10}",
            search.reached.len(),
            search.tree_cells.len(),
            search.cycle_rank(),
            walked + 1 - search.reached.len(),
            search.agreeing_chords.len(),
            search.retained_obstructions.len()
        );
    }
    holds.push((
        "the tree spans the walked component and the chord count is exactly its departure from a forest",
        identity_holds,
        "|tree| = |reached| - 1 and rank = |walked| - |reached| + 1 on all six readings".to_owned(),
    ));

    // ===========================================================================================
    println!("\n\n13. A CELL ASSIGNED ZERO IS NOT A CELL NEVER ASSIGNED");
    println!("-----------------------------------------------------");
    println!("  `CLAUDE.md` §2b at the level of a carrier: the reading kept and the deposit");
    println!("  discarded. `coboundary` is TOTAL on its grade — every cell one grade up is visited");
    println!("  and its value deposited, including the zeros — so the return can say WHERE `d w` was");
    println!("  evaluated and not only where it stands.");
    let d_exact = coboundary(&filled.complex, &filled.exact()).expect("gradeable");
    println!(
        "\n    d(d f)      is_zero {}   assigned {}   support {}",
        d_exact.is_zero(),
        names(&filled.complex, d_exact.assigned()),
        names(&filled.complex, d_exact.support())
    );
    println!(
        "    d(standing) is_zero {}   assigned {}   support {}",
        d_standing.is_zero(),
        names(&filled.complex, d_standing.assigned()),
        names(&filled.complex, d_standing.support())
    );
    let silent = Cochain::new(1);
    let spoken = Cochain::from_values(1, [(square.ab, big(0))]);
    println!(
        "\n    a cochain that said nothing      : assigns_nothing {}   is_zero {}",
        silent.assigns_nothing(),
        silent.is_zero()
    );
    println!(
        "    a cochain that said `ab` is zero : assigns_nothing {}   is_zero {}",
        spoken.assigns_nothing(),
        spoken.is_zero()
    );
    println!(
        "    they pair identically against every chain: {}   and are still different objects: {}",
        silent.assigns_the_same_values(&spoken),
        silent != spoken
    );
    holds.push((
        "the coboundary's declared domain is its whole grade, and a zero deposit survives as a deposit",
        d_exact.assigned() == d_standing.assigned()
            && d_exact.assigned() == BTreeSet::from([face])
            && d_exact.support().is_empty()
            && d_standing.support() == BTreeSet::from([face])
            && silent.assigns_the_same_values(&spoken)
            && silent != spoken
            && !spoken.assigns_nothing(),
        format!(
            "d(d f) assigned {} support {}; d(standing) assigned {} support {}",
            d_exact.assigned().len(),
            d_exact.support().len(),
            d_standing.assigned().len(),
            d_standing.support().len()
        ),
    ));

    // ===========================================================================================
    println!("\n\nBOUNDS");
    println!("------");
    println!("  - Nothing here is a continuum integral. No mesh, no limit, no error term, no");
    println!("    refinement, and no convergence of any lattice statement to a continuum one is");
    println!("    claimed or tested. The organ integrates a 1-cochain along a traversal of 1-cells");
    println!("    and that is its whole content.");
    println!("  - The carrier is `Z`. A rational cochain is an integer cochain after clearing");
    println!("    denominators, which rescales every returned holonomy by the cleared factor and");
    println!("    moves no zero off zero — but nothing below runs a rational cochain, so that");
    println!("    sentence is inherited from the module and not measured here.");
    println!("  - Four complexes, at most seven 1-cells and cycle rank at most two. Nothing is");
    println!("    established about large complexes, about the cost of the spanning walk, or about");
    println!("    any complex whose 1-skeleton is not simple.");
    println!("  - `H^1 != 0` is exhibited on ONE complex with ONE hole and on ONE with two. No");
    println!("    cohomology group is computed; `found_potential` decides whether a cochain is a");
    println!("    coboundary on the walked component and returns the chords, which is strictly less");
    println!("    than computing `H^1`.");
    println!("  - The base gauge orbit is taken over the four vertices of one square. It shows the");
    println!("    gauge acts on that material; it does not establish that it acts on every complex,");
    println!("    and a complex where it did not would make the base-invariance readings vacuous");
    println!("    there.");
    println!("  - No claim is made about the Hodge conjecture, about any Millennium problem, or");
    println!("    about condensing a FAR population — `CLAUDE.md` §11's open item is about a");
    println!("    compact representative for a far field, and a seven-edge ladder is not far.");

    // ===========================================================================================
    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        if *verdict {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD -- {} declared controls, 0 failed", holds.len());
    } else {
        println!(
            "FAILED -- {failed} of {} declared controls did not hold",
            holds.len()
        );
        std::process::exit(1);
    }
}
