//! The exact integer invariants of a **singly graded** causal complex.
//!
//! ## What this is, and what it is not
//!
//! `CONSTRUCTION_STATE.md:91` states the position this driver must not overstate:
//!
//! > **Hodge realization / cycle class** | re-establish | no owner. `Hodge` in the live body names
//! > the *cellular-sheaf Laplacian* in `sheaf_diffusion.rs`, a discrete differential operator —
//! > **not** the supported-realization mechanism. Do not read one for the other.
//!
//! So there is **no `(p, q)` bigrading in this repository and no Hodge decomposition**. A
//! `GradedCausalComplex` carries exactly one grading — the chain degree `k` of
//! `algebraic.rs::CausalCell::grade`, which its own doc comment says implies no ambient coordinate
//! dimension. Everything this driver emits is indexed by that single `k`. Nothing here is a Hodge
//! diamond, nothing here splits a grade into `h^{p,q}`, and the figure built from this TSV must say
//! so on its face.
//!
//! What it does emit is the thing `rebase_invariants.rs` exists to return: the integer homology of
//! a genuine complex — free rank *and* torsion — where a rational rank would keep the first and
//! destroy the second.
//!
//! ## The fixture is derived here, not transcribed
//!
//! A hardcoded face list would be a number I asserted. Instead this enumerates every one of the
//! `C(20, 10)` ten-triangle subsets of the twenty triangles on six vertices and keeps those that
//! are closed surfaces: every edge carrying exactly two triangles, every vertex link a single
//! 5-cycle. The search is exhaustive and its result is a *measurement* — including how many such
//! subsets exist, which is printed rather than assumed.
//!
//! The surviving complex has `chi = 6 - 15 + 10 = 1`. It is then handed to the module's own
//! constructors — `SimplicialComplex::{found_vertex, found_face}` and
//! `SimplicialIncidenceReceipt::realize`, which routes every cell through
//! `GradedCausalComplex::found_cell` and therefore through the `d d = 0` refusal at
//! `algebraic.rs:293` — and its invariants are read by `rebase_invariants`.
//!
//! ## Three falsifiers, all of which can fail
//!
//! 1. **Pivot rule.** All three `PivotRule` variants must return byte-identical invariants;
//!    `invariants_agree` decides it. A pivot order is a solver coordinate and must not reach a
//!    returned number.
//! 2. **Euler characteristic.** The alternating sum of the Betti numbers must equal the alternating
//!    sum of the cell counts. Independent of every rebase.
//! 3. **Divisibility.** Every Smith normal form returned must satisfy `d_i | d_{i+1}`.
//!
//! ## The orientability probe is a refusal, reported as one
//!
//! `SimplicialComplex::found_hinge` refuses an edge whose two cofaces carry the same hand
//! (`SimplicialError::FaceOrientationConflict`). This driver sweeps all `2^10` assignments of a
//! hand to each triangle and counts how many make *every* edge admit a hinge. If that count is
//! zero, the complex is non-orientable and the module said so by refusing — an exact, exhaustive
//! statement, not a description.
//!
//! ## Carrier
//!
//! Every number is `BigInt` or `Rat`. There is no `f32` or `f64` anywhere in this file, and every
//! emitted field goes through `format_rat`, so the TSV carries exact rationals and never a decimal.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::Path;

use holonic_engine::algebraic::{CausalCellId, GradedCausalComplex, SimplicialIncidenceReceipt};
use holonic_engine::causal::EventId;
use holonic_engine::rebase_invariants::{
    IntegerMatrix, PivotRule, RebaseInvariants, boundary_matrix, invariants_agree,
    rebase_invariants, smith_normal_form,
};
use holonic_engine::simplicial::{
    Edge, FaceId, OrientedFace, SimplicialComplex, SimplicialError, VertexId,
};
use num_bigint::BigInt;
use relational_geometry::exact::{Rat, format_rat};

/// Vertices the search runs over. Six is the smallest count on which a closed surface other than
/// the boundary of a tetrahedron can be triangulated at all.
const VERTICES: usize = 6;
/// Triangles a closed surface on `VERTICES` vertices must carry, from `chi` and the fact that every
/// edge of a closed surface has exactly two cofaces.
const TRIANGLES: usize = 10;

/// Exact integers only. This is the single conversion point into the emitted text and it is exact.
fn exact(value: impl Into<BigInt>) -> String {
    format_rat(&Rat::from_integer(value.into()))
}

fn exact_big(value: &BigInt) -> String {
    format_rat(&Rat::from_integer(value.clone()))
}

/// Every three-element subset of the vertex set, in ascending order.
fn all_triangles() -> Vec<[usize; 3]> {
    let mut out = Vec::new();
    for a in 0..VERTICES {
        for b in a + 1..VERTICES {
            for c in b + 1..VERTICES {
                out.push([a, b, c]);
            }
        }
    }
    out
}

fn edges_of(triangle: &[usize; 3]) -> [(usize, usize); 3] {
    [
        (triangle[0], triangle[1]),
        (triangle[1], triangle[2]),
        (triangle[0], triangle[2]),
    ]
}

/// A single cycle through every vertex of the link, walked rather than inferred from degrees.
fn link_is_one_cycle(link: &[(usize, usize)]) -> bool {
    if link.len() != VERTICES - 1 {
        return false;
    }
    let mut adjacency: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (left, right) in link {
        adjacency.entry(*left).or_default().push(*right);
        adjacency.entry(*right).or_default().push(*left);
    }
    if adjacency.len() != link.len() || adjacency.values().any(|neighbours| neighbours.len() != 2) {
        return false;
    }
    let start = *adjacency.keys().next().expect("link is nonempty");
    let mut seen = BTreeSet::from([start]);
    let mut previous = start;
    let mut current = adjacency[&start][0];
    while current != start {
        if !seen.insert(current) {
            return false;
        }
        let next = adjacency[&current]
            .iter()
            .copied()
            .find(|candidate| *candidate != previous);
        match next {
            Some(step) => {
                previous = current;
                current = step;
            }
            None => return false,
        }
    }
    seen.len() == adjacency.len()
}

/// Closed surface: every edge has exactly two triangles and every vertex link is one cycle.
fn is_closed_surface(selection: &[[usize; 3]]) -> bool {
    let mut edge_count: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for triangle in selection {
        for edge in edges_of(triangle) {
            *edge_count.entry(edge).or_default() += 1;
        }
    }
    if edge_count.values().any(|count| *count != 2) {
        return false;
    }
    (0..VERTICES).all(|vertex| {
        let link: Vec<(usize, usize)> = selection
            .iter()
            .filter(|triangle| triangle.contains(&vertex))
            .map(|triangle| {
                let mut rest = triangle.iter().copied().filter(|v| *v != vertex);
                (
                    rest.next().expect("a triangle has three vertices"),
                    rest.next().expect("a triangle has three vertices"),
                )
            })
            .collect();
        link_is_one_cycle(&link)
    })
}

/// Exhaustive over every ten-subset of the twenty triangles. Returns all of them, so the count is
/// a measurement.
fn closed_surfaces_on_six_vertices() -> Vec<Vec<[usize; 3]>> {
    let triangles = all_triangles();
    let mut found = Vec::new();
    for mask in 0u32..(1u32 << triangles.len()) {
        if mask.count_ones() as usize != TRIANGLES {
            continue;
        }
        let selection: Vec<[usize; 3]> = triangles
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, triangle)| *triangle)
            .collect();
        if is_closed_surface(&selection) {
            found.push(selection);
        }
    }
    found
}

/// How many hands-per-triangle assignments make **every** edge admit a hinge.
///
/// A hinge refuses when its two cofaces carry the same hand. Sweeping all `2^n` assignments and
/// finding none is an exhaustive proof of non-orientability, spoken in the module's own refusal.
fn coherent_orientation_count(selection: &[[usize; 3]]) -> (usize, usize) {
    let assignments = 1usize << selection.len();
    let mut coherent = 0usize;
    for assignment in 0..assignments {
        let mut hands: BTreeMap<Edge, Vec<i8>> = BTreeMap::new();
        for (index, triangle) in selection.iter().enumerate() {
            let flipped = assignment & (1 << index) != 0;
            let vertices = if flipped {
                [
                    VertexId(triangle[0] as u64 + 1),
                    VertexId(triangle[2] as u64 + 1),
                    VertexId(triangle[1] as u64 + 1),
                ]
            } else {
                [
                    VertexId(triangle[0] as u64 + 1),
                    VertexId(triangle[1] as u64 + 1),
                    VertexId(triangle[2] as u64 + 1),
                ]
            };
            // The module's own orientation law, not a reimplementation of it.
            let face = OrientedFace {
                id: FaceId(index as u64 + 1),
                name: String::new(),
                source_event: EventId(1),
                vertices,
            };
            for (edge, hand) in face.boundary() {
                hands.entry(edge).or_default().push(hand);
            }
        }
        if hands
            .values()
            .all(|incident| incident.len() == 2 && incident[0] != incident[1])
        {
            coherent += 1;
        }
    }
    (coherent, assignments)
}

/// Ask the module for a hinge at every edge under the ascending-vertex orientation, and keep the
/// refusals verbatim.
fn hinge_refusals(source: &SimplicialComplex) -> (usize, usize, Vec<String>) {
    let mut probe = source.clone();
    let edges: BTreeSet<Edge> = source
        .faces
        .values()
        .flat_map(|face| face.boundary().map(|(edge, _)| edge))
        .collect();
    let total = edges.len();
    let mut refusals = Vec::new();
    let mut founded = 0usize;
    for (index, edge) in edges.iter().enumerate() {
        match probe.found_hinge(format!("hinge-{index}"), EventId(1), *edge) {
            Ok(_) => founded += 1,
            Err(error) => refusals.push(match error {
                SimplicialError::FaceOrientationConflict { edge, left, right } => format!(
                    "edge({:?},{:?}): faces {left:?} and {right:?} carry the same hand",
                    edge.lower, edge.upper
                ),
                other => format!("{other}"),
            }),
        }
    }
    (founded, total, refusals)
}

/// Cell names at one grade, in the complex's own `BTreeMap` order — the order `boundary_matrix`
/// uses for its rows and columns.
fn cell_names_at(complex: &GradedCausalComplex, grade: u32) -> Vec<(CausalCellId, String)> {
    complex
        .cells()
        .values()
        .filter(|cell| cell.grade == grade)
        .map(|cell| (cell.id, cell.name.clone()))
        .collect()
}

fn write_grades(path: &Path, invariants: &RebaseInvariants) -> std::io::Result<()> {
    let mut file = fs::File::create(path)?;
    writeln!(
        file,
        "grade\tcells\tboundary_rank\tfilling_rank\tbetti\ttorsion_factors"
    )?;
    for grade in &invariants.grades {
        let torsion = if grade.torsion.is_empty() {
            "-".to_owned()
        } else {
            grade
                .torsion
                .iter()
                .map(exact_big)
                .collect::<Vec<_>>()
                .join(";")
        };
        writeln!(
            file,
            "{}\t{}\t{}\t{}\t{}\t{torsion}",
            exact(grade.grade),
            exact(grade.cells as u64),
            exact(grade.boundary_rank as u64),
            exact(grade.filling_rank as u64),
            exact(grade.betti as u64),
        )?;
    }
    Ok(())
}

fn write_ladder(
    path: &Path,
    complex: &GradedCausalComplex,
    top: u32,
    rule: PivotRule,
) -> std::io::Result<Vec<(u32, Vec<BigInt>, bool)>> {
    let mut file = fs::File::create(path)?;
    writeln!(file, "grade\tposition\tfactor\trows\tcolumns")?;
    let mut ladders = Vec::new();
    for grade in 1..=top {
        let matrix = boundary_matrix(complex, grade).expect("the complex answers its own grades");
        let form = smith_normal_form(&matrix, rule);
        for (position, factor) in form.factors.iter().enumerate() {
            writeln!(
                file,
                "{}\t{}\t{}\t{}\t{}",
                exact(grade),
                exact(position as u64 + 1),
                exact_big(factor),
                exact(matrix.rows() as u64),
                exact(matrix.columns() as u64),
            )?;
        }
        ladders.push((grade, form.factors.clone(), form.divisibility_holds()));
    }
    Ok(ladders)
}

fn write_matrix(
    path: &Path,
    complex: &GradedCausalComplex,
    matrix: &IntegerMatrix,
    grade: u32,
) -> std::io::Result<()> {
    let rows = cell_names_at(complex, grade - 1);
    let columns = cell_names_at(complex, grade);
    let mut file = fs::File::create(path)?;
    writeln!(file, "grade\trow\tcolumn\tvalue\trow_name\tcolumn_name")?;
    for row in 0..matrix.rows() {
        for column in 0..matrix.columns() {
            writeln!(
                file,
                "{}\t{}\t{}\t{}\t{}\t{}",
                exact(grade),
                exact(row as u64),
                exact(column as u64),
                exact_big(matrix.at(row, column)),
                rows[row].1,
                columns[column].1,
            )?;
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out = Path::new("target/graded-invariants");
    fs::create_dir_all(out)?;

    // ---- the fixture, derived exhaustively -------------------------------------------------
    let surfaces = closed_surfaces_on_six_vertices();
    println!("closed surfaces on {VERTICES} vertices with {TRIANGLES} triangles: {}", surfaces.len());
    let Some(selection) = surfaces.first() else {
        println!("REFUSED: the exhaustive search found no closed surface; nothing to read.");
        return Ok(());
    };
    println!("selected triangulation: {selection:?}");

    let (coherent, assignments) = coherent_orientation_count(selection);
    println!(
        "coherent orientations: {coherent} of {assignments} hand assignments admit a hinge at every edge"
    );

    // ---- through the module's own constructors ---------------------------------------------
    let mut source = SimplicialComplex::default();
    let vertices: Vec<VertexId> = (0..VERTICES)
        .map(|index| source.found_vertex(format!("v{index}"), EventId(index as u64 + 1)))
        .collect();
    for (index, triangle) in selection.iter().enumerate() {
        source.found_face(
            format!("f{}{}{}", triangle[0], triangle[1], triangle[2]),
            EventId(index as u64 + 100),
            [
                vertices[triangle[0]],
                vertices[triangle[1]],
                vertices[triangle[2]],
            ],
        )?;
    }

    let (founded, edge_total, refusals) = hinge_refusals(&source);
    println!("hinges founded: {founded} of {edge_total}; refusals: {}", refusals.len());
    for refusal in &refusals {
        println!("  REFUSED {refusal}");
    }

    let receipt = SimplicialIncidenceReceipt::realize(&source)?;
    let complex = receipt.incidence;
    complex.validate()?;
    let top = complex.dimension().expect("a founded complex carries a grade");
    println!("f-vector: {:?}", complex.f_vector());

    // ---- the invariants, and the falsifier that they do not move ---------------------------
    let mut readings = Vec::new();
    for rule in PivotRule::ALL {
        readings.push((rule, rebase_invariants(&complex, rule)?));
    }
    let reference = &readings[0].1;
    let agreed = readings
        .iter()
        .all(|(_, reading)| invariants_agree(reference, reading));
    println!("three pivot rules agree: {agreed}");
    if !agreed {
        println!("REFUSED: a pivot rule reached a returned invariant; emitting nothing.");
        return Ok(());
    }

    println!("betti vector: {:?}", reference.betti_vector());
    println!(
        "total torsion: {:?}",
        reference.total_torsion().iter().map(exact_big).collect::<Vec<_>>()
    );
    println!(
        "euler characteristic from betti: {} ; from cells: {}",
        exact(reference.euler_characteristic()),
        exact(reference.cell_euler_characteristic()),
    );
    let euler_agrees = reference.euler_characteristic() == reference.cell_euler_characteristic();
    println!("euler cross-check holds: {euler_agrees}");

    // ---- emit ------------------------------------------------------------------------------
    write_grades(&out.join("grade_invariants.tsv"), reference)?;
    let ladders = write_ladder(
        &out.join("smith_ladder.tsv"),
        &complex,
        top,
        PivotRule::SmallestMagnitude,
    )?;
    for (grade, factors, divides) in &ladders {
        println!(
            "d_{grade} invariant factors: [{}] (divisibility holds: {divides})",
            factors.iter().map(exact_big).collect::<Vec<_>>().join(" | ")
        );
    }
    let filling = boundary_matrix(&complex, top)?;
    write_matrix(&out.join("boundary_matrix.tsv"), &complex, &filling, top)?;
    println!(
        "d_{top} is {} x {}",
        exact(filling.rows() as u64),
        exact(filling.columns() as u64)
    );

    let mut meta = fs::File::create(out.join("provenance.tsv"))?;
    writeln!(meta, "key\tvalue")?;
    for (key, value) in [
        ("schema", complex.schema.clone()),
        ("invariant_schema", reference.schema.clone()),
        ("grading", "single (chain degree k); no (p,q) bigrading exists in this repository".to_owned()),
        ("vertices", exact(VERTICES as u64)),
        ("closed_surfaces_found", exact(surfaces.len() as u64)),
        ("coherent_orientations", exact(coherent as u64)),
        ("orientation_assignments", exact(assignments as u64)),
        ("hinges_founded", exact(founded as u64)),
        ("hinges_refused", exact(refusals.len() as u64)),
        ("edges", exact(edge_total as u64)),
        ("pivot_rules_agree", agreed.to_string()),
        ("euler_cross_check", euler_agrees.to_string()),
        ("euler_characteristic", exact(reference.euler_characteristic())),
        (
            "betti_vector",
            reference
                .betti_vector()
                .iter()
                .map(|b| exact(*b as u64))
                .collect::<Vec<_>>()
                .join(";"),
        ),
        (
            "total_torsion",
            reference
                .total_torsion()
                .iter()
                .map(exact_big)
                .collect::<Vec<_>>()
                .join(";"),
        ),
    ] {
        writeln!(meta, "{key}\t{value}")?;
    }

    println!("wrote {}", out.display());
    Ok(())
}
