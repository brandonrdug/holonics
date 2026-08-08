//! Drive `complex_system`: compress a real graded causal complex and return its conduct classes.
//!
//! The material is a 3x3 grid grown as a genuine complex — 9 vertices, 12 oriented 1-cells, and the
//! 4 square 2-cells whose boundaries close, checked by `found_cell`'s own `boundary(boundary) = 0`.
//! Nothing here is a fixture standing in for material: the same `GradedCausalComplex` that
//! `rebase_invariants_on`, `dilate`, `skein` and `closed_hull` already take.
//!
//! What is returned, in order:
//!
//! 1. the receiver family, each a `DilatedSection` with its own focus, horizon and walk order;
//! 2. the addresses each receiver assigns — the whole population, cells outside the horizon
//!    included, taken from `ComplexSystem::addresses` rather than re-derived here;
//! 3. the one-shot classes — what the receivers alone cannot tell apart;
//! 4. the conduct classes — what survives stepping across named 1-cells;
//! 5. the collapsed population, each pair with the shortest word that separates it;
//! 6. the same complex read at a narrower aperture, so the aperture is visibly a coordinate;
//! 7. the same complex under the **other reading** of the same sections, so the walk order is
//!    visibly a coordinate too — and the population of pairs the two readings disagree about;
//! 8. placement against a realizer population that is a second frame: the 1-cells, each reaching
//!    the ends it joins.
//!
//! `CLAUDE.md` §9 — *return the artifact*. Counts appear only alongside the populations they count.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::complex_system::{cell, item, AddressReading, ComplexSystem};
use holonic_engine::dilation::{covering_horizon, dilate, Horizon, WalkOrder};
use holonic_engine::placement::place;
use holonic_engine::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, Partition, ReceiverExactCompression,
    ReceiverId,
};
use holonic_engine::supported_realizers::RealizerId;

const SIDE: usize = 3;

fn source() -> BTreeSet<EventId> {
    BTreeSet::from([EventId(1)])
}

struct Grid {
    complex: GradedCausalComplex,
    vertex: BTreeMap<(usize, usize), CausalCellId>,
    horizontal: BTreeMap<(usize, usize), CausalCellId>,
    vertical: BTreeMap<(usize, usize), CausalCellId>,
    square: BTreeMap<(usize, usize), CausalCellId>,
}

/// Grow the grid. Every 1-cell is `[head] - [tail]`; every square is
/// `H(r,c) + V(r,c+1) - H(r+1,c) - V(r,c)`, whose boundary telescopes to zero — which `found_cell`
/// verifies rather than trusts.
fn grow() -> Grid {
    let mut complex = GradedCausalComplex::default();
    let mut vertex = BTreeMap::new();
    for row in 0..SIDE {
        for column in 0..SIDE {
            let id = complex
                .found_cell(
                    format!("v{row}{column}"),
                    source(),
                    0,
                    CausalChain::default(),
                )
                .expect("a vertex has no boundary");
            vertex.insert((row, column), id);
        }
    }

    let join = |complex: &mut GradedCausalComplex, name: String, tail, head| {
        let mut boundary = CausalChain::default();
        boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
        complex
            .found_cell(name, source(), 1, boundary)
            .expect("an edge closes")
    };

    let mut horizontal = BTreeMap::new();
    for row in 0..SIDE {
        for column in 0..SIDE - 1 {
            let id = join(
                &mut complex,
                format!("h{row}{column}"),
                vertex[&(row, column)],
                vertex[&(row, column + 1)],
            );
            horizontal.insert((row, column), id);
        }
    }
    let mut vertical = BTreeMap::new();
    for row in 0..SIDE - 1 {
        for column in 0..SIDE {
            let id = join(
                &mut complex,
                format!("w{row}{column}"),
                vertex[&(row, column)],
                vertex[&(row + 1, column)],
            );
            vertical.insert((row, column), id);
        }
    }

    let mut square = BTreeMap::new();
    for row in 0..SIDE - 1 {
        for column in 0..SIDE - 1 {
            let mut boundary = CausalChain::default();
            boundary.add_term(
                horizontal[&(row, column)],
                ComparativeMultiplicity::positive(1u32),
            );
            boundary.add_term(
                vertical[&(row, column + 1)],
                ComparativeMultiplicity::positive(1u32),
            );
            boundary.add_term(
                horizontal[&(row + 1, column)],
                ComparativeMultiplicity::negative(1u32),
            );
            boundary.add_term(
                vertical[&(row, column)],
                ComparativeMultiplicity::negative(1u32),
            );
            let id = complex
                .found_cell(format!("s{row}{column}"), source(), 2, boundary)
                .expect("a square's boundary telescopes to zero");
            square.insert((row, column), id);
        }
    }

    Grid {
        complex,
        vertex,
        horizontal,
        vertical,
        square,
    }
}

fn name(complex: &GradedCausalComplex, id: CausalCellId) -> String {
    complex
        .cell(id)
        .map(|body| body.name.clone())
        .unwrap_or_else(|_| format!("{id:?}"))
}

fn spell(complex: &GradedCausalComplex, block: &BTreeSet<ItemId>) -> String {
    let members: Vec<String> = block.iter().map(|held| name(complex, cell(*held))).collect();
    format!("{{{}}}", members.join(" "))
}

fn show_partition(complex: &GradedCausalComplex, label: &str, partition: &Partition) {
    println!("  {label} — {} blocks", partition.blocks.len());
    for (index, block) in partition.blocks.iter().enumerate() {
        let mark = if block.len() > 1 { "*" } else { " " };
        println!("   {mark}[{index:>2}] {}", spell(complex, block));
    }
}

fn show_pairs(complex: &GradedCausalComplex, label: &str, pairs: &[(ItemId, ItemId)]) {
    println!("  {label} — {} pairs", pairs.len());
    if pairs.is_empty() {
        println!("    (EMPTY)");
    }
    for (left, right) in pairs {
        println!(
            "    {:>4} | {}",
            name(complex, cell(*left)),
            name(complex, cell(*right))
        );
    }
}

/// Walk a returned word from one cell using the complex's own vocabulary, or report the terminus.
///
/// `ComplexSystem::crossing` is `successor` in cells rather than items, and this is what it is for:
/// a returned `distinguishing_word` is a list of `InputId` positions, and reading it back as an
/// actual walk over the complex is the check that the word names a step the material has.
fn walk(system: &ComplexSystem, start: CausalCellId, word: &[InputId]) -> Option<CausalCellId> {
    let mut here = start;
    for step in word {
        here = system.crossing(here, system.inputs[step.0 as usize])?;
    }
    Some(here)
}

fn show_collapsed(
    complex: &GradedCausalComplex,
    system: &ComplexSystem,
    reading: &ReceiverExactCompression,
) {
    println!(
        "  collapsed population — {} pairs the receivers merged and conduct separates",
        reading.collapsed.len()
    );
    if reading.collapsed.is_empty() {
        println!("    (empty: this reading is receiver-exact)");
    }
    for pair in &reading.collapsed {
        let word: Vec<String> = pair
            .distinguishing_word
            .iter()
            .map(|step| name(complex, system.inputs[step.0 as usize]))
            .collect();
        let how = if pair.separated_by_terminus {
            "terminus".to_owned()
        } else {
            match pair.witness {
                Some((receiver, Observation(left), Observation(right))) => {
                    format!("receiver {} reads {left} vs {right}", receiver.0)
                }
                None => "unwitnessed".to_owned(),
            }
        };
        let landing = |from: ItemId| -> String {
            walk(system, cell(from), &pair.distinguishing_word)
                .map_or_else(|| "terminus".to_owned(), |there| name(complex, there))
        };
        println!(
            "    {:>4} | {:<4}  after [{}]  by {how}   {} -> {}  against  {} -> {}",
            name(complex, cell(pair.left)),
            name(complex, cell(pair.right)),
            word.join(" "),
            name(complex, cell(pair.left)),
            landing(pair.left),
            name(complex, cell(pair.right)),
            landing(pair.right),
        );
    }
}

/// The receiver's own return, taken from the organ rather than re-derived here.
///
/// `addresses` returns the whole cell population, the cells outside the horizon included at
/// `Observation(0)` — which is why the "address 0" line below is a return and not a subtraction the
/// driver performed on the side.
fn show_receiver(complex: &GradedCausalComplex, system: &ComplexSystem, index: usize) {
    let section = &system.receivers[index];
    println!(
        "  receiver {index}: focus {}  horizon {:?}  order {}  holds {} cells  covering {}",
        name(complex, section.lineage.focus),
        section.lineage.horizon,
        section.lineage.order.name(),
        section.support.len(),
        section.lineage.is_covering(),
    );
    if !section.lineage.closure_added.is_empty() {
        let pivoted: Vec<String> = section
            .lineage
            .closure_added
            .iter()
            .map(|id| name(complex, *id))
            .collect();
        println!("    pivoted off to close: {}", pivoted.join(" "));
    }
    if !section.lineage.open_frontier.is_empty() {
        let frontier: Vec<String> = section
            .lineage
            .open_frontier
            .iter()
            .map(|id| name(complex, *id))
            .collect();
        println!("    open frontier: {}", frontier.join(" "));
    }

    let mut by_address: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    for (id, Observation(address)) in system.addresses(ReceiverId(index as u64)) {
        by_address.entry(address).or_default().push(name(complex, id));
    }
    for (address, held) in &by_address {
        let label = if *address == 0 {
            "  0 (outside this horizon)".to_owned()
        } else {
            format!("{address:>3}")
        };
        println!("    address {label} : {}", held.join(" "));
    }
}

/// Which cells two address populations over one complex disagree about, with both readings.
fn moved(
    left: &[(CausalCellId, Observation)],
    right: &[(CausalCellId, Observation)],
) -> Vec<(CausalCellId, Observation, Observation)> {
    left.iter()
        .zip(right.iter())
        .filter(|((_, here), (_, there))| here != there)
        .map(|((id, here), (_, there))| (*id, *here, *there))
        .collect()
}

fn show_moved(
    complex: &GradedCausalComplex,
    label: &str,
    population: &[(CausalCellId, Observation, Observation)],
) {
    println!("  {label} — {} cells", population.len());
    if population.is_empty() {
        println!("    (EMPTY — nothing moved)");
    }
    for (id, Observation(here), Observation(there)) in population {
        println!("    {:>4} : {here} -> {there}", name(complex, *id));
    }
}

fn main() {
    let grid = grow();
    let complex = &grid.complex;
    complex.validate().expect("the grown complex validates");

    println!("== the material ==");
    println!("  schema {}", complex.schema);
    let f_vector = complex.f_vector();
    for (grade, count) in &f_vector {
        println!("  grade {grade}: {count} cells");
    }
    println!(
        "  {} cells total: {} horizontal and {} vertical 1-cells, {} squares",
        complex.cells().len(),
        grid.horizontal.len(),
        grid.vertical.len(),
        grid.square.len(),
    );

    let corner = grid.vertex[&(0, 0)];
    let far_corner = grid.vertex[&(SIDE - 1, SIDE - 1)];
    let centre = grid.vertex[&(1, 1)];
    println!(
        "  covering horizon from {}: {}",
        name(complex, corner),
        covering_horizon(complex, corner).expect("the corner is a cell")
    );

    let receivers = vec![
        dilate(complex, corner, Horizon::Unbounded, WalkOrder::Breadth).expect("corner dilates"),
        dilate(complex, far_corner, Horizon::Steps(4), WalkOrder::Depth).expect("corner dilates"),
        dilate(complex, centre, Horizon::Steps(2), WalkOrder::Breadth).expect("centre dilates"),
    ];

    let every_edge = ComplexSystem::every_one_cell(complex);
    let system = ComplexSystem::declare(
        complex,
        AddressReading::Metric,
        receivers.clone(),
        every_edge.clone(),
    )
    .expect("every declared input is a 1-cell of this complex and every section was measured on it");
    let reading = compress(&system);

    println!("\n== the receiver family, read metrically ==");
    for index in 0..system.receivers.len() {
        show_receiver(complex, &system, index);
    }

    println!("\n== the reading at the full aperture ==");
    println!(
        "  {} items, {} receivers, {} admitted steps, {} refinement rounds",
        system.items().len(),
        system.receivers().len(),
        system.inputs().len(),
        reading.rounds,
    );
    show_partition(complex, "one-shot classes", &reading.one_shot);
    show_partition(complex, "conduct classes", &reading.conduct);
    show_collapsed(complex, &system, &reading);

    // The aperture is a coordinate, so read the same complex through a narrower one. The narrow
    // aperture is the **boundary of one 2-cell** — the complex's own structure supplying the
    // restriction rather than an author's choice of edges. The receivers are unchanged.
    //
    // The horizontal-only aperture was tried first and returned NOTHING: every one-shot-merged
    // vertex pair still had a horizontal edge incident to one and not the other, so narrowing
    // changed no class. That is the fixture-cannot-vary-the-property defect, and it is recorded
    // here rather than quietly replaced. An aperture only merges what it holds no step between.
    let far_square = grid.square[&(SIDE - 2, SIDE - 2)];
    let one_face_only: Vec<CausalCellId> = complex
        .cell(far_square)
        .expect("the square is a cell")
        .boundary
        .support()
        .into_iter()
        .collect();
    let narrow = ComplexSystem::declare(
        complex,
        AddressReading::Metric,
        receivers.clone(),
        one_face_only,
    )
    .expect("a 2-cell's boundary is made of 1-cells");
    let narrow_reading = compress(&narrow);

    println!("\n== the same complex at a narrower aperture ==");
    println!(
        "  {} admitted steps — the boundary of {} — against {} at the full aperture",
        narrow.inputs().len(),
        name(complex, far_square),
        system.inputs().len(),
    );
    show_partition(complex, "conduct classes", &narrow_reading.conduct);
    show_collapsed(complex, &narrow, &narrow_reading);
    let kept: Vec<(ItemId, ItemId)> = narrow_reading
        .conduct
        .identified_pairs()
        .difference(&reading.conduct.identified_pairs())
        .copied()
        .collect();
    show_pairs(
        complex,
        "held together by the narrow aperture and separated by the full one",
        &kept,
    );

    // The walk order is a coordinate too, and the only way that is visible from here is if the
    // adapter reads the chart as well as the invariant. `AddressReading::Chart` is `1 + position in
    // lineage.reached`; `Metric` is `1 + incidence distance`. `dilate` computes the distance
    // breadth-first whatever order it walked, so:
    //
    //   the metric addresses must NOT move when the same focus is re-walked in the other order
    //   the chart  addresses MUST move, or the chart has been dropped and any gauge claim made
    //                        through this adapter is a comparison of a reading against itself
    //
    // Receiver 1 walks depth-first at horizon four. Re-walk it breadth-first and read both ways.
    let depth = receivers[1].clone();
    let breadth = dilate(complex, far_corner, Horizon::Steps(4), WalkOrder::Breadth)
        .expect("corner dilates");
    println!("\n== the gauge: what the walk order moves and what it does not ==");
    println!(
        "  one focus ({}), one horizon (4 steps), two orders. The charts differ: {}",
        name(complex, far_corner),
        depth.lineage.reached != breadth.lineage.reached,
    );
    for reading_kind in [AddressReading::Metric, AddressReading::Chart] {
        let by_depth =
            ComplexSystem::declare(complex, reading_kind, vec![depth.clone()], every_edge.clone())
                .expect("the section was measured on this complex");
        let by_breadth = ComplexSystem::declare(
            complex,
            reading_kind,
            vec![breadth.clone()],
            every_edge.clone(),
        )
        .expect("the section was measured on this complex");
        let population = moved(
            &by_depth.addresses(ReceiverId(0)),
            &by_breadth.addresses(ReceiverId(0)),
        );
        show_moved(
            complex,
            &format!("{reading_kind:?}: addresses that moved depth -> breadth"),
            &population,
        );
    }

    // And the two readings of the SAME sections return two conducts.
    let by_chart = ComplexSystem::declare(
        complex,
        AddressReading::Chart,
        receivers.clone(),
        every_edge.clone(),
    )
    .expect("the sections were measured on this complex");
    let chart_reading = compress(&by_chart);

    println!("\n== the same sections under the chart reading ==");
    show_partition(complex, "conduct classes", &chart_reading.conduct);
    let metric_pairs = reading.conduct.identified_pairs();
    let chart_pairs = chart_reading.conduct.identified_pairs();
    show_pairs(
        complex,
        "held together by the metric reading and split by the chart",
        &metric_pairs.difference(&chart_pairs).copied().collect::<Vec<_>>(),
    );
    show_pairs(
        complex,
        "held together by the chart reading and split by the metric — a walk position refines a \
         distance, so this must be empty",
        &chart_pairs.difference(&metric_pairs).copied().collect::<Vec<_>>(),
    );

    // Placement, against a realizer population that is a SECOND frame. The receivers are dilated
    // sections; the realizers are the complex's own 1-cells, each reaching the ends it joins. A
    // section auditing itself would have one frame and could not return an obstruction.
    let realizer_of: Vec<CausalCellId> = every_edge.clone();
    let realizers: Vec<RealizerId> = (0..realizer_of.len() as u64).map(RealizerId).collect();
    let placed = place(&system, &realizers, |realizer| {
        complex
            .cell(realizer_of[realizer.0 as usize])
            .expect("a declared realizer is a cell")
            .boundary
            .support()
            .into_iter()
            .map(item)
            .collect()
    });

    println!("\n== placement: what a realizer paid for ==");
    println!(
        "  {} realizers (the 1-cells), each reaching the ends it joins;  closed: {}",
        realizers.len(),
        placed.closed(),
    );
    println!("  STANDING — {} classes", placed.standing.len());
    for standing in &placed.standing {
        let paid: Vec<String> = standing
            .realizers
            .iter()
            .map(|realizer| name(complex, realizer_of[realizer.0 as usize]))
            .collect();
        println!(
            "    [{:>2}] {}  paid by {}",
            standing.class,
            spell(complex, &standing.members),
            paid.join(" "),
        );
    }
    println!("  OPEN — {} classes", placed.open.len());
    for open in &placed.open {
        let multiple = open
            .reached_only_in_multiple
            .as_ref()
            .map(|factor| format!("  reached only in multiple {factor}"))
            .unwrap_or_default();
        println!(
            "    [{:>2}] {}{multiple}",
            open.class,
            spell(complex, &open.members)
        );
    }

    println!("\n== the free and torsion obstruction ==");
    println!(
        "  realizer extent {}   class extent {}   free obstruction {}",
        placed.support.realizer_extent,
        placed.support.class_extent,
        placed.support.free_obstruction(),
    );
    let torsion = placed.support.torsion_obstruction();
    println!(
        "  torsion obstruction: {}",
        if torsion.is_empty() {
            "none — every reached class is reached integrally".to_owned()
        } else {
            torsion
                .iter()
                .map(|factor| format!("Z/{factor}"))
                .collect::<Vec<_>>()
                .join(" ")
        }
    );
    // A second frame on the rank, from the graph rather than from Smith normal form: the unsigned
    // vertex-edge incidence of a connected graph has rank n when it is not bipartite and n-1 when it
    // is. The grid IS bipartite, so nine reached vertex classes must return rank eight, and the free
    // obstruction must exceed the count of unreached classes by exactly that one.
    //
    // `unreached` is the classes NO realizer reaches, not `open.len()`. OPEN also holds classes that
    // ARE reached, only in multiple, and those carry a nonzero column — so subtracting `open.len()`
    // underflows as soon as any such class exists. It does not on this bipartite grid, which is
    // exactly why the wrong form sat here returning a plausible number.
    let unreached = placed
        .open
        .iter()
        .filter(|open| open.reached_only_in_multiple.is_none())
        .count();
    let in_multiple = placed.open.len() - unreached;
    let deficiency = placed
        .support
        .free_obstruction()
        .checked_sub(unreached)
        .expect(
            "a class no realizer reaches contributes a zero column, so the rank deficiency is at \
             least the count of such classes",
        );
    println!(
        "  {} vertex classes are reached and the grid's 1-skeleton is bipartite, so the rank is {}",
        placed.standing.len(),
        placed.support.supported_rank,
    );
    println!(
        "  free obstruction {} = {unreached} classes no realizer reaches + {deficiency} rank \
         deficiency  ({in_multiple} further classes are reached only in multiple)",
        placed.support.free_obstruction(),
    );

    println!("\n== what the grades and the squares did ==");
    let square_classes: BTreeSet<usize> = grid
        .square
        .values()
        .filter_map(|id| reading.conduct.block_of(item(*id)))
        .collect();
    println!(
        "  the {} squares land in {} conduct classes and are termini for every input — the declared",
        grid.square.len(),
        square_classes.len(),
    );
    println!("  1-skeleton aperture, forced by found_cell's grade law and visible in the return");
    let open_cells: Vec<String> = grid
        .square
        .values()
        .chain(grid.vertical.values())
        .filter(|id| {
            placed
                .open
                .iter()
                .any(|open| open.members.contains(&item(**id)))
        })
        .map(|id| name(complex, *id))
        .collect();
    println!("  cells in OPEN classes: {}", open_cells.join(" "));
}
