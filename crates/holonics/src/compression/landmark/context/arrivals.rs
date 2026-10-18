//! Data-only topology schedule for a continuing landmark tree.
//!
//! This pass reads typed addresses and class arrivals. It records all opening-state query paths
//! and class-transition paths, then advances only topology, labels, node masses and carries in the
//! sequential founding order. Chart values are intentionally opaque here; the chart pass consumes
//! the segment references and structural events emitted by this module.

use std::collections::HashMap;

use rayon::prelude::*;

use super::{
    Arena, Chart, ContextError, LandmarkFace, Landmarks, Letter, Nodes, Parting, Splits, Stop,
    Topology, carry_at, shape,
};

pub(super) type SegmentId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegmentRef {
    Stored(SegmentId),
    /// A query's virtual upper chart at a parting. The chart pass derives it from `source` and
    /// `depth`; the topology pass never evaluates `Law::part`.
    PartingUpper {
        source: SegmentId,
        depth: usize,
    },
}

/// A stored level in an opening-state path. `count_node` is the physical node whose masses supply
/// the read; at a query-only parting, `segment` is virtual while those masses remain on the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PathLevel {
    pub node: u32,
    pub segment: SegmentRef,
    pub bottom: usize,
    pub halves: [u32; 2],
    pub count_node: u32,
    pub child: Option<SegmentRef>,
}

/// One branch's opening-state path for a read-only all-class split query or a class transition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BranchPath {
    pub tree: usize,
    pub branch: usize,
    pub dyadic: usize,
    pub symbol: usize,
    pub stop: Stop,
    /// The physical nodes returned by the opening topology walk, before any same-cell relink.
    pub source_nodes: Vec<u32>,
    /// Chart segments owning `source_nodes` at cell opening. A same-cell parting changes the
    /// transition's `levels`, but the read and split initialization still use these segments.
    pub source_segments: Vec<SegmentId>,
    pub levels: Vec<PathLevel>,
    /// Opening masses, separate from post-event per-arrival mass snapshots.
    pub opening_halves: Vec<[u32; 2]>,
    pub parting_depth: Option<usize>,
    pub root_halves: Option<[u32; 2]>,
    pub prior_child: bool,
}

/// A segment is the life of one stored node's chart between structural events. The source chart
/// is supplied by the later chart pass; this schedule stores only its causal placement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SegmentOrigin {
    Existing { node: u32 },
    Leaf { event: usize },
    PartingUpper { event: usize },
    PartingLower { event: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NodeArrival {
    pub cell: usize,
    pub digit_order: usize,
    pub branch: usize,
    pub dyadic: usize,
    pub symbol: usize,
    pub node: u32,
    pub bottom: usize,
    pub halves_before: [u32; 2],
    pub root_halves_before: Option<[u32; 2]>,
    pub child: Option<SegmentRef>,
    pub prior_child: bool,
    pub leaf: bool,
    /// Whether this arrival increments the stored mass register (forced levels pass through).
    pub mass_step: bool,
    /// Whether `Law::apply_branch` steps a chart at this node before any same-arrival founding.
    /// A just-founded leaf has a mass step but no chart step at its founding arrival.
    pub chart_step: bool,
    pub parting_event: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SegmentSchedule {
    pub node: u32,
    pub origin: SegmentOrigin,
    pub level: usize,
    pub arrivals: Vec<NodeArrival>,
    /// The segment whose pre-parting carried chart creates this segment's upper/lower charts.
    pub chart_parent: Option<SegmentId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StructuralEvent {
    LeafFounded {
        cell: usize,
        digit_order: usize,
        branch: usize,
        node: u32,
        segment: SegmentId,
        bottom: usize,
        parent: Option<(u32, u32)>,
        label_end: u32,
    },
    ChainParted {
        cell: usize,
        digit_order: usize,
        branch: usize,
        source: SegmentId,
        upper: SegmentId,
        lower: SegmentId,
        old_node: u32,
        upper_node: u32,
        parent: Option<(u32, u32)>,
        lower_key: u32,
        top: usize,
        depth: usize,
        old_bottom: usize,
        old_end: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CellSchedule {
    pub address: Vec<Vec<u32>>,
    pub class: usize,
    /// Read-only queries for every splitting dyadic, captured before any same-cell deposit.
    pub queries: Vec<Vec<BranchPath>>,
    /// Paths opened by the arrived class, also captured at the cell's opening topology.
    pub transitions: Vec<Vec<BranchPath>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TopologySchedule {
    pub segments: Vec<SegmentSchedule>,
    arrival_lookup: Vec<HashMap<(usize, usize), usize>>,
    pub events: Vec<StructuralEvent>,
    pub cells: Vec<CellSchedule>,
    /// The sequentially founded final topology and carried integer registers. No chart is read or
    /// advanced by the schedule builder.
    pub final_arena: Arena,
    /// Active final chart segment for each physical node, in arena index order.
    pub final_segments: Vec<SegmentId>,
    pub passed: u64,
}

#[derive(Clone)]
struct RawRead {
    tree: usize,
    branch: usize,
    dyadic: usize,
    symbol: usize,
    stop: Stop,
    path: Vec<u32>,
    opening_halves: Vec<[u32; 2]>,
    parting_depth: Option<usize>,
    root_halves: Option<[u32; 2]>,
}

fn flatten_checked(
    tree: &Landmarks,
    address: &[Letter],
    class: usize,
) -> Result<Vec<Vec<u32>>, ContextError> {
    tree.check_causal_address(address, class)?;
    Ok(tree.law.flatten(address))
}

fn opening_reads(
    arena: &Arena,
    law: &super::Law,
    address: &[Vec<u32>],
    dyadic: usize,
    symbol: usize,
) -> Vec<RawRead> {
    law.branches
        .iter()
        .enumerate()
        .map(|(branch, _)| {
            let tree = law.tree(branch, dyadic);
            let walk = arena.walk(tree, &address[branch]);
            let root_halves = arena.root(tree).map(|root| arena.halves(root));
            RawRead {
                tree,
                branch,
                dyadic,
                symbol,
                stop: walk.stop,
                opening_halves: walk.nodes.iter().map(|&node| arena.halves(node)).collect(),
                path: walk.nodes,
                parting_depth: walk.parting,
                root_halves,
            }
        })
        .collect()
}

fn materialize_path(arena: &Arena, active: &HashMap<u32, SegmentId>, read: &RawRead) -> BranchPath {
    let source_segments: Vec<SegmentId> = read.path.iter().map(|node| active[node]).collect();
    let levels: Vec<PathLevel> = read
        .path
        .iter()
        .enumerate()
        .map(|(index, &node)| {
            let parting = read.parting_depth.filter(|_| index + 1 == read.path.len());
            let bottom = parting.unwrap_or_else(|| arena.bottom(node));
            let segment = if let Some(depth) = parting {
                SegmentRef::PartingUpper {
                    source: active[&node],
                    depth,
                }
            } else {
                SegmentRef::Stored(active[&node])
            };
            let child = if index + 1 < read.path.len() {
                let child_index = index + 1;
                let child_node = read.path[child_index];
                Some(if child_index + 1 == read.path.len() {
                    if let Some(depth) = read.parting_depth {
                        SegmentRef::PartingUpper {
                            source: active[&child_node],
                            depth,
                        }
                    } else {
                        SegmentRef::Stored(active[&child_node])
                    }
                } else {
                    SegmentRef::Stored(active[&child_node])
                })
            } else {
                None
            };
            PathLevel {
                node,
                segment,
                bottom,
                halves: arena.halves(node),
                count_node: node,
                child,
            }
        })
        .collect();
    let prior_child = read.stop == Stop::Prior;
    BranchPath {
        tree: read.tree,
        branch: read.branch,
        dyadic: read.dyadic,
        symbol: read.symbol,
        stop: read.stop,
        source_nodes: read.path.clone(),
        source_segments,
        levels,
        opening_halves: read.opening_halves.clone(),
        parting_depth: read.parting_depth,
        root_halves: read.root_halves,
        prior_child,
    }
}

/// Build a chart-free topology schedule for the typed cells. An invalid cell returns its ordinary
/// landmark refusal; callers may schedule a valid prefix separately to preserve sequential partial
/// progress semantics.
pub(super) fn build(
    tree: &Landmarks,
    addresses: &[Vec<Letter>],
    classes: &[usize],
) -> Result<TopologySchedule, ContextError> {
    if addresses.len() != classes.len() {
        return Err(shape(
            "one class for each landmark arrival address",
            addresses.len(),
            classes.len(),
        ));
    }
    let encoded = addresses
        .iter()
        .zip(classes)
        .map(|(address, &class)| flatten_checked(tree, address, class))
        .collect::<Result<Vec<_>, _>>()?;
    build_encoded(tree, &encoded, classes)
}

pub(super) fn build_encoded(
    tree: &Landmarks,
    addresses: &[Vec<Vec<u32>>],
    classes: &[usize],
) -> Result<TopologySchedule, ContextError> {
    if addresses.len() != classes.len() {
        return Err(shape(
            "one class for each landmark arrival address",
            addresses.len(),
            classes.len(),
        ));
    }
    let law = &tree.law;
    let mut arena = tree.nodes.arena.clone();
    let mut segments = Vec::new();
    let mut active = HashMap::<u32, SegmentId>::new();
    for node in 0..arena.len() {
        let node = node as u32;
        let id = segments.len();
        segments.push(SegmentSchedule {
            node,
            origin: SegmentOrigin::Existing { node },
            level: arena.bottom(node),
            arrivals: Vec::new(),
            chart_parent: None,
        });
        active.insert(node, id);
    }

    let mut events = Vec::new();
    let mut cells = Vec::with_capacity(addresses.len());
    let mut passed = tree.nodes.passed;
    for (cell_index, (encoded_address, &class)) in addresses.iter().zip(classes).enumerate() {
        if class >= law.declaration.alphabet {
            return Err(super::ContextError::CellOutside {
                code: class,
                alphabet: law.declaration.alphabet,
            });
        }
        let address = encoded_address.clone();
        if passed >= law.declaration.population {
            return Err(ContextError::PopulationReached {
                population: law.declaration.population,
            });
        }

        let emitted = law.odometer.emitted(class);
        let query_dyadics = law.odometer.splitting();
        // Both read families are fixed at the opening topology before the first same-cell write.
        let queries: Vec<Vec<RawRead>> = query_dyadics
            .iter()
            .map(|&dyadic| opening_reads(&arena, law, &address, dyadic, 0))
            .collect();
        let transition_reads: Vec<Vec<RawRead>> = emitted
            .iter()
            .map(|&(dyadic, symbol)| opening_reads(&arena, law, &address, dyadic, symbol))
            .collect();

        let founding_bound: usize = address.iter().map(|letters| letters.len() + 1).sum();
        let held_bound: usize = address.iter().map(Vec::len).sum();
        arena.founded_within(emitted.len() * founding_bound, held_bound)?;
        let runs: Vec<Option<u32>> = (0..law.branches.len())
            .map(|branch| {
                let top = transition_reads
                    .iter()
                    .flat_map(|reads| reads.iter())
                    .filter(|read| read.branch == branch && read.stop == Stop::Prior)
                    .map(|read| {
                        read.parting_depth.map_or_else(
                            || read.path.last().map_or(0, |node| arena.bottom(*node) + 1),
                            |depth| depth + 1,
                        )
                    })
                    .min()?;
                Some(arena.hold(&address[branch][top..]))
            })
            .collect();

        let query_paths = queries
            .iter()
            .map(|reads| {
                reads
                    .iter()
                    .map(|read| materialize_path(&arena, &active, read))
                    .collect()
            })
            .collect();
        let mut transition_paths = Vec::with_capacity(emitted.len());
        for (order, ((dyadic, symbol), reads)) in emitted.iter().zip(transition_reads).enumerate() {
            let mut paths_for_digit = Vec::with_capacity(reads.len());
            for read in reads {
                let branch = read.branch;
                let mut path_nodes = read.path.clone();
                let source_segments: Vec<SegmentId> =
                    path_nodes.iter().map(|node| active[node]).collect();
                let mut path_segments = source_segments.clone();
                let mut path_halves = Vec::with_capacity(path_nodes.len());
                let mut part_event = None;
                if let Some(depth) = read.parting_depth {
                    let chain = *path_nodes.last().expect("parting requires a stored chain");
                    let old_segment = *path_segments.last().expect("parting requires a segment");
                    let top = if path_nodes.len() > 1 {
                        arena.bottom(path_nodes[path_nodes.len() - 2]) + 1
                    } else {
                        0
                    };
                    let old_bottom = arena.bottom(chain);
                    let halves = if depth >= law.branches[branch].forced {
                        arena.halves(chain)
                    } else {
                        [1, 1]
                    };
                    let old_end = arena.end(chain);
                    let upper_end =
                        old_end - u32::try_from(old_bottom - depth).expect("part depth");
                    let upper_node = arena.push(branch, depth, halves, upper_end);
                    let upper_segment = segments.len();
                    let lower_segment = upper_segment + 1;
                    let event_index = events.len();
                    segments.push(SegmentSchedule {
                        node: upper_node,
                        origin: SegmentOrigin::PartingUpper { event: event_index },
                        level: depth,
                        arrivals: Vec::new(),
                        chart_parent: Some(old_segment),
                    });
                    segments.push(SegmentSchedule {
                        node: chain,
                        origin: SegmentOrigin::PartingLower { event: event_index },
                        level: old_bottom,
                        arrivals: Vec::new(),
                        chart_parent: Some(old_segment),
                    });
                    let lower_key = arena.label(chain, depth + 1);
                    let parent = if top == 0 {
                        None
                    } else {
                        Some((path_nodes[path_nodes.len() - 2], address[branch][top - 1]))
                    };
                    arena.link(read.tree, parent, upper_node);
                    arena.link(read.tree, Some((upper_node, lower_key)), chain);
                    events.push(StructuralEvent::ChainParted {
                        cell: cell_index,
                        digit_order: order,
                        branch,
                        source: old_segment,
                        upper: upper_segment,
                        lower: lower_segment,
                        old_node: chain,
                        upper_node,
                        parent,
                        lower_key,
                        top,
                        depth,
                        old_bottom,
                        old_end,
                    });
                    active.insert(chain, lower_segment);
                    active.insert(upper_node, upper_segment);
                    path_nodes.pop();
                    path_nodes.push(upper_node);
                    path_segments.pop();
                    path_segments.push(upper_segment);
                    part_event = Some(event_index);
                }

                // Attach this arrival to each active stored segment. Its child link is the next
                // stored segment on this same opening-state read; a missing child is the prior.
                for (level, &segment) in path_segments.iter().enumerate() {
                    let node = path_nodes[level];
                    let bottom = if read.parting_depth.is_some() && level + 1 == path_nodes.len() {
                        read.parting_depth.unwrap()
                    } else {
                        arena.bottom(node)
                    };
                    let halves_before = arena.halves(node);
                    path_halves.push(halves_before);
                    let child = path_segments.get(level + 1).copied();
                    let leaf = read.stop == Stop::Node && level + 1 == path_segments.len();
                    let chart_step = bottom >= law.branches[branch].forced;
                    segments[segment].arrivals.push(NodeArrival {
                        cell: cell_index,
                        digit_order: order,
                        branch,
                        dyadic: *dyadic,
                        symbol: *symbol,
                        node,
                        bottom,
                        halves_before,
                        root_halves_before: read.root_halves,
                        child: child.map(SegmentRef::Stored),
                        prior_child: child.is_none() && read.stop == Stop::Prior,
                        leaf,
                        mass_step: chart_step,
                        chart_step,
                        parting_event: part_event.filter(|_| level + 1 == path_segments.len()),
                    });
                }

                let mut founded_leaf = None;
                if read.stop == Stop::Prior {
                    let leaf_top = path_nodes.last().map_or(0, |node| arena.bottom(*node) + 1);
                    let end = runs[branch].expect("prior stop label run");
                    let leaf = arena.push(branch, address[branch].len(), [1, 1], end);
                    let parent = path_nodes
                        .last()
                        .map(|node| (*node, address[branch][leaf_top - 1]));
                    arena.link(read.tree, parent, leaf);
                    let segment = segments.len();
                    let event = events.len();
                    segments.push(SegmentSchedule {
                        node: leaf,
                        origin: SegmentOrigin::Leaf { event },
                        level: address[branch].len(),
                        arrivals: Vec::new(),
                        chart_parent: None,
                    });
                    active.insert(leaf, segment);
                    founded_leaf = Some(leaf);
                    // `apply_branch` appends a newly founded leaf to the counted path before
                    // depositing this digit's unit. Preserve that first arrival on the leaf
                    // segment; otherwise its final masses match but its arrival history is lost.
                    segments[segment].arrivals.push(NodeArrival {
                        cell: cell_index,
                        digit_order: order,
                        branch,
                        dyadic: *dyadic,
                        symbol: *symbol,
                        node: leaf,
                        bottom: address[branch].len(),
                        halves_before: [1, 1],
                        root_halves_before: read.root_halves,
                        child: None,
                        prior_child: false,
                        leaf: true,
                        mass_step: arena.bottom(leaf) >= law.branches[branch].forced,
                        chart_step: false,
                        parting_event: None,
                    });
                    events.push(StructuralEvent::LeafFounded {
                        cell: cell_index,
                        digit_order: order,
                        branch,
                        node: leaf,
                        segment,
                        bottom: address[branch].len(),
                        parent,
                        label_end: end,
                    });
                }

                let mut count_path = read.path.clone();
                if let Some(_) = read.parting_depth {
                    count_path.pop();
                    count_path.push(*path_nodes.last().expect("upper path node"));
                }
                if let Some(leaf) = founded_leaf {
                    // The sequential branch transition appends a just-founded leaf before
                    // counting the digit. The opening walk cannot include this node, but its
                    // first arrival must still update the actual topology registers.
                    count_path.push(leaf);
                }
                for node in count_path {
                    if arena.bottom(node) >= law.branches[branch].forced {
                        let halves = &mut arena.halves[node as usize];
                        halves[*symbol] += law.unit;
                        carry_at(law.ceiling, halves);
                    }
                }
                paths_for_digit.push(BranchPath {
                    tree: read.tree,
                    branch,
                    dyadic: *dyadic,
                    symbol: *symbol,
                    stop: read.stop,
                    source_nodes: read.path.clone(),
                    source_segments,
                    levels: path_segments
                        .iter()
                        .enumerate()
                        .map(|(level, &segment)| {
                            let node = path_nodes[level];
                            let mut bottom = arena.bottom(node);
                            if read.parting_depth.is_some() && level + 1 == path_nodes.len() {
                                bottom = read.parting_depth.unwrap();
                            }
                            PathLevel {
                                node,
                                segment: SegmentRef::Stored(segment),
                                bottom,
                                halves: path_halves[level],
                                count_node: node,
                                child: path_segments
                                    .get(level + 1)
                                    .copied()
                                    .map(SegmentRef::Stored),
                            }
                        })
                        .collect(),
                    opening_halves: read.opening_halves.clone(),
                    parting_depth: read.parting_depth,
                    root_halves: read.root_halves,
                    prior_child: read.stop == Stop::Prior,
                });
            }
            transition_paths.push(paths_for_digit);
        }
        passed += 1;
        cells.push(CellSchedule {
            address,
            class,
            queries: query_paths,
            transitions: transition_paths,
        });
    }

    for segment in &mut segments {
        segment
            .arrivals
            .sort_by_key(|arrival| (arrival.cell, arrival.digit_order));
    }
    Ok(TopologySchedule {
        arrival_lookup: segments
            .iter()
            .map(|segment| {
                segment
                    .arrivals
                    .iter()
                    .enumerate()
                    .map(|(index, arrival)| ((arrival.cell, arrival.digit_order), index))
                    .collect()
            })
            .collect(),
        segments,
        events,
        cells,
        final_arena: arena,
        final_segments: (0..active.len())
            .map(|node| active[&(node as u32)])
            .collect(),
        passed,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FaceKey {
    cell: usize,
    dyadic: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TransitionKey {
    cell: usize,
    digit_order: usize,
}

#[derive(Clone, Copy)]
struct QueryLoc {
    cell: usize,
    query: usize,
    branch: usize,
    level: usize,
}

#[derive(Clone, Copy)]
struct TransitionLoc {
    cell: usize,
    digit_order: usize,
    branch: usize,
    level: usize,
}

#[derive(Default)]
struct SegmentWork {
    dependencies: Vec<SegmentId>,
    opening_cells: Vec<usize>,
    queries: Vec<QueryLoc>,
    transitions: Vec<TransitionLoc>,
}

#[derive(Default)]
struct SegmentTrace {
    final_chart: Option<Chart>,
    opening_charts: HashMap<usize, Chart>,
    query_faces: HashMap<FaceKey, u64>,
    transition_faces: HashMap<TransitionKey, u64>,
    transition_increments: HashMap<TransitionKey, u128>,
    rebases: u64,
    releases: u64,
}

struct JoinTrace {
    chart: Chart,
    opening: Vec<Chart>,
    rebases: u64,
    releases: u64,
}

pub(super) struct ChartExecution {
    pub faces: Vec<LandmarkFace>,
    pub nodes: Nodes,
}

fn add_dependency(work: &mut [SegmentWork], owner: SegmentId, dependency: SegmentId) {
    if owner != dependency && !work[owner].dependencies.contains(&dependency) {
        work[owner].dependencies.push(dependency);
    }
}

fn add_reference_dependency(work: &mut [SegmentWork], owner: SegmentId, reference: &SegmentRef) {
    match reference {
        SegmentRef::Stored(dependency) => add_dependency(work, owner, *dependency),
        SegmentRef::PartingUpper { source, .. } => add_dependency(work, owner, *source),
    }
}

fn path_level_for_segment(path: &BranchPath, segment: SegmentId) -> Option<usize> {
    path.levels
        .iter()
        .position(|level| level.segment == SegmentRef::Stored(segment))
}

fn segment_work(schedule: &TopologySchedule) -> Vec<SegmentWork> {
    let mut work: Vec<SegmentWork> = (0..schedule.segments.len())
        .map(|_| SegmentWork::default())
        .collect();

    for (cell_index, cell) in schedule.cells.iter().enumerate() {
        for (query_index, query) in cell.queries.iter().enumerate() {
            for (branch_index, path) in query.iter().enumerate() {
                for (level_index, level) in path.levels.iter().enumerate() {
                    if let SegmentRef::Stored(owner) = level.segment {
                        work[owner].queries.push(QueryLoc {
                            cell: cell_index,
                            query: query_index,
                            branch: branch_index,
                            level: level_index,
                        });
                        work[owner].opening_cells.push(cell_index);
                        if let Some(child) = &level.child {
                            add_reference_dependency(&mut work, owner, child);
                        }
                    } else if let SegmentRef::PartingUpper { source, .. } = level.segment {
                        work[source].opening_cells.push(cell_index);
                    }
                }
            }
        }
        for (digit_order, transition) in cell.transitions.iter().enumerate() {
            for (branch_index, path) in transition.iter().enumerate() {
                for (level_index, level) in path.levels.iter().enumerate() {
                    if let SegmentRef::Stored(owner) = level.segment {
                        work[owner].transitions.push(TransitionLoc {
                            cell: cell_index,
                            digit_order,
                            branch: branch_index,
                            level: level_index,
                        });
                        work[owner].opening_cells.push(cell_index);
                        if let Some(child) = &level.child {
                            add_reference_dependency(&mut work, owner, child);
                        }
                    } else if let SegmentRef::PartingUpper { source, .. } = level.segment {
                        work[source].opening_cells.push(cell_index);
                    }
                }
            }
        }
    }
    for (segment_id, segment) in schedule.segments.iter().enumerate() {
        let origin_event = match segment.origin {
            SegmentOrigin::Leaf { event }
            | SegmentOrigin::PartingUpper { event }
            | SegmentOrigin::PartingLower { event } => Some(event),
            SegmentOrigin::Existing { .. } => None,
        };
        if let Some(event) = origin_event {
            if let Some(cell) = schedule.events[event].cell() {
                work[segment_id].opening_cells.push(cell);
            }
        }
        if let Some(parent) = segment.chart_parent {
            add_dependency(&mut work, segment_id, parent);
        }
    }
    for event in &schedule.events {
        if let StructuralEvent::ChainParted { cell, source, .. } = *event {
            work[source].opening_cells.push(cell);
        }
    }
    for item in &mut work {
        item.dependencies.sort_unstable();
        item.opening_cells.sort_unstable();
        item.opening_cells.dedup();
        item.queries
            .sort_by_key(|loc| (loc.cell, loc.query, loc.branch));
        item.transitions
            .sort_by_key(|loc| (loc.cell, loc.digit_order, loc.branch));
    }
    work
}

fn segment_levels(work: &[SegmentWork]) -> Result<Vec<Vec<SegmentId>>, ContextError> {
    let mut levels = Vec::new();
    let mut indegrees: Vec<usize> = work.iter().map(|node| node.dependencies.len()).collect();
    let mut dependents = vec![Vec::<SegmentId>::new(); work.len()];
    for (owner, node) in work.iter().enumerate() {
        for &dependency in &node.dependencies {
            dependents[dependency].push(owner);
        }
    }
    for owners in &mut dependents {
        owners.sort_unstable();
    }
    let mut ready: Vec<SegmentId> = indegrees
        .iter()
        .enumerate()
        .filter_map(|(segment, &degree)| (degree == 0).then_some(segment))
        .collect();
    let mut count = 0;
    while count < work.len() {
        if ready.is_empty() {
            return Err(shape(
                "an acyclic landmark chart-segment dependency graph",
                work.len(),
                count,
            ));
        }
        ready.sort_unstable();
        let frontier = std::mem::take(&mut ready);
        for &dependency in &frontier {
            for &owner in &dependents[dependency] {
                indegrees[owner] -= 1;
                if indegrees[owner] == 0 {
                    ready.push(owner);
                }
            }
        }
        count += frontier.len();
        levels.push(frontier);
    }
    Ok(levels)
}

fn chart_open<'a>(trace: &'a SegmentTrace, cell: usize) -> &'a Chart {
    trace
        .opening_charts
        .get(&cell)
        .expect("a scheduled source chart opening")
}

fn parting_for_segment(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    segment_id: SegmentId,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> Option<(usize, Parting)> {
    let origin = &schedule.segments[segment_id].origin;
    let event_id = match *origin {
        SegmentOrigin::PartingUpper { event } | SegmentOrigin::PartingLower { event } => event,
        _ => return None,
    };
    let StructuralEvent::ChainParted {
        cell,
        branch,
        source,
        top,
        depth,
        old_bottom,
        ..
    } = schedule.events[event_id]
    else {
        unreachable!("parting segment origin points at a parting event")
    };
    let source_trace = traces[source].as_ref().expect("parting source dependency");
    let parting = tree.law.part_chart(
        *chart_open(source_trace, cell),
        old_bottom,
        branch,
        top,
        depth,
    );
    Some((event_id, parting))
}

fn chart_for_path_level(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    path: &BranchPath,
    level_index: usize,
    cell: usize,
    current_segment: Option<(SegmentId, Chart)>,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> Chart {
    let level = &path.levels[level_index];
    match level.segment {
        SegmentRef::Stored(segment) => {
            if let Some((current, chart)) = current_segment {
                if current == segment {
                    return chart;
                }
            }
            *chart_open(
                traces[segment]
                    .as_ref()
                    .expect("stored chart dependency is ready"),
                cell,
            )
        }
        SegmentRef::PartingUpper { source, depth } => {
            let source_chart = *chart_open(
                traces[source]
                    .as_ref()
                    .expect("virtual parting source dependency is ready"),
                cell,
            );
            let top = if level_index > 0 {
                path.levels[level_index - 1].bottom + 1
            } else {
                0
            };
            let source_bottom = schedule.segments[source].level;
            tree.law
                .part_chart(source_chart, source_bottom, path.branch, top, depth)
                .upper
        }
    }
}

fn prior_face(tree: &Landmarks, root_halves: Option<[u32; 2]>) -> u64 {
    let split = super::base_sixteenths(tree.law.declaration.base, root_halves);
    (tree.law.full() >> 4) * split[0]
}

fn level_face(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    path: &BranchPath,
    level_index: usize,
    cell: usize,
    transition: Option<TransitionKey>,
    current_segment: Option<(SegmentId, Chart)>,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> u64 {
    let level = &path.levels[level_index];
    let chart = chart_for_path_level(
        tree,
        schedule,
        path,
        level_index,
        cell,
        current_segment,
        traces,
    );
    let masses = if let Some(key) = transition {
        if let SegmentRef::Stored(segment) = level.segment {
            if let Some((current, _)) = current_segment {
                if current == segment {
                    if let Some(&arrival_index) =
                        schedule.arrival_lookup[segment].get(&(cell, key.digit_order))
                    {
                        let arrival = &schedule.segments[segment].arrivals[arrival_index];
                        arrival.halves_before
                    } else {
                        path.opening_halves[level_index]
                    }
                } else {
                    path.opening_halves[level_index]
                }
            } else {
                path.opening_halves[level_index]
            }
        } else {
            path.opening_halves[level_index]
        }
    } else {
        path.opening_halves[level_index]
    };
    let is_leaf = path.stop == Stop::Node && level_index + 1 == path.levels.len();
    if is_leaf {
        return tree.law.leaf_halves(masses, path.root_halves);
    }
    let below = if level_index + 1 == path.levels.len() {
        prior_face(tree, path.root_halves)
    } else {
        match transition {
            Some(key) => {
                let child = &path.levels[level_index + 1].segment;
                match child {
                    SegmentRef::Stored(segment) => *traces[*segment]
                        .as_ref()
                        .expect("transition child dependency is ready")
                        .transition_faces
                        .get(&key)
                        .expect("child transition face at same key"),
                    SegmentRef::PartingUpper { .. } => level_face(
                        tree,
                        schedule,
                        path,
                        level_index + 1,
                        cell,
                        Some(key),
                        current_segment,
                        traces,
                    ),
                }
            }
            None => {
                let child = &path.levels[level_index + 1].segment;
                match child {
                    SegmentRef::Stored(segment) => *traces[*segment]
                        .as_ref()
                        .expect("query child dependency is ready")
                        .query_faces
                        .get(&FaceKey {
                            cell,
                            dyadic: path.dyadic,
                        })
                        .expect("child query face at same opening"),
                    SegmentRef::PartingUpper { .. } => level_face(
                        tree,
                        schedule,
                        path,
                        level_index + 1,
                        cell,
                        None,
                        current_segment,
                        traces,
                    ),
                }
            }
        }
    };
    if level.bottom < tree.law.branches[path.branch].forced {
        return below;
    }
    let (u, v) = tree.law.kt_based_halves(masses, path.root_halves, 0);
    tree.law.mix_stop(chart.stop, u, v, below)
}

fn stream_segment(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    work: &SegmentWork,
    segment_id: SegmentId,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> SegmentTrace {
    let segment = &schedule.segments[segment_id];
    let mut trace = SegmentTrace::default();
    let mut chart = match segment.origin {
        SegmentOrigin::Existing { node } => Some(tree.nodes.charts[node as usize]),
        SegmentOrigin::Leaf { event } => match schedule.events[event] {
            StructuralEvent::LeafFounded { bottom, .. } => Some(tree.law.founding[bottom]),
            _ => unreachable!("leaf origin points at leaf event"),
        },
        SegmentOrigin::PartingUpper { .. } | SegmentOrigin::PartingLower { .. } => None,
    };
    let mut query_cursor = 0usize;
    let mut transition_cursor = 0usize;
    let mut arrival_cursor = 0usize;
    let mut parting_cache: Option<(usize, Parting)> = None;
    let mut scheduled_cells = work.opening_cells.clone();
    scheduled_cells.extend(work.queries.iter().map(|loc| loc.cell));
    scheduled_cells.extend(work.transitions.iter().map(|loc| loc.cell));
    if let Some(event) = match segment.origin {
        SegmentOrigin::Leaf { event }
        | SegmentOrigin::PartingUpper { event }
        | SegmentOrigin::PartingLower { event } => Some(event),
        SegmentOrigin::Existing { .. } => None,
    } {
        if let Some(cell) = schedule.events[event].cell() {
            scheduled_cells.push(cell);
        }
    }
    scheduled_cells.sort_unstable();
    scheduled_cells.dedup();
    for cell in scheduled_cells {
        match segment.origin {
            SegmentOrigin::PartingUpper { event } | SegmentOrigin::PartingLower { event }
                if schedule.events[event].cell() == Some(cell) =>
            {
                let (event, parting) = parting_for_segment(tree, schedule, segment_id, traces)
                    .expect("parting segment has a split origin");
                chart = Some(match segment.origin {
                    SegmentOrigin::PartingUpper { .. } => parting.upper,
                    SegmentOrigin::PartingLower { .. } => parting.lower.unwrap_or_else(|| {
                        let source = match schedule.events[event] {
                            StructuralEvent::ChainParted { source, .. } => source,
                            _ => unreachable!(),
                        };
                        *chart_open(traces[source].as_ref().expect("source trace"), cell)
                    }),
                    _ => unreachable!(),
                });
                parting_cache = Some((event, parting));
            }
            _ => {}
        }
        if let Some(current) = chart {
            if work.opening_cells.binary_search(&cell).is_ok() {
                trace.opening_charts.insert(cell, current);
            }
        }
        while work
            .queries
            .get(query_cursor)
            .is_some_and(|loc| loc.cell == cell)
        {
            let loc = work.queries[query_cursor];
            let path = &schedule.cells[loc.cell].queries[loc.query][loc.branch];
            let q = level_face(
                tree,
                schedule,
                path,
                loc.level,
                cell,
                None,
                Some((segment_id, chart.expect("query segment is active"))),
                traces,
            );
            trace.query_faces.insert(
                FaceKey {
                    cell,
                    dyadic: path.dyadic,
                },
                q,
            );
            query_cursor += 1;
        }
        while work
            .transitions
            .get(transition_cursor)
            .is_some_and(|loc| loc.cell == cell)
        {
            let loc = work.transitions[transition_cursor];
            let path = &schedule.cells[loc.cell].transitions[loc.digit_order][loc.branch];
            let key = TransitionKey {
                cell,
                digit_order: loc.digit_order,
            };
            let current = chart.expect("transition segment is active");
            let face = level_face(
                tree,
                schedule,
                path,
                loc.level,
                cell,
                Some(key),
                Some((segment_id, current)),
                traces,
            );
            trace.transition_faces.insert(key, face);

            while segment.arrivals.get(arrival_cursor).is_some_and(|arrival| {
                (arrival.cell, arrival.digit_order) < (cell, loc.digit_order)
            }) {
                arrival_cursor += 1;
            }
            let arrival = segment
                .arrivals
                .get(arrival_cursor)
                .filter(|arrival| (arrival.cell, arrival.digit_order) == (cell, loc.digit_order));
            let mut increment = 0;
            if let Some(arrival) = arrival.filter(|arrival| arrival.chart_step) {
                let is_top = path.stop == Stop::Node && loc.level + 1 == path.levels.len();
                let below = if is_top {
                    None
                } else if loc.level + 1 == path.levels.len() {
                    Some(prior_face(tree, path.root_halves))
                } else {
                    Some(match &path.levels[loc.level + 1].segment {
                        SegmentRef::Stored(child) => *traces[*child]
                            .as_ref()
                            .expect("transition child dependency")
                            .transition_faces
                            .get(&key)
                            .expect("child transition face"),
                        SegmentRef::PartingUpper { .. } => level_face(
                            tree,
                            schedule,
                            path,
                            loc.level + 1,
                            cell,
                            Some(key),
                            Some((segment_id, current)),
                            traces,
                        ),
                    })
                };
                let (u, v) = tree.law.kt_based_halves(
                    arrival.halves_before,
                    arrival.root_halves_before,
                    arrival.symbol,
                );
                let theta = tree.law.rounding_operands(
                    arrival.branch,
                    arrival.symbol,
                    arrival.bottom,
                    face,
                    below,
                    is_top,
                    u,
                    v,
                );
                let child_increment = arrival
                    .child
                    .as_ref()
                    .and_then(|child| match child {
                        SegmentRef::Stored(child) => traces[*child]
                            .as_ref()
                            .and_then(|trace| trace.transition_increments.get(&key).copied()),
                        SegmentRef::PartingUpper { .. } => None,
                    })
                    .unwrap_or(0);
                let split_units = arrival
                    .parting_event
                    .and_then(|event| {
                        parting_cache
                            .filter(|(cached, _)| *cached == event)
                            .map(|(_, parting)| parting.units)
                    })
                    .unwrap_or(0);
                let step = tree.law.chart_step(
                    current,
                    theta,
                    is_top,
                    u,
                    v,
                    below.map_or(0, |raw_face| tree.law.side(raw_face, arrival.symbol)),
                    child_increment,
                    split_units,
                );
                increment = step.increment;
                chart = Some(step.chart);
                trace.rebases += u64::from(step.rebases);
                trace.releases += u64::from(step.released);
            }
            if arrival.is_some() {
                arrival_cursor += 1;
            }
            trace.transition_increments.insert(key, increment);
            transition_cursor += 1;
        }
    }
    trace.final_chart = chart;
    trace
}

fn branch_face(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    path: &BranchPath,
    cell: usize,
    transition: Option<TransitionKey>,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> u64 {
    let Some(first) = path.levels.first() else {
        return prior_face(tree, path.root_halves);
    };
    match first.segment {
        SegmentRef::Stored(segment) => {
            let trace = traces[segment].as_ref().expect("root segment trace");
            if let Some(key) = transition {
                *trace
                    .transition_faces
                    .get(&key)
                    .expect("root transition face")
            } else {
                *trace
                    .query_faces
                    .get(&FaceKey {
                        cell,
                        dyadic: path.dyadic,
                    })
                    .expect("root query face")
            }
        }
        SegmentRef::PartingUpper { .. } => {
            level_face(tree, schedule, path, 0, cell, transition, None, traces)
        }
    }
}

fn branch_increment(
    path: &BranchPath,
    key: TransitionKey,
    schedule: &TopologySchedule,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
) -> u128 {
    for level in &path.levels {
        let SegmentRef::Stored(segment) = level.segment else {
            continue;
        };
        let chart_step = schedule.arrival_lookup[segment]
            .get(&(key.cell, key.digit_order))
            .is_some_and(|&index| schedule.segments[segment].arrivals[index].chart_step);
        if chart_step {
            return traces[segment]
                .as_ref()
                .expect("first stepped branch segment trace")
                .transition_increments
                .get(&key)
                .copied()
                .unwrap_or(0);
        }
    }
    0
}

fn join_rounding_values(
    tree: &Landmarks,
    symbol: usize,
    joined: u64,
    cells: u64,
    bundles: u64,
) -> u128 {
    let side = |zero| u128::from(tree.law.side(zero, symbol));
    let least = side(joined).min(side(cells)).min(side(bundles));
    super::ceil_div(1u128 << tree.law.widths.certificate, least)
}

fn join_stream(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    traces: &[Option<std::sync::Arc<SegmentTrace>>],
    dyadic: usize,
) -> JoinTrace {
    let mut chart = tree.nodes.joins[dyadic];
    let mut result = JoinTrace {
        chart,
        opening: Vec::with_capacity(schedule.cells.len()),
        rebases: 0,
        releases: 0,
    };
    for (cell_index, cell) in schedule.cells.iter().enumerate() {
        result.opening.push(chart);
        if let Some((digit_order, transition)) = cell
            .transitions
            .iter()
            .enumerate()
            .find(|(_, paths)| paths[0].dyadic == dyadic)
        {
            let symbol = transition[0].symbol;
            let key = TransitionKey {
                cell: cell_index,
                digit_order,
            };
            let q_cells = branch_face(
                tree,
                schedule,
                &transition[0],
                cell_index,
                Some(key),
                traces,
            );
            let q_bundles = branch_face(
                tree,
                schedule,
                &transition[1],
                cell_index,
                Some(key),
                traces,
            );
            let sides = [
                tree.law.side(q_cells, symbol),
                tree.law.side(q_bundles, symbol),
            ];
            let increments = transition.iter().fold(0u128, |sum, path| {
                sum.saturating_add(branch_increment(path, key, schedule, traces))
            });
            let joined = tree.law.join_face_stop(chart.stop, q_cells, q_bundles);
            let theta = join_rounding_values(tree, symbol, joined, q_cells, q_bundles);
            let (step, units) =
                tree.law
                    .beta_step(chart.beta, u128::from(sides[0]), 1, u128::from(sides[1]), 0);
            let rebased = u64::from(step.mantissa.is_some());
            let released = u64::from(step.released.is_some());
            result.rebases += rebased;
            result.releases += released;
            chart.beta = step.beta;
            chart.stop = step
                .beta
                .stop_weight(tree.law.widths.face, tree.law.widths.carrier);
            chart.rebases += rebased as u32;
            chart.drift = chart.drift.saturating_add(increments).saturating_add(units);
            chart.excess = chart.excess.saturating_add(
                theta
                    .saturating_add(units.saturating_mul(2))
                    .saturating_add(increments),
            );
        }
    }
    result.chart = chart;
    result
}

/// Execute independent compressed-segment arrival streams by dependency antichain. Each stream
/// retains its own ordered recurrence; child-face and excess-increment inputs are looked up at the
/// same cell/digit key. All-class opening reads are assembled only after every segment stream has
/// emitted its opening face, before any join stream deposits its class digit.
pub(super) fn execute(
    tree: &Landmarks,
    schedule: &TopologySchedule,
    grain: u64,
) -> Result<ChartExecution, ContextError> {
    let work = segment_work(schedule);
    let levels = segment_levels(&work)?;
    let mut traces: Vec<Option<std::sync::Arc<SegmentTrace>>> =
        (0..schedule.segments.len()).map(|_| None).collect();
    for level in levels {
        let snapshot = traces.clone();
        let completed: Vec<(SegmentId, SegmentTrace)> = level
            .par_iter()
            .map(|&segment| {
                (
                    segment,
                    stream_segment(tree, schedule, &work[segment], segment, &snapshot),
                )
            })
            .collect();
        for (segment, trace) in completed {
            traces[segment] = Some(std::sync::Arc::new(trace));
        }
    }

    let splitting = tree.law.odometer.splitting();
    let join_traces: Vec<JoinTrace> = if tree.law.joined() {
        splitting
            .par_iter()
            .map(|&dyadic| join_stream(tree, schedule, &traces, dyadic))
            .collect()
    } else {
        Vec::new()
    };

    let mut faces = Vec::with_capacity(schedule.cells.len());
    for (cell_index, cell) in schedule.cells.iter().enumerate() {
        let mut numerators = Vec::with_capacity(splitting.len());
        for (query_index, query) in cell.queries.iter().enumerate() {
            let cells = branch_face(tree, schedule, &query[0], cell_index, None, &traces);
            let numerator = if tree.law.joined() {
                let bundles = branch_face(tree, schedule, &query[1], cell_index, None, &traces);
                tree.law.join_face_stop(
                    join_traces
                        .get(query_index)
                        .expect("join stream result")
                        .opening[cell_index]
                        .stop,
                    cells,
                    bundles,
                )
            } else {
                cells
            };
            numerators.push(numerator);
        }
        faces.push(LandmarkFace::of_splits(
            &tree.law.declaration,
            &Splits {
                face_bits: tree.law.widths.face,
                numerators,
            },
            grain,
        )?);
    }

    let mut charts = vec![tree.law.unit(); schedule.final_arena.len()];
    for (node, &segment) in schedule.final_segments.iter().enumerate() {
        charts[node] = traces[segment]
            .as_ref()
            .expect("final active chart segment was executed")
            .final_chart
            .expect("active segment owns a chart");
    }
    let mut joins = tree.nodes.joins.clone();
    for (&dyadic, trace) in splitting.iter().zip(&join_traces) {
        joins[dyadic] = trace.chart;
    }
    let mut rebases = tree.nodes.rebases;
    let mut releases = tree.nodes.releases;
    for trace in traces.iter().flatten() {
        rebases += trace.rebases;
        releases += trace.releases;
    }
    for event in &schedule.events {
        if let StructuralEvent::ChainParted { upper, .. } = *event {
            let parting = parting_for_segment(tree, schedule, upper, &traces)
                .expect("parting upper origin")
                .1;
            rebases += u64::from(parting.rebases);
        }
    }
    for trace in &join_traces {
        rebases += trace.rebases;
        releases += trace.releases;
    }
    Ok(ChartExecution {
        faces,
        nodes: Nodes {
            arena: schedule.final_arena.clone(),
            charts,
            joins,
            rebases,
            releases,
            passed: schedule.passed,
        },
    })
}

impl StructuralEvent {
    fn cell(&self) -> Option<usize> {
        match self {
            Self::LeafFounded { cell, .. } | Self::ChainParted { cell, .. } => Some(*cell),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{
        BaseMeasure, Bundle, Capacity, LandmarkDeclaration, LetterFamily, ObservationPath,
        ObservationRole, ObservedAddress, StopPrior, Walk,
    };

    fn tree() -> Landmarks {
        tree_with(2, Capacity::Unbounded, 64)
    }

    fn tree_with(alphabet: usize, capacity: Capacity, population: u64) -> Landmarks {
        tree_with_law(
            alphabet,
            capacity,
            population,
            StopPrior::half(),
            BaseMeasure::Even,
        )
    }

    fn tree_with_law(
        alphabet: usize,
        capacity: Capacity,
        population: u64,
        prior: StopPrior,
        base: BaseMeasure,
    ) -> Landmarks {
        Landmarks::new(LandmarkDeclaration {
            alphabet,
            depth: 3,
            forced: 0,
            population,
            grain: 16,
            family: LetterFamily::cells(),
            prior,
            capacity,
            mass: 1,
            base,
        })
        .unwrap()
    }

    fn cells() -> (Vec<Vec<Letter>>, Vec<usize>) {
        let words = [
            [Letter::Boundary, Letter::Boundary, Letter::Boundary],
            [Letter::Cell(0), Letter::Cell(1), Letter::Cell(0)],
            [Letter::Cell(0), Letter::Cell(1), Letter::Cell(1)],
            [Letter::Cell(0), Letter::Cell(0), Letter::Cell(1)],
            [Letter::Cell(1), Letter::Cell(0), Letter::Cell(1)],
            [Letter::Cell(0), Letter::Cell(1), Letter::Cell(0)],
            [Letter::Boundary, Letter::Cell(1), Letter::Cell(0)],
        ];
        let classes = vec![0, 1, 1, 0, 1, 0, 1];
        (words.into_iter().map(Vec::from).collect(), classes)
    }

    fn assert_values<T: std::fmt::Debug + PartialEq>(field: &str, actual: &[T], expected: &[T]) {
        assert_eq!(actual.len(), expected.len(), "{field} length");
        for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
            assert_eq!(actual, expected, "{field}[{index}]");
        }
    }

    fn assert_nodes_equal(actual: &Nodes, expected: &Nodes) {
        assert_values("arena roots", &actual.arena.roots, &expected.arena.roots);
        assert!(
            actual.arena.children == expected.arena.children,
            "arena child links differ"
        );
        assert_values("arena depths", &actual.arena.depths, &expected.arena.depths);
        assert_values("arena halves", &actual.arena.halves, &expected.arena.halves);
        assert_values("arena ends", &actual.arena.ends, &expected.arena.ends);
        assert_values(
            "arena letters",
            &actual.arena.letters,
            &expected.arena.letters,
        );
        assert_values("node charts", &actual.charts, &expected.charts);
        assert_values("join charts", &actual.joins, &expected.joins);
        assert_eq!(actual.rebases, expected.rebases, "rebase count");
        assert_eq!(actual.releases, expected.releases, "release count");
        assert_eq!(actual.passed, expected.passed, "passed count");
    }

    fn multi_class_cells(alphabet: usize) -> (Vec<Vec<Letter>>, Vec<usize>) {
        (0..96)
            .map(|index| {
                // Four successive addresses share the first two letters, then diverge inside
                // the stored chain; later groups also exercise root-level relinking.
                let address = vec![
                    Letter::Cell((index / 4) % alphabet),
                    Letter::Cell(0),
                    Letter::Cell(index % alphabet),
                ];
                let class = (index * 7 + 3) % alphabet;
                (address, class)
            })
            .unzip()
    }

    fn assert_scheduled_read_matches_walk(
        tree: &Landmarks,
        path: &BranchPath,
        encoded: &[Vec<u32>],
    ) -> Option<usize> {
        let walk = Walk {
            nodes: path.source_nodes.clone(),
            parting: path.parting_depth,
            stop: path.stop,
        };
        let supplied = tree
            .law
            .read_walk(&tree.nodes, path.branch, path.dyadic, path.symbol, walk);
        let sequential = tree.law.read(
            &tree.nodes,
            path.branch,
            path.dyadic,
            path.symbol,
            &encoded[path.branch],
        );
        assert_eq!(supplied, sequential);
        supplied.parting.map(|parting| parting.depth)
    }

    #[test]
    fn topology_schedule_matches_sequential_foundings_links_labels_and_carries() {
        let opening = tree();
        let (addresses, classes) = cells();
        let schedule = build(&opening, &addresses, &classes).unwrap();
        let mut sequential = opening;
        for (address, class) in addresses.iter().zip(classes) {
            sequential.deposit(address, class).unwrap();
        }
        assert_eq!(schedule.final_arena, sequential.nodes.arena);
        assert_eq!(schedule.passed, sequential.nodes.passed);
        assert_eq!(schedule.cells.len(), addresses.len());
        assert!(
            schedule
                .events
                .iter()
                .any(|event| matches!(event, StructuralEvent::ChainParted { .. }))
        );
        assert!(
            schedule
                .events
                .iter()
                .any(|event| matches!(event, StructuralEvent::LeafFounded { .. }))
        );
        for segment in schedule
            .segments
            .iter()
            .filter(|segment| matches!(&segment.origin, SegmentOrigin::Leaf { .. }))
        {
            let founding_arrival = segment.arrivals.first().expect("leaf founding arrival");
            assert!(founding_arrival.mass_step);
            assert!(!founding_arrival.chart_step);
        }
    }

    #[test]
    fn multi_class_capped_topology_matches_sequential_arrivals_and_carries() {
        // Repeated paths drive capped registers through carries; non-power-of-two and wider
        // alphabets exercise forced and emitted odometer digits beyond the binary fixture.
        for alphabet in [5, 17] {
            let opening = tree_with(alphabet, Capacity::Ceiling(2), 128);
            let (addresses, classes) = multi_class_cells(alphabet);
            let schedule = build(&opening, &addresses, &classes).unwrap();
            let mut sequential = opening;
            for (address, class) in addresses.iter().zip(classes) {
                sequential.deposit(address, class).unwrap();
            }
            assert_eq!(schedule.final_arena, sequential.nodes.arena);
            assert_eq!(schedule.passed, sequential.nodes.passed);
        }
    }

    #[test]
    fn opening_queries_and_transition_walks_match_the_sequential_reader() {
        let opening = tree();
        let (addresses, classes) = cells();
        let schedule = build(&opening, &addresses, &classes).unwrap();
        let mut sequential = opening;
        for (cell_index, (address, &class)) in addresses.iter().zip(&classes).enumerate() {
            let encoded = sequential.law.flatten(address);
            let cell = &schedule.cells[cell_index];
            let splits = sequential.law.odometer.splitting();
            assert_eq!(cell.queries.len(), splits.len());
            for (query, dyadic) in cell.queries.iter().zip(splits) {
                let expected = sequential.law.digit(&sequential.nodes, dyadic, 0, &encoded);
                for (branch_path, read) in query.iter().zip(expected.reads) {
                    assert_eq!(branch_path.source_nodes, read.nodes);
                    assert_eq!(branch_path.stop, read.stop);
                    assert_eq!(
                        branch_path.parting_depth,
                        read.parting.map(|part| part.depth)
                    );
                    assert_eq!(
                        branch_path
                            .levels
                            .iter()
                            .map(|level| level.bottom)
                            .collect::<Vec<_>>(),
                        read.bottoms
                    );
                    assert_eq!(
                        branch_path.root_halves,
                        read.nodes
                            .first()
                            .map(|&node| sequential.nodes.arena.halves(node))
                    );
                }
            }
            let emitted = sequential.law.odometer.emitted(class);
            assert_eq!(cell.transitions.len(), emitted.len());
            for (transition, (dyadic, symbol)) in cell.transitions.iter().zip(emitted) {
                let expected = sequential
                    .law
                    .digit(&sequential.nodes, dyadic, symbol, &encoded);
                for (branch_path, read) in transition.iter().zip(expected.reads) {
                    assert_eq!(branch_path.source_nodes, read.nodes);
                    assert_eq!(branch_path.stop, read.stop);
                    assert_eq!(
                        branch_path.parting_depth,
                        read.parting.map(|part| part.depth)
                    );
                    assert_eq!(
                        branch_path
                            .levels
                            .iter()
                            .map(|level| level.bottom)
                            .collect::<Vec<_>>(),
                        read.bottoms
                    );
                    assert_eq!(branch_path.symbol, symbol);
                }
            }
            sequential.deposit(address, class).unwrap();
        }
    }

    #[test]
    fn scheduled_walk_reads_match_sequential_reads_with_root_base_and_prior_variants() {
        for (alphabet, prior) in [
            (5, StopPrior::per_depth(vec![1, 3]).unwrap()),
            (17, StopPrior::half()),
        ] {
            let opening =
                tree_with_law(alphabet, Capacity::Unbounded, 128, prior, BaseMeasure::Root);
            let (addresses, classes) = multi_class_cells(alphabet);
            let schedule = build(&opening, &addresses, &classes).unwrap();
            let mut sequential = opening;
            let mut saw_interior_parting = false;
            for (cell_index, (address, &class)) in addresses.iter().zip(&classes).enumerate() {
                let encoded = sequential.law.flatten(address);
                let cell = &schedule.cells[cell_index];
                for query in &cell.queries {
                    for path in query {
                        saw_interior_parting |=
                            assert_scheduled_read_matches_walk(&sequential, path, &encoded)
                                .is_some_and(|depth| depth > 0);
                    }
                }
                for transition in &cell.transitions {
                    for path in transition {
                        saw_interior_parting |=
                            assert_scheduled_read_matches_walk(&sequential, path, &encoded)
                                .is_some_and(|depth| depth > 0);
                    }
                }
                sequential.deposit(address, class).unwrap();
            }
            assert!(saw_interior_parting);
            assert_eq!(schedule.final_arena, sequential.nodes.arena);
        }
    }

    #[test]
    fn chart_dag_matches_sequential_faces_and_full_standing_across_worker_counts() {
        for (alphabet, capacity, prior, base) in [
            (
                5,
                Capacity::Ceiling(2),
                StopPrior::per_depth(vec![1, 3]).unwrap(),
                BaseMeasure::Root,
            ),
            (
                17,
                Capacity::Ceiling(3),
                StopPrior::half(),
                BaseMeasure::Even,
            ),
        ] {
            let family = LetterFamily::new(vec![3, 2]).unwrap();
            let opening = Landmarks::new(LandmarkDeclaration {
                alphabet,
                depth: 3,
                forced: 0,
                population: 96,
                grain: 16,
                family: family.clone(),
                prior,
                capacity,
                mass: 1,
                base,
            })
            .unwrap();
            let addresses: Vec<Vec<Letter>> = (0..24)
                .map(|index| {
                    (0..3)
                        .map(|depth| {
                            let cell = (index * (depth + 2) + depth) % alphabet;
                            let first = ((index + depth) % 3) as u64;
                            let second = ((index / (depth + 1)) % 2) as u64;
                            Letter::Bundle(Bundle {
                                cell,
                                features: family.encode(&[first, second]).unwrap(),
                            })
                        })
                        .collect()
                })
                .collect();
            let classes: Vec<usize> = (0..addresses.len())
                .map(|index| (index * 7 + 3) % alphabet)
                .collect();
            let schedule = build(&opening, &addresses, &classes).unwrap();
            assert!(
                schedule
                    .events
                    .iter()
                    .any(|event| { matches!(event, StructuralEvent::ChainParted { .. }) })
            );
            assert!(
                schedule
                    .events
                    .iter()
                    .any(|event| { matches!(event, StructuralEvent::LeafFounded { .. }) })
            );

            let mut sequential = opening.clone();
            let mut expected_faces = Vec::new();
            for (address, &class) in addresses.iter().zip(&classes) {
                expected_faces.push(sequential.face(address, 16).unwrap());
                sequential.deposit(address, class).unwrap();
            }

            let mut received = opening.clone();
            assert_eq!(
                received.receive_arrivals(&addresses, &classes, 16).unwrap(),
                expected_faces
            );
            assert_eq!(received.nodes, sequential.nodes);

            let mut refused = opening.clone();
            let before_refusal = refused.nodes.clone();
            assert!(
                refused
                    .receive_arrivals(&addresses, &classes[..classes.len() - 1], 16)
                    .is_err()
            );
            assert_eq!(refused.nodes, before_refusal);

            let observed_opening =
                Landmarks::new_observed(opening.law.declaration.clone(), 1, ObservationRole::Route)
                    .unwrap();
            let observed_addresses: Vec<ObservedAddress> = addresses
                .iter()
                .map(|causal| {
                    ObservedAddress::new(
                        ObservationPath::from_section_bits(vec![true]).unwrap(),
                        causal.clone(),
                    )
                })
                .collect();
            let mut observed_sequential = observed_opening.clone();
            let mut observed_faces = Vec::with_capacity(classes.len());
            for (address, &class) in observed_addresses.iter().zip(&classes) {
                observed_faces.push(observed_sequential.face_observed(address, 16).unwrap());
                observed_sequential
                    .deposit_observed(address, class)
                    .unwrap();
            }
            let mut observed_received = observed_opening.clone();
            assert_eq!(
                observed_received
                    .receive_observed_arrivals(&observed_addresses, &classes, 16)
                    .unwrap(),
                observed_faces
            );
            assert_eq!(observed_received.nodes, observed_sequential.nodes);

            for workers in [1, 2, 24] {
                let pool = rayon::ThreadPoolBuilder::new()
                    .num_threads(workers)
                    .build()
                    .unwrap();
                let actual = pool.install(|| execute(&opening, &schedule, 16)).unwrap();
                assert_eq!(actual.faces.len(), expected_faces.len());
                for (cell, (actual, expected)) in
                    actual.faces.iter().zip(&expected_faces).enumerate()
                {
                    assert_eq!(actual, expected, "face mismatch at cell {cell}");
                }
                assert_nodes_equal(&actual.nodes, &sequential.nodes);
            }
        }
    }
}
