//! **Deed H1 — the adversary pass.** Every test here asserts what the owner SHOULD do. A green test
//! is an attack the owner HELD; a red test is an attack that REFUTED it.
//!
//! Public API only: the point of the pass is that a caller outside the module can reach these
//! states. Nothing in the builder's files is edited.

use std::collections::BTreeMap;

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::hardware_cover::{Chart, CpuDeclaration, HardwareCover};
use holonic_engine::reduction_junction::*;
use holonic_engine::section_partition::*;
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;

// -------------------------------------------------------------------------------------------------
// fixtures
// -------------------------------------------------------------------------------------------------

const KERNEL: &str = "h1_adversary";

fn region(r0: usize, r1: usize, c0: usize, c1: usize) -> SectionRegion {
    SectionRegion::new(r0, r1, c0, c1).expect("well-formed")
}

fn lineage() -> SectionLineage {
    SectionLineage {
        source: "adversary".to_owned(),
        population: "section".to_owned(),
        body: "h1-adversary".to_owned(),
    }
}

/// One species over the WRITTEN face, so a cell with no reads still has a nonzero demand.
fn written_species(capacity: u32) -> ResourceDeclaration {
    ResourceDeclaration {
        species: vec![DeclaredSpecies {
            name: "resident-lanes".to_owned(),
            unit: 1,
            face: DemandFace::Written,
            capacity: BigUint::from(capacity),
            characteristic_delay: 1,
            // Added 2026-08-19: the sink capacity is a caller declaration with no default.
            sink_capacity: BigUint::from(1u32),
        }],
        enactment_aperture: 4096,
    }
}

fn partition_of(shape: SectionShape, cells: Vec<SectionCell>) -> SectionPartition {
    SectionPartition {
        lineage: lineage(),
        shape,
        populations: BTreeMap::new(),
        cells,
    }
}

fn owned_cell(index: usize, write: SectionRegion) -> SectionCell {
    SectionCell {
        index,
        write,
        reads: Vec::new(),
        partial_of: None,
    }
}

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn matrix(rows: &[&[(i64, i64)]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|(n, d)| rat(*n, *d)).collect())
            .collect(),
    )
    .expect("well-formed")
}

fn scalar_partial(index: usize, from: usize, to: usize, value: Rat) -> PartialTerm {
    PartialTerm {
        index,
        inner: region(0, 1, from, to),
        carried: vec![value.clone()],
        enclosure: vec![(value.clone(), value)],
        chart: ExactRatMatrix::identity(1).expect("identity"),
        domain_metric: ExactRatMatrix::identity(1).expect("identity"),
    }
}

/// A scalar junction over the declared partials, with a coarse boundary and a wide aperture.
fn scalar_junction(
    partials: Vec<PartialTerm>,
    inner_width: usize,
    aperture: u64,
    carrier: u32,
    boundary: u32,
) -> ReductionJunction {
    ReductionJunction {
        owner: "adversary".to_owned(),
        output: region(0, 1, 0, 1),
        output_dimension: 1,
        inner_shape: SectionShape::of(1, inner_width, 0),
        word: ReductionWord::left_leaning(partials.len()).expect("a word"),
        partials,
        overflow_aperture: aperture,
        carrier_exponent: carrier,
        boundary_exponent: boundary,
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        codomain_metric: ExactRatMatrix::identity(1).expect("identity"),
        returned_covector: vec![rat(1, 1)],
    }
}

// =================================================================================================
// A — completeness and disjointness: is the sweep computed, and can it be fooled?
// =================================================================================================

/// **A(i).** Two cells whose extents SUM to the section's extent while leaving a hole and
/// double-covering elsewhere. A sum check certifies; the real check must not.
///
/// HELD. `covered_extent == section_extent == 32` — the quantity a summing owner would have used —
/// and the reading still refuses, naming both the meet and the hole.
#[test]
fn a_hole_and_a_double_cover_with_a_matching_extent_sum_still_refuses() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    // [0,4)x[0,4) is 16 and [0,4)x[2,6) is 16: 32 = the section's extent, with columns 6..8 uncovered
    // and columns 2..4 covered twice.
    let cells = vec![
        owned_cell(0, region(0, 4, 0, 4)),
        owned_cell(1, region(0, 4, 2, 6)),
    ];
    let defects = partition_of(shape, cells)
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect_err("a hole and a double cover are not a partition");
    let hole = defects.iter().find_map(|defect| match defect {
        PartitionDefect::RegionUncovered { region } => Some(*region),
        _ => None,
    });
    let meet = defects.iter().find_map(|defect| match defect {
        PartitionDefect::RegionsOverlap { region, .. } => Some(*region),
        _ => None,
    });
    assert_eq!(hole, Some(region(0, 4, 6, 8)), "the hole is named");
    assert_eq!(meet, Some(region(0, 4, 2, 4)), "the meet is named");
}

/// **A(ii).** The overlap is between the FIRST and the LAST declared cell, with a non-overlapping
/// cell between them, so an owner that compared only adjacent declarations would miss it.
///
/// HELD — the disjointness loop is all-pairs.
#[test]
fn an_overlap_between_the_first_and_last_declared_cells_is_found() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let cells = vec![
        owned_cell(0, region(0, 4, 0, 3)),
        owned_cell(1, region(0, 4, 6, 8)),
        owned_cell(2, region(0, 4, 2, 6)),
    ];
    let defects = partition_of(shape, cells)
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect_err("cells 0 and 2 overlap");
    let pairs: Vec<(usize, usize)> = defects
        .iter()
        .filter_map(|defect| match defect {
            PartitionDefect::RegionsOverlap { cells, .. } => Some(*cells),
            _ => None,
        })
        .collect();
    assert!(
        pairs.contains(&(0, 2)),
        "the non-adjacent pair is found: {pairs:?}"
    );
}

/// **A(iii).** A DEGENERATE cell: `row_from == row_to`. `SectionRegion::new` refuses it by name, but
/// the fields are public, so a caller reaches the state by a struct literal — and `certify` never
/// re-checks. The partition should refuse a zero-extent cell.
///
/// REFUTES: it certifies. The `EmptyRegion` guard lives only in a constructor nothing forces a
/// caller to use, so the doc's stated reason for the guard ("a partition of empty regions covers
/// nothing and would certify") is not enforced by the certifier.
// REFUTES: a zero-extent cell certifies. `SectionRegion::new` refuses `EmptyRegion`, but the fields are public and `certify` never re-checks.
#[test]
fn a_degenerate_zero_extent_cell_must_refuse() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let degenerate = SectionRegion {
        row_from: 2,
        row_to: 2,
        column_from: 0,
        column_to: 8,
    };
    let cells = vec![
        owned_cell(0, region(0, 4, 0, 4)),
        owned_cell(1, region(0, 4, 4, 8)),
        owned_cell(2, degenerate),
    ];
    let outcome = partition_of(shape, cells).certify(&cover, &[], &written_species(8), KERNEL);
    assert!(
        outcome.is_err(),
        "a cell whose region holds no coordinate must be refused by name; it certified instead: \
         cells {:?}",
        outcome.map(|receipt| receipt
            .cells
            .iter()
            .map(|cell| (cell.index, cell.write_extent))
            .collect::<Vec<_>>())
    );
}

/// **A(iii) extended.** A section with zero rows and no cells at all. The sweep returns early on a
/// zero-extent shape, so completeness is `true` over no material.
///
/// REFUTES: `is_partition()` is true for a partition of nothing — exactly the failure the
/// `EmptyRegion` refusal says it exists to prevent, reached one level up at the shape.
// REFUTES: a 0 x 8 section with no cells certifies as a complete, disjoint partition.
#[test]
fn an_empty_section_with_no_cells_must_not_certify_as_a_partition() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(0, 8, 0);
    let outcome = partition_of(shape, Vec::new()).certify(&cover, &[], &written_species(8), KERNEL);
    match outcome {
        Err(_) => {}
        Ok(receipt) => assert!(
            !receipt.is_partition(),
            "an empty section with no cells certified as a complete, disjoint partition: \
             complete {} covered {}/{}",
            receipt.completeness.complete,
            receipt.completeness.covered_extent,
            receipt.completeness.section_extent
        ),
    }
}

/// **A(iv).** A single cell whose region is the section exactly — touching every boundary.
///
/// HELD: it certifies, and touching is not overlapping.
#[test]
fn a_cell_touching_the_boundary_exactly_certifies() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let receipt = partition_of(shape, vec![owned_cell(0, shape.whole())])
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect("the whole section is a partition of itself");
    assert!(receipt.is_partition());
    assert!(receipt.completeness.uncovered.is_empty());
}

/// **A(iv) sibling.** Two cells that TOUCH at a column boundary and do not overlap.
///
/// HELD: the half-open meet is empty and both are certified.
#[test]
fn two_cells_touching_at_a_column_boundary_do_not_overlap() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let cells = vec![
        owned_cell(0, region(0, 4, 0, 4)),
        owned_cell(1, region(0, 4, 4, 8)),
    ];
    let receipt = partition_of(shape, cells)
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect("touching bands are disjoint");
    assert_eq!(receipt.disjointness.overlaps.len(), 0);
    assert!(receipt.disjointness.disjoint);
}

/// **A(v).** A foreign cell one row past the section.
///
/// HELD: `RegionOutsideSection` names the cell and the region.
#[test]
fn a_foreign_tile_one_row_past_the_section_refuses_by_name() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let cells = vec![
        owned_cell(0, region(0, 4, 0, 4)),
        owned_cell(1, region(0, 5, 4, 8)),
    ];
    let defects = partition_of(shape, cells)
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect_err("a tile past the last row is foreign");
    assert!(
        defects.iter().any(|defect| matches!(
            defect,
            PartitionDefect::RegionOutsideSection { cell: 1, .. }
        )),
        "{defects:?}"
    );
}

/// **A(v) turned on the JUNCTION.** `certify` checks `within` for every cell's write and for no
/// junction output. A junction output that runs past the section's last column is therefore counted
/// as covering material the section does not have — and it masks a real hole while doing it.
///
/// REFUTES: the partition certifies with a covering region that is not inside the section.
// REFUTES: `within` is checked for every cell write and for no junction output; a foreign junction output covers a hole and certifies.
#[test]
fn a_junction_output_beyond_the_section_must_refuse() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    // The junction claims columns 0..16 of an 8-wide section.
    let junction = JunctionOutput {
        owner: "foreign".to_owned(),
        output: region(0, 4, 0, 16),
        partials: 1,
    };
    let cells = vec![SectionCell {
        index: 0,
        write: region(0, 4, 0, 4),
        reads: Vec::new(),
        partial_of: Some(PartialAddress {
            junction: 0,
            partial: 0,
        }),
    }];
    let outcome = partition_of(shape, cells).certify(
        &cover,
        std::slice::from_ref(&junction),
        &written_species(8),
        KERNEL,
    );
    assert!(
        outcome.is_err(),
        "a junction output outside the section must refuse the way a foreign CELL does; it \
         certified instead, complete = {:?}",
        outcome.map(|receipt| receipt.completeness.complete)
    );
}

// =================================================================================================
// B — footprints
// =================================================================================================

/// **B.** A cell that declares NO reads at all is certified interchangeable with a cell that reads
/// everything. The read footprint is a caller DECLARATION and H1 never compares it with a
/// contraction, because H1 enacts no contraction.
///
/// The sharper half of the attack is moot and here is why: `SectionCell` has no write population —
/// its write is always a region of the section (or of its junction's partial slot). A cell that
/// writes the map rows is therefore not expressible, so "declared reads omit the map rows another
/// cell writes" has no construction. The hazard the certificate CAN see is a read of the section's
/// own population, which is covered by the builder's control one.
#[test]
fn a_cell_that_declares_no_reads_is_certified_independent_of_one_that_reads_everything() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let mut populations = BTreeMap::new();
    populations.insert("map".to_owned(), SectionShape::of(8, 8, 0));
    let cells = vec![
        SectionCell {
            index: 0,
            write: region(0, 4, 0, 4),
            reads: vec![ReadRegion {
                population: "map".to_owned(),
                region: region(0, 8, 0, 8),
            }],
            partial_of: None,
        },
        // Declares nothing. Whatever it will actually read is invisible to the certificate.
        owned_cell(1, region(0, 4, 4, 8)),
    ];
    let receipt = SectionPartition {
        lineage: lineage(),
        shape,
        populations,
        cells,
    }
    .certify(&cover, &[], &written_species(8), KERNEL)
    .expect("declared footprints are disjoint");
    assert!(receipt.is_interchangeable());
    assert_eq!(receipt.cells[1].read_extent, 0);
    assert_eq!(receipt.shared_reads.len(), 0);
}

/// **B sibling.** A cell reading the region it itself writes is certified — `certify_footprints`
/// compares pairs and never a member with itself.
///
/// HELD, and it is correct: a member's own read of its own write is sequential inside that member.
#[test]
fn a_cell_reading_its_own_write_is_not_a_hazard() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let mut populations = BTreeMap::new();
    populations.insert("section".to_owned(), shape);
    let cells = vec![SectionCell {
        index: 0,
        write: shape.whole(),
        reads: vec![ReadRegion {
            population: "section".to_owned(),
            region: shape.whole(),
        }],
        partial_of: None,
    }];
    let receipt = SectionPartition {
        lineage: lineage(),
        shape,
        populations,
        cells,
    }
    .certify(&cover, &[], &written_species(8), KERNEL)
    .expect("one member's own read of its own write is not a front hazard");
    assert!(receipt.is_interchangeable());
}

// =================================================================================================
// C — shared output
// =================================================================================================

/// **C(a).** Two cells writing one region with no junction declared.
///
/// HELD: `RegionsOverlap` names the region and the footprint certificate refuses beside it.
#[test]
fn two_cells_writing_one_region_without_a_junction_refuse() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let cells = vec![owned_cell(0, shape.whole()), owned_cell(1, shape.whole())];
    let defects = partition_of(shape, cells)
        .certify(&cover, &[], &written_species(8), KERNEL)
        .expect_err("a shared output without a junction is not independent");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, PartitionDefect::RegionsOverlap { .. }))
    );
    assert!(defects.iter().any(|defect| matches!(
        defect,
        PartitionDefect::FootprintRefused {
            region: Some(_),
            ..
        }
    )));
}

/// **C(b).** A junction is declared and its two partial cells write only a 1x1 corner of an output
/// region that covers the whole section. Nothing checks that the partials cover the output, so the
/// junction's output enters the covering population by DECLARATION and completeness is satisfied by
/// a region no cell writes.
///
/// REFUTES: "completeness COMPUTED" holds for cells and not for junctions. The partials' union is
/// one entry; the section has thirty-two; the reading is complete.
// REFUTES: the junction output enters the covering population by DECLARATION; nothing computes that its partials cover it.
#[test]
fn a_junction_whose_partials_do_not_cover_its_output_must_refuse() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let junction = JunctionOutput {
        owner: "reduction".to_owned(),
        output: shape.whole(),
        partials: 2,
    };
    let cells = vec![
        SectionCell {
            index: 0,
            write: region(0, 1, 0, 1),
            reads: Vec::new(),
            partial_of: Some(PartialAddress {
                junction: 0,
                partial: 0,
            }),
        },
        SectionCell {
            index: 1,
            write: region(0, 1, 0, 1),
            reads: Vec::new(),
            partial_of: Some(PartialAddress {
                junction: 0,
                partial: 1,
            }),
        },
    ];
    let outcome = partition_of(shape, cells).certify(
        &cover,
        std::slice::from_ref(&junction),
        &written_species(8),
        KERNEL,
    );
    assert!(
        outcome.is_err(),
        "a junction owning {} whose partials together write {} entries must refuse; it certified \
         with complete = {:?}",
        shape.whole(),
        1,
        outcome.map(|receipt| receipt.completeness.complete)
    );
}

/// **C(c).** Two cells declaring the SAME partial ordinal of one junction. They then share one
/// partial address slot, so the footprint certificate must refuse.
///
/// HELD: `FootprintRefused`, with the region recovered.
#[test]
fn two_cells_claiming_the_same_partial_ordinal_refuse() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let junction = JunctionOutput {
        owner: "reduction".to_owned(),
        output: shape.whole(),
        partials: 2,
    };
    let address = PartialAddress {
        junction: 0,
        partial: 0,
    };
    let cells = vec![
        SectionCell {
            index: 0,
            write: shape.whole(),
            reads: Vec::new(),
            partial_of: Some(address),
        },
        SectionCell {
            index: 1,
            write: shape.whole(),
            reads: Vec::new(),
            partial_of: Some(address),
        },
    ];
    let defects = partition_of(shape, cells)
        .certify(
            &cover,
            std::slice::from_ref(&junction),
            &written_species(8),
            KERNEL,
        )
        .expect_err("two cells in one partial slot are not independent");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, PartitionDefect::FootprintRefused { .. })),
        "{defects:?}"
    );
}

/// **C(d).** A partial whose write does not lie inside its junction's output.
///
/// HELD: `PartialOutsideOutput` names the cell, its region and the output.
#[test]
fn a_partial_written_outside_its_junctions_output_refuses() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let junction = JunctionOutput {
        owner: "reduction".to_owned(),
        output: region(0, 4, 0, 4),
        partials: 1,
    };
    let cells = vec![
        SectionCell {
            index: 0,
            write: region(0, 4, 2, 6),
            reads: Vec::new(),
            partial_of: Some(PartialAddress {
                junction: 0,
                partial: 0,
            }),
        },
        owned_cell(1, region(0, 4, 4, 8)),
    ];
    let defects = partition_of(shape, cells)
        .certify(
            &cover,
            std::slice::from_ref(&junction),
            &written_species(8),
            KERNEL,
        )
        .expect_err("a partial outside its junction's output is not a partial of it");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, PartitionDefect::PartialOutsideOutput { .. })),
        "{defects:?}"
    );
}

/// **C(e).** `T_a` that does not land in the output chart: a 3x2 chart into a 2-dimensional output.
///
/// HELD: `ChartShape` names the partial and both shapes.
#[test]
fn a_chart_that_does_not_land_in_the_output_refuses() {
    let mut junction = scalar_junction(
        vec![
            scalar_partial(0, 0, 1, rat(1, 1)),
            scalar_partial(1, 1, 2, rat(1, 1)),
        ],
        2,
        64,
        0,
        0,
    );
    junction.output_dimension = 2;
    junction.codomain_metric = ExactRatMatrix::identity(2).expect("identity");
    junction.returned_covector = vec![rat(1, 1), rat(1, 1)];
    let defects = junction
        .certify()
        .expect_err("a 1x1 chart does not land in a 2-dimensional output");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, ReductionDefect::ChartShape { .. })),
        "{defects:?}"
    );
}

// =================================================================================================
// D — the fixed tree
// =================================================================================================

/// **D(i).** The reversed tree agrees on the value.
///
/// HELD — and it is forced by exactness, which the module says of itself. See the tautology reading.
#[test]
fn the_reversed_word_agrees_on_the_value() {
    let junction = scalar_junction(
        vec![
            scalar_partial(0, 0, 1, rat(1, 2)),
            // Dyadic since 2026-08-19: the declared carrier grain 2^-4 is now checked against the
            // carried material, and 1/3 and 1/5 stand at no dyadic grain whatever.
            scalar_partial(1, 1, 2, rat(1, 4)),
            scalar_partial(2, 2, 3, rat(1, 8)),
        ],
        3,
        64,
        4,
        2,
    );
    let receipt = junction.certify().expect("certifies");
    assert!(receipt.words_agree);
    assert_eq!(receipt.declared.value, receipt.reversed.value);
}

/// **D(ii).** Partials `1/2`, `1/4`, `1/4`. The PAIRWISE node stands at `3/4` — five bits of exact
/// rational — while the TOTAL is `1`, two bits. An aperture of four must refuse the node and name
/// it, with both leaves and the root inside.
///
/// HELD: `WidthExceedsAperture` names leaves `[0, 1]` at 5 bits against 4.
///
/// Material made dyadic 2026-08-19: it carried three `1/3`s, and the declared carrier grain is now
/// checked against what is carried.
#[test]
fn a_node_above_the_aperture_refuses_and_names_the_node_while_the_total_fits() {
    let partials = || {
        vec![
            scalar_partial(0, 0, 1, rat(1, 2)),
            scalar_partial(1, 1, 2, rat(1, 4)),
            scalar_partial(2, 2, 3, rat(1, 4)),
        ]
    };
    // First: the total's own width, read at a wide aperture.
    let wide = scalar_junction(partials(), 3, 64, 4, 2)
        .certify()
        .expect("certifies at a wide aperture");
    let root_width = wide
        .declared
        .nodes
        .iter()
        .find(|node| node.leaves.len() == 3)
        .expect("a root node")
        .width_bits;
    assert_eq!(root_width, 2, "the total 1 costs two bits");

    // Then: an aperture BETWEEN the pairwise node and the root.
    let defects = scalar_junction(partials(), 3, 4, 4, 2)
        .certify()
        .expect_err("the pairwise node stands above the aperture");
    let named = defects.iter().find_map(|defect| match defect {
        ReductionDefect::WidthExceedsAperture {
            leaves, width_bits, ..
        } => Some((leaves.clone(), *width_bits)),
        _ => None,
    });
    let (leaves, width) = named.expect("the aperture defect names its node");
    assert_eq!(width, 5, "3/4 costs five bits");
    assert!(
        leaves == vec![0, 1] || leaves == vec![2, 1],
        "the refusal names the NODE, not the junction: {leaves:?}"
    );
    assert!(
        root_width <= 4,
        "the total fits the aperture the node broke"
    );
}

/// **D(iii).** A word with a missing leaf, and a word with a duplicated leaf.
///
/// HELD: both return `WordDisagrees` carrying the declared leaves.
#[test]
fn a_word_with_a_missing_leaf_and_one_with_a_duplicate_both_refuse() {
    let partials = || {
        vec![
            scalar_partial(0, 0, 1, rat(1, 1)),
            scalar_partial(1, 1, 2, rat(1, 1)),
            scalar_partial(2, 2, 3, rat(1, 1)),
        ]
    };
    let mut missing = scalar_junction(partials(), 3, 64, 0, 0);
    missing.word = ReductionWord {
        root: ReductionNode::Join(
            Box::new(ReductionNode::Leaf(0)),
            Box::new(ReductionNode::Leaf(1)),
        ),
    };
    let defects = missing.certify().expect_err("a leaf is missing");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, ReductionDefect::WordDisagrees { .. })),
        "{defects:?}"
    );

    let mut duplicated = scalar_junction(partials(), 3, 64, 0, 0);
    duplicated.word = ReductionWord {
        root: ReductionNode::Join(
            Box::new(ReductionNode::Join(
                Box::new(ReductionNode::Leaf(0)),
                Box::new(ReductionNode::Leaf(1)),
            )),
            Box::new(ReductionNode::Leaf(1)),
        ),
    };
    let defects = duplicated.certify().expect_err("a leaf is named twice");
    assert!(
        defects
            .iter()
            .any(|defect| matches!(defect, ReductionDefect::WordDisagrees { .. })),
        "{defects:?}"
    );
}

/// **D(iii) at the public reader.** `read_word` is public and is what the builder's own control uses
/// to exhibit the two-rounding reading. Handed a word naming a leaf no partial holds, it substitutes
/// an exact ZERO and returns a value with no defect: a silent wrap at the public API, saved inside
/// `certify` only by the leaf check running first.
///
/// REFUTES: an unknown leaf must be refused, not read as zero.
// REFUTES: the public `read_word` substitutes an exact zero for an unknown leaf and pushes no defect.
#[test]
fn read_word_must_refuse_a_leaf_that_names_no_partial() {
    let junction = scalar_junction(
        vec![
            scalar_partial(0, 0, 1, rat(3, 1)),
            scalar_partial(1, 1, 2, rat(5, 1)),
        ],
        2,
        64,
        0,
        0,
    );
    let carried: Vec<Vec<Rat>> = junction
        .partials
        .iter()
        .map(|partial| partial.carried.clone())
        .collect();
    let bogus = ReductionWord {
        root: ReductionNode::Join(
            Box::new(ReductionNode::Leaf(0)),
            Box::new(ReductionNode::Leaf(99)),
        ),
    };
    let mut defects: Vec<ReductionDefect> = Vec::new();
    let reading = junction.read_word(
        &bogus,
        &carried,
        RoundingPolicy::OnceAtBoundary,
        &mut defects,
    );
    assert!(
        !defects.is_empty(),
        "leaf 99 names no partial; the reader returned {:?} with no defect",
        reading.value
    );
}

/// **D(iv).** The dependency span is the tree DEPTH and not the leaf count: eight leaves, a balanced
/// word spans three and a left-leaning word spans seven.
///
/// HELD.
#[test]
fn the_dependency_span_is_the_tree_depth_and_not_the_leaf_count() {
    let leaves = 8usize;
    let partials: Vec<PartialTerm> = (0..leaves)
        .map(|index| scalar_partial(index, index, index + 1, rat(index as i64 + 1, 1)))
        .collect();
    let mut balanced = scalar_junction(partials.clone(), leaves, 128, 0, 0);
    balanced.word = ReductionWord::balanced(leaves).expect("a word");
    let balanced = balanced.certify().expect("certifies");
    assert_eq!(balanced.declared.dependency_span, 3);
    assert_eq!(balanced.declared.leaves.len(), leaves);

    let leaning = scalar_junction(partials, leaves, 128, 0, 0)
        .certify()
        .expect("certifies");
    assert_eq!(leaning.declared.dependency_span, 7);
    // The same material, the same value, two different spans.
    assert_eq!(leaning.declared.value, balanced.declared.value);
}

/// **D extension.** The inner regions are checked for overlap and for holes against `inner_shape`,
/// but never for lying INSIDE it. A partial contracting `K` coordinates the inner axis does not have
/// is admitted, and its foreign extent even suppresses the hole check.
///
/// REFUTES: the inner partition is certified complete by a region outside `K`.
// REFUTES: the inner regions are never checked to lie within `inner_shape`; a foreign inner region also suppresses the hole check.
#[test]
fn an_inner_region_outside_k_must_refuse() {
    let junction = scalar_junction(
        vec![
            scalar_partial(0, 0, 1, rat(1, 1)),
            scalar_partial(1, 1, 2, rat(1, 1)),
            // K is three wide; this partial claims columns 2..9.
            scalar_partial(2, 2, 9, rat(1, 1)),
        ],
        3,
        64,
        0,
        0,
    );
    let outcome = junction.certify();
    assert!(
        outcome.is_err(),
        "a partial contracting [2..9) of a 3-wide inner axis must refuse the way a foreign CELL \
         does; it certified with inner_uncovered {:?}",
        outcome.map(|receipt| receipt.inner_uncovered)
    );
}

// =================================================================================================
// E — the one rounding
// =================================================================================================

/// **E.** Partials `1/8`, `1/2`, `3/8` at a boundary grain of `2^-2`. Summing once and rounding once
/// returns `4/4 = 1` exactly with a zero residual; rounding at every node takes the partial sum
/// `5/8` outward to `3/4` and returns `5/4`. The one rounding is therefore load-bearing on this
/// material and the two-rounding control differs.
///
/// HELD. Material made dyadic 2026-08-19 (it carried three `1/3`s) with every returned figure —
/// the total, the boundary value, the residual, the two-rounding value — unchanged.
#[test]
fn one_rounding_at_the_boundary_differs_from_rounding_at_every_node() {
    let partials = vec![
        scalar_partial(0, 0, 1, rat(1, 8)),
        scalar_partial(1, 1, 2, rat(1, 2)),
        scalar_partial(2, 2, 3, rat(3, 8)),
    ];
    let junction = scalar_junction(partials, 3, 64, 4, 2);
    let receipt = junction.certify().expect("certifies");
    // One rounding, at the boundary: the exact total is 1 and 1 is on the grain.
    assert_eq!(receipt.declared.value, vec![rat(1, 1)]);
    assert_eq!(receipt.boundary_value, vec![BigInt::from(4)]);
    assert_eq!(receipt.boundary_residual, vec![rat(0, 1)]);
    assert_eq!(receipt.declared.roundings, 0, "no rounding inside the tree");

    // The two-rounding control over the same material, through the public reader.
    let carried: Vec<Vec<Rat>> = junction
        .partials
        .iter()
        .map(|partial| partial.carried.clone())
        .collect();
    let mut ignored = Vec::new();
    let per_node = junction.read_word(
        &junction.word,
        &carried,
        RoundingPolicy::AtEveryNode,
        &mut ignored,
    );
    assert_eq!(per_node.roundings, 2, "two joins, two roundings");
    assert_eq!(per_node.value, vec![rat(5, 4)]);
    assert_ne!(
        per_node.value, receipt.declared.value,
        "rounding twice moves the value"
    );
}

/// **E, the hand.** A negative total: `-5/8` at a boundary grain of `2^-2` rounds OUTWARD to `-3/4`,
/// so the residual is `+1/8` — opposite in sign to the value. The receipt must carry it.
///
/// HELD.
#[test]
fn the_outward_residual_opposes_the_hand_on_a_negative_value() {
    let partials = vec![
        scalar_partial(0, 0, 1, rat(-1, 4)),
        scalar_partial(1, 1, 2, rat(-3, 8)),
    ];
    let receipt = scalar_junction(partials, 2, 64, 3, 2)
        .certify()
        .expect("certifies");
    assert_eq!(receipt.declared.value, vec![rat(-5, 8)]);
    assert_eq!(receipt.boundary_value, vec![BigInt::from(-3)]);
    assert_eq!(receipt.boundary_residual, vec![rat(1, 8)]);
    // The boundary encloses: |rounded| >= |exact|.
    assert_eq!(receipt.boundary_rational(), vec![rat(-3, 4)]);
    // And the residual's hand opposes the value's.
    assert!(receipt.declared.value[0] < rat(0, 1));
    assert!(receipt.boundary_residual[0] > rat(0, 1));
}

/// **E, the carrier.** `carrier_exponent` is compared only with `boundary_exponent`; nothing checks
/// that the partials stand at `2^-carrier_exponent`. A partial carrying `1/3` — a rational that is
/// not a dyadic at any exponent — is admitted at a declared carrier of `2^-4`, so
/// `BoundaryFinerThanCarrier` compares two declared numbers with no material behind either.
///
/// REFUTES. (The builder's own scalar fixture carries `1/3` at `carrier_exponent = 4`.)
// REFUTES: `carrier_exponent` is compared only with `boundary_exponent`; the carried material is never checked against it.
#[test]
fn the_carrier_grain_must_be_checked_against_the_material() {
    let partials = vec![
        scalar_partial(0, 0, 1, rat(1, 3)),
        scalar_partial(1, 1, 2, rat(1, 3)),
    ];
    let outcome = scalar_junction(partials, 2, 64, 4, 2).certify();
    assert!(
        outcome.is_err(),
        "1/3 does not stand exactly at 2^-4; the declared carrier must be checked against the \
         carried material, and it certified with carrier 2^-4 over {:?}",
        outcome.map(|receipt| receipt
            .partials
            .iter()
            .map(|partial| partial.carried.clone())
            .collect::<Vec<_>>())
    );
}

/// **E, the count.** `roundings` is the literal `1` in the receipt. On a two-dimensional output the
/// junction performs TWO outward roundings — one per coordinate, both carried in
/// `boundary_value` / `boundary_residual` — and still reports one.
///
/// REPAIRED 2026-08-19: `roundings` is now the counted total of `round_outward` invocations on the
/// certified path — one per output coordinate — so a declared input moves it and the assertion
/// below reads 2 on a two-coordinate output.
#[test]
fn the_roundings_field_is_a_constant_and_not_a_count() {
    let junction = two_wide_junction(
        matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]),
        ExactRatMatrix::identity(2).expect("identity"),
        matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (3, 1)]]),
        vec![rat(1, 1), rat(1, 1)],
    );
    let receipt = junction.certify().expect("certifies");
    assert_eq!(
        receipt.boundary_value.len(),
        2,
        "two coordinates were rounded"
    );
    assert_eq!(receipt.boundary_residual.len(), 2);
    assert_eq!(
        receipt.roundings, 2,
        "the field counts one round_outward per output coordinate"
    );
}

// =================================================================================================
// F — the adjoint under a declared metric
// =================================================================================================

/// A two-wide junction with one partial, so a metric can be declared on a genuine 2x2 chart.
fn two_wide_junction(
    chart: ExactRatMatrix,
    domain_metric: ExactRatMatrix,
    codomain_metric: ExactRatMatrix,
    covector: Vec<Rat>,
) -> ReductionJunction {
    let carried = vec![rat(3, 1), rat(-1, 2)];
    ReductionJunction {
        owner: "adversary".to_owned(),
        output: region(0, 1, 0, 2),
        output_dimension: 2,
        inner_shape: SectionShape::of(1, 2, 0),
        word: ReductionWord::left_leaning(1).expect("a word"),
        partials: vec![PartialTerm {
            index: 0,
            inner: region(0, 1, 0, 2),
            carried: carried.clone(),
            enclosure: carried.iter().map(|v| (v.clone(), v.clone())).collect(),
            chart,
            domain_metric,
        }],
        overflow_aperture: 256,
        carrier_exponent: 4,
        boundary_exponent: 2,
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        codomain_metric,
        returned_covector: covector,
    }
}

/// **F.** A NON-DIAGONAL SPD metric on both charts — `[[2,1],[1,2]]` on the domain and on the
/// codomain — with two partials carrying genuinely different charts. Every adjoint defect must be
/// exactly zero and every bare transpose must be refuted.
///
/// HELD: `adjoint_defect == 0` for both partials, both `bare_transpose_defect` nonzero
/// (`-10` and `-22`), and both partial charts receive an adjoint.
#[test]
fn the_adjoint_is_exact_under_a_non_diagonal_spd_metric_and_the_bare_transpose_is_not() {
    let first = PartialTerm {
        index: 0,
        inner: region(0, 1, 0, 2),
        carried: vec![rat(3, 1), rat(-1, 1)],
        enclosure: vec![(rat(3, 1), rat(3, 1)), (rat(-1, 1), rat(-1, 1))],
        chart: matrix(&[&[(1, 1), (2, 1)], &[(0, 1), (1, 1)]]),
        // NON-DIAGONAL SPD: det 3, both leading minors positive.
        domain_metric: matrix(&[&[(2, 1), (1, 1)], &[(1, 1), (2, 1)]]),
    };
    let second = PartialTerm {
        index: 1,
        inner: region(0, 1, 2, 4),
        carried: vec![rat(1, 2), rat(2, 1)],
        chart: matrix(&[&[(3, 1), (0, 1)], &[(1, 1), (-1, 1)]]),
        enclosure: vec![(rat(1, 2), rat(1, 2)), (rat(2, 1), rat(2, 1))],
        // A second, different NON-DIAGONAL SPD metric: det 11.
        domain_metric: matrix(&[&[(5, 1), (2, 1)], &[(2, 1), (3, 1)]]),
    };
    let junction = ReductionJunction {
        owner: "adversary".to_owned(),
        output: region(0, 1, 0, 2),
        output_dimension: 2,
        inner_shape: SectionShape::of(1, 4, 0),
        word: ReductionWord::balanced(2).expect("a word"),
        partials: vec![first, second],
        overflow_aperture: 256,
        carrier_exponent: 8,
        boundary_exponent: 3,
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        // NON-DIAGONAL SPD on the output chart too.
        codomain_metric: matrix(&[&[(2, 1), (1, 1)], &[(1, 1), (2, 1)]]),
        returned_covector: vec![rat(1, 1), rat(-2, 1)],
    };
    let receipt = junction.certify().expect("the junction certifies");
    assert_eq!(
        receipt.adjoints.len(),
        receipt.partials.len(),
        "every partial chart receives an adjoint"
    );
    for adjoint in &receipt.adjoints {
        assert!(
            adjoint.defect.is_zero(),
            "partial {} adjoint defect {} under a non-diagonal SPD metric",
            adjoint.partial,
            adjoint.defect
        );
        assert!(
            !adjoint.bare_transpose_defect.is_zero(),
            "partial {} bare transpose was NOT refuted",
            adjoint.partial
        );
    }
    // The defect is the widest entry of the OPERATOR residual `G_X T^T - T^T G_Y` since
    // 2026-08-19; it was read at one authored probe pair (`x = (1, 2)`) until then, which returned
    // -10 and -22 and could vanish while the operator identity failed.
    assert_eq!(receipt.adjoints[0].bare_transpose_defect, rat(2, 1));
    assert_eq!(receipt.adjoints[1].bare_transpose_defect, rat(8, 1));
    // And the residual itself is exhibited rather than summarized.
    assert_eq!(
        receipt.adjoints[0].bare_transpose_residual.to_rows(),
        vec![vec![rat(2, 1), rat(0, 1)], vec![rat(0, 1), rat(-2, 1)]]
    );
    assert!(
        receipt.adjoints[0]
            .residual
            .entries()
            .iter()
            .all(|entry| entry.is_zero())
    );
    // The adjoint carries the covector into a genuinely different chart than the transpose would.
    let transposed_return = receipt.adjoints[0]
        .adjoint
        .apply(&junction.returned_covector);
    assert!(transposed_return.is_ok());
}

/// **F, the vacuous control.** `adjoint_defect` is evaluated at ONE probe pair: the fixed
/// `x = (1, 2, ..., n)` and the junction's declared covector. Choose a declared non-identity metric
/// `G_Y = diag(1, 3)`, the identity chart and the covector `(1, 0)`: the defect is
/// `x^T (T^T G_Y - G_X T^T) y = 2 x_2 y_2 = 0`, so the BARE TRANSPOSE reports a zero defect under a
/// metric that is not the identity.
///
/// REFUTES the documented claim on `bare_transpose_defect` — "Zero only when both metrics are the
/// identity" — and with it the generality of the driver's control six, whose verdict requires every
/// bare transpose to be refuted. The covector is nonzero and the metric is non-identity; the control
/// still goes silently vacuous and nothing refuses.
// REFUTES: `bare_transpose_defect` is documented "zero only when both metrics are the identity"; here it is zero under G_Y = diag(1,3).
#[test]
fn the_bare_transpose_control_must_not_go_silently_vacuous() {
    let junction = two_wide_junction(
        ExactRatMatrix::identity(2).expect("identity"),
        ExactRatMatrix::identity(2).expect("identity"),
        // G_Y is declared and is NOT the identity.
        matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (3, 1)]]),
        // A nonzero covector whose second coordinate the defect probe happens to need.
        vec![rat(1, 1), rat(0, 1)],
    );
    let receipt = junction.certify().expect("certifies");
    assert_ne!(
        junction.codomain_metric,
        ExactRatMatrix::identity(2).expect("identity"),
        "the metric is genuinely non-identity"
    );
    assert!(
        !receipt.adjoints[0].bare_transpose_defect.is_zero(),
        "the bare transpose reports defect {} under a NON-IDENTITY metric, so the receipt cannot \
         be told apart from the Euclidean case and the control's evidence has vanished with no \
         refusal",
        receipt.adjoints[0].bare_transpose_defect
    );
}

/// **F, the degenerate covector.** With `ybar = 0` every claimed adjoint had zero defect, including
/// a bare transpose under any metric, because the defect was read at one probe pair against the
/// declared covector.
///
/// REPAIRED 2026-08-19: the defect is the operator residual `G_X T* - T^T G_Y`, which does not
/// depend on `ybar` at all, so a degenerate covector no longer makes the control vacuous. The
/// adjoint's own defect stays zero — it is exact — and the bare transpose is refuted.
#[test]
fn a_zero_covector_makes_every_adjoint_defect_zero() {
    let junction = two_wide_junction(
        matrix(&[&[(1, 1), (2, 1)], &[(0, 1), (1, 1)]]),
        matrix(&[&[(2, 1), (1, 1)], &[(1, 1), (2, 1)]]),
        matrix(&[&[(2, 1), (1, 1)], &[(1, 1), (2, 1)]]),
        vec![rat(0, 1), rat(0, 1)],
    );
    let receipt = junction.certify().expect("certifies");
    assert!(receipt.adjoints[0].defect.is_zero());
    assert!(
        !receipt.adjoints[0].bare_transpose_defect.is_zero(),
        "the control must not depend on the covector: a zero ybar no longer hides a bare \
         transpose under a non-identity metric"
    );
}

// =================================================================================================
// G — pressure
// =================================================================================================

/// **G(a).** No combined coordinate exists anywhere in the pressure receipt. The builder's own
/// control compares two SPLITS with an equal sum, which a receipt carrying an extra `total` field
/// would still pass; this one reads the receipt's own field names and would not.
///
/// HELD: the derived `Debug` of `PressureReceipt` names exactly `cell` and `species`, and the
/// species coordinates carry no cross-species name.
#[test]
fn the_pressure_receipt_names_no_combined_coordinate() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let resources = ResourceDeclaration {
        species: vec![
            DeclaredSpecies {
                name: "resident-lanes".to_owned(),
                unit: 1,
                face: DemandFace::Written,
                capacity: BigUint::from(8u32),
                characteristic_delay: 1,
                sink_capacity: BigUint::from(1u32),
            },
            DeclaredSpecies {
                name: "sectors".to_owned(),
                unit: 4,
                face: DemandFace::Written,
                capacity: BigUint::from(3u32),
                characteristic_delay: 2,
                sink_capacity: BigUint::from(1u32),
            },
        ],
        enactment_aperture: 4096,
    };
    let receipt = partition_of(shape, vec![owned_cell(0, shape.whole())])
        .certify(&cover, &[], &resources, KERNEL)
        .expect("certifies");
    let rendered = format!("{:?}", receipt.pressure[0]);
    for forbidden in [
        "total",
        "sum:",
        "combined",
        "utilization",
        "utilisation",
        "score",
        "aggregate",
        "overall",
    ] {
        assert!(
            !rendered.to_lowercase().contains(forbidden),
            "the pressure receipt names a combined coordinate `{forbidden}`: {rendered}"
        );
    }
    let names: Vec<&str> = receipt.pressure[0]
        .coordinates()
        .iter()
        .map(|(name, _)| *name)
        .collect();
    assert_eq!(names, vec!["resident-lanes", "sectors"]);
}

/// **G(b).** `R = ceil(N / C)` per species, moving with the declared capacity, with the boundary
/// residual `R*C - N` exhibited. `receiver_current`'s own enacted rounds agree with the stated
/// ceiling at every capacity, or the reading would have refused with `ServiceRoundsDisagree`.
///
/// HELD.
#[test]
fn service_rounds_follow_ceil_n_over_c_when_the_capacity_moves() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    // N = 32 written entries at unit 1.
    for (capacity, rounds, residual) in [(8u32, 4u32, 0u32), (5, 7, 3), (32, 1, 0), (64, 1, 32)] {
        let receipt = partition_of(shape, vec![owned_cell(0, shape.whole())])
            .certify(&cover, &[], &written_species(capacity), KERNEL)
            .unwrap_or_else(|defects| panic!("certifies at C={capacity}: {defects:?}"));
        let species = receipt.pressure[0]
            .species_named("resident-lanes")
            .expect("declared");
        assert_eq!(species.incoming, BigUint::from(32u32));
        assert_eq!(
            species.service_rounds,
            BigUint::from(rounds),
            "C = {capacity}"
        );
        assert_eq!(
            species.boundary_residual,
            BigUint::from(residual),
            "C = {capacity}"
        );
        assert!(
            matches!(species.enacted, EnactedCurrent::Radiated { .. }),
            "receiver_current conducted it at C = {capacity}"
        );
    }
}

/// **G(c).** The declared cover is NOT an input to the pressure reading: `capacity` comes from the
/// caller's `DeclaredSpecies` and from nowhere else, so two different covers return byte-identical
/// pressure. The driver couples the two by hand when it passes the cover's lane count into the
/// declaration; the owner does not.
///
/// Reported as a reading. It is lawful (a caller declaration), but "C from the device declaration"
/// is the driver's doing and not the owner's.
#[test]
fn the_declared_cover_does_not_enter_the_pressure_reading() {
    let shape = SectionShape::of(4, 8, 0);
    let one = HardwareCover::cpu_only();
    let two = HardwareCover::of_charts(vec![
        Chart::Cpu(CpuDeclaration::declare()),
        Chart::Cpu(CpuDeclaration::declare()),
    ]);
    let material = partition_of(shape, vec![owned_cell(0, shape.whole())]);
    let left = material
        .certify(&one, &[], &written_species(8), KERNEL)
        .expect("certifies");
    let right = material
        .certify(&two, &[], &written_species(8), KERNEL)
        .expect("certifies");
    assert_eq!(
        left.pressure, right.pressure,
        "the cover does not reach the pressure"
    );
    // And the covers really are different objects at the cover face.
    assert_ne!(left.cover.work.len(), right.cover.work.len());
}

/// **G(d).** A genuine ZERO demand was returned as `BeyondAperture { demand: 0 }` — the variant
/// whose whole purpose is to say *unknown, never zero*, so a zero demand and an over-aperture
/// demand returned the same variant.
///
/// REPAIRED 2026-08-19: a zero demand now returns the named `NoDemand` face carrying the face whose
/// material was empty, and the unknown variant is reserved for what is genuinely unknown. The
/// assertion below is updated from the observation to the repair.
#[test]
fn a_zero_demand_is_returned_as_beyond_the_aperture() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let resources = ResourceDeclaration {
        species: vec![DeclaredSpecies {
            name: "map-ingress".to_owned(),
            unit: 1,
            // The cell declares no reads, so the READ face is a true zero.
            face: DemandFace::Read,
            capacity: BigUint::from(8u32),
            characteristic_delay: 1,
            // Added 2026-08-19: the sink capacity is a caller declaration with no default.
            sink_capacity: BigUint::from(1u32),
        }],
        enactment_aperture: 4096,
    };
    let receipt = partition_of(shape, vec![owned_cell(0, shape.whole())])
        .certify(&cover, &[], &resources, KERNEL)
        .expect("certifies");
    let species = receipt.pressure[0]
        .species_named("map-ingress")
        .expect("declared");
    assert!(species.incoming.is_zero());
    match &species.enacted {
        EnactedCurrent::NoDemand { face } => {
            assert!(
                matches!(face, DemandFace::Read),
                "the named zero carries the face whose material was empty"
            );
        }
        EnactedCurrent::BeyondAperture { demand, aperture } => panic!(
            "a genuine zero demand is still returned as the UNKNOWN variant: demand {demand} \
             against aperture {aperture}"
        ),
        EnactedCurrent::Radiated { .. } => panic!("observed a radiation on a zero demand"),
    }
}

// =================================================================================================
// the refusals, in words — a defect that names a region must SAY the region
// =================================================================================================

/// Every refusal above is rendered through its `Display`, so the text a caller sees is pinned here
/// rather than inferred from a variant name.
#[test]
fn the_refusals_name_their_regions_in_words() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);

    // a hole and a double cover
    let defects = partition_of(
        shape,
        vec![
            owned_cell(0, region(0, 4, 0, 4)),
            owned_cell(1, region(0, 4, 2, 6)),
        ],
    )
    .certify(&cover, &[], &written_species(8), KERNEL)
    .expect_err("refuses");
    let rendered: Vec<String> = defects.iter().map(|defect| defect.to_string()).collect();
    assert!(
        rendered.contains(&"cells 0 and 1 both write [0..4) x [2..4)".to_owned()),
        "{rendered:?}"
    );
    assert!(
        rendered.contains(&"no cell and no junction writes [0..4) x [6..8)".to_owned()),
        "{rendered:?}"
    );

    // a foreign tile
    let defects = partition_of(
        shape,
        vec![
            owned_cell(0, region(0, 4, 0, 4)),
            owned_cell(1, region(0, 5, 4, 8)),
        ],
    )
    .certify(&cover, &[], &written_species(8), KERNEL)
    .expect_err("refuses");
    assert!(
        defects.iter().any(|defect| defect.to_string()
            == "cell 1 writes [0..5) x [4..8), which lies outside the 4 x 8 section"),
        "{:?}",
        defects.iter().map(ToString::to_string).collect::<Vec<_>>()
    );

    // the node above the aperture
    let defects = scalar_junction(
        vec![
            scalar_partial(0, 0, 1, rat(1, 3)),
            scalar_partial(1, 1, 2, rat(1, 3)),
            scalar_partial(2, 2, 3, rat(1, 3)),
        ],
        3,
        3,
        4,
        2,
    )
    .certify()
    .expect_err("refuses");
    assert!(
        defects.iter().any(|defect| defect.to_string()
            == "in ((0 + 1) + 2), the node over [0, 1] stands at 4 bits against an aperture of 3"),
        "{:?}",
        defects.iter().map(ToString::to_string).collect::<Vec<_>>()
    );
}

// =================================================================================================
// I — the tautology probes: which declared input, varied, moves two members of a class apart?
// =================================================================================================

/// **Control five's second perturbation is a property of the MATERIAL, not of the policy.** The
/// builder's driver reads its control-five verdict partly from `forward.value != backward.value`
/// under `AtEveryNode`. On symmetric material — three partials all carrying `1/3` — the reversed
/// word visits the same numbers in the same shape, so the two words AGREE under two roundings and
/// that clause returns false.
///
/// Green: the observation is on record. The rounding policy is still refused by `certify`, which is
/// the part that does not depend on the fixture.
#[test]
fn rounding_at_every_node_does_not_separate_the_words_on_symmetric_material() {
    let junction = scalar_junction(
        vec![
            // Dyadic since 2026-08-19; symmetric, which is the whole point of the fixture.
            scalar_partial(0, 0, 1, rat(1, 4)),
            scalar_partial(1, 1, 2, rat(1, 4)),
            scalar_partial(2, 2, 3, rat(1, 4)),
        ],
        3,
        64,
        4,
        2,
    );
    let carried: Vec<Vec<Rat>> = junction
        .partials
        .iter()
        .map(|partial| partial.carried.clone())
        .collect();
    let mut ignored = Vec::new();
    let forward = junction.read_word(
        &junction.word,
        &carried,
        RoundingPolicy::AtEveryNode,
        &mut ignored,
    );
    let backward = junction.read_word(
        &junction.word.reversed(junction.partials.len()),
        &carried,
        RoundingPolicy::AtEveryNode,
        &mut ignored,
    );
    assert_eq!(
        forward.value, backward.value,
        "on symmetric material the two-rounding control separates nothing"
    );
    // The widths do not separate them either, so control five's whole non-forced half is empty here.
    let receipt = junction.certify().expect("certifies");
    assert_eq!(
        receipt.declared.peak_width_bits, receipt.reversed.peak_width_bits,
        "and the per-node widths agree too"
    );
}

/// **The write/read hazard is keyed on a declared population NAME.** `writer_of` returns a writer
/// only when the read's population string equals `lineage.population`, and `address_bases` gives
/// that one name base zero. Declare the identical coordinates under any other name and the same
/// material certifies as an immutable shared standing.
///
/// Green: the class returned by controls one and two is the preimage of a caller-set string, not of
/// a computed storage identity. The interval arithmetic beneath it is real; the decision of WHICH
/// address space a read lands in is a name comparison.
#[test]
fn the_write_read_hazard_is_decided_by_a_declared_population_name() {
    let cover = HardwareCover::cpu_only();
    let shape = SectionShape::of(4, 8, 0);
    let hazard = |name: &str| {
        let mut populations = BTreeMap::new();
        populations.insert(name.to_owned(), shape);
        SectionPartition {
            lineage: lineage(),
            shape,
            populations,
            cells: vec![
                SectionCell {
                    index: 0,
                    write: region(0, 4, 0, 4),
                    // exactly the coordinates cell 1 writes
                    reads: vec![ReadRegion {
                        population: name.to_owned(),
                        region: region(0, 4, 4, 8),
                    }],
                    partial_of: None,
                },
                owned_cell(1, region(0, 4, 4, 8)),
            ],
        }
        .certify(&cover, &[], &written_species(8), KERNEL)
    };
    // Named as the section's own population: refused.
    assert!(
        hazard("section").is_err(),
        "the same coordinates under the section's own name are a hazard"
    );
    // The identical coordinates under any other name: certified, with the standing called immutable.
    let renamed = hazard("staging").expect("the same coordinates under another name certify");
    assert!(renamed.is_interchangeable());
}
