//! The launch law's own receipts.
//!
//! Every test here is the executable form of a named theorem in
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/DeviceLaunchLaw.lean`, or a negative
//! test for a clause that theorem's hypotheses exclude.  The negatives are the point: a decoder or
//! constructor taking declared extents earns its hostile-input tests alongside it.

use super::*;

/// A synthetic card for the cpu tests.  It is not a reading of any device and cannot be
/// constructed outside `cfg(test)`; the production paths are `LaunchLimits::read` and
/// `LaunchLimits::from_census`.
fn synthetic_limits() -> LaunchLimits {
    LaunchLimits::synthetic(
        512,
        Some(512),
        Some(Dim3 {
            x: 4096,
            y: 64,
            z: 1,
        }),
        Some(Dim3 {
            x: 512,
            y: 512,
            z: 64,
        }),
        Some(49_152),
        Some(32),
    )
}

fn device_argument(name: &'static str, address: u64, elements: usize) -> ArgumentSpan {
    ArgumentSpan::device_raw(name, address, elements, 4, Access::Read)
}

fn one_argument_requirement() -> Vec<ArgumentRequirement> {
    vec![ArgumentRequirement::device(
        "cells",
        Access::Read,
        4,
        Extent::AtLeast(1),
    )]
}

// -------------------------------------------------------------------------------------------
// D1 positives
// -------------------------------------------------------------------------------------------

/// `DeviceLaunchLaw.LaunchShape.cover_covers` and `cover_tail`: the derived shape reaches the
/// declared extent and its guarded tail is strictly below one block.
#[test]
fn the_derived_cover_reaches_the_extent_with_a_tail_below_one_block() {
    let limits = synthetic_limits();
    for extent in [1u64, 2, 511, 512, 513, 1_000, 262_144, 262_145] {
        let requirement = LaunchRequirement::guarded(
            "cover",
            extent,
            vec![ArgumentRequirement::device("cells", Access::Read, 4, Extent::Any)],
        );
        let shape = requirement.cover_with(&limits).expect("a cover exists");
        let threads = shape.threads().expect("the product is representable");
        let block = shape.block_threads().expect("the block is representable");
        assert!(threads >= extent, "extent {extent} is covered");
        assert!(
            threads - extent < block as u64,
            "extent {extent}: tail {} is below one {block}-thread block",
            threads - extent
        );
    }
}

/// A lawful launch returns a receipt naming exactly the clauses it proved, and with complete
/// device evidence it defers nothing.
#[test]
fn a_lawful_launch_returns_a_receipt_naming_every_proved_clause() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("cover", 1_000, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 1_000)];
    let lawful =
        LawfulLaunch::cover(&requirement, &limits, &arguments).expect("the launch is lawful");
    let receipt = lawful.receipt();
    assert_eq!(receipt.kernel, "cover");
    assert_eq!(receipt.extent, 1_000);
    assert_eq!(receipt.threads, 1_024);
    assert_eq!(receipt.guard_threads, 24);
    assert_eq!(receipt.x_stride, 1_024);
    assert_eq!(receipt.shared_bytes, 0);
    assert!(receipt.deferred().is_empty(), "{receipt:?}");
    assert!(receipt.proves(LaunchClause::BlockDimensionWithinDevice));
    for clause in [
        LaunchClause::PositiveExtent,
        LaunchClause::PositiveBlock,
        LaunchClause::PositiveGrid,
        LaunchClause::ThreadProductRepresentable,
        LaunchClause::StrideRepresentable,
        LaunchClause::BlockWithinFunction,
        LaunchClause::BlockWithinDevice,
        LaunchClause::GridWithinDevice,
        LaunchClause::CoverageGuarded,
        LaunchClause::SharedBytesMatch,
        LaunchClause::SharedWithinDevice,
        LaunchClause::ArgumentCount,
        LaunchClause::ArgumentName,
        LaunchClause::ArgumentResidency,
        LaunchClause::ArgumentExtent,
        LaunchClause::ArgumentAddress,
        LaunchClause::ArgumentAliasing,
    ] {
        assert!(receipt.proves(clause), "{} was not proved", clause.name());
    }
    assert_eq!(receipt.arguments.len(), 1);
    assert_eq!(receipt.arguments[0].bytes, 4_000);
}

/// `DeviceLaunchLaw.exists_unique_thread`: an exact cover leaves no thread idle.
#[test]
fn an_exact_cover_leaves_no_guarded_thread() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::exact(
        "exact",
        1_024,
        Dim3::x(256),
        vec![ArgumentRequirement::device("cells", Access::Read, 4, Extent::Any)],
    );
    let arguments = [device_argument("cells", 0x2000, 1_024)];
    let receipt = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect("the exact cover is lawful")
        .receipt()
        .clone();
    assert_eq!(receipt.threads, 1_024);
    assert_eq!(receipt.guard_threads, 0);
    assert_eq!(receipt.grid, Dim3::x(4));
    assert!(receipt.proves(LaunchClause::CoverageExact));
    assert!(receipt.proves(LaunchClause::BlockExact));
}

/// A mouth with no device evidence still proves every arithmetic and function clause, and **says
/// aloud** which device clauses it deferred.
#[test]
fn a_function_only_proof_defers_the_device_clauses_instead_of_assuming_them() {
    let limits = LaunchLimits::synthetic(512, None, None, None, None, None);
    let requirement = LaunchRequirement::guarded("partial", 256, one_argument_requirement());
    let arguments = [device_argument("cells", 0x3000, 256)];
    let shape = LaunchShape::linear(1, 256);
    let receipt = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect("the arithmetic clauses hold")
        .receipt()
        .clone();
    assert!(receipt.proves(LaunchClause::BlockWithinFunction));
    assert!(receipt.defers(LaunchClause::BlockWithinDevice));
    assert!(receipt.defers(LaunchClause::GridWithinDevice));
    assert!(receipt.defers(LaunchClause::SharedWithinDevice));
    assert!(!receipt.proves(LaunchClause::GridWithinDevice));
}

/// Shared memory is declared as a function of the block shape, evaluated with checked arithmetic.
#[test]
fn the_shared_extent_is_a_function_of_the_block_and_not_a_number() {
    let shared = SharedRequirement {
        per_block_bytes: 64,
        per_thread_bytes: 8,
    };
    assert_eq!(shared.bytes_for(32).unwrap(), 64 + 256);
    assert_eq!(shared.bytes_for(0).unwrap(), 64);
    assert!(shared.bytes_for(u32::MAX).is_err());
    assert_eq!(SharedRequirement::NONE.bytes_for(1_024).unwrap(), 0);
}

// -------------------------------------------------------------------------------------------
// D1 negatives — hostile declared extents
// -------------------------------------------------------------------------------------------

#[test]
fn a_zero_extent_is_refused_before_any_driver_call() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("empty", 0, one_argument_requirement());
    let refusal = requirement.cover_with(&limits).expect_err("zero is refused");
    assert_eq!(refusal.clause, LaunchClause::PositiveExtent);

    let arguments = [device_argument("cells", 0x1000, 1)];
    let refusal = LawfulLaunch::prove(&requirement, &limits, LaunchShape::linear(1, 1), &arguments)
        .expect_err("zero is refused at the proof too");
    assert_eq!(refusal.clause, LaunchClause::PositiveExtent);
    assert_eq!(refusal.kernel, "empty");
}

#[test]
fn a_grid_past_the_device_limit_is_refused_naming_the_clause() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("wide", 4_096 * 64, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 4_096 * 64)];
    // 4097 blocks in X, one past the synthetic aperture of 4096.
    let shape = LaunchShape::linear(4_097, 64);
    let refusal = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect_err("the grid is past the device aperture");
    assert_eq!(refusal.clause, LaunchClause::GridWithinDevice);
    assert!(refusal.detail.contains("4097"), "{}", refusal.detail);
}

#[test]
fn a_cover_that_cannot_fit_the_device_aperture_is_refused_rather_than_clipped() {
    let limits = synthetic_limits();
    // 4096 * 64 blocks * 512 threads is the whole synthetic aperture; one element past it cannot
    // be covered and must refuse instead of dropping work.
    let extent = 4_096u64 * 64 * 512 + 1;
    let requirement = LaunchRequirement::guarded("overflowing", extent, one_argument_requirement());
    let refusal = requirement
        .cover_with(&limits)
        .expect_err("the aperture cannot carry it");
    assert_eq!(refusal.clause, LaunchClause::GridWithinDevice);
}

#[test]
fn a_u32_overflow_in_grid_times_block_is_refused() {
    // A function cap wide enough to reach the wire, so the stride clause is the one that fires.
    let limits = LaunchLimits::synthetic(1 << 20, None, None, None, None, None);
    let requirement = LaunchRequirement::strided("striding", 1_000, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 1_000)];
    let shape = LaunchShape::linear(1 << 20, 1 << 13);
    let refusal = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect_err("grid.x * block.x leaves the u32 wire");
    assert_eq!(refusal.clause, LaunchClause::StrideRepresentable);
}

#[test]
fn a_u64_overflow_in_the_thread_product_is_refused() {
    let limits = LaunchLimits::synthetic(u32::MAX, None, None, None, None, None);
    let requirement = LaunchRequirement::strided("striding", 1, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 1)];
    let shape = LaunchShape {
        grid: Dim3 {
            x: u32::MAX,
            y: u32::MAX,
            z: u32::MAX,
        },
        block: Dim3 {
            x: u32::MAX,
            y: 1,
            z: 1,
        },
        shared_bytes: 0,
    };
    let refusal = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect_err("the thread product leaves u64");
    assert_eq!(refusal.clause, LaunchClause::ThreadProductRepresentable);
}

#[test]
fn a_usize_overflow_in_an_argument_extent_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("wide-argument", 1, one_argument_requirement());
    let arguments = [ArgumentSpan::device_raw(
        "cells",
        0x1000,
        usize::MAX,
        4,
        Access::Read,
    )];
    let refusal = LawfulLaunch::prove(&requirement, &limits, LaunchShape::linear(1, 1), &arguments)
        .expect_err("the octet extent leaves usize");
    assert_eq!(refusal.clause, LaunchClause::ArgumentExtent);
}

#[test]
fn an_undersized_buffer_is_refused_naming_the_argument() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded(
        "undersized",
        1_000,
        vec![ArgumentRequirement::device(
            "cells",
            Access::Read,
            4,
            Extent::AtLeast(1_000),
        )],
    );
    let arguments = [device_argument("cells", 0x1000, 999)];
    let refusal = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect_err("999 elements do not carry 1000");
    assert_eq!(refusal.clause, LaunchClause::ArgumentExtent);
    assert!(refusal.detail.contains("cells"), "{}", refusal.detail);
    assert!(refusal.detail.contains("999"), "{}", refusal.detail);
}

#[test]
fn a_wrong_residency_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("resident", 4, one_argument_requirement());
    let host = [1u32, 2, 3, 4];
    let arguments = [ArgumentSpan::host("cells", &host)];
    let refusal = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect_err("a kernel does not dereference pageable host memory");
    assert_eq!(refusal.clause, LaunchClause::ArgumentResidency);
    assert!(refusal.detail.contains("device-resident"), "{}", refusal.detail);
}

#[test]
fn a_shared_memory_mismatch_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement {
        shared: SharedRequirement {
            per_block_bytes: 256,
            per_thread_bytes: 0,
        },
        ..LaunchRequirement::guarded("reducing", 256, one_argument_requirement())
    };
    let arguments = [device_argument("cells", 0x1000, 256)];
    let refusal = LawfulLaunch::prove(
        &requirement,
        &limits,
        LaunchShape::linear(1, 256),
        &arguments,
    )
    .expect_err("the offered shared extent is not the declared one");
    assert_eq!(refusal.clause, LaunchClause::SharedBytesMatch);

    // The same requirement with the declared extent is lawful.
    let shape = LaunchShape {
        shared_bytes: 256,
        ..LaunchShape::linear(1, 256)
    };
    assert!(LawfulLaunch::prove(&requirement, &limits, shape, &arguments).is_ok());
}

#[test]
fn a_shared_extent_past_the_device_is_refused() {
    let limits = LaunchLimits::synthetic(512, Some(512), None, None, Some(1_024), None);
    let requirement = LaunchRequirement {
        shared: SharedRequirement {
            per_block_bytes: 4_096,
            per_thread_bytes: 0,
        },
        ..LaunchRequirement::guarded("reducing", 256, one_argument_requirement())
    };
    let arguments = [device_argument("cells", 0x1000, 256)];
    let shape = LaunchShape {
        shared_bytes: 4_096,
        ..LaunchShape::linear(1, 256)
    };
    let refusal = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect_err("4096 shared octets exceed the declared 1024");
    assert_eq!(refusal.clause, LaunchClause::SharedWithinDevice);
}

#[test]
fn a_block_past_the_lowered_function_limit_is_refused() {
    let limits = LaunchLimits::synthetic(128, Some(512), None, None, None, None);
    let requirement = LaunchRequirement::guarded("narrow", 256, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 256)];
    let refusal = LawfulLaunch::prove(
        &requirement,
        &limits,
        LaunchShape::linear(1, 256),
        &arguments,
    )
    .expect_err("the lowered entry caps the block at 128");
    assert_eq!(refusal.clause, LaunchClause::BlockWithinFunction);
}

#[test]
fn an_argument_population_or_name_mismatch_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("named", 4, one_argument_requirement());
    let refusal = LawfulLaunch::cover(&requirement, &limits, &[])
        .expect_err("no arguments were presented");
    assert_eq!(refusal.clause, LaunchClause::ArgumentCount);

    let arguments = [device_argument("wrong", 0x1000, 4)];
    let refusal = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect_err("the presented name is not the declared one");
    assert_eq!(refusal.clause, LaunchClause::ArgumentName);
}

#[test]
fn a_null_device_argument_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("null", 4, one_argument_requirement());
    let arguments = [device_argument("cells", 0, 4)];
    let refusal = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect_err("a null device address is not standing");
    assert_eq!(refusal.clause, LaunchClause::ArgumentAddress);
}

#[test]
fn a_guarded_shape_that_over_covers_by_a_whole_block_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("over", 100, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 100)];
    // Two 128-thread blocks for 100 elements: the second block is entirely idle.
    let refusal = LawfulLaunch::prove(
        &requirement,
        &limits,
        LaunchShape::linear(2, 128),
        &arguments,
    )
    .expect_err("a whole idle block is over-covering, not guarding");
    assert_eq!(refusal.clause, LaunchClause::CoverageGuarded);
}

#[test]
fn a_shape_that_under_covers_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("under", 1_000, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 1_000)];
    let refusal = LawfulLaunch::prove(
        &requirement,
        &limits,
        LaunchShape::linear(1, 512),
        &arguments,
    )
    .expect_err("512 threads do not reach 1000 elements");
    assert_eq!(refusal.clause, LaunchClause::CoverageGuarded);
}

#[test]
fn a_refusal_crossing_into_the_driver_result_stays_a_construction_refusal() {
    let refusal = LaunchRefusal::new("entry", LaunchClause::CoverageGuarded, "under-covered");
    let error: CudaError = refusal.into();
    assert_eq!(error.name, "LAUNCH_LAW_REFUSAL");
    assert_eq!(error.context, "coverage-guarded");
    assert!(error.message.contains("entry"));
}

// -------------------------------------------------------------------------------------------
// D2 — partitions
// -------------------------------------------------------------------------------------------

/// `DeviceLaunchLaw.DisjointPartition.uniform` with `region_disjoint` and `region_subset`.
#[test]
fn a_uniform_partition_is_disjoint_and_stays_inside_its_span() {
    let partition = DisjointPartition::uniform(64, 8, 8, 8).expect("the uniform form is proved");
    assert_eq!(partition.regions(), 8);
    assert_eq!(partition.covered(), 64);
    assert_eq!(partition.region(0), Some(0..8));
    assert_eq!(partition.region(7), Some(56..64));
    assert_eq!(partition.region(8), None);
    partition
        .verify_pairwise_disjoint()
        .expect("every pair is disjoint and inside the span");

    // A width narrower than the stride leaves declared gaps and is still lawful.
    let sparse = DisjointPartition::uniform(64, 8, 8, 3).expect("a narrow write width is lawful");
    assert_eq!(sparse.covered(), 24);
    assert_eq!(sparse.region(1), Some(8..11));
    sparse.verify_pairwise_disjoint().expect("still disjoint");
}

#[test]
fn a_uniform_partition_refuses_a_width_beyond_its_stride() {
    let refusal = DisjointPartition::uniform(64, 8, 8, 9).expect_err("regions would overlap");
    assert_eq!(refusal.clause, PartitionClause::WidthWithinStride);
}

#[test]
fn a_uniform_partition_refuses_a_cover_beyond_its_span() {
    let refusal = DisjointPartition::uniform(63, 8, 8, 8).expect_err("the last region escapes");
    assert_eq!(refusal.clause, PartitionClause::CoverWithinSpan);

    let refusal = DisjointPartition::uniform(usize::MAX, usize::MAX, 2, 1)
        .expect_err("the covered extent overflows usize");
    assert_eq!(refusal.clause, PartitionClause::CoverWithinSpan);

    assert_eq!(
        DisjointPartition::uniform(64, 0, 8, 8)
            .expect_err("zero regions")
            .clause,
        PartitionClause::PositiveRegions
    );
    assert_eq!(
        DisjointPartition::uniform(64, 8, 0, 0)
            .expect_err("zero stride")
            .clause,
        PartitionClause::PositiveStride
    );
}

/// `DeviceLaunchLaw.DisjointPartition.ofOffsets` with `offsets_mono`.
#[test]
fn an_offsets_table_is_admitted_only_when_monotone_and_in_bounds() {
    let partition = DisjointPartition::from_offsets(20, vec![0, 3, 3, 11, 20])
        .expect("a monotone table with one empty region is lawful");
    assert_eq!(partition.regions(), 4);
    assert_eq!(partition.region(1), Some(3..3));
    assert_eq!(partition.region(2), Some(3..11));
    assert_eq!(partition.covered(), 20);
    partition
        .verify_pairwise_disjoint()
        .expect("empty regions are vacuously disjoint");

    assert_eq!(
        DisjointPartition::from_offsets(20, vec![0, 5, 4, 20])
            .expect_err("descending boundary")
            .clause,
        PartitionClause::OffsetsMonotone
    );
    assert_eq!(
        DisjointPartition::from_offsets(20, vec![0, 5, 21])
            .expect_err("past the span")
            .clause,
        PartitionClause::OffsetsWithinSpan
    );
    assert_eq!(
        DisjointPartition::from_offsets(20, vec![0])
            .expect_err("a table needs a boundary and an end")
            .clause,
        PartitionClause::OffsetsLength
    );
}

/// `DeviceLaunchLaw.DisjointPartition.raceFree`: applying the per-thread writes in any order
/// yields the same final state.  This runs the theorem on a host model of the device state.
#[test]
fn per_thread_writes_under_a_disjoint_partition_commute() {
    fn apply(state: &mut [u64], partition: &DisjointPartition, order: &[usize]) {
        for thread in order {
            let region = partition.region(*thread).expect("the thread has a region");
            for address in region {
                state[address] = (*thread as u64 + 1) * 1_000 + address as u64;
            }
        }
    }

    let partition = DisjointPartition::uniform(24, 6, 4, 4).expect("proved");
    let forward: Vec<usize> = (0..6).collect();
    let reverse: Vec<usize> = (0..6).rev().collect();
    let shuffled = vec![3usize, 0, 5, 1, 4, 2];

    let mut first = vec![0u64; 24];
    let mut second = vec![0u64; 24];
    let mut third = vec![0u64; 24];
    apply(&mut first, &partition, &forward);
    apply(&mut second, &partition, &reverse);
    apply(&mut third, &partition, &shuffled);
    assert_eq!(first, second, "reverse interleaving agrees");
    assert_eq!(first, third, "an arbitrary interleaving agrees");

    // `foldl_write_mem`: the final state is exactly the per-region write, not merely consistent.
    for thread in 0..6 {
        for address in partition.region(thread).unwrap() {
            assert_eq!(first[address], (thread as u64 + 1) * 1_000 + address as u64);
        }
    }
}

/// `DeviceLaunchLaw.DisjointPartition.scatter_perm`: an injective incidence map is admitted, and
/// its writes are order-independent.
#[test]
fn an_injective_scatter_is_admitted_and_order_independent() {
    let partition = DisjointPartition::scatter(8, vec![7, 0, 3, 5], ScatterLaw::Injective)
        .expect("an injective incidence map is disjoint");
    assert_eq!(partition.regions(), 4);
    assert_eq!(partition.region(0), Some(7..8));
    partition
        .verify_pairwise_disjoint()
        .expect("injective targets do not overlap");

    let targets = [7usize, 0, 3, 5];
    let mut forward = [0u64; 8];
    let mut reverse = [0u64; 8];
    for thread in 0..4 {
        forward[targets[thread]] = thread as u64 + 1;
    }
    for thread in (0..4).rev() {
        reverse[targets[thread]] = thread as u64 + 1;
    }
    assert_eq!(forward, reverse);
}

/// `DeviceLaunchLaw.DisjointPartition.scatter_order_dependent`: the counterexample, executed.  A
/// colliding index map under plain stores is order-dependent, so the constructor refuses it and
/// names the colliding pair.
#[test]
fn a_colliding_scatter_is_refused_and_is_genuinely_order_dependent() {
    let refusal = DisjointPartition::scatter(8, vec![3, 1, 3], ScatterLaw::Injective)
        .expect_err("threads 0 and 2 collide");
    assert_eq!(refusal.clause, PartitionClause::ScatterInjective);
    assert!(refusal.detail.contains("slot 3"), "{}", refusal.detail);

    // The refusal is not pedantry: the two orders disagree.
    let targets = [3usize, 1, 3];
    let values = [10u64, 20, 30];
    let mut forward = [0u64; 8];
    let mut reverse = [0u64; 8];
    for thread in 0..3 {
        forward[targets[thread]] = values[thread];
    }
    for thread in (0..3).rev() {
        reverse[targets[thread]] = values[thread];
    }
    assert_ne!(forward, reverse, "a colliding plain-store scatter is order-dependent");
    assert_eq!(forward[3], 30);
    assert_eq!(reverse[3], 10);
}

/// `DeviceLaunchLaw.DisjointPartition.scatterAdd_perm`: the same colliding map is admissible, and
/// order-independent, under a declared associative-commutative accumulation.  This is the D3 seam.
#[test]
fn a_colliding_scatter_is_admitted_under_a_declared_accumulation() {
    let partition = DisjointPartition::scatter(8, vec![3, 1, 3], ScatterLaw::Accumulated)
        .expect("an accumulation law admits collisions");
    assert_eq!(partition.scatter_law(), Some(ScatterLaw::Accumulated));
    partition
        .verify_pairwise_disjoint()
        .expect("the disjointness half is carried by the accumulation, and says so");

    let targets = [3usize, 1, 3];
    let values = [10u64, 20, 30];
    let mut forward = [0u64; 8];
    let mut reverse = [0u64; 8];
    for thread in 0..3 {
        forward[targets[thread]] += values[thread];
    }
    for thread in (0..3).rev() {
        reverse[targets[thread]] += values[thread];
    }
    assert_eq!(forward, reverse, "accumulation restores order-independence");
    assert_eq!(forward[3], 40);
}

#[test]
fn a_scatter_past_the_span_is_refused() {
    let refusal = DisjointPartition::scatter(4, vec![0, 4], ScatterLaw::Injective)
        .expect_err("slot 4 is outside a span of 4");
    assert_eq!(refusal.clause, PartitionClause::ScatterWithinSpan);
    let refusal = DisjointPartition::scatter(4, Vec::new(), ScatterLaw::Accumulated)
        .expect_err("an empty incidence is not a scatter");
    assert_eq!(refusal.clause, PartitionClause::PositiveRegions);
}

// -------------------------------------------------------------------------------------------
// D2 — aliasing
// -------------------------------------------------------------------------------------------

#[test]
fn read_spans_may_alias_one_another() {
    let left = ArgumentSpan::device_raw("left", 0x1000, 64, 4, Access::Read);
    let right = ArgumentSpan::device_raw("right", 0x1080, 64, 4, Access::Read);
    let audit = AliasAudit::admit_all(&[left, right]).expect("overlapping reads are lawful");
    assert_eq!(audit.len(), 2);
}

#[test]
fn a_write_span_may_alias_nothing_of_the_same_residency() {
    let read = ArgumentSpan::device_raw("read", 0x1000, 64, 4, Access::Read);
    let write = ArgumentSpan::device_raw("write", 0x1080, 64, 4, Access::Write);
    let refusal =
        AliasAudit::admit_all(&[read, write]).expect_err("a write may not overlap a read");
    assert_eq!(refusal.clause, PartitionClause::Aliasing);
    assert!(refusal.detail.contains("write"), "{}", refusal.detail);

    let first = ArgumentSpan::device_raw("first", 0x1000, 64, 4, Access::Write);
    let second = ArgumentSpan::device_raw("second", 0x10F0, 64, 4, Access::Write);
    assert_eq!(
        AliasAudit::admit_all(&[first, second])
            .expect_err("two writes may not overlap")
            .clause,
        PartitionClause::Aliasing
    );

    // Disjoint carvings of one backing allocation are lawful.
    let low = ArgumentSpan::device_raw("low", 0x1000, 64, 4, Access::Write);
    let high = ArgumentSpan::device_raw("high", 0x1100, 64, 4, Access::Write);
    AliasAudit::admit_all(&[low, high]).expect("disjoint carvings are lawful");
}

#[test]
fn a_zero_length_span_is_inert_in_the_audit() {
    let empty = ArgumentSpan::device_raw("empty", 0x1000, 0, 4, Access::Write);
    let write = ArgumentSpan::device_raw("write", 0x1000, 64, 4, Access::Write);
    AliasAudit::admit_all(&[empty, write]).expect("an empty span writes nothing");
}

#[test]
fn spans_of_different_residency_never_alias() {
    let device = ArgumentSpan::device_raw("device", 0x1000, 64, 4, Access::Write);
    let host_values = [0u32; 64];
    let mut host = ArgumentSpan::host("host", &host_values);
    host.address = 0x1000; // a private field, reachable only from inside this owner's module
    AliasAudit::admit_all(&[device, host]).expect("a device address is not a host address");
}

#[test]
fn a_launch_presenting_an_aliased_write_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded(
        "aliasing",
        64,
        vec![
            ArgumentRequirement::device("source", Access::Read, 4, Extent::Any),
            ArgumentRequirement::device("target", Access::Write, 4, Extent::Any),
        ],
    );
    let arguments = [
        ArgumentSpan::device_raw("source", 0x1000, 64, 4, Access::Read),
        ArgumentSpan::device_raw("target", 0x1040, 64, 4, Access::Write),
    ];
    let refusal = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect_err("the target overlaps the source");
    assert_eq!(refusal.clause, LaunchClause::ArgumentAliasing);
}

#[test]
fn a_partition_must_match_the_extent_of_the_span_it_is_bound_to() {
    // No device is needed: the mismatch is arithmetic and is checked before any driver call.
    let partition = DisjointPartition::uniform(64, 8, 8, 8).expect("proved");
    assert_eq!(partition.elements(), 64);
    let narrower = DisjointPartition::uniform(32, 4, 8, 8).expect("proved");
    assert_eq!(narrower.elements(), 32);
    assert_ne!(partition.elements(), narrower.elements());
}

// -------------------------------------------------------------------------------------------
// The device
// -------------------------------------------------------------------------------------------

/// Read every launch bound off the mounted card and prove a real entry's cover against it.  The
/// point of this test is that **no bound in it is authored**: each one comes from
/// `cuDeviceGetAttribute` or `cuFuncGetAttribute`, and the receipt defers nothing.
#[test]
#[ignore = "requires a CUDA device visible to the test process"]
fn the_launch_law_reads_every_bound_off_the_mounted_device() -> Result<()> {
    crate::cuda::init()?;
    let device = Device::get(0)?;
    let context = Context::create(&device)?;
    let module = crate::cuda::Module::load_ptx(crate::SOMA_PTX)?;
    let function = module.function(holonics_portable::wire::register::Entry::Scope.symbol())?;

    let limits = LaunchLimits::read(&device, &function)?;
    assert!(limits.max_grid().is_some());
    assert!(limits.max_block().is_some());
    assert!(limits.device_max_threads_per_block().is_some());
    assert!(limits.max_shared_bytes_per_block().is_some());
    assert!(limits.warp().is_some());
    assert!(limits.multiprocessors().is_some());
    eprintln!(
        "device={} · function block cap={} · device block cap={:?} · grid={:?} · block={:?} · shared/block={:?} · warp={:?}",
        device.name,
        limits.function_max_threads_per_block(),
        limits.device_max_threads_per_block(),
        limits.max_grid(),
        limits.max_block(),
        limits.max_shared_bytes_per_block(),
        limits.warp(),
    );

    let requirement = LaunchRequirement::guarded(
        holonics_portable::wire::register::Entry::Scope.symbol(),
        100_000,
        vec![ArgumentRequirement::device(
            "lanes",
            Access::Write,
            4,
            Extent::AtLeast(1),
        )],
    );
    let lanes = DeviceBuffer::<u32>::alloc_zeroed(100_000)?;
    let arguments = [ArgumentSpan::device("lanes", &lanes, Access::Write)];
    let lawful = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect("the covering launch is lawful on the mounted card");
    let receipt = lawful.receipt();
    assert!(receipt.deferred().is_empty(), "{receipt}");
    assert!(receipt.threads >= 100_000);
    assert!(receipt.guard_threads < receipt.block.x as u64);
    eprintln!("{receipt}");

    // The census path proves the same shape and defers exactly the three bounds a census omits.
    let census = device.launch_census()?;
    let census_limits = LaunchLimits::from_census(census, &function)?;
    let census_lawful = LawfulLaunch::cover(&requirement, &census_limits, &arguments)
        .expect("the census path is lawful too");
    assert_eq!(census_lawful.receipt().grid, receipt.grid);
    assert_eq!(census_lawful.receipt().block, receipt.block);
    assert!(census_lawful
        .receipt()
        .defers(LaunchClause::SharedWithinDevice));
    assert!(census_lawful
        .receipt()
        .defers(LaunchClause::BlockDimensionWithinDevice));

    drop(lanes);
    context.destroy()?;
    Ok(())
}

// -------------------------------------------------------------------------------------------
// D2 — the settle discipline
//
// These tests construct `PartitionedWrite` values, which nothing tested before: the review found
// the settle discipline entirely untested, so a `drop(in_flight)` that released the exclusive
// borrow while the kernel was still running would have passed every test in this file.
// -------------------------------------------------------------------------------------------

/// A `Settles` the tests can count.  The trait is sealed, so outside `cfg(test)` the only
/// implementors are `Stream` and `Context` and no caller can hollow out the guarantee with a
/// no-op.
#[derive(Debug, Default)]
pub(crate) struct RecordedSettle {
    waits: std::cell::Cell<usize>,
    fail: bool,
}

impl RecordedSettle {
    fn new() -> Self {
        Self::default()
    }

    fn failing() -> Self {
        Self {
            waits: std::cell::Cell::new(0),
            fail: true,
        }
    }

    pub(crate) fn record(&self) -> Result<()> {
        self.waits.set(self.waits.get() + 1);
        if self.fail {
            return Err(CudaError {
                code: -1,
                name: String::from("SYNTHETIC_SYNCHRONIZE_FAILURE"),
                message: String::from("the recorded apparatus refuses to settle"),
                context: "RecordedSettle::record",
            });
        }
        Ok(())
    }

    fn waits(&self) -> usize {
        self.waits.get()
    }
}

fn synthetic_partitioned_write() -> PartitionedWrite<'static, u32> {
    let span = DeviceWriteSpan::<u32>::synthetic(0x2000, 64);
    let partition = DisjointPartition::uniform(64, 8, 8, 8).expect("the partition is proved");
    PartitionedWrite::bind(span, partition).expect("the extents agree")
}

/// A launch scope waits **exactly once**, after the closure returns, and hands the closure the
/// proved address, extent and partition.  Nothing the closure can do shortens the wait, because
/// the closure is handed no value whose disposal ends the borrow.
#[test]
fn a_launch_scope_settles_after_the_closure_and_only_once() {
    let mut write = synthetic_partitioned_write();
    let settle = RecordedSettle::new();
    let seen = write
        .scope(&settle, |open| {
            // The kernel is "in flight" here: nothing has been waited on yet.
            assert_eq!(open.address(), 0x2000);
            assert_eq!(open.elements(), 64);
            assert_eq!(open.partition().regions(), 8);
            assert_eq!(open.argument("cells").access(), Access::Write);
            open.address()
        })
        .expect("the synthetic apparatus settles");
    assert_eq!(seen, 0x2000);
    assert_eq!(settle.waits(), 1, "the scope waits once, after the closure");
}

/// The synchronization's own failure reaches the caller rather than being swallowed.
#[test]
fn a_launch_scope_returns_the_apparatus_failure() {
    let mut write = synthetic_partitioned_write();
    let settle = RecordedSettle::failing();
    let refusal = write
        .scope(&settle, |_open| ())
        .expect_err("the apparatus refused to settle");
    assert_eq!(refusal.name, "SYNTHETIC_SYNCHRONIZE_FAILURE");
    assert_eq!(settle.waits(), 1);
}

/// **On an unwind the scope still waits**, from a guard living in the scope's own frame rather
/// than in the caller's, so a panicking enqueue cannot leave the kernel running against a span
/// whose borrow has been released.
#[test]
fn a_launch_scope_settles_on_unwind() {
    let settle = RecordedSettle::new();
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut write = synthetic_partitioned_write();
        let _ = write.scope(&settle, |_open| panic!("the enqueue failed"));
    }));
    assert!(outcome.is_err(), "the panic propagates");
    assert_eq!(
        settle.waits(),
        1,
        "the scope waited for the apparatus while unwinding"
    );
}

/// The escape hatch's weaker guarantee, stated and tested: `settle` waits and returns the span,
/// and merely dropping an `InFlightWrite` waits too.
#[test]
fn an_in_flight_write_settles_explicitly_and_on_drop() {
    let settle = RecordedSettle::new();
    let held = synthetic_partitioned_write()
        .in_flight(&settle)
        .settle()
        .expect("the synthetic apparatus settles");
    assert_eq!(held.partition().regions(), 8);
    assert_eq!(settle.waits(), 1);

    let dropping = RecordedSettle::new();
    drop(synthetic_partitioned_write().in_flight(&dropping));
    assert_eq!(
        dropping.waits(),
        1,
        "dropping an in-flight write synchronizes as a second line"
    );
}

/// A partition bound to a span of a different extent is a typed refusal, not a silent truncation.
#[test]
fn binding_a_partition_to_a_span_of_another_extent_is_refused() {
    let span = DeviceWriteSpan::<u32>::synthetic(0x2000, 64);
    let partition = DisjointPartition::uniform(32, 4, 8, 8).expect("proved");
    let refusal = PartitionedWrite::bind(span, partition).expect_err("the extents disagree");
    assert_eq!(refusal.clause, PartitionClause::SpanMismatch);
}

// -------------------------------------------------------------------------------------------
// D2 — the linear disjointness proof agrees with the quadratic reference
// -------------------------------------------------------------------------------------------

/// `verify_pairwise_disjoint` no longer compares every pair.  For the address-ordered forms the
/// adjacency check is a complete proof (`DisjointPartition.offsets_mono`), and for an injective
/// scatter a sort is; this test holds the two against each other on every fixture, including the
/// overlapping ones, so the linear argument is not taken on trust.
#[test]
fn the_linear_disjointness_proof_agrees_with_the_quadratic_reference() {
    let fixtures: Vec<DisjointPartition> = vec![
        DisjointPartition::uniform(64, 8, 8, 8).expect("proved"),
        DisjointPartition::uniform(64, 8, 8, 4).expect("proved"),
        DisjointPartition::uniform(1, 1, 1, 1).expect("proved"),
        DisjointPartition::from_offsets(64, vec![0, 0, 16, 16, 64]).expect("proved"),
        DisjointPartition::from_offsets(64, vec![0, 64]).expect("proved"),
        DisjointPartition::scatter(8, vec![7, 1, 3], ScatterLaw::Injective).expect("proved"),
        DisjointPartition::scatter(8, vec![1, 1, 3], ScatterLaw::Accumulated).expect("proved"),
    ];
    for partition in &fixtures {
        assert_eq!(
            partition.verify_pairwise_disjoint().is_ok(),
            partition.verify_pairwise_disjoint_quadratic().is_ok(),
            "the two proofs disagree on {partition:?}"
        );
        partition
            .verify_pairwise_disjoint()
            .expect("every fixture above is disjoint");
    }
}

// -------------------------------------------------------------------------------------------
// D1 — the declared access clause, distinct from aliasing
// -------------------------------------------------------------------------------------------

/// A span presented with the wrong access is `ArgumentAccess`, not `ArgumentAliasing`: the two are
/// different faults and were formerly reported under one clause name.
#[test]
fn a_misdeclared_access_is_its_own_clause() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded(
        "access",
        64,
        vec![ArgumentRequirement::device(
            "target",
            Access::Write,
            4,
            Extent::Any,
        )],
    );
    let arguments = [ArgumentSpan::device_raw("target", 0x1000, 64, 4, Access::Read)];
    let refusal =
        LawfulLaunch::cover(&requirement, &limits, &arguments).expect_err("the access disagrees");
    assert_eq!(refusal.clause, LaunchClause::ArgumentAccess);
    assert_eq!(LaunchClause::ArgumentAccess.name(), "argument-access");
    assert_ne!(refusal.clause, LaunchClause::ArgumentAliasing);
}

// -------------------------------------------------------------------------------------------
// D1 — a receipt's proof scope is a type, and declared scalars come out of the receipt
// -------------------------------------------------------------------------------------------

/// A completely proved receipt yields a `FullyProvedReceipt`; a receipt with a deferred device
/// clause cannot, so a consumer that needs the complete proof can ask for it in its signature.
#[test]
fn a_deferred_receipt_is_not_a_fully_proved_one() {
    let requirement = LaunchRequirement::guarded("scope", 1_000, one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 1_000)];

    let complete = LawfulLaunch::cover(&requirement, &synthetic_limits(), &arguments)
        .expect("lawful")
        .receipt()
        .clone();
    assert!(complete.is_fully_proved());
    let full = complete
        .clone()
        .fully_proved()
        .expect("nothing was deferred");
    assert_eq!(full.receipt().kernel, "scope");
    assert!(matches!(complete.proof_scope(), ProofScope::FullyProved(_)));

    // The same launch against evidence that carries no device bounds.
    let partial = LaunchLimits::synthetic(512, None, None, None, None, None);
    let deferred = LawfulLaunch::cover(&requirement, &partial, &arguments)
        .expect("lawful")
        .receipt()
        .clone();
    assert!(!deferred.is_fully_proved());
    assert!(deferred.clone().fully_proved().is_none());
    match deferred.proof_scope() {
        ProofScope::Deferred(receipt) => {
            assert!(receipt.deferred().contains(&LaunchClause::GridWithinDevice));
            assert!(!receipt.deferred().is_empty());
        }
        ProofScope::FullyProved(_) => panic!("the device clauses were deferred"),
    }
}

/// A scalar declared past the entry's buffer pairs is refused at proof time.
#[test]
fn a_scalar_declared_past_the_argument_population_is_refused() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("scalars", 64, one_argument_requirement())
        .with_scalars(vec![ScalarRequirement::at("axis", ScalarWidth::U32, 2)]);
    let arguments = [device_argument("cells", 0x1000, 64)];
    let refusal =
        LawfulLaunch::cover(&requirement, &limits, &arguments).expect_err("no second pair exists");
    assert_eq!(refusal.clause, LaunchClause::ScalarArguments);
    assert_eq!(LaunchClause::ScalarArguments.name(), "scalar-arguments");
}

/// A declared scalar is carried on the requirement and survives onto the proof, so the parameter
/// block the driver receives is generated rather than hand-assembled.
#[test]
fn a_declared_scalar_is_carried_by_the_requirement() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::guarded("scalars", 64, one_argument_requirement())
        .with_scalars(vec![
            ScalarRequirement::at("axis", ScalarWidth::U32, 1),
            ScalarRequirement::trailing("count", ScalarWidth::U64, 1),
        ]);
    assert_eq!(requirement.scalars.len(), 2);
    assert_eq!(requirement.scalars[0].width, ScalarWidth::U32);
    assert_eq!(requirement.scalars[0].width.name(), "u32");
    assert_eq!(requirement.scalars[1].after_arguments, 1);
    let arguments = [device_argument("cells", 0x1000, 64)];
    let proof = LawfulLaunch::cover(&requirement, &limits, &arguments)
        .expect("a scalar after the single pair is lawful");
    assert_eq!(proof.receipt().kernel, "scalars");
}

/// `Coverage::Undeclared` is now reachable only by a caller who *declares* it — the launcher
/// mouths no longer fall into it silently. It still proves every other clause and names the
/// coverage clause as deferred, so a receipt says exactly what it did and did not establish.
#[test]
fn a_declared_undeclared_coverage_defers_only_its_own_clause() {
    let limits = synthetic_limits();
    let requirement = LaunchRequirement::undeclared("undeclared", one_argument_requirement());
    let arguments = [device_argument("cells", 0x1000, 64)];
    let shape = LaunchShape::linear(4, 64);
    let receipt = LawfulLaunch::prove(&requirement, &limits, shape, &arguments)
        .expect("every clause but coverage is provable without an extent")
        .receipt()
        .clone();
    assert!(receipt.defers(LaunchClause::CoverageGuarded));
    assert!(receipt.defers(LaunchClause::PositiveExtent));
    assert!(receipt.proves(LaunchClause::ArgumentAliasing));
    assert!(receipt.proves(LaunchClause::ArgumentAccess));
    assert!(receipt.proves(LaunchClause::GridWithinDevice));
    assert!(!receipt.is_fully_proved());
    // And a shape cannot be derived from an extent that was never declared.
    let refusal = requirement
        .cover_with(&limits)
        .expect_err("there is no extent to cover");
    assert_eq!(refusal.clause, LaunchClause::PositiveExtent);
}
