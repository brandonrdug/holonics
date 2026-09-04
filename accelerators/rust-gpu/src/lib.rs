#![cfg_attr(target_arch = "spirv", no_std)]
//! THE FELT-SERIES CARD — M4's first-person lineage ⊕ configuration legs (`FORMULA §XXVIII`).
//!
//! `scope_felt` carries one raw-light lineage into one disjoint OWN region and whole carrier. Once
//! every world cursor reaches that light's true end, the ratified light-end product follows:
//!
//! 1. `link_grain` — standing ⊕ every OWN form declare the whole-Rung grain;
//! 2. `link_sum` — every contribution re-bases once and atomically adds in the exact wide hand;
//! 3. `link_finish` — each touched place performs the single final re-base while the whole final
//!    region folds into its addressed topology read.
//!
//! Dispatch boundaries are the two passes of ONE resolving operation, never lineage time. No CAS,
//! retry, fixed lane fold, shared mid-light visibility, flow word, digit, or scheduled audit exists.

use spirv_std::arch::{atomic_i_add, atomic_load, atomic_store, atomic_u_max, IndexUnchecked};
use spirv_std::glam::UVec3;
use spirv_std::memory::{Scope, Semantics};
use spirv_std::spirv;

// ONE MOUTH — the same types and scalar fold primitives the cpu compiles.
#[path = "../../body/src/arrow.rs"]
mod arrow;
#[path = "../../body/src/boundary.rs"]
mod boundary;
#[path = "../../body/src/carriage.rs"]
mod carriage;
#[path = "../../body/src/chart.rs"]
mod chart;
#[path = "../../body/src/channel.rs"]
mod channel;
#[path = "../../body/src/geom.rs"]
mod geom;
#[path = "../../body/src/law.rs"]
mod law;
#[path = "../../body/src/manifold.rs"]
mod manifold;
#[path = "../../body/src/medium.rs"]
mod medium;
#[path = "../../body/src/num.rs"]
mod num;
#[path = "../../body/src/place.rs"]
mod place;
#[path = "../../body/src/register.rs"]
mod register;
#[path = "../../body/src/seam.rs"]
mod seam;
#[path = "../../body/src/soul.rs"]
mod soul;

use medium::{RegionalForm, FORM_WORDS};

const SCOPE: u32 = Scope::QueueFamily as u32;
const SEM: u32 = Semantics::NONE.bits();

struct SpirvWordSeam;

// Each scope invocation receives carved, disjoint mutable ranges before entering the shared
// carriage law. QueueFamily/NONE is only the SPIR-V spelling; the single writer is determinism.
unsafe impl carriage::WordSeam for SpirvWordSeam {
    #[inline(always)]
    unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
        *words.index_unchecked(at)
    }

    #[inline(always)]
    unsafe fn store_u32_unchecked(words: &mut [u32], at: usize, value: u32) {
        atomic_store::<u32, SCOPE, SEM>(words.index_unchecked_mut(at), value);
    }
}

#[derive(Clone, Copy)]
struct DenseRanges {
    lane_at: usize,
    own: carriage::WordSpan,
    carrier: carriage::WordSpan,
    count_at: usize,
}

/// Scalar-only ABI proof kept out of the pointer-heavy entry. One failure returns before the body
/// can mutate, without structurally nesting the whole lineage stroke beneath every product.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn dense_ranges(
    lane: usize,
    lane_count: usize,
    cells: usize,
    row_words: usize,
    lanes_len: usize,
    counts_len: usize,
) -> Option<DenseRanges> {
    if lane >= lane_count || cells == 0 || row_words < manifold::CARRIER_HEADER_WORDS {
        return None;
    }
    let lane_at = carriage::checked_extent_mul(lane, 6)?;
    let lane_end = carriage::checked_extent_add(lane_at, 6)?;
    let own_words = carriage::checked_extent_mul(cells, FORM_WORDS)?;
    let own_base = carriage::checked_extent_mul(lane, own_words)?;
    let _own_end = carriage::checked_extent_add(own_base, own_words)?;
    let row_base = carriage::checked_extent_mul(lane, row_words)?;
    let _row_end = carriage::checked_extent_add(row_base, row_words)?;
    let count_at = carriage::checked_extent_mul(lane, 4)?;
    let count_end = carriage::checked_extent_add(count_at, 4)?;
    if lane_end > lanes_len || count_end > counts_len {
        return None;
    }
    Some(DenseRanges {
        lane_at,
        own: carriage::WordSpan::new(own_base, own_words),
        carrier: carriage::WordSpan::new(row_base, row_words),
        count_at,
    })
}

#[derive(Clone, Copy)]
struct FoundedHeader {
    lane_at: usize,
    carrier: carriage::WordSpan,
    count_at: usize,
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn founded_header(
    lane: usize,
    lane_count: usize,
    cells: usize,
    row_words: usize,
    lanes_len: usize,
    counts_len: usize,
) -> Option<FoundedHeader> {
    if lane >= lane_count || cells == 0 || row_words < manifold::CARRIER_HEADER_WORDS {
        return None;
    }
    let lane_at = carriage::checked_extent_mul(lane, 8)?;
    let lane_end = carriage::checked_extent_add(lane_at, 8)?;
    let row_base = carriage::checked_extent_mul(lane, row_words)?;
    let _row_end = carriage::checked_extent_add(row_base, row_words)?;
    let count_at = carriage::checked_extent_mul(lane, 4)?;
    let count_end = carriage::checked_extent_add(count_at, 4)?;
    if lane_end > lanes_len || count_end > counts_len {
        return None;
    }
    Some(FoundedHeader {
        lane_at,
        carrier: carriage::WordSpan::new(row_base, row_words),
        count_at,
    })
}

#[derive(Clone, Copy)]
struct FoundedRanges {
    own_axis: usize,
    own_cells: usize,
    own: carriage::WordSpan,
    radiation: carriage::WordSpan,
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn founded_ranges(
    own_cell_base: usize,
    own_axis: usize,
    offset: usize,
    count: usize,
    radiation_stride: usize,
) -> Option<FoundedRanges> {
    if own_axis == 0 || own_axis & (own_axis - 1) != 0 {
        return None;
    }
    let own_cells = carriage::checked_extent_mul(own_axis, own_axis)?;
    let own_base = carriage::checked_extent_mul(own_cell_base, manifold::OWN_CELL_WORDS)?;
    let own_words = carriage::checked_extent_mul(own_cells, manifold::OWN_CELL_WORDS)?;
    let _own_end = carriage::checked_extent_add(own_base, own_words)?;
    let radiation = if radiation_stride == manifold::RADIATION_WORDS {
        let base = carriage::checked_extent_mul(offset, radiation_stride)?;
        let words = carriage::checked_extent_mul(count, radiation_stride)?;
        let _end = carriage::checked_extent_add(base, words)?;
        carriage::WordSpan::new(base, words)
    } else {
        carriage::WordSpan::empty()
    };
    Some(FoundedRanges {
        own_axis,
        own_cells,
        own: carriage::WordSpan::new(own_base, own_words),
        radiation,
    })
}

/// M4b — ONE THREAD, ONE DENSE LINEAGE. The shell decodes the storage ABI, then carves
/// exactly one invocation-owned OWN plane and carrier/K row. Every decision that advances the
/// worldline belongs to body::carriage; count publication remains this substrate's boundary.
/// Params are `[axis, cells, lanes, carrier_row_words, stroke_atoms, drive, x_thread_stride,
/// interior_installment]`;
/// lane rows are
/// `[byte_offset, byte_count, seed_prev, seed_cur, worldline_base_lo, worldline_base_hi]`.
#[spirv(compute(threads(64)))]
pub fn scope_felt(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] carriers: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] bytes: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] lanes: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] counts: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 6)] params: &[u32],
) {
    if params.len() < 8 || params[6] == 0 {
        return;
    }
    let lane = id.x as u64 + id.y as u64 * params[6] as u64;
    if lane >= params[2] as u64 {
        return;
    }
    let lane = lane as usize;
    let lane_count = params[2] as usize;
    let cells = params[1] as usize;
    let row_words = params[3] as usize;
    let Some(ranges) = dense_ranges(
        lane,
        lane_count,
        cells,
        row_words,
        lanes.len(),
        counts.len(),
    ) else {
        return;
    };
    let lane_at = ranges.lane_at;
    let offset = lanes[lane_at] as usize;
    let count = lanes[lane_at + 1] as usize;
    let worldline_base =
        lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let stroke = carriage::LineageStroke::dense(
        params[0] as i64,
        cells,
        offset,
        count,
        lanes[lane_at + 2],
        lanes[lane_at + 3],
        worldline_base,
        params[4] as usize,
        params[5],
    )
    .with_interior_installment(params[7] as usize);

    // SPIR-V cannot materialize dynamic Rust subslices. These checked spans are the invocation's
    // complete single-writer ranges; no local carriage coordinate can name a sibling lane.
    let Some(result) = carriage::carry_dense_stroke_trusted::<SpirvWordSeam>(
        standing,
        owns,
        ranges.own,
        carriers,
        ranges.carrier,
        bytes,
        stroke,
    ) else {
        return;
    };

    // The four-word count aperture is likewise single-writer; counts remain a shell read.
    let count_at = ranges.count_at;
    unsafe {
        atomic_i_add::<u64, SCOPE, SEM>(&mut counts[count_at], result.terms.ride);
        atomic_i_add::<u64, SCOPE, SEM>(
            &mut counts[count_at + 1],
            result.terms.found_this,
        );
        atomic_i_add::<u64, SCOPE, SEM>(
            &mut counts[count_at + 2],
            result.terms.found_that,
        );
        atomic_i_add::<u64, SCOPE, SEM>(&mut counts[count_at + 3], result.terms.dark);
    }
}

/// M5 — ONE THREAD, ONE FOUNDED LINEAGE. The shell carves one reservation-sized OWN
/// chart, one complete carrier/K row, and this lineage's available radiation aperture before the
/// same body::carriage stroke runs. Standing and raw light remain shared read-only.
/// Params add `radiation_stride, x_thread_stride, interior_installment`; lane rows add
/// `[own_cell_offset, own_axis]`.
#[spirv(compute(threads(64)))]
pub fn scope_founded(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] carriers: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] bytes: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] lanes: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] counts: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 6)] params: &[u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 7)] radiation: &mut [u32],
) {
    if params.len() < 9 || params[7] == 0 {
        return;
    }
    let lane = id.x as u64 + id.y as u64 * params[7] as u64;
    if lane >= params[2] as u64 {
        return;
    }
    let lane = lane as usize;
    let lane_count = params[2] as usize;
    let cells = params[1] as usize;
    let row_words = params[3] as usize;
    let Some(header) = founded_header(
        lane,
        lane_count,
        cells,
        row_words,
        lanes.len(),
        counts.len(),
    ) else {
        return;
    };
    let lane_at = header.lane_at;
    let offset = lanes[lane_at] as usize;
    let count = lanes[lane_at + 1] as usize;
    let own_cell_base = lanes[lane_at + 6] as usize;
    let own_axis = lanes[lane_at + 7] as usize;
    let worldline_base =
        lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let radiation_stride = params[6] as usize;
    let Some(ranges) = founded_ranges(
        own_cell_base,
        own_axis,
        offset,
        count,
        radiation_stride,
    ) else {
        return;
    };
    let stroke = carriage::LineageStroke::founded(
        params[0] as i64,
        ranges.own_axis as i64,
        cells,
        ranges.own_cells,
        offset,
        count,
        lanes[lane_at + 2],
        lanes[lane_at + 3],
        worldline_base,
        params[4] as usize,
        params[5],
        radiation_stride,
    )
    .with_interior_installment(params[8] as usize);

    // The three checked spans are invocation-exclusive. Relaxed atomic spelling cannot choose an
    // outcome because no sibling invocation can name any of these local coordinates.
    let Some(result) = carriage::carry_founded_stroke_trusted::<SpirvWordSeam>(
        standing,
        owns,
        ranges.own,
        carriers,
        header.carrier,
        bytes,
        radiation,
        ranges.radiation,
        stroke,
    ) else {
        return;
    };

    let count_at = header.count_at;
    unsafe {
        atomic_i_add::<u64, SCOPE, SEM>(&mut counts[count_at], result.terms.ride);
        atomic_i_add::<u64, SCOPE, SEM>(
            &mut counts[count_at + 1],
            result.terms.found_this,
        );
        atomic_i_add::<u64, SCOPE, SEM>(
            &mut counts[count_at + 2],
            result.terms.found_that,
        );
        atomic_i_add::<u64, SCOPE, SEM>(&mut counts[count_at + 3], result.terms.dark);
    }
}

/// Flatten a two-dimensional dispatch. Params: `[cells, lanes, xstride]`; there are `lanes + 1`
/// sources because pre-light standing participates once beside every lane-local OWN form.
#[inline(always)]
fn source_and_cell(id: UVec3, params: &[u32]) -> Option<(usize, usize, usize)> {
    if params.len() < 3 {
        return None;
    }
    let cells = params[0] as usize;
    if cells == 0 {
        return None;
    }
    let linear = id.x as usize + id.y as usize * params[2] as usize;
    let source = linear / cells;
    if source > params[1] as usize {
        return None;
    }
    Some((source, linear - source * cells, cells))
}

#[inline(always)]
fn read_standing(standing: &[u32], cell: usize) -> RegionalForm {
    let at = cell * FORM_WORDS;
    if at + FORM_WORDS <= standing.len() {
        unsafe { RegionalForm::unpack_unchecked_with::<SpirvWordSeam>(standing, at) }
    } else {
        RegionalForm::UNBORN
    }
}

#[inline(always)]
fn read_form(standing: &[u32], owns: &[u32], source: usize, cell: usize, cells: usize) -> RegionalForm {
    if source == 0 {
        read_standing(standing, cell)
    } else {
        let at = ((source - 1) * cells + cell) * FORM_WORDS;
        if at + FORM_WORDS <= owns.len() {
            unsafe { RegionalForm::unpack_unchecked_with::<SpirvWordSeam>(owns, at) }
        } else {
            RegionalForm::UNBORN
        }
    }
}

#[inline(always)]
fn store_form(standing: &mut [u32], cell: usize, form: RegionalForm) {
    let at = cell * FORM_WORDS;
    if at + FORM_WORDS > standing.len() {
        return;
    }
    let mut i = 0usize;
    while i < FORM_WORDS {
        unsafe { atomic_store::<u32, SCOPE, SEM>(&mut standing[at + i], form.packed_word(i)) };
        i += 1;
    }
}

#[inline(always)]
fn read_founded_form(standing: &[u32], owns: &[u32], own: bool, at: usize) -> RegionalForm {
    if own && at + FORM_WORDS <= owns.len() {
        unsafe { RegionalForm::unpack_unchecked_with::<SpirvWordSeam>(owns, at) }
    } else if !own && at + FORM_WORDS <= standing.len() {
        unsafe { RegionalForm::unpack_unchecked_with::<SpirvWordSeam>(standing, at) }
    } else {
        RegionalForm::UNBORN
    }
}

/// M5 PASS 1 — variable lineage charts declare one receiving grain by re-grounding each live
/// cell's founding construction. Traversal order has no face: only atomic max and touch stand.
#[spirv(compute(threads(64)))]
pub fn link_founded_grain(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] cog_grains: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] arm_grains: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] touched: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] params: &[u32],
) {
    if params.len() < 4 || params[0] == 0 || params[3] == 0 {
        return;
    }
    let linear = id.x as usize + id.y as usize * params[2] as usize;
    let standing_cells = params[0] as usize;
    let own = linear >= standing_cells;
    let (at, cell) = if !own {
        (linear * FORM_WORDS, linear)
    } else {
        let own_cell = linear - standing_cells;
        if own_cell >= params[1] as usize {
            return;
        }
        let own_at = own_cell * manifold::OWN_CELL_WORDS;
        if own_at + manifold::OWN_CELL_WORDS > owns.len() || owns[own_at + manifold::OWN_CELL_LIVE] == 0 {
            return;
        }
        let position = manifold::own_cell_position(owns, own_at);
        let target = place::ground(position, params[3] as i64) as usize;
        if target >= standing_cells {
            return;
        }
        (own_at + manifold::OWN_CELL_FORM, target)
    };
    let form = read_founded_form(standing, owns, own, at);
    if own && cell < touched.len() {
        unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut touched[cell], 1) };
    }
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() {
        if same.mag != 0 {
            unsafe { atomic_u_max::<u64, SCOPE, SEM>(&mut cog_grains[base], medium::grain_key(same.rank)) };
        }
        if other.mag != 0 {
            unsafe { atomic_u_max::<u64, SCOPE, SEM>(&mut cog_grains[base + 1], medium::grain_key(other.rank)) };
        }
    }
    if base + 1 < arm_grains.len() {
        if this_way.mag != 0 {
            unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut arm_grains[base], this_way.rank as u32 + 1) };
        }
        if that_way.mag != 0 {
            unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut arm_grains[base + 1], that_way.rank as u32 + 1) };
        }
    }
}

/// M5 PASS 2 — the same construction traversal contributes once at the already-declared receiving
/// grain. Integer atomic addition is the exact wide hand; no lane order or stored address enters.
#[spirv(compute(threads(64)))]
pub fn link_founded_sum(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] cog_grains: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] arm_grains: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] cog_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] arm_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 6)] touched: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 7)] params: &[u32],
) {
    if params.len() < 4 || params[0] == 0 || params[3] == 0 {
        return;
    }
    let linear = id.x as usize + id.y as usize * params[2] as usize;
    let standing_cells = params[0] as usize;
    let own = linear >= standing_cells;
    let (at, cell) = if !own {
        (linear * FORM_WORDS, linear)
    } else {
        let own_cell = linear - standing_cells;
        if own_cell >= params[1] as usize {
            return;
        }
        let own_at = own_cell * manifold::OWN_CELL_WORDS;
        if own_at + manifold::OWN_CELL_WORDS > owns.len() || owns[own_at + manifold::OWN_CELL_LIVE] == 0 {
            return;
        }
        let position = manifold::own_cell_position(owns, own_at);
        let target = place::ground(position, params[3] as i64) as usize;
        if target >= standing_cells {
            return;
        }
        (own_at + manifold::OWN_CELL_FORM, target)
    };
    if cell >= touched.len() || unsafe { atomic_load::<u32, SCOPE, SEM>(&touched[cell]) } == 0 {
        return;
    }
    let form = read_founded_form(standing, owns, own, at);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() && base + 1 < cog_sums.len() {
        let same_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base]) };
        let other_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base + 1]) };
        if same_key != 0 {
            unsafe {
                atomic_i_add::<u64, SCOPE, SEM>(
                    &mut cog_sums[base],
                    medium::cog_at_grain(same, medium::grain_from_key(same_key)),
                )
            };
        }
        if other_key != 0 {
            unsafe {
                atomic_i_add::<u64, SCOPE, SEM>(
                    &mut cog_sums[base + 1],
                    medium::cog_at_grain(other, medium::grain_from_key(other_key)),
                )
            };
        }
    }
    if base + 1 < arm_grains.len() && base + 1 < arm_sums.len() {
        let this_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base]) };
        let that_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base + 1]) };
        if this_grain != 0 {
            unsafe {
                atomic_i_add::<u64, SCOPE, SEM>(
                    &mut arm_sums[base],
                    medium::arm_at_grain(this_way, this_grain as i32 - 1),
                )
            };
        }
        if that_grain != 0 {
            unsafe {
                atomic_i_add::<u64, SCOPE, SEM>(
                    &mut arm_sums[base + 1],
                    medium::arm_at_grain(that_way, that_grain as i32 - 1),
                )
            };
        }
    }
}

/// PASS 1 — THE GRAIN DECLARES ITSELF. `cog_grains` is two whole-Rung keys per place;
/// `arm_grains` stores `Rung.rank + 1` (zero means no arm contribution). OWN alone marks touch:
/// standing by itself must remain byte-identical at an untouched place.
#[spirv(compute(threads(64)))]
pub fn link_grain(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] cog_grains: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] arm_grains: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] touched: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] params: &[u32],
) {
    let Some((source, cell, cells)) = source_and_cell(id, params) else {
        return;
    };
    let form = read_form(standing, owns, source, cell, cells);
    if source != 0 && form != RegionalForm::UNBORN && cell < touched.len() {
        unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut touched[cell], 1) };
    }
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let cbase = cell * 2;
    if cbase + 1 < cog_grains.len() {
        if same.mag != 0 {
            unsafe { atomic_u_max::<u64, SCOPE, SEM>(&mut cog_grains[cbase], medium::grain_key(same.rank)) };
        }
        if other.mag != 0 {
            unsafe { atomic_u_max::<u64, SCOPE, SEM>(&mut cog_grains[cbase + 1], medium::grain_key(other.rank)) };
        }
    }
    if cbase + 1 < arm_grains.len() {
        if this_way.mag != 0 {
            unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut arm_grains[cbase], this_way.rank as u32 + 1) };
        }
        if that_way.mag != 0 {
            unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut arm_grains[cbase + 1], that_way.rank as u32 + 1) };
        }
    }
}

/// PASS 2 — THE EXACT SUM AT THE GRAIN. The atomics are associative integer addition after every
/// source has re-based exactly once; hardware order therefore has no physical face.
#[spirv(compute(threads(64)))]
pub fn link_sum(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] cog_grains: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] arm_grains: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] cog_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] arm_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 6)] touched: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 7)] params: &[u32],
) {
    let Some((source, cell, cells)) = source_and_cell(id, params) else {
        return;
    };
    if cell >= touched.len() || unsafe { atomic_load::<u32, SCOPE, SEM>(&touched[cell]) } == 0 {
        return;
    }
    let form = read_form(standing, owns, source, cell, cells);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() && base + 1 < cog_sums.len() {
        let same_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base]) };
        let other_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base + 1]) };
        if same_key != 0 {
            let contribution = medium::cog_at_grain(same, medium::grain_from_key(same_key));
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut cog_sums[base], contribution) };
        }
        if other_key != 0 {
            let contribution = medium::cog_at_grain(other, medium::grain_from_key(other_key));
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut cog_sums[base + 1], contribution) };
        }
    }
    if base + 1 < arm_grains.len() && base + 1 < arm_sums.len() {
        let this_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base]) };
        let that_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base + 1]) };
        if this_grain != 0 {
            let contribution = medium::arm_at_grain(this_way, (this_grain - 1) as i32);
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut arm_sums[base], contribution) };
        }
        if that_grain != 0 {
            let contribution = medium::arm_at_grain(that_way, (that_grain - 1) as i32);
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut arm_sums[base + 1], contribution) };
        }
    }
}

/// THE ONE FINAL RE-BASE. `reads` is the on-card M2c projection:
/// occupied ⊕ resultant ⊕ fiber ⊕ two-armed place counts. Exact addressed forms remain in standing.
#[spirv(compute(threads(64)))]
pub fn link_finish(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] cog_grains: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] arm_grains: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] cog_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 4)] arm_sums: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 5)] touched: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 6)] reads: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 7)] params: &[u32],
) {
    if params.len() < 3 {
        return;
    }
    let cell = id.x as usize + id.y as usize * params[2] as usize;
    if cell >= params[0] as usize || cell >= touched.len() {
        return;
    }
    let was_touched = unsafe { atomic_load::<u32, SCOPE, SEM>(&touched[cell]) } != 0;
    let base = cell * 2;
    let form = if !was_touched {
        read_standing(standing, cell)
    } else {
        if base + 1 >= cog_grains.len()
            || base + 1 >= arm_grains.len()
            || base + 1 >= cog_sums.len()
            || base + 1 >= arm_sums.len()
        {
            return;
        }
        let same_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base]) };
        let other_key = unsafe { atomic_load::<u64, SCOPE, SEM>(&cog_grains[base + 1]) };
        let this_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base]) };
        let that_grain = unsafe { atomic_load::<u32, SCOPE, SEM>(&arm_grains[base + 1]) };
        let same = if same_key == 0 {
            num::Cog::lit(0)
        } else {
            medium::cog_from_sum(medium::grain_from_key(same_key), unsafe {
                atomic_load::<u64, SCOPE, SEM>(&cog_sums[base])
            })
        };
        let other = if other_key == 0 {
            num::Cog::lit(0)
        } else {
            medium::cog_from_sum(medium::grain_from_key(other_key), unsafe {
                atomic_load::<u64, SCOPE, SEM>(&cog_sums[base + 1])
            })
        };
        let this_way = if this_grain == 0 {
            num::Rung::ZERO
        } else {
            medium::arm_from_sum((this_grain - 1) as i32, unsafe {
                atomic_load::<u64, SCOPE, SEM>(&arm_sums[base])
            })
        };
        let that_way = if that_grain == 0 {
            num::Rung::ZERO
        } else {
            medium::arm_from_sum((that_grain - 1) as i32, unsafe {
                atomic_load::<u64, SCOPE, SEM>(&arm_sums[base + 1])
            })
        };
        let resolved = RegionalForm::from_components(same, other, this_way, that_way).occupy();
        store_form(standing, cell, resolved);
        resolved
    };

    if reads.len() >= 4 && form != RegionalForm::UNBORN {
        let (same, other) = form.resultant();
        let (this_way, that_way) = form.fiber();
        unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut reads[0], 1) };
        if same.mag != 0 || other.mag != 0 {
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut reads[1], 1) };
        }
        if this_way.mag != 0 || that_way.mag != 0 {
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut reads[2], 1) };
        }
        if this_way.mag != 0 && that_way.mag != 0 {
            unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut reads[3], 1) };
        }
    }
}

/// §XXXII-b · PRE-INTEGRATION CAST. Every live lineage-local construction declares its grip in
/// the candidate receiving gauge. The bit is presence only; all form arithmetic remains behind the
/// later configuration fold. Atomic max makes coincident casts one co-present arrival without lane
/// order, a map, a sort, or a search.
#[spirv(compute(threads(64)))]
pub fn chart_mark(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] owns: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] marks: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] params: &[u32],
) {
    if params.len() < 3 || params[1] == 0 {
        return;
    }
    let own_cell = id.x as usize + id.y as usize * params[2] as usize;
    if own_cell >= params[0] as usize {
        return;
    }
    let at = own_cell * manifold::OWN_CELL_WORDS;
    if at + manifold::OWN_CELL_WORDS > owns.len() || owns[at + manifold::OWN_CELL_LIVE] == 0 {
        return;
    }
    let position = manifold::own_cell_position(owns, at);
    let grip = place::ground(position, params[1] as i64) as usize;
    if grip < marks.len() {
        unsafe { atomic_u_max::<u32, SCOPE, SEM>(&mut marks[grip], 1) };
    }
}

/// §XXXII-b · THE CHART'S OWN REGISTER. One thread stands at each distinct arriving grip. A grip
/// already occupied by zero-extended standing is residence, not arrival, and contributes nothing.
/// Every genuinely new grip performs one unit increment; the increment's returned BEFORE face and
/// its AFTER face declare whether the hand received a carry. There is no occupancy comparison.
#[spirv(compute(threads(64)))]
pub fn chart_count(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] marks: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] chart_register: &mut [u64],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 3)] params: &[u32],
) {
    if params.len() < 4 || chart_register.len() < 2 || params[0] == 0 || params[1] == 0 {
        return;
    }
    let grip = id.x as usize + id.y as usize * params[3] as usize;
    if grip >= params[2] as usize || grip >= marks.len() || marks[grip] == 0 {
        return;
    }

    let standing_occupies =
        match chart::zero_extended_source(grip as u32, params[0], params[1]) {
            Some(old_grip) => read_standing(standing, old_grip as usize).occupied(),
            None => false,
        };
    if standing_occupies {
        return;
    }

    let before = unsafe { atomic_i_add::<u64, SCOPE, SEM>(&mut chart_register[0], 1) };
    let after = before.wrapping_add(1);
    if chart::carried_into_hand(before, after, params[1]) {
        unsafe { atomic_store::<u64, SCOPE, SEM>(&mut chart_register[1], 1) };
    }
}

/// §XXXII-b · ZERO'S OWN RECAST. The chart digit has already been forced. Each occupied old grip
/// writes its unchanged form at `(x,y) -> (2^r x, 2^r y)` in the wider gauge. The target is unique,
/// so merged history stays merged and no founder or content-derived address can enter.
#[spirv(compute(threads(64)))]
pub fn chart_recast(
    #[spirv(global_invocation_id)] id: UVec3,
    #[spirv(storage_buffer, descriptor_set = 0, binding = 0)] old_standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 1)] new_standing: &mut [u32],
    #[spirv(storage_buffer, descriptor_set = 0, binding = 2)] params: &[u32],
) {
    if params.len() < 4 || params[0] == 0 || params[1] == 0 {
        return;
    }
    let old_grip = id.x as usize + id.y as usize * params[3] as usize;
    if old_grip >= params[2] as usize {
        return;
    }
    let form = read_standing(old_standing, old_grip);
    if !form.occupied() {
        return;
    }
    let new_grip = chart::zero_extend_grip(old_grip as u32, params[0], params[1]) as usize;
    store_form(new_standing, new_grip, form);
}
