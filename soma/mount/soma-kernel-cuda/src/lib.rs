//! Record: research/records/2026-08-12_THE_RECURRENT_LAW_CROSSES_THE_CORPUS_DEPARTURE_THE_UNSEEN_SECTION_RIDES_ITS_DEPOSIT.md
//! THE CONFIGURATION FOLD — the CUDA/PTX port of the M4a-accepted entry family
//! (`FORMULA §XXVIII`): `link_grain` · `link_sum` · `link_finish`. The light-end product of one
//! configuration of co-present lineages, folded ONCE per touched place.
//!
//!   1. `link_grain`  — standing ⊕ every OWN form declare the whole-Rung receiving grain (atomic max);
//!   2. `link_sum`    — every contribution re-bases once and atomically adds in the exact wide hand;
//!   3. `link_finish` — each touched place performs the ONE final re-base and folds the region into
//!                      its addressed topology read (occupied ⊕ resultant ⊕ fiber ⊕ two-armed).
//!
//! Beside it, the M5 FOUNDED-CELL fold (`link_founded_grain` · `link_founded_sum`, folded by the same
//! `link_finish`), the CUDA-only registered receiving fold (`link_register_grain` ·
//! `link_register_sum` · `link_register_finish`), and the §XXXII-b CHART family (`chart_mark` ·
//! `chart_register_mark` · `chart_count` · `chart_recast`): the founded and registered passes
//! re-ground each live reservation-sized OWN cell's founding construction at the receiving grain
//! (`place::ground`), and the chart passes cast into the candidate gauge, tally the occupancy
//! register's OWN carry event, and zero-extend the standing form into the widened chart.
//! The scope family (`scope_felt` / `scope_founded` / CUDA-only `scope_register`) compiles here.
//! The earlier port was blocked while the lineage law lived kernel-side with no `body` mouth; Route A
//! (commit a778567d) relocated the whole lineage stroke into `body::carriage` behind the `WordSeam`
//! trait, so the ONE MOUTH now exists: the trusted device carriage and checked cpu-reference
//! carriage compile the SAME interior stroke. Only the entry SHELLS — span
//! carving ⊕ guards ⊕ `(ptr,len)` reconstruction — are re-expressed here. `body::seam::SliceWordSeam`
//! (the ordinary Rust slice realization) compiles for nvptx, and each lane's OWN/carrier spans are
//! invocation-exclusive (single-writer), so its plain scalar store is the faithful mirror of the
//! SPIR-V atomic-store seam; correctness comes from the span's single writer, never atomic arbitration.
//!
//! ONE MOUTH: this crate DEPENDS ON `body` (no_std, zero deps), so `RegionalForm`, `medium::*`,
//! `manifold::*`, `place::*`, `chart::*`, and `num::*` are the SAME CODE the SPIR-V card and the cpu
//! reference compile. Only the entry SHELLS are re-expressed here — global invocation indexing
//! through `%ctaid/%ntid/%tid` in place of spirv-std's `GlobalInvocationId`, and `core::sync::atomic`
//! in place of spirv-std's atomic intrinsics. The SPIR-V entries use NO workgroup barrier (pure
//! grid-wide `atomic_u_max` / `atomic_i_add` / `atomic_load` / `atomic_store`), so none is introduced
//! here: the fold stays order-free by construction — the clipped field lawfully drops order, and
//! integer atomic addition is associative, so hardware order has no physical face. No CAS, retry,
//! fixed lane fold, sort, shared mid-light visibility, flow word, digit, or scheduled audit exists.
//!
//! The shared entry buffer contracts (word layouts, pointer arithmetic, guards) mirror the SPIR-V
//! entries exactly. `scope_register` is CUDA-only while its production continuation remains under
//! construction. PTX passes raw device pointers, so each `&mut [_]` argument arrives as a
//! `(ptr, len)` pair reconstructed with `from_raw_parts_mut` before the identical body.
#![no_std]
#![feature(abi_ptx, link_llvm_intrinsics, stdarch_nvptx)]

use core::arch::nvptx;
use core::slice;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

use body::arrow::Arrow;
use body::carriage::{
    self, carry_dense_stroke_trusted, carry_founded_stroke_trusted,
    carry_register_stroke_trusted_with_completion,
    carry_register_stroke_trusted_with_completion_surface, form_register_contact, LineageStroke,
    RegisterContactSnapshot, RegisterContactSurface, RegisterStrokeStatus, WordSpan,
};
use body::chart;
use body::manifold::{
    directed_event_contact_over_standing, node_packed_word, own_cell_position,
    packed_node_is_canonical, unpack_node, CarrierGrowth, CarrierStorage, ErosBody, EventEmanation,
    EventIncidence, Face, LiveBodyHeader, Node, SparseOwnCell, SparseOwnStorage, StandingQuery,
    CARRIER_HEADER_WORDS, ENCLOSURE_WORDS, FACE_WORDS, NODE_WORDS, OWN_CELL_FORM, OWN_CELL_LIVE,
    OWN_CELL_WORDS, OWN_REGISTER_WORDS,
};
use body::medium::{
    arm_at_grain, arm_from_sum, cog_at_grain, cog_from_sum, grain_from_key, grain_key,
    RegionalForm, FORM_WORDS,
};
use body::num::{self, Cog, Rung, COG_WORDS};
use body::place;
use body::register;
use body::seam::SliceWordSeam;
use soma_abi::emission::{DeedEmission, DEED_WORDS};
use soma_abi::live_event_cuda as event_cuda;
use soma_abi::material_shadow_cuda;
use soma_abi::morphological_condition_cuda as morph_condition_cuda;
use soma_abi::morphological_conduct_cuda as morph_cuda;
use soma_abi::recurrent_law_cuda;
use soma_abi::returned_contact_cuda as returned_cuda;
use soma_abi::text_restrict_cuda as text_cuda;
use soma_abi::{contact as contact_abi, register as register_abi};

const REGISTER_STATUS_WORDS: usize = register_abi::STATUS_WORDS;
const REGISTER_STATUS_KIND: usize = register_abi::STATUS_KIND;
const REGISTER_STATUS_OLD_AXIS: usize = register_abi::STATUS_OLD_AXIS;
const REGISTER_STATUS_NEW_AXIS: usize = register_abi::STATUS_NEW_AXIS;
const REGISTER_STATUS_COMPLETE: u32 = register_abi::STATUS_COMPLETE;
const REGISTER_STATUS_NEEDS_OWN_RECAST: u32 = register_abi::STATUS_NEEDS_OWN_RECAST;
const REGISTER_STATUS_CONTINUE: u32 = register_abi::STATUS_CONTINUE;
const REGISTER_STATUS_NEEDS_CARRIER_REBASE: u32 = register_abi::STATUS_NEEDS_CARRIER_REBASE;
const REGISTER_RECAST_INCOMPLETE: u32 = register_abi::RECAST_INCOMPLETE;
const REGISTER_LANE_WORDS: usize = register_abi::LANE_WORDS;
const REGISTER_LANE_OWN_WORD_BASE: usize = register_abi::LANE_OWN_WORD_BASE;
const REGISTER_LANE_CAPACITY_CELLS: usize = register_abi::LANE_CAPACITY_CELLS;
const REGISTER_LANE_CARRIER_WORD_BASE: usize = register_abi::LANE_CARRIER_WORD_BASE;
const REGISTER_LANE_CARRIER_ROW_WORDS: usize = register_abi::LANE_CARRIER_ROW_WORDS;

// One transient cooperative contact sheet per mounted lineage. This is CUDA apparatus, never
// carried body state: the owner publishes one immutable arrival face, REGISTER workers derive its
// contacts, and the owner consumes them in the body's unchanged chronological order.
const CONTACT_COMMAND: usize = contact_abi::COMMAND;
const CONTACT_LIVE: usize = contact_abi::LIVE;
const CONTACT_HEAD: usize = contact_abi::HEAD;
const CONTACT_REGISTER_LO: usize = contact_abi::REGISTER_LO;
const CONTACT_REGISTER_HI: usize = contact_abi::REGISTER_HI;
const CONTACT_NODE: usize = contact_abi::NODE;
const CONTACT_FRAME: usize = contact_abi::FRAME;
const CONTACT_FLY: usize = contact_abi::FLY;
const CONTACT_FLY_LIVE: usize = contact_abi::FLY_LIVE;
const CONTACT_OUTPUT: usize = contact_abi::OUTPUT;
const CONTACT_OUTPUT_LIVE: usize = contact_abi::OUTPUT_LIVE;
const CONTACT_OUTPUT_SAME: usize = contact_abi::OUTPUT_SAME;
const CONTACT_OUTPUT_OTHER: usize = contact_abi::OUTPUT_OTHER;
const CONTACT_OUTPUT_WORDS: usize = contact_abi::OUTPUT_WORDS;
const CONTACT_RECEIPT: usize = contact_abi::RECEIPT;
const CONTACT_SURFACE_WORDS: usize = contact_abi::SURFACE_WORDS;
const CONTACT_FORM: u32 = contact_abi::COMMAND_FORM;
const CONTACT_STOP: u32 = contact_abi::COMMAND_STOP;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// --- the atomic mouth ----------------------------------------------------------------------------
// Relaxed order is the faithful mirror of spirv-std's `Semantics::NONE` / `Scope::QueueFamily`:
// no ordering is claimed within a dispatch; the two passes are ordered by the DISPATCH boundary
// (two separate launches on one stream), never by lineage time. atom.global.{max,add}.{u32,u64}.
#[inline(always)]
unsafe fn amax_u32(slot: &mut u32, v: u32) {
    AtomicU32::from_ptr(slot as *mut u32).fetch_max(v, Ordering::Relaxed);
}
#[inline(always)]
unsafe fn amax_u64(slot: &mut u64, v: u64) {
    AtomicU64::from_ptr(slot as *mut u64).fetch_max(v, Ordering::Relaxed);
}
#[inline(always)]
unsafe fn aadd_u64(slot: &mut u64, v: u64) {
    AtomicU64::from_ptr(slot as *mut u64).fetch_add(v, Ordering::Relaxed);
}
#[inline(always)]
unsafe fn aload_u32(slot: &u32) -> u32 {
    AtomicU32::from_ptr(slot as *const u32 as *mut u32).load(Ordering::Relaxed)
}
#[inline(always)]
unsafe fn aload_u64(slot: &u64) -> u64 {
    AtomicU64::from_ptr(slot as *const u64 as *mut u64).load(Ordering::Relaxed)
}
#[inline(always)]
unsafe fn astore_u32(slot: &mut u32, v: u32) {
    AtomicU32::from_ptr(slot as *mut u32).store(v, Ordering::Relaxed);
}
#[inline(always)]
unsafe fn astore_u64(slot: &mut u64, v: u64) {
    AtomicU64::from_ptr(slot as *mut u64).store(v, Ordering::Relaxed);
}
// The BEFORE face of the increment (spirv `atomic_i_add` returns the original value); the chart
// register reads its own returned transition to name the carry, never a resident comparison.
#[inline(always)]
unsafe fn aadd_u64_prev(slot: &mut u64, v: u64) -> u64 {
    AtomicU64::from_ptr(slot as *mut u64).fetch_add(v, Ordering::Relaxed)
}

/// The global invocation index of the calling thread. `threads(64)` on the card is a 64-wide X
/// block with Y/Z of 1, so `id.x = ctaid.x*ntid.x + tid.x` and `id.y = ctaid.y` (ntid.y == 1).
#[inline(always)]
unsafe fn global_xy() -> (u32, u32) {
    let x =
        nvptx::_block_idx_x() as u32 * nvptx::_block_dim_x() as u32 + nvptx::_thread_idx_x() as u32;
    let y =
        nvptx::_block_idx_y() as u32 * nvptx::_block_dim_y() as u32 + nvptx::_thread_idx_y() as u32;
    (x, y)
}

#[inline(always)]
fn recurrent_read_i64(words: &[u32], at: usize) -> Option<i64> {
    recurrent_law_cuda::decode_i64(words, at)
}

#[inline(always)]
fn recurrent_write_i64(words: &mut [u32], at: usize, value: i64) -> bool {
    if at > words.len() || recurrent_law_cuda::I64_WORDS > words.len() - at {
        return false;
    }
    let encoded = recurrent_law_cuda::encode_i64(value);
    words[at] = encoded[0];
    words[at + 1] = encoded[1];
    true
}

extern "C" {
    #[link_name = "llvm.nvvm.bar.warp.sync"]
    fn contact_warp_sync(mask: u32);
}

#[inline(always)]
unsafe fn contact_sync() {
    // One contact block is exactly the derived 15-lane REGISTER and therefore one partial warp.
    // A warp barrier is legal across the owner/helper divergence; a block barrier is not.
    unsafe { contact_warp_sync((1u32 << register::REGISTER) - 1) };
}

#[inline(always)]
unsafe fn contact_load(words: *mut u32, at: usize) -> u32 {
    AtomicU32::from_ptr(unsafe { words.add(at) }).load(Ordering::Relaxed)
}

#[inline(always)]
unsafe fn contact_store(words: *mut u32, at: usize, value: u32) {
    AtomicU32::from_ptr(unsafe { words.add(at) }).store(value, Ordering::Relaxed);
}

#[inline(always)]
unsafe fn contact_add(words: *mut u32, at: usize, value: u32) {
    AtomicU32::from_ptr(unsafe { words.add(at) }).fetch_add(value, Ordering::Relaxed);
}

/// One CUDA block's transient realization of the immutable REGISTER contact surface. All methods
/// are called only by the block owner except `worker_loop`; the two exact partial-warp meetings
/// delimit every published snapshot and its complete derived sheet.
struct CudaRegisterContactSurface {
    words: *mut u32,
    len: usize,
    base: usize,
}

impl CudaRegisterContactSurface {
    #[inline(always)]
    unsafe fn form(words: *mut u32, len: usize, lane: usize) -> Option<Self> {
        let base = lane.checked_mul(CONTACT_SURFACE_WORDS)?;
        if base > len || CONTACT_SURFACE_WORDS > len - base {
            None
        } else {
            Some(CudaRegisterContactSurface { words, len, base })
        }
    }

    #[inline(always)]
    fn at(&self, local: usize) -> usize {
        self.base + local
    }

    #[inline(always)]
    unsafe fn load(&self, local: usize) -> u32 {
        debug_assert!(self.at(local) < self.len);
        unsafe { contact_load(self.words, self.at(local)) }
    }

    #[inline(always)]
    unsafe fn store(&self, local: usize, value: u32) {
        debug_assert!(self.at(local) < self.len);
        unsafe { contact_store(self.words, self.at(local), value) };
    }

    #[inline(always)]
    unsafe fn cog(&self, at: usize) -> Cog {
        Cog {
            mag: unsafe { self.load(at) },
            rank: Rung {
                mag: unsafe { self.load(at + 1) },
                rank: unsafe { self.load(at + 2) } as i32,
                neg: unsafe { self.load(at + 3) } != 0,
            },
            turn: unsafe { self.load(at + 4) },
        }
    }

    #[inline(always)]
    unsafe fn store_cog(&self, at: usize, cog: Cog) {
        let mut word = 0usize;
        while word < COG_WORDS {
            unsafe { self.store(at + word, num::cog_packed_word(cog, word)) };
            word += 1;
        }
    }

    #[inline(always)]
    unsafe fn snapshot(&self) -> RegisterContactSnapshot {
        let register_at = unsafe { self.load(CONTACT_REGISTER_LO) } as u64
            | ((unsafe { self.load(CONTACT_REGISTER_HI) } as u64) << 32);
        RegisterContactSnapshot {
            register_at: register_at as usize,
            head: unsafe { self.load(CONTACT_HEAD) } as usize,
            live: unsafe { self.load(CONTACT_LIVE) } as usize,
            node: Node {
                well: unsafe { self.cog(CONTACT_NODE) },
                place: (unsafe { self.cog(CONTACT_NODE + COG_WORDS) }, unsafe {
                    self.cog(CONTACT_NODE + 2 * COG_WORDS)
                }),
                len: unsafe { self.load(CONTACT_NODE + 3 * COG_WORDS) },
            },
            frame: (unsafe { self.cog(CONTACT_FRAME) }, unsafe {
                self.cog(CONTACT_FRAME + COG_WORDS)
            }),
            fly: Face {
                arrow: Arrow {
                    reach: unsafe { self.cog(CONTACT_FLY) },
                    aim: unsafe { self.cog(CONTACT_FLY + COG_WORDS) },
                    cross: unsafe { self.cog(CONTACT_FLY + 2 * COG_WORDS) },
                },
            },
            fly_live: unsafe { self.load(CONTACT_FLY_LIVE) } != 0,
        }
    }

    #[inline(always)]
    unsafe fn publish(&self, snapshot: RegisterContactSnapshot) {
        unsafe { self.store(CONTACT_LIVE, snapshot.live as u32) };
        unsafe { self.store(CONTACT_HEAD, snapshot.head as u32) };
        unsafe { self.store(CONTACT_REGISTER_LO, snapshot.register_at as u64 as u32) };
        unsafe {
            self.store(
                CONTACT_REGISTER_HI,
                ((snapshot.register_at as u64) >> 32) as u32,
            )
        };
        let mut word = 0usize;
        while word < NODE_WORDS {
            unsafe {
                self.store(
                    CONTACT_NODE + word,
                    body::manifold::node_packed_word(snapshot.node, word),
                )
            };
            word += 1;
        }
        word = 0;
        while word < COG_WORDS {
            unsafe {
                self.store(
                    CONTACT_FRAME + word,
                    num::cog_packed_word(snapshot.frame.0, word),
                )
            };
            unsafe {
                self.store(
                    CONTACT_FRAME + COG_WORDS + word,
                    num::cog_packed_word(snapshot.frame.1, word),
                )
            };
            word += 1;
        }
        word = 0;
        while word < FACE_WORDS {
            unsafe {
                self.store(
                    CONTACT_FLY + word,
                    body::manifold::face_packed_word(snapshot.fly, word),
                )
            };
            word += 1;
        }
        unsafe { self.store(CONTACT_FLY_LIVE, snapshot.fly_live as u32) };
    }

    #[inline(never)]
    unsafe fn form_contact(&self, carriers: &[u32], worker: usize) {
        if worker >= register::REGISTER as usize {
            return;
        }
        let output = CONTACT_OUTPUT + worker * CONTACT_OUTPUT_WORDS;
        unsafe { self.store(output + CONTACT_OUTPUT_LIVE, 0) };
        let snapshot = unsafe { self.snapshot() };
        if worker < snapshot.live {
            let mut same = Cog::ZERO;
            let mut other = Cog::ZERO;
            if form_register_contact::<SliceWordSeam>(
                carriers, snapshot, worker, &mut same, &mut other,
            ) {
                unsafe { self.store_cog(output + CONTACT_OUTPUT_SAME, same) };
                unsafe { self.store_cog(output + CONTACT_OUTPUT_OTHER, other) };
                unsafe { self.store(output + CONTACT_OUTPUT_LIVE, 1) };
            }
            unsafe {
                contact_add(self.words, self.at(CONTACT_RECEIPT + worker), 1);
            }
        }
    }

    #[inline(never)]
    unsafe fn worker_loop(&self, carriers: &[u32], worker: usize) {
        loop {
            unsafe { contact_sync() };
            let command = unsafe { self.load(CONTACT_COMMAND) };
            if command == CONTACT_FORM {
                unsafe { self.form_contact(carriers, worker) };
                unsafe { contact_sync() };
            } else {
                // STOP and any malformed command both release the complete block. No helper can
                // outlive its owner's invocation or wait across a CUDA launch boundary.
                unsafe { contact_sync() };
                break;
            }
        }
    }

    #[inline(always)]
    unsafe fn stop(&self) {
        unsafe { self.store(CONTACT_COMMAND, CONTACT_STOP) };
        unsafe { contact_sync() };
        unsafe { contact_sync() };
    }
}

impl RegisterContactSurface<SliceWordSeam> for CudaRegisterContactSurface {
    #[inline(never)]
    fn prepare(&mut self, carriers: &[u32], snapshot: RegisterContactSnapshot) {
        unsafe { self.publish(snapshot) };
        unsafe { self.store(CONTACT_COMMAND, CONTACT_FORM) };
        unsafe { contact_sync() };
        unsafe { self.form_contact(carriers, 0) };
        unsafe { contact_sync() };
    }

    #[inline(always)]
    fn select(
        &self,
        _carriers: &[u32],
        _snapshot: RegisterContactSnapshot,
        index: usize,
        same: &mut Cog,
        other: &mut Cog,
    ) -> bool {
        *same = Cog::ZERO;
        *other = Cog::ZERO;
        if index >= register::REGISTER as usize {
            return false;
        }
        let output = CONTACT_OUTPUT + index * CONTACT_OUTPUT_WORDS;
        let live = unsafe { self.load(output + CONTACT_OUTPUT_LIVE) };
        if live == 0 {
            false
        } else {
            *same = unsafe { self.cog(output + CONTACT_OUTPUT_SAME) };
            *other = unsafe { self.cog(output + CONTACT_OUTPUT_OTHER) };
            true
        }
    }
}

// --- the addressing glue (identical to the card's kernel-local helpers) --------------------------

#[inline(always)]
fn source_and_cell(idx: u32, idy: u32, params: &[u32]) -> Option<(usize, usize, usize)> {
    if params.len() < 3 {
        return None;
    }
    let cells = params[0] as usize;
    if cells == 0 {
        return None;
    }
    let linear = idx as usize + idy as usize * params[2] as usize;
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
        unsafe { RegionalForm::unpack_unchecked_with::<body::seam::SliceWordSeam>(standing, at) }
    } else {
        RegionalForm::UNBORN
    }
}

#[inline(always)]
fn read_form(
    standing: &[u32],
    owns: &[u32],
    source: usize,
    cell: usize,
    cells: usize,
) -> RegionalForm {
    if source == 0 {
        read_standing(standing, cell)
    } else {
        let at = ((source - 1) * cells + cell) * FORM_WORDS;
        if at + FORM_WORDS <= owns.len() {
            unsafe { RegionalForm::unpack_unchecked_with::<body::seam::SliceWordSeam>(owns, at) }
        } else {
            RegionalForm::UNBORN
        }
    }
}

#[inline(always)]
unsafe fn store_form(standing: &mut [u32], cell: usize, form: RegionalForm) {
    let at = cell * FORM_WORDS;
    if at + FORM_WORDS > standing.len() {
        return;
    }
    let mut i = 0usize;
    while i < FORM_WORDS {
        astore_u32(&mut standing[at + i], form.packed_word(i));
        i += 1;
    }
}

// A founded source reads its whole form directly at the addressed word; a standing source reads the
// dense standing cell. `at` is already the founded `OWN_CELL_FORM` offset or the dense `cell` offset.
#[inline(always)]
fn read_founded_form(standing: &[u32], owns: &[u32], own: bool, at: usize) -> RegionalForm {
    if own && at + FORM_WORDS <= owns.len() {
        unsafe { RegionalForm::unpack_unchecked_with::<body::seam::SliceWordSeam>(owns, at) }
    } else if !own && at + FORM_WORDS <= standing.len() {
        unsafe { RegionalForm::unpack_unchecked_with::<body::seam::SliceWordSeam>(standing, at) }
    } else {
        RegionalForm::UNBORN
    }
}

// --- PASS 1 — THE GRAIN DECLARES ITSELF ----------------------------------------------------------
// standing ⊕ every OWN form declare the whole-Rung receiving grain. Traversal order has no face:
// only atomic max and touch stand.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_grain(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    let (idx, idy) = global_xy();
    let (source, cell, cells) = match source_and_cell(idx, idy, params) {
        Some(t) => t,
        None => return,
    };
    let form = read_form(standing, owns, source, cell, cells);
    if source != 0 && form != RegionalForm::UNBORN && cell < touched.len() {
        amax_u32(&mut touched[cell], 1);
    }
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let cbase = cell * 2;
    if cbase + 1 < cog_grains.len() {
        if same.mag != 0 {
            amax_u64(&mut cog_grains[cbase], grain_key(same.rank));
        }
        if other.mag != 0 {
            amax_u64(&mut cog_grains[cbase + 1], grain_key(other.rank));
        }
    }
    if cbase + 1 < arm_grains.len() {
        if this_way.mag != 0 {
            amax_u32(&mut arm_grains[cbase], this_way.rank as u32 + 1);
        }
        if that_way.mag != 0 {
            amax_u32(&mut arm_grains[cbase + 1], that_way.rank as u32 + 1);
        }
    }
}

// --- PASS 2 — THE EXACT SUM AT THE GRAIN ---------------------------------------------------------
// Every contribution re-bases once and atomically adds. Associative integer addition after each
// source has re-based exactly once; hardware order therefore has no physical face.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_sum(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    cog_sums: *mut u64,
    cog_sums_len: usize,
    arm_sums: *mut u64,
    arm_sums_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let cog_sums = slice::from_raw_parts_mut(cog_sums, cog_sums_len);
    let arm_sums = slice::from_raw_parts_mut(arm_sums, arm_sums_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    let (idx, idy) = global_xy();
    let (source, cell, cells) = match source_and_cell(idx, idy, params) {
        Some(t) => t,
        None => return,
    };
    if cell >= touched.len() || aload_u32(&touched[cell]) == 0 {
        return;
    }
    let form = read_form(standing, owns, source, cell, cells);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() && base + 1 < cog_sums.len() {
        let same_key = aload_u64(&cog_grains[base]);
        let other_key = aload_u64(&cog_grains[base + 1]);
        if same_key != 0 {
            let contribution = cog_at_grain(same, grain_from_key(same_key));
            aadd_u64(&mut cog_sums[base], contribution);
        }
        if other_key != 0 {
            let contribution = cog_at_grain(other, grain_from_key(other_key));
            aadd_u64(&mut cog_sums[base + 1], contribution);
        }
    }
    if base + 1 < arm_grains.len() && base + 1 < arm_sums.len() {
        let this_grain = aload_u32(&arm_grains[base]);
        let that_grain = aload_u32(&arm_grains[base + 1]);
        if this_grain != 0 {
            let contribution = arm_at_grain(this_way, (this_grain - 1) as i32);
            aadd_u64(&mut arm_sums[base], contribution);
        }
        if that_grain != 0 {
            let contribution = arm_at_grain(that_way, (that_grain - 1) as i32);
            aadd_u64(&mut arm_sums[base + 1], contribution);
        }
    }
}

// --- THE ONE FINAL RE-BASE -----------------------------------------------------------------------
// Each touched place performs the single final re-base; the region folds into its addressed
// topology read (occupied ⊕ resultant ⊕ fiber ⊕ two-armed). Exact addressed forms remain in standing.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_finish(
    standing: *mut u32,
    standing_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    cog_sums: *mut u64,
    cog_sums_len: usize,
    arm_sums: *mut u64,
    arm_sums_len: usize,
    touched: *mut u32,
    touched_len: usize,
    reads: *mut u64,
    reads_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let cog_sums = slice::from_raw_parts_mut(cog_sums, cog_sums_len);
    let arm_sums = slice::from_raw_parts_mut(arm_sums, arm_sums_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let reads = slice::from_raw_parts_mut(reads, reads_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 3 {
        return;
    }
    let (idx, idy) = global_xy();
    let cell = idx as usize + idy as usize * params[2] as usize;
    if cell >= params[0] as usize || cell >= touched.len() {
        return;
    }
    let was_touched = aload_u32(&touched[cell]) != 0;
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
        let same_key = aload_u64(&cog_grains[base]);
        let other_key = aload_u64(&cog_grains[base + 1]);
        let this_grain = aload_u32(&arm_grains[base]);
        let that_grain = aload_u32(&arm_grains[base + 1]);
        let same = if same_key == 0 {
            Cog::lit(0)
        } else {
            cog_from_sum(grain_from_key(same_key), aload_u64(&cog_sums[base]))
        };
        let other = if other_key == 0 {
            Cog::lit(0)
        } else {
            cog_from_sum(grain_from_key(other_key), aload_u64(&cog_sums[base + 1]))
        };
        let this_way = if this_grain == 0 {
            Rung::ZERO
        } else {
            arm_from_sum((this_grain - 1) as i32, aload_u64(&arm_sums[base]))
        };
        let that_way = if that_grain == 0 {
            Rung::ZERO
        } else {
            arm_from_sum((that_grain - 1) as i32, aload_u64(&arm_sums[base + 1]))
        };
        let resolved = RegionalForm::from_components(same, other, this_way, that_way).occupy();
        store_form(standing, cell, resolved);
        resolved
    };

    if reads.len() >= 4 && form != RegionalForm::UNBORN {
        let (same, other) = form.resultant();
        let (this_way, that_way) = form.fiber();
        aadd_u64(&mut reads[0], 1);
        if same.mag != 0 || other.mag != 0 {
            aadd_u64(&mut reads[1], 1);
        }
        if this_way.mag != 0 || that_way.mag != 0 {
            aadd_u64(&mut reads[2], 1);
        }
        if this_way.mag != 0 && that_way.mag != 0 {
            aadd_u64(&mut reads[3], 1);
        }
    }
}

// --- M5 · THE FOUNDED-CELL FOLD ------------------------------------------------------------------
// The reservation-sized OWN buffer is a concatenation of live founded cells (`OWN_CELL_WORDS` each:
// a live flag ⊕ the founding POSITION ⊕ the accumulated form), never `lanes × standing`. Both passes
// re-ground each live cell's founding construction at the receiving standing grain (`place::ground`);
// the shared `link_finish` performs the one final re-base. Standing participates once at its own
// cell exactly as in the dense fold. Params: `[standing_cells, own_cells, xstride, standing_axis]`.

// M5 PASS 1 — variable lineage charts declare one receiving grain by re-grounding each live cell's
// founding construction. Traversal order has no face: only atomic max and touch stand.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_founded_grain(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 || params[0] == 0 || params[3] == 0 {
        return;
    }
    let (idx, idy) = global_xy();
    let linear = idx as usize + idy as usize * params[2] as usize;
    let standing_cells = params[0] as usize;
    let own = linear >= standing_cells;
    let (at, cell) = if !own {
        (linear * FORM_WORDS, linear)
    } else {
        let own_cell = linear - standing_cells;
        if own_cell >= params[1] as usize {
            return;
        }
        let own_at = own_cell * OWN_CELL_WORDS;
        if own_at + OWN_CELL_WORDS > owns.len() || owns[own_at + OWN_CELL_LIVE] == 0 {
            return;
        }
        let position = own_cell_position(owns, own_at);
        let target = place::ground(position, params[3] as i64) as usize;
        if target >= standing_cells {
            return;
        }
        (own_at + OWN_CELL_FORM, target)
    };
    let form = read_founded_form(standing, owns, own, at);
    if own && cell < touched.len() {
        amax_u32(&mut touched[cell], 1);
    }
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() {
        if same.mag != 0 {
            amax_u64(&mut cog_grains[base], grain_key(same.rank));
        }
        if other.mag != 0 {
            amax_u64(&mut cog_grains[base + 1], grain_key(other.rank));
        }
    }
    if base + 1 < arm_grains.len() {
        if this_way.mag != 0 {
            amax_u32(&mut arm_grains[base], this_way.rank as u32 + 1);
        }
        if that_way.mag != 0 {
            amax_u32(&mut arm_grains[base + 1], that_way.rank as u32 + 1);
        }
    }
}

// M5 PASS 2 — the same construction traversal contributes once at the already-declared receiving
// grain. Integer atomic addition is the exact wide hand; no lane order or stored address enters.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_founded_sum(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    cog_sums: *mut u64,
    cog_sums_len: usize,
    arm_sums: *mut u64,
    arm_sums_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let cog_sums = slice::from_raw_parts_mut(cog_sums, cog_sums_len);
    let arm_sums = slice::from_raw_parts_mut(arm_sums, arm_sums_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 || params[0] == 0 || params[3] == 0 {
        return;
    }
    let (idx, idy) = global_xy();
    let linear = idx as usize + idy as usize * params[2] as usize;
    let standing_cells = params[0] as usize;
    let own = linear >= standing_cells;
    let (at, cell) = if !own {
        (linear * FORM_WORDS, linear)
    } else {
        let own_cell = linear - standing_cells;
        if own_cell >= params[1] as usize {
            return;
        }
        let own_at = own_cell * OWN_CELL_WORDS;
        if own_at + OWN_CELL_WORDS > owns.len() || owns[own_at + OWN_CELL_LIVE] == 0 {
            return;
        }
        let position = own_cell_position(owns, own_at);
        let target = place::ground(position, params[3] as i64) as usize;
        if target >= standing_cells {
            return;
        }
        (own_at + OWN_CELL_FORM, target)
    };
    if cell >= touched.len() || aload_u32(&touched[cell]) == 0 {
        return;
    }
    let form = read_founded_form(standing, owns, own, at);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let base = cell * 2;
    if base + 1 < cog_grains.len() && base + 1 < cog_sums.len() {
        let same_key = aload_u64(&cog_grains[base]);
        let other_key = aload_u64(&cog_grains[base + 1]);
        if same_key != 0 {
            aadd_u64(
                &mut cog_sums[base],
                cog_at_grain(same, grain_from_key(same_key)),
            );
        }
        if other_key != 0 {
            aadd_u64(
                &mut cog_sums[base + 1],
                cog_at_grain(other, grain_from_key(other_key)),
            );
        }
    }
    if base + 1 < arm_grains.len() && base + 1 < arm_sums.len() {
        let this_grain = aload_u32(&arm_grains[base]);
        let that_grain = aload_u32(&arm_grains[base + 1]);
        if this_grain != 0 {
            aadd_u64(
                &mut arm_sums[base],
                arm_at_grain(this_way, this_grain as i32 - 1),
            );
        }
        if that_grain != 0 {
            aadd_u64(
                &mut arm_sums[base + 1],
                arm_at_grain(that_way, that_grain as i32 - 1),
            );
        }
    }
}

// --- §XXXII-c · THE REGISTERED RECEIVING FOLD ---------------------------------------------------
// A registered OWN row is `[REGISTER_HEADER; capacity × founded cell]`. The row's active chart is
// event-born and may widen or narrow during carriage, so receiving never imports its transient
// local grip. Every live founder is grounded anew in the receiving standing chart. The scratch
// buffers are one band wide; no global standing-sized intermediate or lane×standing plane enters.

#[derive(Clone, Copy)]
struct RegisteredRows {
    lanes: usize,
    scan_cells: usize,
    ground_axis: u32,
    xstride: u64,
    work: u64,
}

// Prove the complete lane-descriptor extent before any invocation forms a row/cell address. Each
// descriptor carries its own exact flat OWN word base and capacity; no rectangular row stride
// survives into receiving.
#[inline(never)]
fn registered_rows(
    lanes: u32,
    scan_cells: u32,
    ground_axis: u32,
    xstride: u32,
    lane_words_len: usize,
) -> Option<RegisteredRows> {
    if scan_cells == 0 || ground_axis == 0 || ground_axis & (ground_axis - 1) != 0 || xstride == 0 {
        return None;
    }
    let lanes = lanes as usize;
    let scan_cells = scan_cells as usize;
    let required_lane_words = carriage::checked_extent_mul(lanes, REGISTER_LANE_WORDS)?;
    if required_lane_words > lane_words_len {
        return None;
    }

    // Both factors originate as u32, so their product is represented whole in the u64 work hand.
    let work = lanes as u64 * scan_cells as u64;
    Some(RegisteredRows {
        lanes,
        scan_cells,
        ground_axis,
        xstride: xstride as u64,
        work,
    })
}

#[derive(Clone, Copy)]
struct RegisteredCell {
    form_at: usize,
    target: usize,
}

// Arithmetic rectangular traversal only: the linear invocation names exactly one lane/cell pair.
// The founder supplies the receiving target; no resident address, list, search, or map participates.
#[inline(always)]
fn registered_cell(
    owns: &[u32],
    lane_words: &[u32],
    rows: RegisteredRows,
    linear: u64,
) -> Option<RegisteredCell> {
    if linear >= rows.work {
        return None;
    }
    let scan = rows.scan_cells as u64;
    let lane = (linear / scan) as usize;
    let cell = (linear - lane as u64 * scan) as usize;
    if lane >= rows.lanes || cell >= rows.scan_cells {
        return None;
    }

    let lane_at = carriage::checked_extent_mul(lane, REGISTER_LANE_WORDS)?;
    let lane_end = carriage::checked_extent_add(lane_at, REGISTER_LANE_WORDS)?;
    if lane_end > lane_words.len() {
        return None;
    }
    let row_base = lane_words[lane_at + REGISTER_LANE_OWN_WORD_BASE] as usize;
    let capacity = lane_words[lane_at + REGISTER_LANE_CAPACITY_CELLS] as usize;
    if capacity == 0 || cell >= capacity {
        return None;
    }
    let cell_extent = carriage::checked_extent_mul(capacity, OWN_CELL_WORDS)?;
    let row_words = carriage::checked_extent_add(OWN_REGISTER_WORDS, cell_extent)?;
    let row_end = carriage::checked_extent_add(row_base, row_words)?;
    if row_end > owns.len() {
        return None;
    }
    let active_axis = owns[row_base + body::manifold::OWN_REGISTER_AXIS];
    let active_cells = carriage::checked_extent_mul(active_axis as usize, active_axis as usize)?;
    if active_axis == 0 || active_axis & (active_axis - 1) != 0 || active_cells > capacity {
        return None;
    }
    let cell_base = carriage::checked_extent_add(row_base, OWN_REGISTER_WORDS)?;
    let cell_words = carriage::checked_extent_mul(cell, OWN_CELL_WORDS)?;
    let at = carriage::checked_extent_add(cell_base, cell_words)?;
    let end = carriage::checked_extent_add(at, OWN_CELL_WORDS)?;
    if end > row_end || end > owns.len() || owns[at + OWN_CELL_LIVE] == 0 {
        return None;
    }
    let form_at = carriage::checked_extent_add(at, OWN_CELL_FORM)?;
    let form_end = carriage::checked_extent_add(form_at, FORM_WORDS)?;
    if form_end > end {
        return None;
    }

    let position = own_cell_position(owns, at);
    Some(RegisteredCell {
        form_at,
        target: place::ground(position, rows.ground_axis as i64) as usize,
    })
}

#[derive(Clone, Copy)]
struct RegisterBand {
    rows: RegisteredRows,
    standing_cells: usize,
    band_lo: usize,
    band_cells: usize,
    band_end: usize,
    include_standing: bool,
    total_work: u64,
}

// Params: `[standing_axis, standing_cells, lanes, scan_cells, band_lo, band_cells, xstride,
// include_standing?]`. The historical seven-word ABI includes standing. Production cohort passes
// append zero after the first cohort so the one global prefix contributes exactly once.
// Standing and the complete lane-descriptor array are proved before the band can be read.
#[inline(never)]
fn register_band(
    params: &[u32],
    standing_len: usize,
    lane_words_len: usize,
) -> Option<RegisterBand> {
    if params.len() < 7 || params[1] == 0 || params[5] == 0 {
        return None;
    }
    let rows = registered_rows(params[2], params[3], params[0], params[6], lane_words_len)?;
    let standing_axis = params[0] as usize;
    let standing_cells = params[1] as usize;
    let axis_cells = carriage::checked_extent_mul(standing_axis, standing_axis)?;
    let standing_words = carriage::checked_extent_mul(standing_cells, FORM_WORDS)?;
    if axis_cells != standing_cells || standing_words > standing_len {
        return None;
    }
    let band_lo = params[4] as usize;
    let band_cells = params[5] as usize;
    let band_end = carriage::checked_extent_add(band_lo, band_cells)?;
    if band_end > standing_cells {
        return None;
    }

    let include_standing = params.get(7).map(|word| *word != 0).unwrap_or(true);
    // `rows.work <= (u32::MAX)^2`; adding one u32 band remains strictly below u64::MAX.
    let total_work = if include_standing {
        band_cells as u64 + rows.work
    } else {
        rows.work
    };
    Some(RegisterBand {
        rows,
        standing_cells,
        band_lo,
        band_cells,
        band_end,
        include_standing,
        total_work,
    })
}

#[derive(Clone, Copy)]
struct RegisterContribution {
    own: bool,
    form_at: usize,
    local: usize,
}

// The band's standing prefix is read globally. Its registered suffix is lane/cell arithmetic, then
// a founder re-grounding and band filter. Scratch addressing is always the resulting local target.
#[inline(always)]
fn register_contribution(
    standing: &[u32],
    owns: &[u32],
    lane_words: &[u32],
    band: RegisterBand,
    idx: u32,
    idy: u32,
) -> Option<RegisterContribution> {
    let linear = idx as u64 + idy as u64 * band.rows.xstride;
    if linear >= band.total_work {
        return None;
    }
    let standing_work = if band.include_standing {
        band.band_cells as u64
    } else {
        0
    };
    if linear < standing_work {
        let local = linear as usize;
        let global = carriage::checked_extent_add(band.band_lo, local)?;
        let form_at = carriage::checked_extent_mul(global, FORM_WORDS)?;
        let form_end = carriage::checked_extent_add(form_at, FORM_WORDS)?;
        if global >= band.standing_cells || form_end > standing.len() {
            return None;
        }
        return Some(RegisterContribution {
            own: false,
            form_at,
            local,
        });
    }

    let own_linear = linear - standing_work;
    let cell = registered_cell(owns, lane_words, band.rows, own_linear)?;
    if cell.target < band.band_lo || cell.target >= band.band_end {
        return None;
    }
    Some(RegisterContribution {
        own: true,
        form_at: cell.form_at,
        local: cell.target - band.band_lo,
    })
}

#[inline(always)]
fn register_grain_extents(
    band_cells: usize,
    cog_grains_len: usize,
    arm_grains_len: usize,
    touched_len: usize,
) -> Option<usize> {
    let pair_words = carriage::checked_extent_mul(band_cells, 2)?;
    if pair_words > cog_grains_len || pair_words > arm_grains_len || band_cells > touched_len {
        return None;
    }
    Some(pair_words)
}

// REGISTER PASS 1. The first `band_cells` invocations contribute global standing; every remaining
// invocation names one registered lane/cell. Atomic max and touch operate only on band-local scratch.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_register_grain(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    lane_words: *const u32,
    lane_words_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let lane_words = slice::from_raw_parts(lane_words, lane_words_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    let Some(band) = register_band(params, standing.len(), lane_words.len()) else {
        return;
    };
    if register_grain_extents(
        band.band_cells,
        cog_grains.len(),
        arm_grains.len(),
        touched.len(),
    )
    .is_none()
    {
        return;
    }
    let (idx, idy) = global_xy();
    let Some(contribution) = register_contribution(standing, owns, lane_words, band, idx, idy)
    else {
        return;
    };
    let form = read_founded_form(standing, owns, contribution.own, contribution.form_at);
    if contribution.own {
        amax_u32(&mut touched[contribution.local], 1);
    }
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let Some(base) = carriage::checked_extent_mul(contribution.local, 2) else {
        return;
    };
    if same.mag != 0 {
        amax_u64(&mut cog_grains[base], grain_key(same.rank));
    }
    if other.mag != 0 {
        amax_u64(&mut cog_grains[base + 1], grain_key(other.rank));
    }
    if this_way.mag != 0 {
        amax_u32(&mut arm_grains[base], this_way.rank as u32 + 1);
    }
    if that_way.mag != 0 {
        amax_u32(&mut arm_grains[base + 1], that_way.rank as u32 + 1);
    }
}

// REGISTER PASS 2. Each contribution uses the already-declared band-local grain and adds once in
// the exact wide hand. The global receiving grip never becomes row state.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_register_sum(
    standing: *mut u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    lane_words: *const u32,
    lane_words_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    cog_sums: *mut u64,
    cog_sums_len: usize,
    arm_sums: *mut u64,
    arm_sums_len: usize,
    touched: *mut u32,
    touched_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let lane_words = slice::from_raw_parts(lane_words, lane_words_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let cog_sums = slice::from_raw_parts_mut(cog_sums, cog_sums_len);
    let arm_sums = slice::from_raw_parts_mut(arm_sums, arm_sums_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let params = slice::from_raw_parts(params, params_len);

    let Some(band) = register_band(params, standing.len(), lane_words.len()) else {
        return;
    };
    let Some(pair_words) = register_grain_extents(
        band.band_cells,
        cog_grains.len(),
        arm_grains.len(),
        touched.len(),
    ) else {
        return;
    };
    if pair_words > cog_sums.len() || pair_words > arm_sums.len() {
        return;
    }
    let (idx, idy) = global_xy();
    let Some(contribution) = register_contribution(standing, owns, lane_words, band, idx, idy)
    else {
        return;
    };
    if aload_u32(&touched[contribution.local]) == 0 {
        return;
    }
    let form = read_founded_form(standing, owns, contribution.own, contribution.form_at);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    let Some(base) = carriage::checked_extent_mul(contribution.local, 2) else {
        return;
    };
    let same_key = aload_u64(&cog_grains[base]);
    let other_key = aload_u64(&cog_grains[base + 1]);
    if same_key != 0 {
        aadd_u64(
            &mut cog_sums[base],
            cog_at_grain(same, grain_from_key(same_key)),
        );
    }
    if other_key != 0 {
        aadd_u64(
            &mut cog_sums[base + 1],
            cog_at_grain(other, grain_from_key(other_key)),
        );
    }
    let this_grain = aload_u32(&arm_grains[base]);
    let that_grain = aload_u32(&arm_grains[base + 1]);
    if this_grain != 0 {
        aadd_u64(
            &mut arm_sums[base],
            arm_at_grain(this_way, this_grain as i32 - 1),
        );
    }
    if that_grain != 0 {
        aadd_u64(
            &mut arm_sums[base + 1],
            arm_at_grain(that_way, that_grain as i32 - 1),
        );
    }
}

// REGISTER FINISH. Scratch is local to this band, while standing is addressed at `band_lo+local`.
// `reads` deliberately accumulates across band launches into one topology census.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn link_register_finish(
    standing: *mut u32,
    standing_len: usize,
    cog_grains: *mut u64,
    cog_grains_len: usize,
    arm_grains: *mut u32,
    arm_grains_len: usize,
    cog_sums: *mut u64,
    cog_sums_len: usize,
    arm_sums: *mut u64,
    arm_sums_len: usize,
    touched: *mut u32,
    touched_len: usize,
    reads: *mut u64,
    reads_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let cog_grains = slice::from_raw_parts_mut(cog_grains, cog_grains_len);
    let arm_grains = slice::from_raw_parts_mut(arm_grains, arm_grains_len);
    let cog_sums = slice::from_raw_parts_mut(cog_sums, cog_sums_len);
    let arm_sums = slice::from_raw_parts_mut(arm_sums, arm_sums_len);
    let touched = slice::from_raw_parts_mut(touched, touched_len);
    let reads = slice::from_raw_parts_mut(reads, reads_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 || params[0] == 0 || params[2] == 0 || params[3] == 0 {
        return;
    }
    let standing_cells = params[0] as usize;
    let band_lo = params[1] as usize;
    let band_cells = params[2] as usize;
    let Some(standing_words) = carriage::checked_extent_mul(standing_cells, FORM_WORDS) else {
        return;
    };
    let Some(band_end) = carriage::checked_extent_add(band_lo, band_cells) else {
        return;
    };
    let Some(pair_words) = carriage::checked_extent_mul(band_cells, 2) else {
        return;
    };
    if standing_words > standing.len()
        || band_end > standing_cells
        || pair_words > cog_grains.len()
        || pair_words > arm_grains.len()
        || pair_words > cog_sums.len()
        || pair_words > arm_sums.len()
        || band_cells > touched.len()
    {
        return;
    }

    let (idx, idy) = global_xy();
    let linear = idx as u64 + idy as u64 * params[3] as u64;
    if linear >= band_cells as u64 {
        return;
    }
    let local = linear as usize;
    let Some(global) = carriage::checked_extent_add(band_lo, local) else {
        return;
    };
    let Some(base) = carriage::checked_extent_mul(local, 2) else {
        return;
    };
    let was_touched = aload_u32(&touched[local]) != 0;
    let form = if !was_touched {
        read_standing(standing, global)
    } else {
        let same_key = aload_u64(&cog_grains[base]);
        let other_key = aload_u64(&cog_grains[base + 1]);
        let this_grain = aload_u32(&arm_grains[base]);
        let that_grain = aload_u32(&arm_grains[base + 1]);
        let same = if same_key == 0 {
            Cog::lit(0)
        } else {
            cog_from_sum(grain_from_key(same_key), aload_u64(&cog_sums[base]))
        };
        let other = if other_key == 0 {
            Cog::lit(0)
        } else {
            cog_from_sum(grain_from_key(other_key), aload_u64(&cog_sums[base + 1]))
        };
        let this_way = if this_grain == 0 {
            Rung::ZERO
        } else {
            arm_from_sum((this_grain - 1) as i32, aload_u64(&arm_sums[base]))
        };
        let that_way = if that_grain == 0 {
            Rung::ZERO
        } else {
            arm_from_sum((that_grain - 1) as i32, aload_u64(&arm_sums[base + 1]))
        };
        let resolved = RegionalForm::from_components(same, other, this_way, that_way).occupy();
        store_form(standing, global, resolved);
        resolved
    };

    if reads.len() >= 4 && form != RegionalForm::UNBORN {
        let (same, other) = form.resultant();
        let (this_way, that_way) = form.fiber();
        aadd_u64(&mut reads[0], 1);
        if same.mag != 0 || other.mag != 0 {
            aadd_u64(&mut reads[1], 1);
        }
        if this_way.mag != 0 || that_way.mag != 0 {
            aadd_u64(&mut reads[2], 1);
        }
        if this_way.mag != 0 && that_way.mag != 0 {
            aadd_u64(&mut reads[3], 1);
        }
    }
}

// --- §XXXII-b · THE CHART FAMILY -----------------------------------------------------------------
// The standing axis is the cut's chart grain; the grain re-bases when occupancy passes the chart's
// hand. `chart_mark` casts each live OWN cell into the candidate gauge (presence only); `chart_count`
// stands one thread at each distinct arriving grip and reads the occupancy register's OWN carry
// event (never a `≥`); `chart_recast` zero-extends each occupied standing form into the widened chart.

// PRE-INTEGRATION CAST. Every live lineage-local construction declares its grip in the candidate
// receiving gauge. Atomic max makes coincident casts one arrival with no lane order, map, or sort.
// Params: `[own_cells, mark_axis, xstride]`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn chart_mark(
    owns: *mut u32,
    owns_len: usize,
    marks: *mut u32,
    marks_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let marks = slice::from_raw_parts_mut(marks, marks_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 3 || params[1] == 0 {
        return;
    }
    let (idx, idy) = global_xy();
    let own_cell = idx as usize + idy as usize * params[2] as usize;
    if own_cell >= params[0] as usize {
        return;
    }
    let at = own_cell * OWN_CELL_WORDS;
    if at + OWN_CELL_WORDS > owns.len() || owns[at + OWN_CELL_LIVE] == 0 {
        return;
    }
    let position = own_cell_position(owns, at);
    let grip = place::ground(position, params[1] as i64) as usize;
    if grip < marks.len() {
        amax_u32(&mut marks[grip], 1);
    }
}

// PRE-INTEGRATION REGISTER CAST. Rectangular lane/capacity traversal names each registered cell
// arithmetically; each lane descriptor supplies its exact OWN base/capacity, and every live founder
// is re-grounded directly into the global candidate mark chart. A production spatial band keeps
// the one global chart union while bounding the marks apparatus. Params:
// `[lanes, scan_cells, mark_axis, xstride, band_lo?]`; the historical four-word ABI starts at zero.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn chart_register_mark(
    owns: *mut u32,
    owns_len: usize,
    lane_words: *const u32,
    lane_words_len: usize,
    marks: *mut u32,
    marks_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let lane_words = slice::from_raw_parts(lane_words, lane_words_len);
    let marks = slice::from_raw_parts_mut(marks, marks_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 {
        return;
    }
    let Some(rows) = registered_rows(params[0], params[1], params[2], params[3], lane_words.len())
    else {
        return;
    };
    let (idx, idy) = global_xy();
    let linear = idx as u64 + idy as u64 * rows.xstride;
    let Some(cell) = registered_cell(owns, lane_words, rows, linear) else {
        return;
    };
    let band_lo = params.get(4).copied().unwrap_or(0) as usize;
    let Some(band_end) = carriage::checked_extent_add(band_lo, marks.len()) else {
        return;
    };
    if cell.target >= band_lo && cell.target < band_end {
        amax_u32(&mut marks[cell.target - band_lo], 1);
    }
}

// THE CHART'S OWN REGISTER. A grip already occupied by zero-extended standing is residence, not
// arrival, and contributes nothing. Every genuinely new grip performs one unit increment; the
// increment's BEFORE/AFTER faces declare whether the hand received a carry. No occupancy comparison.
// Params: `[old_axis, new_axis, band_cells, xstride, band_lo?]`; `chart_register` is
// `[occupancy, carried]`. The historical four-word ABI names the complete zero-origin chart.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn chart_count(
    standing: *mut u32,
    standing_len: usize,
    marks: *mut u32,
    marks_len: usize,
    chart_register: *mut u64,
    chart_register_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts_mut(standing, standing_len);
    let marks = slice::from_raw_parts_mut(marks, marks_len);
    let chart_register = slice::from_raw_parts_mut(chart_register, chart_register_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 || chart_register.len() < 2 || params[0] == 0 || params[1] == 0 {
        return;
    }
    let (idx, idy) = global_xy();
    let local = idx as usize + idy as usize * params[3] as usize;
    if local >= params[2] as usize || local >= marks.len() || marks[local] == 0 {
        return;
    }
    let band_lo = params.get(4).copied().unwrap_or(0) as usize;
    let Some(grip) = carriage::checked_extent_add(band_lo, local) else {
        return;
    };
    let Some(chart_cells) = carriage::checked_extent_mul(params[1] as usize, params[1] as usize)
    else {
        return;
    };
    if grip >= chart_cells {
        return;
    }

    let standing_occupies = match chart::zero_extended_source(grip as u32, params[0], params[1]) {
        Some(old_grip) => read_standing(standing, old_grip as usize).occupied(),
        None => false,
    };
    if standing_occupies {
        return;
    }

    let before = aadd_u64_prev(&mut chart_register[0], 1);
    let after = before.wrapping_add(1);
    if chart::carried_into_hand(before, after, params[1]) {
        astore_u64(&mut chart_register[1], 1);
    }
}

// ZERO'S OWN RECAST. The chart digit has already been forced. Each occupied old grip writes its
// unchanged form at `(x,y) -> (2^r x, 2^r y)` in the wider gauge; the target is unique, so merged
// history stays merged. Params: `[old_axis, new_axis, old_grip_count, xstride]`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn chart_recast(
    old_standing: *mut u32,
    old_standing_len: usize,
    new_standing: *mut u32,
    new_standing_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let old_standing = slice::from_raw_parts_mut(old_standing, old_standing_len);
    let new_standing = slice::from_raw_parts_mut(new_standing, new_standing_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 4 || params[0] == 0 || params[1] == 0 {
        return;
    }
    let (idx, idy) = global_xy();
    let old_grip = idx as usize + idy as usize * params[3] as usize;
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

// --- §XXXII-c · OUT-OF-PLACE REGISTER RECAST ----------------------------------------------------
// The old REGISTER row remains immutable while each live cell crosses by the body's exact
// zero-extension into a fresh zero row. The two launches are one transaction at the CUDA boundary:
// `register_own_recast` carries cells, then a later launch of `register_own_recast_finish` copies
// the seven-word header, installs the already-requested axis, and publishes Complete. The launch
// boundary is the global completion seam; neither entry invents a device-grid barrier or body
// progress cursor.

#[derive(Clone, Copy)]
struct RegisterRecastRanges {
    old_word_base: usize,
    new_word_base: usize,
    old_capacity: usize,
    old_axis: u32,
    new_axis: u32,
    completion_at: usize,
    requested: bool,
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn register_recast_ranges(
    old_owns: &[u32],
    fresh_owns_len: usize,
    old_lanes: &[u32],
    new_lanes: &[u32],
    requests: &[u32],
    completions: &[u32],
    lane: usize,
    lane_count: usize,
    max_old_capacity: usize,
) -> Option<RegisterRecastRanges> {
    if lane >= lane_count || max_old_capacity == 0 {
        return None;
    }
    let lane_at = carriage::checked_extent_mul(lane, REGISTER_LANE_WORDS)?;
    let lane_end = carriage::checked_extent_add(lane_at, REGISTER_LANE_WORDS)?;
    if lane_end > old_lanes.len() || lane_end > new_lanes.len() {
        return None;
    }
    let request_at = carriage::checked_extent_mul(lane, REGISTER_STATUS_WORDS)?;
    let request_end = carriage::checked_extent_add(request_at, REGISTER_STATUS_WORDS)?;
    if request_end > requests.len()
        || lane >= completions.len()
        || completions[lane] != REGISTER_RECAST_INCOMPLETE
    {
        return None;
    }

    let kind = requests[request_at + REGISTER_STATUS_KIND];
    if kind != REGISTER_STATUS_COMPLETE
        && kind != REGISTER_STATUS_NEEDS_OWN_RECAST
        && kind != REGISTER_STATUS_CONTINUE
    {
        return None;
    }
    let requested = kind == REGISTER_STATUS_NEEDS_OWN_RECAST;
    let diagnosed_old_axis = requests[request_at + REGISTER_STATUS_OLD_AXIS];
    let diagnosed_new_axis = requests[request_at + REGISTER_STATUS_NEW_AXIS];
    let old_capacity = old_lanes[lane_at + REGISTER_LANE_CAPACITY_CELLS] as usize;
    let new_capacity = new_lanes[lane_at + REGISTER_LANE_CAPACITY_CELLS] as usize;
    let old_word_base = old_lanes[lane_at + REGISTER_LANE_OWN_WORD_BASE] as usize;
    let new_word_base = new_lanes[lane_at + REGISTER_LANE_OWN_WORD_BASE] as usize;
    let old_header_end = carriage::checked_extent_add(old_word_base, OWN_REGISTER_WORDS)?;
    let new_header_end = carriage::checked_extent_add(new_word_base, OWN_REGISTER_WORDS)?;
    if old_header_end > old_owns.len() || new_header_end > fresh_owns_len {
        return None;
    }
    let mounted_axis = old_owns[old_word_base + body::manifold::OWN_REGISTER_AXIS];
    let effective_axis = if mounted_axis == 0 { 1 } else { mounted_axis };
    if effective_axis & (effective_axis - 1) != 0 {
        return None;
    }
    let (old_axis, new_axis) = if requested {
        if diagnosed_old_axis != effective_axis
            || diagnosed_old_axis == 0
            || diagnosed_old_axis & (diagnosed_old_axis - 1) != 0
            || diagnosed_old_axis.checked_mul(2) != Some(diagnosed_new_axis)
        {
            return None;
        }
        (diagnosed_old_axis, diagnosed_new_axis)
    } else {
        if diagnosed_old_axis != 0 || diagnosed_new_axis != 0 {
            return None;
        }
        (effective_axis, effective_axis)
    };
    let exact_old = carriage::checked_extent_mul(old_axis as usize, old_axis as usize)?;
    let exact_new = carriage::checked_extent_mul(new_axis as usize, new_axis as usize)?;
    let capacity_formed = if requested {
        old_capacity == exact_old && new_capacity == exact_new
    } else {
        exact_old <= old_capacity && new_capacity == old_capacity
    };
    if !capacity_formed || old_capacity > max_old_capacity {
        return None;
    }

    let old_cell_words = carriage::checked_extent_mul(old_capacity, OWN_CELL_WORDS)?;
    let new_cell_words = carriage::checked_extent_mul(new_capacity, OWN_CELL_WORDS)?;
    let old_words = carriage::checked_extent_add(OWN_REGISTER_WORDS, old_cell_words)?;
    let new_words = carriage::checked_extent_add(OWN_REGISTER_WORDS, new_cell_words)?;
    let old_end = carriage::checked_extent_add(old_word_base, old_words)?;
    let new_end = carriage::checked_extent_add(new_word_base, new_words)?;
    if old_end > old_owns.len() || new_end > fresh_owns_len {
        return None;
    }

    Some(RegisterRecastRanges {
        old_word_base,
        new_word_base,
        old_capacity,
        old_axis,
        new_axis,
        completion_at: lane,
        requested,
    })
}

/// Carry each live cell from immutable old REGISTER rows into exact fresh zero rows. Old and new
/// lane descriptors use the ten-word REGISTER lane shape; only word six (flat OWN word offset)
/// and word seven (capacity cells) participate. Carrier span words eight and nine pass unchanged.
/// Requests are three immutable words
/// per lane: `[NeedsOwnRecast, old_axis, new_axis]` widens by zero-extension, while `[Complete, 0, 0]`
/// carries a non-requesting sibling byte-whole at the same mounted axis and capacity. Completion
/// is a separate one-word-per-lane aperture, freshly seeded to `u32::MAX`. Params are
/// `[lanes, max_old_capacity, x_thread_stride]`. The launch supplies one logical work item per
/// `lanes × max_old_capacity`; padding above a lane's exact old capacity is invisible.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn register_own_recast(
    old_owns: *const u32,
    old_owns_len: usize,
    fresh_owns: *mut u32,
    fresh_owns_len: usize,
    old_lanes: *const u32,
    old_lanes_len: usize,
    new_lanes: *const u32,
    new_lanes_len: usize,
    requests: *const u32,
    requests_len: usize,
    completions: *mut u32,
    completions_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let old_owns = slice::from_raw_parts(old_owns, old_owns_len);
    let fresh_owns = slice::from_raw_parts_mut(fresh_owns, fresh_owns_len);
    let old_lanes = slice::from_raw_parts(old_lanes, old_lanes_len);
    let new_lanes = slice::from_raw_parts(new_lanes, new_lanes_len);
    let requests = slice::from_raw_parts(requests, requests_len);
    let completions = slice::from_raw_parts_mut(completions, completions_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 3 || params[0] == 0 || params[1] == 0 || params[2] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let linear = global_x as u64 + global_y as u64 * params[2] as u64;
    let max_old_capacity = params[1] as usize;
    let lane = linear / params[1] as u64;
    if lane >= params[0] as u64 {
        return;
    }
    let local = (linear - lane * params[1] as u64) as usize;
    let Some(ranges) = register_recast_ranges(
        old_owns,
        fresh_owns.len(),
        old_lanes,
        new_lanes,
        requests,
        completions,
        lane as usize,
        params[0] as usize,
        max_old_capacity,
    ) else {
        return;
    };
    if local >= ranges.old_capacity {
        return;
    }

    let from = ranges.old_word_base + OWN_REGISTER_WORDS + local * OWN_CELL_WORDS;
    if old_owns[from + OWN_CELL_LIVE] == 0 {
        return;
    }
    let moved = if ranges.requested {
        chart::zero_extend_grip(local as u32, ranges.old_axis, ranges.new_axis) as usize
    } else {
        local
    };
    let to = ranges.new_word_base + OWN_REGISTER_WORDS + moved * OWN_CELL_WORDS;
    let mut word = 0usize;
    while word < OWN_CELL_WORDS {
        fresh_owns[to + word] = old_owns[from + word];
        word += 1;
    }
}

/// Finish one already-carried REGISTER recast per logical lane. This entry must be launched only
/// after `register_own_recast` has completed in the same CUDA ordering domain. Params retain the
/// same `[lanes, max_old_capacity, x_thread_stride]` shape, but this launch supplies one logical
/// work item per lane. Requests remain immutable. Complete is terminal-stored into the separate
/// completion aperture, so a rejected non-requesting lane cannot masquerade as finished.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn register_own_recast_finish(
    old_owns: *const u32,
    old_owns_len: usize,
    fresh_owns: *mut u32,
    fresh_owns_len: usize,
    old_lanes: *const u32,
    old_lanes_len: usize,
    new_lanes: *const u32,
    new_lanes_len: usize,
    requests: *const u32,
    requests_len: usize,
    completions: *mut u32,
    completions_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let old_owns = slice::from_raw_parts(old_owns, old_owns_len);
    let fresh_owns = slice::from_raw_parts_mut(fresh_owns, fresh_owns_len);
    let old_lanes = slice::from_raw_parts(old_lanes, old_lanes_len);
    let new_lanes = slice::from_raw_parts(new_lanes, new_lanes_len);
    let requests = slice::from_raw_parts(requests, requests_len);
    let completions = slice::from_raw_parts_mut(completions, completions_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 3 || params[0] == 0 || params[1] == 0 || params[2] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let lane = global_x as u64 + global_y as u64 * params[2] as u64;
    if lane >= params[0] as u64 {
        return;
    }
    let Some(ranges) = register_recast_ranges(
        old_owns,
        fresh_owns.len(),
        old_lanes,
        new_lanes,
        requests,
        completions,
        lane as usize,
        params[0] as usize,
        params[1] as usize,
    ) else {
        return;
    };

    let mut word = 0usize;
    while word < OWN_REGISTER_WORDS {
        if fresh_owns[ranges.new_word_base + word] != 0 {
            return;
        }
        word += 1;
    }
    word = 0;
    while word < OWN_REGISTER_WORDS {
        fresh_owns[ranges.new_word_base + word] = old_owns[ranges.old_word_base + word];
        word += 1;
    }
    if ranges.requested {
        fresh_owns[ranges.new_word_base + body::manifold::OWN_REGISTER_AXIS] = ranges.new_axis;
    }
    // The separate launch is the global completion seam for every preceding unique cell write.
    // Publish Complete last; leaving this store unreachable preserves the incomplete sentinel.
    astore_u32(
        &mut completions[ranges.completion_at],
        REGISTER_STATUS_COMPLETE,
    );
}

// --- THE CARRIER REBASE ------------------------------------------------------------------------
// One CUDA worker owns one complete carrier row.  A pressured lane moves its canonical live row
// into the exact deeper reservation requested by the carried continuation; every co-mounted
// sibling crosses byte-whole.  This is a device-local physical remount, not a Soma deed.

#[no_mangle]
pub unsafe extern "ptx-kernel" fn register_carrier_rebase(
    old_carriers: *const u32,
    old_carriers_len: usize,
    fresh_carriers: *mut u32,
    fresh_carriers_len: usize,
    old_lanes: *const u32,
    old_lanes_len: usize,
    new_lanes: *const u32,
    new_lanes_len: usize,
    requests: *const u32,
    requests_len: usize,
    completions: *mut u32,
    completions_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let old_carriers = slice::from_raw_parts(old_carriers, old_carriers_len);
    let fresh_carriers = slice::from_raw_parts_mut(fresh_carriers, fresh_carriers_len);
    let old_lanes = slice::from_raw_parts(old_lanes, old_lanes_len);
    let new_lanes = slice::from_raw_parts(new_lanes, new_lanes_len);
    let requests = slice::from_raw_parts(requests, requests_len);
    let completions = slice::from_raw_parts_mut(completions, completions_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 2 || params[0] == 0 || params[1] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let lane = global_x as u64 + global_y as u64 * params[1] as u64;
    if lane >= params[0] as u64 {
        return;
    }
    let lane = lane as usize;
    let Some(lane_at) = carriage::checked_extent_mul(lane, REGISTER_LANE_WORDS) else {
        return;
    };
    let Some(lane_end) = carriage::checked_extent_add(lane_at, REGISTER_LANE_WORDS) else {
        return;
    };
    let Some(request_at) = carriage::checked_extent_mul(lane, REGISTER_STATUS_WORDS) else {
        return;
    };
    let Some(request_end) = carriage::checked_extent_add(request_at, REGISTER_STATUS_WORDS) else {
        return;
    };
    if lane_end > old_lanes.len()
        || lane_end > new_lanes.len()
        || request_end > requests.len()
        || lane >= completions.len()
        || completions[lane] != REGISTER_RECAST_INCOMPLETE
    {
        return;
    }

    let kind = requests[request_at + REGISTER_STATUS_KIND];
    if kind != REGISTER_STATUS_COMPLETE
        && kind != REGISTER_STATUS_NEEDS_OWN_RECAST
        && kind != REGISTER_STATUS_CONTINUE
        && kind != REGISTER_STATUS_NEEDS_CARRIER_REBASE
    {
        return;
    }
    let old_base = old_lanes[lane_at + REGISTER_LANE_CARRIER_WORD_BASE] as usize;
    let old_words = old_lanes[lane_at + REGISTER_LANE_CARRIER_ROW_WORDS] as usize;
    let new_base = new_lanes[lane_at + REGISTER_LANE_CARRIER_WORD_BASE] as usize;
    let new_words = new_lanes[lane_at + REGISTER_LANE_CARRIER_ROW_WORDS] as usize;
    let Some(old_end) = carriage::checked_extent_add(old_base, old_words) else {
        return;
    };
    let Some(new_end) = carriage::checked_extent_add(new_base, new_words) else {
        return;
    };
    if old_end > old_carriers.len() || new_end > fresh_carriers.len() {
        return;
    }
    let old = &old_carriers[old_base..old_end];
    let fresh = &mut fresh_carriers[new_base..new_end];
    if kind == REGISTER_STATUS_NEEDS_CARRIER_REBASE {
        let required = requests[request_at + REGISTER_STATUS_OLD_AXIS] as u64
            | ((requests[request_at + REGISTER_STATUS_NEW_AXIS] as u64) << 32);
        let Ok(required) = usize::try_from(required) else {
            return;
        };
        if body::manifold::carrier_row_words(required) != new_words
            || carriage::required_carrier_rebase_depth(old) != Some(required as u64)
            || carriage::rebase_carrier_row(old, fresh).is_none()
        {
            return;
        }
    } else {
        if old_words != new_words || fresh.iter().any(|&word| word != 0) {
            return;
        }
        fresh.copy_from_slice(old);
    }
    astore_u32(&mut completions[lane], REGISTER_STATUS_COMPLETE);
}

// --- §XXVIII-b · THE SCOPE FAMILY (CUDA LADDER RUNG 3) -------------------------------------------
// One thread carries one raw-light lineage into one invocation-exclusive OWN region and complete
// carrier/K row through the shared `body::carriage` stroke. The SHELL decodes the storage ABI and
// carves the disjoint spans; every decision that advances the worldline belongs to `carriage`. The
// span is single-writer, so `SliceWordSeam`'s plain scalar store is the faithful mirror of the
// SPIR-V atomic-store seam. Count publication stays this substrate's atomic boundary exactly as the
// SPIR-V entries use `atomic_i_add`; the four-word count aperture is itself lane-disjoint. Dispatch
// may span both grid dimensions (block 64 × 1); the explicit runtime X-thread stride linearizes
// each global `(x, y)` into one lane without cutting the co-present configuration.

#[derive(Clone, Copy)]
struct DenseRanges {
    lane_at: usize,
    own: WordSpan,
    carrier: WordSpan,
    count_at: usize,
}

// Scalar-only ABI proof (mirrors the SPIR-V shell's `dense_ranges`). One failure returns before the
// body can mutate. Lane rows are `[byte_offset, byte_count, seed_prev, seed_cur, base_lo, base_hi]`.
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
    if lane >= lane_count || cells == 0 || row_words < CARRIER_HEADER_WORDS {
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
        own: WordSpan::new(own_base, own_words),
        carrier: WordSpan::new(row_base, row_words),
        count_at,
    })
}

#[derive(Clone, Copy)]
struct FoundedHeader {
    lane_at: usize,
    carrier: WordSpan,
    count_at: usize,
}

// Founded lane rows extend the dense row with `[own_cell_offset, own_axis]` (8 words).
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
    if lane >= lane_count || cells == 0 || row_words < CARRIER_HEADER_WORDS {
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
        carrier: WordSpan::new(row_base, row_words),
        count_at,
    })
}

// REGISTER production carries the exact carrier span in the lane descriptor. The descriptor is
// boundary framing only: it carves one complete invocation-exclusive row from the concatenated
// carrier reservation and survives OWN recasts unchanged.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn registered_header(
    lane: usize,
    lane_count: usize,
    cells: usize,
    lanes: &[u32],
    counts_len: usize,
    carriers_len: usize,
) -> Option<FoundedHeader> {
    if lane >= lane_count || cells == 0 {
        return None;
    }
    let lane_at = carriage::checked_extent_mul(lane, REGISTER_LANE_WORDS)?;
    let lane_end = carriage::checked_extent_add(lane_at, REGISTER_LANE_WORDS)?;
    let count_at = carriage::checked_extent_mul(lane, 4)?;
    let count_end = carriage::checked_extent_add(count_at, 4)?;
    if lane_end > lanes.len() || count_end > counts_len {
        return None;
    }
    let row_base = lanes[lane_at + REGISTER_LANE_CARRIER_WORD_BASE] as usize;
    let row_words = lanes[lane_at + REGISTER_LANE_CARRIER_ROW_WORDS] as usize;
    if row_words < CARRIER_HEADER_WORDS {
        return None;
    }
    let row_end = carriage::checked_extent_add(row_base, row_words)?;
    if row_end > carriers_len {
        return None;
    }
    Some(FoundedHeader {
        lane_at,
        carrier: WordSpan::new(row_base, row_words),
        count_at,
    })
}

#[derive(Clone, Copy)]
struct FoundedRanges {
    own_axis: usize,
    own_cells: usize,
    own: WordSpan,
    radiation: WordSpan,
}

// The founded reservation is `own_axis²` concatenated OWN cells at the lane's declared cell offset.
// A radiation aperture forms only at the exact `RADIATION_WORDS` stride; every other stride keeps
// the historical no-radiation face (an empty span) without fabricating a backing region.
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
    let own_base = carriage::checked_extent_mul(own_cell_base, OWN_CELL_WORDS)?;
    let own_words = carriage::checked_extent_mul(own_cells, OWN_CELL_WORDS)?;
    let _own_end = carriage::checked_extent_add(own_base, own_words)?;
    let radiation = if radiation_stride == body::manifold::RADIATION_WORDS {
        let base = carriage::checked_extent_mul(offset, radiation_stride)?;
        let words = carriage::checked_extent_mul(count, radiation_stride)?;
        let _end = carriage::checked_extent_add(base, words)?;
        WordSpan::new(base, words)
    } else {
        WordSpan::empty()
    };
    Some(FoundedRanges {
        own_axis,
        own_cells,
        own: WordSpan::new(own_base, own_words),
        radiation,
    })
}

#[derive(Clone, Copy)]
struct RegisterRanges {
    own: WordSpan,
    radiation: WordSpan,
    completion: WordSpan,
}

// The event-born REGISTER row begins at the lane's declared OWN word offset and carries its seven
// header words beside every cell the mounted aperture affords. Capacity is storage only; the
// current's active axis lives in that mutable header. Radiation follows the founded ABI exactly.
#[inline(never)]
fn register_ranges(
    own_word_base: usize,
    capacity_cells: usize,
    offset: usize,
    count: usize,
    radiation_stride: usize,
    lane: usize,
    completion_stride: usize,
) -> Option<RegisterRanges> {
    let cell_words = carriage::checked_extent_mul(capacity_cells, OWN_CELL_WORDS)?;
    let own_words = carriage::checked_extent_add(OWN_REGISTER_WORDS, cell_words)?;
    let _own_end = carriage::checked_extent_add(own_word_base, own_words)?;
    let radiation = if radiation_stride == body::manifold::RADIATION_WORDS {
        let base = carriage::checked_extent_mul(offset, radiation_stride)?;
        let words = carriage::checked_extent_mul(count, radiation_stride)?;
        let _end = carriage::checked_extent_add(base, words)?;
        WordSpan::new(base, words)
    } else {
        WordSpan::empty()
    };
    let completion = if completion_stride >= body::manifold::COMPLETION_WORDS
        && completion_stride % body::manifold::COMPLETION_WORDS == 0
    {
        let base = carriage::checked_extent_mul(lane, completion_stride)?;
        let _end = carriage::checked_extent_add(base, completion_stride)?;
        WordSpan::new(base, completion_stride)
    } else {
        WordSpan::empty()
    };
    Some(RegisterRanges {
        own: WordSpan::new(own_word_base, own_words),
        radiation,
        completion,
    })
}

/// ONE THREAD, ONE DENSE LINEAGE. Decodes the storage ABI, carves exactly one invocation-owned OWN
/// plane and carrier/K row, then runs the shared trusted device carriage. Standing and raw
/// light are shared read-only. Params:
/// `[axis, cells, lanes, carrier_row_words, stroke_atoms, drive, x_thread_stride,
/// interior_installment]`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn scope_felt(
    standing: *const u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    bytes: *const u32,
    bytes_len: usize,
    lanes: *const u32,
    lanes_len: usize,
    counts: *mut u64,
    counts_len: usize,
    params: *const u32,
    params_len: usize,
) {
    let standing = slice::from_raw_parts(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let carriers = slice::from_raw_parts_mut(carriers, carriers_len);
    let bytes = slice::from_raw_parts(bytes, bytes_len);
    let lanes = slice::from_raw_parts(lanes, lanes_len);
    let counts = slice::from_raw_parts_mut(counts, counts_len);
    let params = slice::from_raw_parts(params, params_len);

    if params.len() < 8 || params[6] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let lane = global_x as u64 + global_y as u64 * params[6] as u64;
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
    let worldline_base = lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let stroke = LineageStroke::dense(
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

    // The checked spans are the invocation's complete single-writer ranges; no local carriage
    // coordinate can name a sibling lane, so `SliceWordSeam`'s plain store needs no arbitration.
    let Some(result) = carry_dense_stroke_trusted::<SliceWordSeam>(
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

    // The four-word count aperture is likewise lane-disjoint; counts remain a shell boundary read.
    let count_at = ranges.count_at;
    aadd_u64(&mut counts[count_at], result.terms.ride);
    aadd_u64(&mut counts[count_at + 1], result.terms.found_this);
    aadd_u64(&mut counts[count_at + 2], result.terms.found_that);
    aadd_u64(&mut counts[count_at + 3], result.terms.dark);
}

/// ONE THREAD, ONE FOUNDED LINEAGE. Carves one reservation-sized OWN chart, one complete carrier/K
/// row, and this lineage's radiation aperture before the shared trusted founded carriage.
/// Params add `radiation_stride, x_thread_stride, interior_installment`; lane rows add
/// `[own_cell_offset, own_axis]`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn scope_founded(
    standing: *const u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    bytes: *const u32,
    bytes_len: usize,
    lanes: *const u32,
    lanes_len: usize,
    counts: *mut u64,
    counts_len: usize,
    params: *const u32,
    params_len: usize,
    radiation: *mut u32,
    radiation_len: usize,
) {
    let standing = slice::from_raw_parts(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let carriers = slice::from_raw_parts_mut(carriers, carriers_len);
    let bytes = slice::from_raw_parts(bytes, bytes_len);
    let lanes = slice::from_raw_parts(lanes, lanes_len);
    let counts = slice::from_raw_parts_mut(counts, counts_len);
    let params = slice::from_raw_parts(params, params_len);
    let radiation = slice::from_raw_parts_mut(radiation, radiation_len);

    if params.len() < 9 || params[7] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let lane = global_x as u64 + global_y as u64 * params[7] as u64;
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
    let worldline_base = lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let radiation_stride = params[6] as usize;
    let Some(ranges) = founded_ranges(own_cell_base, own_axis, offset, count, radiation_stride)
    else {
        return;
    };
    let stroke = LineageStroke::founded(
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

    // The three checked spans are invocation-exclusive; no sibling can name these local coordinates.
    let Some(result) = carry_founded_stroke_trusted::<SliceWordSeam>(
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
    aadd_u64(&mut counts[count_at], result.terms.ride);
    aadd_u64(&mut counts[count_at + 1], result.terms.found_this);
    aadd_u64(&mut counts[count_at + 2], result.terms.found_that);
    aadd_u64(&mut counts[count_at + 3], result.terms.dark);
}

/// ONE THREAD, ONE EVENT-BORN REGISTER LINEAGE. Params are identical to `scope_founded`:
/// `[standing_axis, cells, lanes, carrier_row_words, stroke_atoms, drive, radiation_stride,
/// x_thread_stride, interior_installment, completion_stride]`. `carrier_row_words` remains a
/// fixed-entry ABI word but
/// REGISTER production reads each current's structural span from its lane row:
/// `[offset, count, seed_prev, seed_cur, base_lo, base_hi, own_word_offset, capacity_cells,
/// carrier_word_offset, carrier_row_words]`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn scope_register(
    standing: *const u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    bytes: *const u32,
    bytes_len: usize,
    lanes: *const u32,
    lanes_len: usize,
    counts: *mut u64,
    counts_len: usize,
    params: *const u32,
    params_len: usize,
    radiation: *mut u32,
    radiation_len: usize,
    completion: *mut u32,
    completion_len: usize,
    statuses: *mut u32,
    statuses_len: usize,
) {
    let standing = slice::from_raw_parts(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let carriers = slice::from_raw_parts_mut(carriers, carriers_len);
    let bytes = slice::from_raw_parts(bytes, bytes_len);
    let lanes = slice::from_raw_parts(lanes, lanes_len);
    let counts = slice::from_raw_parts_mut(counts, counts_len);
    let params = slice::from_raw_parts(params, params_len);
    let radiation = slice::from_raw_parts_mut(radiation, radiation_len);
    let completion = slice::from_raw_parts_mut(completion, completion_len);
    let statuses = slice::from_raw_parts_mut(statuses, statuses_len);

    if params.len() < 10 || params[7] == 0 {
        return;
    }
    let (global_x, global_y) = global_xy();
    let lane = global_x as u64 + global_y as u64 * params[7] as u64;
    if lane >= params[2] as u64 {
        return;
    }
    let lane = lane as usize;
    let Some(status_at) = lane.checked_mul(REGISTER_STATUS_WORDS) else {
        return;
    };
    let Some(status_end) = status_at.checked_add(REGISTER_STATUS_WORDS) else {
        return;
    };
    if status_end > statuses.len() {
        return;
    }
    let lane_count = params[2] as usize;
    let cells = params[1] as usize;
    let Some(header) =
        registered_header(lane, lane_count, cells, lanes, counts.len(), carriers.len())
    else {
        return;
    };
    let lane_at = header.lane_at;
    let offset = lanes[lane_at] as usize;
    let count = lanes[lane_at + 1] as usize;
    let own_word_base = lanes[lane_at + 6] as usize;
    let capacity_cells = lanes[lane_at + 7] as usize;
    let worldline_base = lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let radiation_stride = params[6] as usize;
    let completion_stride = params[9] as usize;
    let Some(ranges) = register_ranges(
        own_word_base,
        capacity_cells,
        offset,
        count,
        radiation_stride,
        lane,
        completion_stride,
    ) else {
        return;
    };
    let stroke = LineageStroke::registered(
        params[0] as i64,
        cells,
        capacity_cells,
        offset,
        count,
        lanes[lane_at + 2],
        lanes[lane_at + 3],
        worldline_base,
        params[4] as usize,
        params[5],
        radiation_stride,
    )
    .with_interior_installment(params[8] as usize)
    .with_completion_stride(completion_stride);

    let Some(result) = carry_register_stroke_trusted_with_completion::<SliceWordSeam>(
        standing,
        owns,
        ranges.own,
        carriers,
        header.carrier,
        bytes,
        radiation,
        ranges.radiation,
        completion,
        ranges.completion,
        stroke,
    ) else {
        return;
    };

    let count_at = header.count_at;
    aadd_u64(&mut counts[count_at], result.terms.ride);
    aadd_u64(&mut counts[count_at + 1], result.terms.found_this);
    aadd_u64(&mut counts[count_at + 2], result.terms.found_that);
    aadd_u64(&mut counts[count_at + 3], result.terms.dark);
    let (kind, old_axis, new_axis) = match result.status {
        RegisterStrokeStatus::Complete => (REGISTER_STATUS_COMPLETE, 0, 0),
        RegisterStrokeStatus::Continue => (REGISTER_STATUS_CONTINUE, 0, 0),
        RegisterStrokeStatus::NeedsOwnRecast { old_axis, new_axis } => {
            (REGISTER_STATUS_NEEDS_OWN_RECAST, old_axis, new_axis)
        }
        RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => (
            REGISTER_STATUS_NEEDS_CARRIER_REBASE,
            required_depth as u32,
            (required_depth >> 32) as u32,
        ),
    };
    astore_u32(
        &mut statuses[status_at + REGISTER_STATUS_OLD_AXIS],
        old_axis,
    );
    astore_u32(
        &mut statuses[status_at + REGISTER_STATUS_NEW_AXIS],
        new_axis,
    );
    // The kind is the terminal store. A shell/layout rejection therefore leaves the caller's
    // invalid sentinel untouched instead of masquerading as a completed stroke.
    astore_u32(&mut statuses[status_at + REGISTER_STATUS_KIND], kind);
}

/// ONE BLOCK, ONE EVENT-BORN REGISTER LINEAGE. The block's derived REGISTER extent forms the
/// active enclosure's immutable contacts together; thread zero alone carries their chronological
/// deeds, K, enclosure mutation, radiation, and completion. The final scratch pair is transient
/// apparatus and has `CONTACT_SURFACE_WORDS` words per lineage.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn scope_register_surface(
    standing: *const u32,
    standing_len: usize,
    owns: *mut u32,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    bytes: *const u32,
    bytes_len: usize,
    lanes: *const u32,
    lanes_len: usize,
    counts: *mut u64,
    counts_len: usize,
    params: *const u32,
    params_len: usize,
    radiation: *mut u32,
    radiation_len: usize,
    completion: *mut u32,
    completion_len: usize,
    statuses: *mut u32,
    statuses_len: usize,
    contact_words: *mut u32,
    contact_words_len: usize,
) {
    let params = slice::from_raw_parts(params, params_len);
    let lanes = slice::from_raw_parts(lanes, lanes_len);
    if params.len() < 10
        || unsafe { nvptx::_block_dim_x() } != register::REGISTER
        || unsafe { nvptx::_block_dim_y() } != 1
        || unsafe { nvptx::_block_dim_z() } != 1
    {
        return;
    }
    let lane = unsafe { nvptx::_block_idx_x() } as u64
        + unsafe { nvptx::_block_idx_y() } as u64 * unsafe { nvptx::_grid_dim_x() } as u64;
    if lane >= params[2] as u64 {
        return;
    }
    let lane = lane as usize;
    let worker = unsafe { nvptx::_thread_idx_x() } as usize;
    let Some(status_at) = lane.checked_mul(REGISTER_STATUS_WORDS) else {
        return;
    };
    let Some(status_end) = status_at.checked_add(REGISTER_STATUS_WORDS) else {
        return;
    };
    if status_end > statuses_len {
        return;
    }
    let lane_count = params[2] as usize;
    let cells = params[1] as usize;
    let Some(header) = registered_header(lane, lane_count, cells, lanes, counts_len, carriers_len)
    else {
        return;
    };
    let lane_at = header.lane_at;
    let offset = lanes[lane_at] as usize;
    let count = lanes[lane_at + 1] as usize;
    let own_word_base = lanes[lane_at + 6] as usize;
    let capacity_cells = lanes[lane_at + 7] as usize;
    let worldline_base = lanes[lane_at + 4] as u64 | ((lanes[lane_at + 5] as u64) << 32);
    let radiation_stride = params[6] as usize;
    let completion_stride = params[9] as usize;
    let Some(ranges) = register_ranges(
        own_word_base,
        capacity_cells,
        offset,
        count,
        radiation_stride,
        lane,
        completion_stride,
    ) else {
        return;
    };
    let Some(mut surface) =
        (unsafe { CudaRegisterContactSurface::form(contact_words, contact_words_len, lane) })
    else {
        return;
    };

    if worker != 0 {
        let carriers = slice::from_raw_parts(carriers as *const u32, carriers_len);
        unsafe { surface.worker_loop(carriers, worker) };
        return;
    }

    let standing = slice::from_raw_parts(standing, standing_len);
    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let carriers = slice::from_raw_parts_mut(carriers, carriers_len);
    let bytes = slice::from_raw_parts(bytes, bytes_len);
    let counts = slice::from_raw_parts_mut(counts, counts_len);
    let radiation = slice::from_raw_parts_mut(radiation, radiation_len);
    let completion = slice::from_raw_parts_mut(completion, completion_len);
    let statuses = slice::from_raw_parts_mut(statuses, statuses_len);
    let stroke = LineageStroke::registered(
        params[0] as i64,
        cells,
        capacity_cells,
        offset,
        count,
        lanes[lane_at + 2],
        lanes[lane_at + 3],
        worldline_base,
        params[4] as usize,
        params[5],
        radiation_stride,
    )
    .with_interior_installment(params[8] as usize)
    .with_completion_stride(completion_stride);

    let result = carry_register_stroke_trusted_with_completion_surface::<SliceWordSeam, _>(
        standing,
        owns,
        ranges.own,
        carriers,
        header.carrier,
        bytes,
        radiation,
        ranges.radiation,
        completion,
        ranges.completion,
        stroke,
        &mut surface,
    );
    unsafe { surface.stop() };
    let Some(result) = result else {
        return;
    };

    let count_at = header.count_at;
    aadd_u64(&mut counts[count_at], result.terms.ride);
    aadd_u64(&mut counts[count_at + 1], result.terms.found_this);
    aadd_u64(&mut counts[count_at + 2], result.terms.found_that);
    aadd_u64(&mut counts[count_at + 3], result.terms.dark);
    let (kind, old_axis, new_axis) = match result.status {
        RegisterStrokeStatus::Complete => (REGISTER_STATUS_COMPLETE, 0, 0),
        RegisterStrokeStatus::Continue => (REGISTER_STATUS_CONTINUE, 0, 0),
        RegisterStrokeStatus::NeedsOwnRecast { old_axis, new_axis } => {
            (REGISTER_STATUS_NEEDS_OWN_RECAST, old_axis, new_axis)
        }
        RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => (
            REGISTER_STATUS_NEEDS_CARRIER_REBASE,
            required_depth as u32,
            (required_depth >> 32) as u32,
        ),
    };
    astore_u32(
        &mut statuses[status_at + REGISTER_STATUS_OLD_AXIS],
        old_axis,
    );
    astore_u32(
        &mut statuses[status_at + REGISTER_STATUS_NEW_AXIS],
        new_axis,
    );
    astore_u32(&mut statuses[status_at + REGISTER_STATUS_KIND], kind);
}

// --- one contemporary live-current event --------------------------------------------------------

struct EventStanding<'a> {
    words: &'a [u32],
    axis: u32,
    cells: usize,
}

impl EventStanding<'_> {
    fn new(words: &[u32], axis: u32) -> Option<EventStanding<'_>> {
        if axis == 0 || !axis.is_power_of_two() || axis > (1 << 16) {
            return None;
        }
        let cells = *words.get(event_cuda::STANDING_CELLS)? as usize;
        let required = event_cuda::STANDING_HEADER_WORDS
            .checked_add(cells.checked_mul(event_cuda::STANDING_ROW_WORDS)?)?;
        if words.len() != required {
            return None;
        }
        let extent = (axis as u64).checked_mul(axis as u64)?;
        let mut previous = None;
        let mut row = 0usize;
        while row < cells {
            let at = event_cuda::STANDING_HEADER_WORDS + row * event_cuda::STANDING_ROW_WORDS;
            let grip = words[at + event_cuda::STANDING_ROW_GRIP];
            let form =
                RegionalForm::unpack_compact_checked(words, at + event_cuda::STANDING_ROW_FORM)
                    .ok()?;
            if grip as u64 >= extent
                || !form.occupied()
                || previous.is_some_and(|prior| prior >= grip)
            {
                return None;
            }
            previous = Some(grip);
            row += 1;
        }
        Some(EventStanding { words, axis, cells })
    }

    fn form_at_grip(&self, grip: u32) -> RegionalForm {
        let mut first = 0usize;
        let mut after = self.cells;
        while first < after {
            let middle = first + (after - first) / 2;
            let at = event_cuda::STANDING_HEADER_WORDS + middle * event_cuda::STANDING_ROW_WORDS;
            let found = self.words[at + event_cuda::STANDING_ROW_GRIP];
            if found < grip {
                first = middle + 1;
            } else {
                after = middle;
            }
        }
        if first < self.cells {
            let at = event_cuda::STANDING_HEADER_WORDS + first * event_cuda::STANDING_ROW_WORDS;
            if self.words[at + event_cuda::STANDING_ROW_GRIP] == grip {
                return RegionalForm::unpack_compact_trusted(
                    self.words,
                    at + event_cuda::STANDING_ROW_FORM,
                );
            }
        }
        RegionalForm::UNBORN
    }
}

impl StandingQuery for EventStanding<'_> {
    fn receiver_rank(&self) -> u64 {
        self.axis.trailing_zeros() as u64
    }

    fn form_at_position(&self, position: body::place::Place) -> Option<RegionalForm> {
        Some(self.form_at_grip(body::place::ground(position, self.axis as i64)))
    }

    fn form_at_flat_grip(&self, grip: u32) -> Option<RegionalForm> {
        Some(self.form_at_grip(grip))
    }
}

/// One lane forms one co-present regional contact from the same immutable receiver-before field.
/// No lane owns or mutates the lineage carrier. The later `lineage_event` launch remains the sole
/// carrier writer, while the live machine performs the canonical cpu-resident graded-cell
/// junction fold over these exact returned contacts.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn regional_contacts(
    standing_words: *const u32,
    standing_words_len: usize,
    standing_axis: u32,
    receiver_words: *const u32,
    receiver_words_len: usize,
    directed_events: *const u32,
    directed_events_len: usize,
    directed_contacts: *mut u32,
    directed_contacts_len: usize,
    statuses: *mut u32,
    statuses_len: usize,
) {
    let (x, y) = unsafe { global_xy() };
    if y != 0 || directed_events_len % event_cuda::DIRECTED_EVENT_WORDS != 0 {
        return;
    }
    let work = directed_events_len / event_cuda::DIRECTED_EVENT_WORDS;
    let lane = x as usize;
    if lane >= work || statuses_len != work {
        return;
    }
    let statuses = slice::from_raw_parts_mut(statuses, statuses_len);
    if receiver_words_len != event_cuda::RECEIVER_WORDS
        || directed_contacts_len != work * event_cuda::DIRECTED_CONTACT_WORDS
    {
        statuses[lane] = event_cuda::REGIONAL_STATUS_STRUCTURE;
        return;
    }
    let standing_words = slice::from_raw_parts(standing_words, standing_words_len);
    let Some(standing) = EventStanding::new(standing_words, standing_axis) else {
        statuses[lane] = event_cuda::REGIONAL_STATUS_STRUCTURE;
        return;
    };
    let receiver_words = slice::from_raw_parts(receiver_words, receiver_words_len);
    let mut receiver_row = [0u32; event_cuda::RECEIVER_WORDS];
    receiver_row.copy_from_slice(receiver_words);
    let Some(receiver) = event_cuda::ReceiverRow::from_words(receiver_row) else {
        statuses[lane] = event_cuda::REGIONAL_STATUS_STRUCTURE;
        return;
    };
    let directed_events = slice::from_raw_parts(directed_events, directed_events_len);
    let input_at = lane * event_cuda::DIRECTED_EVENT_WORDS;
    let mut directed_row = [0u32; event_cuda::DIRECTED_EVENT_WORDS];
    directed_row
        .copy_from_slice(&directed_events[input_at..input_at + event_cuda::DIRECTED_EVENT_WORDS]);
    let Some(directed) = event_cuda::DirectedEventRow::from_words(directed_row) else {
        statuses[lane] = event_cuda::REGIONAL_STATUS_STRUCTURE;
        return;
    };
    let Some(contact) = directed_event_contact_over_standing(
        &standing,
        receiver.receiver(),
        directed.from(),
        directed.to(),
    ) else {
        statuses[lane] = event_cuda::REGIONAL_STATUS_QUERY_REFUSED;
        return;
    };
    let Some(row) = event_cuda::DirectedContactRow::new(contact) else {
        statuses[lane] = event_cuda::REGIONAL_STATUS_STRUCTURE;
        return;
    };
    let directed_contacts = slice::from_raw_parts_mut(directed_contacts, directed_contacts_len);
    let output_at = lane * event_cuda::DIRECTED_CONTACT_WORDS;
    directed_contacts[output_at..output_at + event_cuda::DIRECTED_CONTACT_WORDS]
        .copy_from_slice(&row.words());
    statuses[lane] = event_cuda::REGIONAL_STATUS_COMPLETE;
}

struct EventOwn<'a> {
    cells: &'a mut [SparseOwnCell],
    required: usize,
}

impl SparseOwnStorage for EventOwn<'_> {
    fn reset(&mut self) -> bool {
        self.required = 0;
        self.cells.reset()
    }

    fn as_slice(&self) -> &[SparseOwnCell] {
        SparseOwnStorage::as_slice(self.cells)
    }

    fn live_slice_mut(&mut self, live: usize) -> Option<&mut [SparseOwnCell]> {
        self.cells.live_slice_mut(live)
    }

    fn insert_at(&mut self, live: usize, at: usize, cell: SparseOwnCell) -> bool {
        if live >= self.cells.len() {
            self.required = self.required.max(live.saturating_add(1));
            return false;
        }
        self.cells.insert_at(live, at, cell)
    }

    fn remove_at(&mut self, live: usize, at: usize) -> bool {
        self.cells.remove_at(live, at)
    }
}

struct EventCarrier<'a> {
    words: &'a mut [u32],
    depth: usize,
    max_depth: usize,
    overflow_words: &'a mut [u32],
    overflow_counts: &'a mut [u32],
    overflow_capacity: usize,
    required_depth: usize,
    required_overflow: usize,
}

impl EventCarrier<'_> {
    fn node_at(&self, depth: usize, at: usize) -> Option<usize> {
        depth
            .checked_mul(self.overflow_capacity)?
            .checked_add(at)?
            .checked_mul(NODE_WORDS)
    }
}

impl CarrierStorage for EventCarrier<'_> {
    fn words(&self) -> &[u32] {
        &self.words[..self.depth * ENCLOSURE_WORDS]
    }

    fn words_mut(&mut self) -> &mut [u32] {
        let extent = self.depth * ENCLOSURE_WORDS;
        &mut self.words[..extent]
    }

    fn ensure_depth(&mut self, depth: usize) -> CarrierGrowth {
        if depth <= self.depth {
            return CarrierGrowth::Present;
        }
        if depth > self.max_depth {
            self.required_depth = self.required_depth.max(depth);
            return CarrierGrowth::Refused;
        }
        let first = self.depth * ENCLOSURE_WORDS;
        let after = depth * ENCLOSURE_WORDS;
        for word in &mut self.words[first..after] {
            *word = 0;
        }
        for count in &mut self.overflow_counts[self.depth..depth] {
            *count = 0;
        }
        self.depth = depth;
        CarrierGrowth::Present
    }

    fn co_present_overflow_len(&self, depth: usize) -> usize {
        self.overflow_counts.get(depth).copied().unwrap_or(0) as usize
    }

    fn co_present_overflow_node(&self, depth: usize, at: usize) -> Option<Node> {
        if at >= self.co_present_overflow_len(depth) {
            return None;
        }
        let word = self.node_at(depth, at)?;
        packed_node_is_canonical(self.overflow_words, word)
            .then(|| unpack_node(self.overflow_words, word))
    }

    fn append_co_present_overflow(&mut self, depth: usize, node: Node) -> CarrierGrowth {
        if depth >= self.depth {
            return CarrierGrowth::Refused;
        }
        let at = self.overflow_counts[depth] as usize;
        if at >= self.overflow_capacity {
            self.required_overflow = self.required_overflow.max(at.saturating_add(1));
            return CarrierGrowth::Refused;
        }
        let Some(base) = self.node_at(depth, at) else {
            return CarrierGrowth::Refused;
        };
        let mut word = 0usize;
        while word < NODE_WORDS {
            self.overflow_words[base + word] = node_packed_word(node, word);
            word += 1;
        }
        self.overflow_counts[depth] += 1;
        CarrierGrowth::Present
    }

    fn clear_co_present_overflow(&mut self, depth: usize) -> CarrierGrowth {
        if depth >= self.depth {
            return CarrierGrowth::Refused;
        }
        self.overflow_counts[depth] = 0;
        CarrierGrowth::Present
    }

    fn legacy_projection_complete(&self) -> bool {
        !self.overflow_counts[..self.depth]
            .iter()
            .any(|count| *count != 0)
    }
}

struct EventEmissionTarget<'a> {
    words: &'a mut [u32],
    capacity: usize,
    emitted: usize,
    invalid: bool,
}

impl body::manifold::FeltEmissionTarget for EventEmissionTarget<'_> {
    fn emit(&mut self, emission: body::manifold::FeltEmission) {
        let ordinal = self.emitted;
        self.emitted = self.emitted.saturating_add(1);
        if ordinal >= self.capacity {
            return;
        }
        let Some(row) = DeedEmission::new(emission, 0, 1) else {
            self.invalid = true;
            return;
        };
        let at = ordinal * DEED_WORDS;
        self.words[at..at + DEED_WORDS].copy_from_slice(&row.words());
    }
}

struct EventRelationIncidence<'a> {
    words: &'a [u32],
    relations: usize,
}

impl EventIncidence for EventRelationIncidence<'_> {
    fn len(&self) -> usize {
        self.relations
    }

    fn relation(&self, at: usize) -> Cog {
        num::read_cog(self.words, at * COG_WORDS)
    }
}

fn event_status(control: &mut [u32], kind: u32) {
    control[event_cuda::CONTROL_STATUS + event_cuda::STATUS_KIND] = kind;
}

fn event_put_u64(words: &mut [u32], lo: usize, hi: usize, value: u64) {
    words[lo] = value as u32;
    words[hi] = (value >> 32) as u32;
}

/// Follow the resident feature-incidence links and publish only a bounded caused handle aperture.
///
/// Feature incidence is append-only and each head points toward older sections. The one physical
/// selector therefore performs an exact descending multiway merge of those resident lists. Equal
/// section handles across feature lists advance together, so complete-population testimony counts
/// the union without constructing or returning an all-section population. The first `aperture`
/// handles remain in the returned body; no role, chronology, semantic rank, or dominance law enters
/// the selection.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn text_incidence_select(
    query_words: *mut u32,
    query_words_len: usize,
    feature_heads: *const u32,
    feature_heads_len: usize,
    feature_nodes: *const u32,
    feature_nodes_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    active_sections: u32,
    active_features: u32,
) {
    let (x, y) = unsafe { global_xy() };
    if x != 0
        || y != 0
        || query_words_len < text_cuda::HEADER_WORDS
        || output_words_len < text_cuda::RETURN_HEADER_WORDS
        || feature_heads_len < active_features as usize
        || feature_nodes_len % text_cuda::FEATURE_NODE_WORDS != 0
    {
        return;
    }
    let query = slice::from_raw_parts_mut(query_words, query_words_len);
    let aperture = query[text_cuda::APERTURE] as usize;
    let leader_features = query[text_cuda::LEADER_FEATURES] as usize;
    let query_transports = query[text_cuda::QUERY_TRANSPORTS] as usize;
    let feature_words = query[text_cuda::FEATURE_MASK_WORDS] as usize;
    let transport_words = query[text_cuda::TRANSPORT_MASK_WORDS] as usize;
    let leader_features_at = query[text_cuda::LEADER_FEATURES_AT] as usize;
    let query_transports_at = query[text_cuda::QUERY_TRANSPORTS_AT] as usize;
    let cursors_at = query[text_cuda::FEATURE_CURSORS_AT] as usize;
    let transport_query_words = match query_transports.checked_mul(text_cuda::TRANSPORT_WORDS) {
        Some(words) => words,
        None => return,
    };
    let row_words = match feature_words
        .checked_add(transport_words)
        .and_then(|words| words.checked_add(text_cuda::RETURN_MASK_AT))
    {
        Some(words) if words > text_cuda::RETURN_MASK_AT => words,
        _ => return,
    };
    let expected_output = match aperture
        .checked_mul(row_words)
        .and_then(|words| words.checked_add(text_cuda::RETURN_HEADER_WORDS))
    {
        Some(words) => words,
        None => return,
    };
    if aperture == 0
        || aperture > active_sections as usize
        || leader_features == 0
        || query[text_cuda::VERSION] != text_cuda::LAYOUT_VERSION
        || query[text_cuda::TOTAL_WORDS] as usize != query_words_len
        || query[text_cuda::EPOCH] == 0
        || feature_words != text_cuda::mask_words(leader_features)
        || transport_words != text_cuda::mask_words(query_transports)
        || leader_features_at != text_cuda::HEADER_WORDS
        || query_transports_at != leader_features_at.saturating_add(leader_features)
        || cursors_at != query_transports_at.saturating_add(transport_query_words)
        || query_words_len != cursors_at.saturating_add(leader_features)
        || output_words_len != expected_output
    {
        return;
    }

    let heads = slice::from_raw_parts(feature_heads, feature_heads_len);
    let nodes = slice::from_raw_parts(feature_nodes, feature_nodes_len);
    let output = slice::from_raw_parts_mut(output_words, output_words_len);
    output[text_cuda::RETURN_COMPLETE_POPULATION] = 0;
    output[text_cuda::RETURN_HANDLE_POPULATION] = 0;
    let mut returned_at = 0usize;
    while returned_at < aperture {
        output[text_cuda::RETURN_HEADER_WORDS
            + returned_at * row_words
            + text_cuda::RETURN_SECTION_HANDLE] = text_cuda::OPEN_LINK;
        returned_at += 1;
    }
    let mut feature_at = 0usize;
    while feature_at < leader_features {
        let feature = query[leader_features_at + feature_at] as usize;
        if feature >= active_features as usize {
            return;
        }
        query[cursors_at + feature_at] = heads[feature];
        feature_at += 1;
    }

    let node_population = feature_nodes_len / text_cuda::FEATURE_NODE_WORDS;
    let mut complete = 0usize;
    let mut returned = 0usize;
    loop {
        let mut next_section = text_cuda::OPEN_LINK;
        feature_at = 0;
        while feature_at < leader_features {
            let cursor = query[cursors_at + feature_at];
            if cursor != text_cuda::OPEN_LINK {
                let node = cursor as usize;
                if node >= node_population {
                    output[text_cuda::RETURN_COMPLETE_POPULATION] = 0;
                    output[text_cuda::RETURN_HANDLE_POPULATION] = 0;
                    return;
                }
                let section =
                    nodes[node * text_cuda::FEATURE_NODE_WORDS + text_cuda::FEATURE_NODE_SECTION];
                if section >= active_sections {
                    output[text_cuda::RETURN_COMPLETE_POPULATION] = 0;
                    output[text_cuda::RETURN_HANDLE_POPULATION] = 0;
                    return;
                }
                if next_section == text_cuda::OPEN_LINK || section > next_section {
                    next_section = section;
                }
            }
            feature_at += 1;
        }
        if next_section == text_cuda::OPEN_LINK {
            break;
        }
        complete += 1;
        if returned < aperture {
            output[text_cuda::RETURN_HEADER_WORDS
                + returned * row_words
                + text_cuda::RETURN_SECTION_HANDLE] = next_section;
            returned += 1;
        }
        feature_at = 0;
        while feature_at < leader_features {
            let cursor = query[cursors_at + feature_at];
            if cursor != text_cuda::OPEN_LINK {
                let node = cursor as usize;
                let node_at = node * text_cuda::FEATURE_NODE_WORDS;
                if nodes[node_at + text_cuda::FEATURE_NODE_SECTION] == next_section {
                    query[cursors_at + feature_at] = nodes[node_at + text_cuda::FEATURE_NODE_NEXT];
                }
            }
            feature_at += 1;
        }
    }
    output[text_cuda::RETURN_COMPLETE_POPULATION] = complete as u32;
    output[text_cuda::RETURN_HANDLE_POPULATION] = returned as u32;
}

/// Restrict one resident-selected section handle per lane against the complete sparse query.
/// Every output bit is exact set incidence. The handles were emitted by the resident incidence
/// owner immediately before this launch on the same stream.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn text_section_restrict(
    query_words: *const u32,
    query_words_len: usize,
    section_rows: *const u32,
    section_rows_len: usize,
    section_features: *const u32,
    section_features_len: usize,
    section_tokens: *const u32,
    section_tokens_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    active_sections: u32,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if query_words_len < text_cuda::HEADER_WORDS
        || section_rows_len
            < match (active_sections as usize).checked_mul(text_cuda::SECTION_ROW_WORDS) {
                Some(words) => words,
                None => return,
            }
    {
        return;
    }
    let query = slice::from_raw_parts(query_words, query_words_len);
    let aperture = query[text_cuda::APERTURE] as usize;
    let leader_features = query[text_cuda::LEADER_FEATURES] as usize;
    let query_transports = query[text_cuda::QUERY_TRANSPORTS] as usize;
    let feature_words = query[text_cuda::FEATURE_MASK_WORDS] as usize;
    let transport_words = query[text_cuda::TRANSPORT_MASK_WORDS] as usize;
    let leader_features_at = query[text_cuda::LEADER_FEATURES_AT] as usize;
    let query_transports_at = query[text_cuda::QUERY_TRANSPORTS_AT] as usize;
    let cursors_at = query[text_cuda::FEATURE_CURSORS_AT] as usize;
    let transport_query_words = match query_transports.checked_mul(text_cuda::TRANSPORT_WORDS) {
        Some(words) => words,
        None => return,
    };
    if lane >= aperture
        || aperture == 0
        || aperture > active_sections as usize
        || query[text_cuda::VERSION] != text_cuda::LAYOUT_VERSION
        || query[text_cuda::TOTAL_WORDS] as usize != query_words_len
        || query[text_cuda::EPOCH] == 0
        || feature_words != text_cuda::mask_words(leader_features)
        || transport_words != text_cuda::mask_words(query_transports)
        || leader_features_at != text_cuda::HEADER_WORDS
        || query_transports_at != leader_features_at.saturating_add(leader_features)
        || cursors_at != query_transports_at.saturating_add(transport_query_words)
        || query_words_len != cursors_at.saturating_add(leader_features)
    {
        return;
    }
    let row_words = match feature_words
        .checked_add(transport_words)
        .and_then(|words| words.checked_add(text_cuda::RETURN_MASK_AT))
    {
        Some(words) if words > text_cuda::RETURN_MASK_AT => words,
        _ => return,
    };
    if output_words_len
        != match aperture
            .checked_mul(row_words)
            .and_then(|words| words.checked_add(text_cuda::RETURN_HEADER_WORDS))
        {
            Some(words) => words,
            None => return,
        }
    {
        return;
    }
    let output = slice::from_raw_parts_mut(output_words, output_words_len);
    let returned = output[text_cuda::RETURN_HANDLE_POPULATION] as usize;
    if returned > aperture || lane >= returned {
        return;
    }
    let output_at = text_cuda::RETURN_HEADER_WORDS + lane * row_words;
    let section = output[output_at + text_cuda::RETURN_SECTION_HANDLE] as usize;
    if section >= active_sections as usize {
        return;
    }
    let rows = slice::from_raw_parts(section_rows, section_rows_len);
    let features = slice::from_raw_parts(section_features, section_features_len);
    let tokens = slice::from_raw_parts(section_tokens, section_tokens_len);
    let section_row = section * text_cuda::SECTION_ROW_WORDS;
    let feature_at = rows[section_row + text_cuda::SECTION_FEATURE_AT] as usize;
    let feature_extent = rows[section_row + text_cuda::SECTION_FEATURES] as usize;
    let token_at = rows[section_row + text_cuda::SECTION_TOKEN_AT] as usize;
    let token_extent = rows[section_row + text_cuda::SECTION_TOKENS] as usize;
    if feature_at > features.len()
        || feature_extent > features.len() - feature_at
        || token_at > tokens.len()
        || token_extent > tokens.len() - token_at
    {
        return;
    }

    let mask_at = output_at + text_cuda::RETURN_MASK_AT;
    let mut word = 0usize;
    while word < feature_words + transport_words {
        output[mask_at + word] = 0;
        word += 1;
    }
    let mut query_at = 0usize;
    while query_at < leader_features {
        let query_feature = query[leader_features_at + query_at];
        let mut section_at = 0usize;
        while section_at < feature_extent {
            if features[feature_at + section_at] == query_feature {
                output[mask_at + query_at / u32::BITS as usize] |=
                    1u32 << (query_at % u32::BITS as usize);
                break;
            }
            section_at += 1;
        }
        query_at += 1;
    }
    let mut transport_at = 0usize;
    while transport_at < query_transports {
        let query_at = query_transports_at + transport_at * text_cuda::TRANSPORT_WORDS;
        let source = query[query_at];
        let target = query[query_at + 1];
        let mut token = 1usize;
        while token < token_extent {
            if tokens[token_at + token - 1] == source && tokens[token_at + token] == target {
                output[mask_at + feature_words + transport_at / u32::BITS as usize] |=
                    1u32 << (transport_at % u32::BITS as usize);
                break;
            }
            token += 1;
        }
        transport_at += 1;
    }
}

/// **The law one lane enacts: one current of one contemporary event, together with every supplied
/// hand arriving at that current.**
///
/// This is the body, and it wears two entry shells — [`lineage_event`], which enacts a single
/// current on lane zero, and [`lineage_event_population`], which enacts a whole co-present
/// population one lane per current. The crate's own design is stated in its header: *one mouth*,
/// with only the entry shells re-expressed. Before 2026-08-10 there was one shell and it was the
/// single-current one, so a contemporary population of `n` currents cost `n` launches of one lane
/// each and the card ran as a very slow single core.
///
/// All storage is reusable apparatus for the current this call enacts. A resource status reports
/// actual pressure and the cpu retries from the unchanged live predecessor with a larger mouth.
unsafe fn enact_one_lineage(
    standing_words: *const u32,
    standing_words_len: usize,
    control_words: *mut u32,
    control_words_len: usize,
    relation_words: *const u32,
    relation_words_len: usize,
    owns: *mut SparseOwnCell,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    overflow_nodes: *mut u32,
    overflow_nodes_len: usize,
    overflow_counts: *mut u32,
    overflow_counts_len: usize,
    directed_events: *const u32,
    directed_events_len: usize,
    directed_contacts: *mut u32,
    directed_contacts_len: usize,
    emissions: *mut u32,
    emissions_len: usize,
    emanation: *mut u32,
    emanation_len: usize,
) {
    if control_words_len != event_cuda::CONTROL_WORDS {
        return;
    }
    let control = slice::from_raw_parts_mut(control_words, control_words_len);
    let params =
        &control[event_cuda::CONTROL_PARAMS..event_cuda::CONTROL_PARAMS + event_cuda::PARAM_WORDS];
    let source_grain = params[event_cuda::PARAM_SOURCE_GRAIN];
    let event_cells = event_cuda::join_u64(
        params,
        event_cuda::PARAM_EVENT_CELLS_LO,
        event_cuda::PARAM_EVENT_CELLS_HI,
    );
    let event_incidences = event_cuda::join_u64(
        params,
        event_cuda::PARAM_EVENT_INCIDENCES_LO,
        event_cuda::PARAM_EVENT_INCIDENCES_HI,
    );
    let event_resolving = event_cuda::join_u64(
        params,
        event_cuda::PARAM_EVENT_RESOLVING_LO,
        event_cuda::PARAM_EVENT_RESOLVING_HI,
    );
    let event_compounds = event_cuda::join_u64(
        params,
        event_cuda::PARAM_EVENT_COMPOUNDS_LO,
        event_cuda::PARAM_EVENT_COMPOUNDS_HI,
    );
    let event_formed = event_cuda::join_u64(
        params,
        event_cuda::PARAM_EVENT_FORMED_LO,
        event_cuda::PARAM_EVENT_FORMED_HI,
    );
    if params[event_cuda::PARAM_VERSION] != event_cuda::LAYOUT_VERSION
        || params[event_cuda::PARAM_MOUNT] > 1
        || params[event_cuda::PARAM_WHOLE_DARK] > 1
        || params[event_cuda::PARAM_ENDING] > 1
        || params[event_cuda::PARAM_COMPLEX] > 1
        || params[event_cuda::PARAM_OWN_CAPACITY] as usize != owns_len
        || params[event_cuda::PARAM_CARRIER_DEPTH] == 0
        || params[event_cuda::PARAM_CARRIER_MAX_DEPTH] < params[event_cuda::PARAM_CARRIER_DEPTH]
        || carriers_len != params[event_cuda::PARAM_CARRIER_MAX_DEPTH] as usize * ENCLOSURE_WORDS
        || overflow_counts_len != params[event_cuda::PARAM_CARRIER_MAX_DEPTH] as usize
        || overflow_nodes_len
            != params[event_cuda::PARAM_CARRIER_MAX_DEPTH] as usize
                * params[event_cuda::PARAM_OVERFLOW_CAPACITY] as usize
                * NODE_WORDS
        || source_grain == 0
        || event_cells == 0
        || event_resolving > event_cells
        || event_compounds > event_cells
        || event_formed > event_incidences
        || (params[event_cuda::PARAM_RELATIONS] == 1) != (params[event_cuda::PARAM_COMPLEX] == 0)
        || params[event_cuda::PARAM_RELATIONS] > 1
        || relation_words_len != params[event_cuda::PARAM_RELATIONS] as usize * COG_WORDS
        || directed_events_len
            != params[event_cuda::PARAM_DIRECTED_EVENTS] as usize * event_cuda::DIRECTED_EVENT_WORDS
        || directed_contacts_len
            != params[event_cuda::PARAM_DIRECTED_EVENTS] as usize
                * event_cuda::DIRECTED_CONTACT_WORDS
        || emissions_len != params[event_cuda::PARAM_EMISSION_CAPACITY] as usize * DEED_WORDS
        || emanation_len != event_cuda::EMANATION_WORDS
    {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    }
    let mut event_words = [0u32; event_cuda::EVENT_WORDS];
    event_words.copy_from_slice(
        &control[event_cuda::CONTROL_EVENT..event_cuda::CONTROL_EVENT + event_cuda::EVENT_WORDS],
    );
    let Some(event) = event_cuda::EventRow::from_words(event_words) else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    let relation_words = slice::from_raw_parts(relation_words, relation_words_len);
    let relation_extent = params[event_cuda::PARAM_RELATIONS] as usize;
    let mut resolving_relations = 0usize;
    let mut relation_at = 0usize;
    while relation_at < relation_extent {
        let word = relation_at * COG_WORDS;
        if !num::packed_cog_is_canonical(relation_words, word) {
            event_status(control, event_cuda::STATUS_STRUCTURE);
            return;
        }
        if num::read_cog(relation_words, word).mag != 0 {
            resolving_relations += 1;
        }
        relation_at += 1;
    }
    if params[event_cuda::PARAM_COMPLEX] == 0
        && (resolving_relations == 0) != (params[event_cuda::PARAM_WHOLE_DARK] == 1)
    {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    }
    if params[event_cuda::PARAM_COMPLEX] == 1 && params[event_cuda::PARAM_WHOLE_DARK] != 0 {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    }
    let incidence = EventRelationIncidence {
        words: relation_words,
        relations: relation_extent,
    };
    let standing_words = slice::from_raw_parts(standing_words, standing_words_len);
    let Some(standing) =
        EventStanding::new(standing_words, params[event_cuda::PARAM_STANDING_AXIS])
    else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };

    let owns = slice::from_raw_parts_mut(owns, owns_len);
    let carriers = slice::from_raw_parts_mut(carriers, carriers_len);
    let overflow_nodes = slice::from_raw_parts_mut(overflow_nodes, overflow_nodes_len);
    let overflow_counts = slice::from_raw_parts_mut(overflow_counts, overflow_counts_len);
    let directed_events = slice::from_raw_parts(directed_events, directed_events_len);
    let directed_contacts = slice::from_raw_parts_mut(directed_contacts, directed_contacts_len);
    let emissions = slice::from_raw_parts_mut(emissions, emissions_len);
    let emanation_words = slice::from_raw_parts_mut(emanation, emanation_len);
    let mut own = EventOwn {
        cells: owns,
        required: 0,
    };
    let mut carrier = EventCarrier {
        words: carriers,
        depth: params[event_cuda::PARAM_CARRIER_DEPTH] as usize,
        max_depth: params[event_cuda::PARAM_CARRIER_MAX_DEPTH] as usize,
        overflow_words: overflow_nodes,
        overflow_counts,
        overflow_capacity: params[event_cuda::PARAM_OVERFLOW_CAPACITY] as usize,
        required_depth: 0,
        required_overflow: 0,
    };
    let mut output = EventEmissionTarget {
        words: emissions,
        capacity: params[event_cuda::PARAM_EMISSION_CAPACITY] as usize,
        emitted: 0,
        invalid: false,
    };
    let header_words =
        &control[event_cuda::CONTROL_HEADER..event_cuda::CONTROL_HEADER + CARRIER_HEADER_WORDS];
    let header = if params[event_cuda::PARAM_MOUNT] == 1 {
        LiveBodyHeader::from_words_checked(header_words)
    } else {
        None
    };
    if params[event_cuda::PARAM_MOUNT] == 1 && header.is_none() {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    }
    let cursor = header.map_or(0, LiveBodyHeader::cursor);
    let Some(next_cursor) = cursor.checked_add(1) else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    let body = match header {
        Some(header) => ErosBody::resume_standing_world_storage_from_live_header(
            &standing,
            &mut own,
            header,
            &mut carrier,
        ),
        None => ErosBody::over_standing_world_storage_from_first_difference(
            &standing,
            &mut own,
            event.anchor(),
            &mut carrier,
        ),
    };
    let Some(mut body) = body else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    let Some(receiver) = body.event_receiver_at_source_grain(source_grain) else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    let mut directed_at = 0usize;
    while directed_at < params[event_cuda::PARAM_DIRECTED_EVENTS] as usize {
        let input_at = directed_at * event_cuda::DIRECTED_EVENT_WORDS;
        let mut input_words = [0u32; event_cuda::DIRECTED_EVENT_WORDS];
        input_words.copy_from_slice(
            &directed_events[input_at..input_at + event_cuda::DIRECTED_EVENT_WORDS],
        );
        let Some(directed) = event_cuda::DirectedEventRow::from_words(input_words) else {
            event_status(control, event_cuda::STATUS_STRUCTURE);
            return;
        };
        if directed.to() != event.face().place {
            event_status(control, event_cuda::STATUS_STRUCTURE);
            return;
        }
        let contact = body.directed_event_contact_at_source_grain(
            receiver,
            source_grain,
            directed.from(),
            directed.to(),
        );
        let Some(row) = event_cuda::DirectedContactRow::new(contact) else {
            event_status(control, event_cuda::STATUS_STRUCTURE);
            return;
        };
        let output_at = directed_at * event_cuda::DIRECTED_CONTACT_WORDS;
        directed_contacts[output_at..output_at + event_cuda::DIRECTED_CONTACT_WORDS]
            .copy_from_slice(&row.words());
        directed_at += 1;
    }
    let mut pending_dark = event.pending_dark();
    let mut result = if params[event_cuda::PARAM_WHOLE_DARK] == 1 {
        pending_dark = pending_dark.add(event.action());
        EventEmanation {
            cells: event_cells,
            incidences: event_incidences,
            resolving_cells: 0,
            formed_incidences: event_formed,
            compounds: event_compounds,
            folds: 0,
            receiver,
        }
    } else {
        if pending_dark.mag != 0 {
            body.resolve_dark_action_emitting(pending_dark, &mut output);
            pending_dark = Cog::ZERO;
        }
        if params[event_cuda::PARAM_COMPLEX] == 0 {
            let mut result =
                body.live_event_incidence_emitting(&incidence, event.action(), &mut output);
            result.cells = event_cells;
            result.incidences = event_incidences;
            result.resolving_cells = event_resolving;
            result.formed_incidences = event_formed;
            result.compounds = event_compounds;
            result
        } else {
            let folded = body.live_completed_event_node_at_grain_emitting(
                event.face(),
                source_grain,
                event.action(),
                &mut output,
            );
            EventEmanation {
                cells: event_cells,
                incidences: event_incidences,
                resolving_cells: event_resolving,
                formed_incidences: event_formed,
                compounds: event_compounds,
                folds: u64::from(folded),
                receiver,
            }
        }
    };
    if params[event_cuda::PARAM_ENDING] == 1 && pending_dark.mag != 0 {
        body.resolve_dark_action_emitting(pending_dark, &mut output);
        pending_dark = Cog::ZERO;
    }
    let Some(after_receiver) = body.event_receiver_at_source_grain(source_grain) else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    result.receiver = after_receiver;
    let body_required_depth = body.required_carrier_depth().unwrap_or(0);
    let body_refused = body.resource_refused();
    let own_axis = body.own_axis();
    let own_live = body.sparse_own_cells().map_or(0, <[_]>::len);
    let breath = body.breath();
    let thoughts = body.thoughts();
    let next_header = body.live_header(next_cursor);
    drop(body);

    let required_own = own.required;
    let required_depth = body_required_depth.max(carrier.required_depth);
    let required_overflow = carrier.required_overflow;
    let required_emissions = output.emitted;
    if body_refused
        || required_own > owns_len
        || required_depth > carrier.max_depth
        || required_overflow > carrier.overflow_capacity
        || required_emissions > output.capacity
    {
        let status = event_cuda::CONTROL_STATUS;
        control[status + event_cuda::STATUS_REQUIRED_OWN] = required_own as u32;
        event_put_u64(
            control,
            status + event_cuda::STATUS_REQUIRED_DEPTH_LO,
            status + event_cuda::STATUS_REQUIRED_DEPTH_HI,
            required_depth as u64,
        );
        control[status + event_cuda::STATUS_REQUIRED_OVERFLOW] = required_overflow as u32;
        control[status + event_cuda::STATUS_REQUIRED_EMISSIONS] = required_emissions as u32;
        event_status(control, event_cuda::STATUS_RESOURCE);
        return;
    }
    if output.invalid || own_axis <= 0 || own_axis & (own_axis - 1) != 0 {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    }

    control[event_cuda::CONTROL_HEADER..event_cuda::CONTROL_HEADER + CARRIER_HEADER_WORDS]
        .copy_from_slice(next_header.words());
    event_cuda::write_cog(
        control,
        event_cuda::CONTROL_EVENT + event_cuda::EVENT_PENDING_DARK,
        pending_dark,
    );
    let state = event_cuda::CONTROL_STATE;
    control[state + event_cuda::STATE_OWN_AXIS] = own_axis as u32;
    control[state + event_cuda::STATE_OWN_LIVE] = own_live as u32;
    event_put_u64(
        control,
        state + event_cuda::STATE_RELEASES_LO,
        state + event_cuda::STATE_RELEASES_HI,
        breath.0,
    );
    event_put_u64(
        control,
        state + event_cuda::STATE_NARROWS_LO,
        state + event_cuda::STATE_NARROWS_HI,
        breath.1,
    );
    control[state + event_cuda::STATE_CARRIER_DEPTH] = carrier.depth as u32;
    control[state + event_cuda::STATE_EMISSIONS] = output.emitted as u32;
    control[state + event_cuda::STATE_THOUGHTS] = thoughts;
    let Some(row) = event_cuda::EmanationRow::new(result) else {
        event_status(control, event_cuda::STATUS_STRUCTURE);
        return;
    };
    emanation_words.copy_from_slice(&row.words());
    event_status(control, event_cuda::STATUS_COMPLETE);
}

/// **One current, on lane zero.** The pre-2026-08-10 shape, retained because it is the exact
/// reference the population shell must agree with: a caller that enacts a population and a caller
/// that enacts its currents one at a time must obtain the same standing, the same radiation, and
/// the same carriers.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn lineage_event(
    standing_words: *const u32,
    standing_words_len: usize,
    control_words: *mut u32,
    control_words_len: usize,
    relation_words: *const u32,
    relation_words_len: usize,
    owns: *mut SparseOwnCell,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    overflow_nodes: *mut u32,
    overflow_nodes_len: usize,
    overflow_counts: *mut u32,
    overflow_counts_len: usize,
    directed_events: *const u32,
    directed_events_len: usize,
    directed_contacts: *mut u32,
    directed_contacts_len: usize,
    emissions: *mut u32,
    emissions_len: usize,
    emanation: *mut u32,
    emanation_len: usize,
) {
    let (x, y) = unsafe { global_xy() };
    if x != 0 || y != 0 {
        return;
    }
    unsafe {
        enact_one_lineage(
            standing_words,
            standing_words_len,
            control_words,
            control_words_len,
            relation_words,
            relation_words_len,
            owns,
            owns_len,
            carriers,
            carriers_len,
            overflow_nodes,
            overflow_nodes_len,
            overflow_counts,
            overflow_counts_len,
            directed_events,
            directed_events_len,
            directed_contacts,
            directed_contacts_len,
            emissions,
            emissions_len,
            emanation,
            emanation_len,
        )
    }
}

/// **One lane per current: the whole co-present population in one crossing.**
///
/// The currents of one contemporary event are independent — that is what makes the event
/// contemporary, and `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER…` states the
/// condition exactly: two events are independent only when their complete exact consequences
/// commute. Here they do, and disjointly: **every buffer is a contiguous array of `count`
/// per-current regions, and lane `i` touches only region `i`.** No lane reads or writes another's
/// region, so there is nothing to synchronize and no atomic anywhere on this path.
///
/// **Every stride is derived, not passed.** A region's extent is `len / count` for each buffer, and
/// a length that does not divide is refused rather than rounded — a partial region would place one
/// current's carrier inside another's, which is the absolute-frame defect at the level of memory.
/// The only new datum is `count`, which the cpu reads off the population it is enacting.
///
/// `standing_words` is **shared and read-only**: standing-before is one immutable field every
/// current reads, exactly as `regional_contacts` already treats the receiver row. It is not strided.
///
/// `relation_words` **is** strided, at one `COG_WORDS` region per current — a current whose geometry
/// is a cell carries a relation and one whose geometry is a complex carries none, so the population
/// is not uniform in this buffer. Each lane's *declared* relation extent is read from its own
/// control block as `PARAM_RELATIONS * COG_WORDS`, which is exactly what the body checks, so a
/// complex current is handed a zero extent at its own region's base and a cell current is handed
/// one whole cog. Padding the region uniformly and declaring the extent per lane keeps the body's
/// structural check intact rather than relaxing it for the population.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn lineage_event_population(
    standing_words: *const u32,
    standing_words_len: usize,
    control_words: *mut u32,
    control_words_len: usize,
    relation_words: *const u32,
    relation_words_len: usize,
    owns: *mut SparseOwnCell,
    owns_len: usize,
    carriers: *mut u32,
    carriers_len: usize,
    overflow_nodes: *mut u32,
    overflow_nodes_len: usize,
    overflow_counts: *mut u32,
    overflow_counts_len: usize,
    directed_events: *const u32,
    directed_events_len: usize,
    directed_contacts: *mut u32,
    directed_contacts_len: usize,
    emissions: *mut u32,
    emissions_len: usize,
    emanation: *mut u32,
    emanation_len: usize,
    count: usize,
) {
    let (x, y) = unsafe { global_xy() };
    if y != 0 || count == 0 {
        return;
    }
    let lane = x as usize;
    if lane >= count {
        return;
    }

    // Every region is derived. A buffer whose extent does not divide by the population would give
    // one current a partial region, so it is refused — and refused by every lane, so no lane
    // proceeds on a body another lane has rejected.
    let divides = |len: usize| len % count == 0;
    if !divides(relation_words_len)
        || !divides(control_words_len)
        || !divides(owns_len)
        || !divides(carriers_len)
        || !divides(overflow_nodes_len)
        || !divides(overflow_counts_len)
        || !divides(directed_events_len)
        || !divides(directed_contacts_len)
        || !divides(emissions_len)
        || !divides(emanation_len)
    {
        // Lane zero stamps the structural refusal into its own control block so the cpu reads a
        // named status rather than an unchanged buffer.
        if lane == 0 && control_words_len >= event_cuda::CONTROL_WORDS {
            let control =
                unsafe { slice::from_raw_parts_mut(control_words, event_cuda::CONTROL_WORDS) };
            event_status(control, event_cuda::STATUS_STRUCTURE);
        }
        return;
    }

    let control_stride = control_words_len / count;
    let relation_stride = relation_words_len / count;
    let owns_stride = owns_len / count;
    let carriers_stride = carriers_len / count;
    let overflow_nodes_stride = overflow_nodes_len / count;
    let overflow_counts_stride = overflow_counts_len / count;
    let directed_events_stride = directed_events_len / count;
    let directed_contacts_stride = directed_contacts_len / count;
    let emissions_stride = emissions_len / count;
    let emanation_stride = emanation_len / count;

    // The lane's own declared relation extent, read from the lane's own control block. The body
    // refuses when the two disagree, and that check is what keeps a complex current from being
    // handed a cell's cog.
    if control_stride < event_cuda::CONTROL_PARAMS + event_cuda::PARAM_WORDS {
        return;
    }
    let lane_control =
        unsafe { slice::from_raw_parts(control_words.add(lane * control_stride), control_stride) };
    let lane_relations =
        lane_control[event_cuda::CONTROL_PARAMS + event_cuda::PARAM_RELATIONS] as usize;
    let Some(lane_relation_words) = lane_relations.checked_mul(COG_WORDS) else {
        return;
    };
    if lane_relation_words > relation_stride {
        return;
    }

    unsafe {
        enact_one_lineage(
            standing_words,
            standing_words_len,
            control_words.add(lane * control_stride),
            control_stride,
            relation_words.add(lane * relation_stride),
            lane_relation_words,
            owns.add(lane * owns_stride),
            owns_stride,
            carriers.add(lane * carriers_stride),
            carriers_stride,
            overflow_nodes.add(lane * overflow_nodes_stride),
            overflow_nodes_stride,
            overflow_counts.add(lane * overflow_counts_stride),
            overflow_counts_stride,
            directed_events.add(lane * directed_events_stride),
            directed_events_stride,
            directed_contacts.add(lane * directed_contacts_stride),
            directed_contacts_stride,
            emissions.add(lane * emissions_stride),
            emissions_stride,
            emanation.add(lane * emanation_stride),
            emanation_stride,
        )
    }
}

// --- returned-contact grouping ------------------------------------------------------------------

#[derive(Clone, Copy)]
struct ReturnedContactShape {
    epoch: u32,
    targets: usize,
    occurrences: usize,
    relations: usize,
    mask_words: usize,
    target_row_words: usize,
    occurrence_rows_at: usize,
    output_words: usize,
}

#[inline(always)]
fn returned_contact_shape(
    control: &[u32],
    relation_words_len: usize,
    output_words_len: usize,
) -> Option<ReturnedContactShape> {
    if control.len() != returned_cuda::CONTROL_WORDS
        || control[returned_cuda::CONTROL_VERSION] != returned_cuda::LAYOUT_VERSION
        || control[returned_cuda::CONTROL_EPOCH] == 0
        || control[returned_cuda::CONTROL_TOTAL_WORDS] as usize != returned_cuda::CONTROL_WORDS
    {
        return None;
    }
    let targets = control[returned_cuda::CONTROL_TARGETS] as usize;
    let occurrences = control[returned_cuda::CONTROL_OCCURRENCES] as usize;
    let relations = control[returned_cuda::CONTROL_RELATIONS] as usize;
    let mask_words = returned_cuda::mask_words(occurrences);
    let target_row_words = returned_cuda::target_row_words(occurrences)?;
    let relation_words = relations.checked_mul(returned_cuda::RELATION_WORDS)?;
    let occurrence_rows_at = returned_cuda::occurrence_rows_at(targets, occurrences)?;
    let output_words = returned_cuda::output_words(targets, occurrences)?;
    if control[returned_cuda::CONTROL_OCCURRENCE_MASK_WORDS] as usize != mask_words
        || control[returned_cuda::CONTROL_RELATION_WORDS] as usize != returned_cuda::RELATION_WORDS
        || control[returned_cuda::CONTROL_RELATION_TOTAL_WORDS] as usize != relation_words
        || control[returned_cuda::CONTROL_TARGET_ROW_WORDS] as usize != target_row_words
        || control[returned_cuda::CONTROL_TARGET_ROWS_AT] as usize
            != returned_cuda::OUTPUT_HEADER_WORDS
        || control[returned_cuda::CONTROL_OCCURRENCE_ROW_WORDS] as usize
            != returned_cuda::OCCURRENCE_ROW_WORDS
        || control[returned_cuda::CONTROL_OCCURRENCE_ROWS_AT] as usize != occurrence_rows_at
        || control[returned_cuda::CONTROL_OUTPUT_TOTAL_WORDS] as usize != output_words
        || relation_words_len != relation_words
        || output_words_len != output_words
    {
        return None;
    }
    Some(ReturnedContactShape {
        epoch: control[returned_cuda::CONTROL_EPOCH],
        targets,
        occurrences,
        relations,
        mask_words,
        target_row_words,
        occurrence_rows_at,
        output_words,
    })
}

#[inline(always)]
fn returned_relation_is_valid(row: &[u32], shape: ReturnedContactShape) -> bool {
    let before = row[returned_cuda::RELATION_STOOD_BEFORE];
    let after = row[returned_cuda::RELATION_STANDS_AFTER];
    (row[returned_cuda::RELATION_TARGET] as usize) < shape.targets
        && (row[returned_cuda::RELATION_OCCURRENCE] as usize) < shape.occurrences
        && before <= 1
        && after <= 1
        && before != after
}

/// Group exact returned local movements on the card.
///
/// Lane zero validates and returns the dynamic layout.  The next `targets` lanes each own one
/// complete target row and write its two exact occurrence masks.  The final `occurrences` lanes
/// independently return the disposition of one occurrence over every target.  No intermediate
/// pair matrix leaves the device, and no lane needs an inter-lane barrier or an authored launch
/// extent.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn returned_contact_group(
    control_words: *const u32,
    control_words_len: usize,
    relation_words: *const u32,
    relation_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if control_words_len != returned_cuda::CONTROL_WORDS
        || output_words_len < returned_cuda::OUTPUT_HEADER_WORDS
    {
        return;
    }
    let control = unsafe { slice::from_raw_parts(control_words, control_words_len) };
    let Some(shape) = returned_contact_shape(control, relation_words_len, output_words_len) else {
        if lane == 0 {
            let output = unsafe {
                slice::from_raw_parts_mut(output_words, returned_cuda::OUTPUT_HEADER_WORDS)
            };
            output[returned_cuda::OUTPUT_STATUS] = returned_cuda::STATUS_INVALID;
            output[returned_cuda::OUTPUT_INVALID_RELATION] = returned_cuda::OPEN_RELATION;
        }
        return;
    };
    let work = match 1usize
        .checked_add(shape.targets)
        .and_then(|extent| extent.checked_add(shape.occurrences))
    {
        Some(work) => work,
        None => return,
    };
    if lane >= work {
        return;
    }
    let relations = unsafe { slice::from_raw_parts(relation_words, relation_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };

    if lane == 0 {
        output[returned_cuda::OUTPUT_VERSION] = returned_cuda::LAYOUT_VERSION;
        output[returned_cuda::OUTPUT_EPOCH] = shape.epoch;
        output[returned_cuda::OUTPUT_TARGETS] = shape.targets as u32;
        output[returned_cuda::OUTPUT_OCCURRENCES] = shape.occurrences as u32;
        output[returned_cuda::OUTPUT_RELATIONS] = shape.relations as u32;
        output[returned_cuda::OUTPUT_OCCURRENCE_MASK_WORDS] = shape.mask_words as u32;
        output[returned_cuda::OUTPUT_TARGET_ROW_WORDS] = shape.target_row_words as u32;
        output[returned_cuda::OUTPUT_TARGET_ROWS_AT] = returned_cuda::OUTPUT_HEADER_WORDS as u32;
        output[returned_cuda::OUTPUT_OCCURRENCE_ROW_WORDS] =
            returned_cuda::OCCURRENCE_ROW_WORDS as u32;
        output[returned_cuda::OUTPUT_OCCURRENCE_ROWS_AT] = shape.occurrence_rows_at as u32;
        output[returned_cuda::OUTPUT_TOTAL_WORDS] = shape.output_words as u32;
        output[returned_cuda::OUTPUT_INVALID_RELATION] = returned_cuda::OPEN_RELATION;
        let mut relation = 0usize;
        while relation < shape.relations {
            let at = relation * returned_cuda::RELATION_WORDS;
            let row = &relations[at..at + returned_cuda::RELATION_WORDS];
            if !returned_relation_is_valid(row, shape) {
                output[returned_cuda::OUTPUT_INVALID_RELATION] = relation as u32;
                output[returned_cuda::OUTPUT_STATUS] = returned_cuda::STATUS_INVALID;
                return;
            }
            relation += 1;
        }
        output[returned_cuda::OUTPUT_STATUS] = returned_cuda::STATUS_COMPLETE;
        return;
    }

    if lane <= shape.targets {
        let target = lane - 1;
        let row_at = returned_cuda::OUTPUT_HEADER_WORDS + target * shape.target_row_words;
        let founded_mask_at = returned_cuda::TARGET_WITHDRAWN_MASK_AT + shape.mask_words;
        output[row_at + returned_cuda::TARGET_EPOCH] = shape.epoch;
        output[row_at + returned_cuda::TARGET_ORDINAL] = target as u32;
        let mut mask = 0usize;
        while mask < shape.mask_words * 2 {
            output[row_at + returned_cuda::TARGET_WITHDRAWN_MASK_AT + mask] = 0;
            mask += 1;
        }
        let mut withdrawn = 0u32;
        let mut founded = 0u32;
        let mut invalid = false;
        let mut relation = 0usize;
        while relation < shape.relations {
            let at = relation * returned_cuda::RELATION_WORDS;
            let row = &relations[at..at + returned_cuda::RELATION_WORDS];
            if !returned_relation_is_valid(row, shape) {
                invalid = true;
                relation += 1;
                continue;
            }
            if row[returned_cuda::RELATION_TARGET] as usize != target {
                relation += 1;
                continue;
            }
            let occurrence = row[returned_cuda::RELATION_OCCURRENCE] as usize;
            let word = occurrence / u32::BITS as usize;
            let bit = 1u32 << (occurrence % u32::BITS as usize);
            let withdrawn_at = row_at + returned_cuda::TARGET_WITHDRAWN_MASK_AT + word;
            let founded_at = row_at + founded_mask_at + word;
            if output[withdrawn_at] & bit != 0 || output[founded_at] & bit != 0 {
                // Two rows cannot claim one local target/occurrence movement.
                invalid = true;
                relation += 1;
                continue;
            }
            if row[returned_cuda::RELATION_STOOD_BEFORE] == 1 {
                output[withdrawn_at] |= bit;
                withdrawn = match withdrawn.checked_add(1) {
                    Some(count) => count,
                    None => {
                        invalid = true;
                        withdrawn
                    }
                };
            } else {
                output[founded_at] |= bit;
                founded = match founded.checked_add(1) {
                    Some(count) => count,
                    None => {
                        invalid = true;
                        founded
                    }
                };
            }
            relation += 1;
        }
        output[row_at + returned_cuda::TARGET_WITHDRAWN] = withdrawn;
        output[row_at + returned_cuda::TARGET_FOUNDED] = founded;
        output[row_at + returned_cuda::TARGET_STATUS] = if invalid {
            returned_cuda::STATUS_INVALID
        } else {
            returned_cuda::STATUS_COMPLETE
        };
        return;
    }

    let occurrence = lane - 1 - shape.targets;
    let row_at = shape.occurrence_rows_at + occurrence * returned_cuda::OCCURRENCE_ROW_WORDS;
    output[row_at + returned_cuda::OCCURRENCE_EPOCH] = shape.epoch;
    output[row_at + returned_cuda::OCCURRENCE_ORDINAL] = occurrence as u32;
    let mut withdrawn = 0u32;
    let mut founded = 0u32;
    let mut invalid = false;
    let mut relation = 0usize;
    while relation < shape.relations {
        let at = relation * returned_cuda::RELATION_WORDS;
        let row = &relations[at..at + returned_cuda::RELATION_WORDS];
        if !returned_relation_is_valid(row, shape) {
            invalid = true;
            relation += 1;
            continue;
        }
        if row[returned_cuda::RELATION_OCCURRENCE] as usize == occurrence {
            if row[returned_cuda::RELATION_STOOD_BEFORE] == 1 {
                withdrawn = match withdrawn.checked_add(1) {
                    Some(count) => count,
                    None => {
                        invalid = true;
                        withdrawn
                    }
                };
            } else {
                founded = match founded.checked_add(1) {
                    Some(count) => count,
                    None => {
                        invalid = true;
                        founded
                    }
                };
            }
        }
        relation += 1;
    }
    output[row_at + returned_cuda::OCCURRENCE_WITHDRAWN_TARGETS] = withdrawn;
    output[row_at + returned_cuda::OCCURRENCE_FOUNDED_TARGETS] = founded;
    output[row_at + returned_cuda::OCCURRENCE_STATUS] = if invalid {
        returned_cuda::STATUS_INVALID
    } else {
        returned_cuda::STATUS_COMPLETE
    };
}

// --- sparse returned-contact grouping -----------------------------------------------------------

/// Validate and census a strictly addressed sparse returned-contact population.
///
/// Lane zero returns the exact dynamic layout. One lane per relation validates its local row and
/// the immediately preceding address, copies that row into the returned sparse sheet, and adds its
/// exact target/occurrence disposition. The input order is a presentation chart only; strict
/// adjacency lets the card prove uniqueness without materialising a target×occurrence bitmap.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn returned_contact_sparse_group(
    control_words: *const u32,
    control_words_len: usize,
    relation_words: *const u32,
    relation_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if control_words_len != returned_cuda::SPARSE_CONTROL_WORDS
        || output_words_len < returned_cuda::SPARSE_OUTPUT_HEADER_WORDS
    {
        return;
    }
    let control = unsafe { slice::from_raw_parts(control_words, control_words_len) };
    if !returned_cuda::sparse_control_is_canonical(control) {
        if lane == 0 {
            let output = unsafe {
                slice::from_raw_parts_mut(
                    output_words,
                    returned_cuda::SPARSE_OUTPUT_HEADER_WORDS,
                )
            };
            output[returned_cuda::SPARSE_OUTPUT_STATUS] = returned_cuda::STATUS_INVALID;
        }
        return;
    }
    let epoch = control[returned_cuda::SPARSE_CONTROL_EPOCH];
    let targets = control[returned_cuda::SPARSE_CONTROL_TARGETS] as usize;
    let occurrences = control[returned_cuda::SPARSE_CONTROL_OCCURRENCES] as usize;
    let relations = control[returned_cuda::SPARSE_CONTROL_RELATIONS] as usize;
    let Some(expected_relation_words) = relations.checked_mul(returned_cuda::RELATION_WORDS) else {
        return;
    };
    let Some(expected_output_words) = returned_cuda::sparse_output_words(
        targets,
        occurrences,
        relations,
    ) else {
        return;
    };
    if relation_words_len != expected_relation_words || output_words_len != expected_output_words {
        if lane == 0 {
            let output = unsafe {
                slice::from_raw_parts_mut(
                    output_words,
                    returned_cuda::SPARSE_OUTPUT_HEADER_WORDS,
                )
            };
            output[returned_cuda::SPARSE_OUTPUT_STATUS] = returned_cuda::STATUS_INVALID;
        }
        return;
    }
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    if lane == 0 {
        output[returned_cuda::SPARSE_OUTPUT_STATUS] = returned_cuda::STATUS_COMPLETE;
        output[returned_cuda::SPARSE_OUTPUT_VERSION] = returned_cuda::SPARSE_LAYOUT_VERSION;
        output[returned_cuda::SPARSE_OUTPUT_EPOCH] = epoch;
        output[returned_cuda::SPARSE_OUTPUT_TARGETS] = targets as u32;
        output[returned_cuda::SPARSE_OUTPUT_OCCURRENCES] = occurrences as u32;
        output[returned_cuda::SPARSE_OUTPUT_RELATIONS] = relations as u32;
        output[returned_cuda::SPARSE_OUTPUT_TARGET_ROWS_AT] =
            returned_cuda::SPARSE_OUTPUT_HEADER_WORDS as u32;
        output[returned_cuda::SPARSE_OUTPUT_OCCURRENCE_ROWS_AT] =
            returned_cuda::sparse_occurrence_rows_at(targets).unwrap_or(0) as u32;
        output[returned_cuda::SPARSE_OUTPUT_RELATION_ROWS_AT] =
            returned_cuda::sparse_relation_rows_at(targets, occurrences).unwrap_or(0) as u32;
        output[returned_cuda::SPARSE_OUTPUT_TOTAL_WORDS] = expected_output_words as u32;
        // INVALID_RELATIONS remains zero from the apparatus-owned pre-launch zero. Relation lanes
        // are its only writers, through exact atomic addition.
        return;
    }
    let relation = lane - 1;
    if relation >= relations {
        return;
    }
    let input = unsafe { slice::from_raw_parts(relation_words, relation_words_len) };
    let at = relation * returned_cuda::RELATION_WORDS;
    let row = &input[at..at + returned_cuda::RELATION_WORDS];
    let relation_rows_at = returned_cuda::sparse_relation_rows_at(targets, occurrences).unwrap_or(0);
    let returned_at = relation_rows_at + at;
    let mut word = 0usize;
    while word < returned_cuda::RELATION_WORDS {
        output[returned_at + word] = row[word];
        word += 1;
    }
    let before = row[returned_cuda::RELATION_STOOD_BEFORE];
    let after = row[returned_cuda::RELATION_STANDS_AFTER];
    let target = row[returned_cuda::RELATION_TARGET] as usize;
    let occurrence = row[returned_cuda::RELATION_OCCURRENCE] as usize;
    let mut valid = target < targets
        && occurrence < occurrences
        && before <= 1
        && after <= 1
        && before != after;
    if relation != 0 {
        let prior_at = at - returned_cuda::RELATION_WORDS;
        let prior_target = input[prior_at + returned_cuda::RELATION_TARGET];
        let prior_occurrence = input[prior_at + returned_cuda::RELATION_OCCURRENCE];
        valid &= prior_target < row[returned_cuda::RELATION_TARGET]
            || (prior_target == row[returned_cuda::RELATION_TARGET]
                && prior_occurrence < row[returned_cuda::RELATION_OCCURRENCE]);
    }
    if !valid {
        unsafe {
            contact_add(
                output_words,
                returned_cuda::SPARSE_OUTPUT_INVALID_RELATIONS,
                1,
            )
        };
        return;
    }
    let disposition = if before == 1 { 0 } else { 1 };
    let target_at = returned_cuda::SPARSE_OUTPUT_HEADER_WORDS
        + target * returned_cuda::SPARSE_TARGET_ROW_WORDS
        + disposition;
    let occurrence_rows_at = returned_cuda::sparse_occurrence_rows_at(targets).unwrap_or(0);
    let occurrence_at = occurrence_rows_at
        + occurrence * returned_cuda::SPARSE_OCCURRENCE_ROW_WORDS
        + disposition;
    unsafe {
        contact_add(output_words, target_at, 1);
        contact_add(output_words, occurrence_at, 1);
    }
}

// --- morphological-conduct attachment -----------------------------------------------------------

#[derive(Clone, Copy)]
struct MorphologicalConductShape {
    epoch: u32,
    candidates: usize,
    deposits: usize,
    key_rows: usize,
    key_words: usize,
    max_candidate_keys: usize,
    deposit_row_words: usize,
    key_row_words: usize,
    candidate_row_words: usize,
    output_words: usize,
}

/// A shape refusal: which agreement failed, and the two extents that disagreed where the check is
/// an equality of extents. Answering roughly twenty agreements with one status word made every
/// decline look alike to the cpu.
#[derive(Clone, Copy)]
struct MorphologicalConductShapeRefusal {
    cause: u32,
    declared: u32,
    found: u32,
}

#[inline(always)]
const fn morphological_shape_refusal(
    cause: u32,
    declared: usize,
    found: usize,
) -> MorphologicalConductShapeRefusal {
    MorphologicalConductShapeRefusal {
        cause,
        declared: declared as u32,
        found: found as u32,
    }
}

#[inline(always)]
fn morphological_conduct_shape(
    control: &[u32],
    candidate_words_len: usize,
    deposit_words_len: usize,
    key_row_words_len: usize,
    output_words_len: usize,
) -> Result<MorphologicalConductShape, MorphologicalConductShapeRefusal> {
    if control.len() != morph_cuda::CONTROL_WORDS {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_CONTROL_EXTENT,
            morph_cuda::CONTROL_WORDS,
            control.len(),
        ));
    }
    if control[morph_cuda::CONTROL_VERSION] != morph_cuda::LAYOUT_VERSION {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_CONTROL_VERSION,
            morph_cuda::LAYOUT_VERSION as usize,
            control[morph_cuda::CONTROL_VERSION] as usize,
        ));
    }
    if control[morph_cuda::CONTROL_EPOCH] == 0 {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_CONTROL_EPOCH_ZERO,
            0,
            0,
        ));
    }
    if control[morph_cuda::CONTROL_TOTAL_WORDS] as usize != morph_cuda::CONTROL_WORDS {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_CONTROL_TOTAL_WORDS,
            morph_cuda::CONTROL_WORDS,
            control[morph_cuda::CONTROL_TOTAL_WORDS] as usize,
        ));
    }
    let candidates = control[morph_cuda::CONTROL_CANDIDATES] as usize;
    let deposits = control[morph_cuda::CONTROL_DEPOSITS] as usize;
    let key_rows = control[morph_cuda::CONTROL_KEY_ROWS] as usize;
    let key_words = control[morph_cuda::CONTROL_KEY_WORDS] as usize;
    let max_candidate_keys = control[morph_cuda::CONTROL_MAX_CANDIDATE_KEYS] as usize;
    if key_words == 0 {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_KEY_WORDS_ZERO,
            0,
            0,
        ));
    }
    if max_candidate_keys > key_rows {
        return Err(morphological_shape_refusal(
            morph_cuda::REFUSAL_MAX_CANDIDATE_KEYS,
            key_rows,
            max_candidate_keys,
        ));
    }
    let overflow = morphological_shape_refusal(morph_cuda::REFUSAL_EXTENT_OVERFLOW, 0, 0);
    let Some(candidate_total_words) = candidates.checked_mul(morph_cuda::CANDIDATE_WORDS) else {
        return Err(overflow);
    };
    let Some(deposit_row_words) = morph_cuda::deposit_row_words(key_words) else {
        return Err(overflow);
    };
    let Some(deposit_total_words) = deposits.checked_mul(deposit_row_words) else {
        return Err(overflow);
    };
    let Some(key_row_words) = morph_cuda::key_row_words(key_words) else {
        return Err(overflow);
    };
    let Some(key_row_total_words) = key_rows.checked_mul(key_row_words) else {
        return Err(overflow);
    };
    let Some(candidate_row_words) = morph_cuda::candidate_row_words(max_candidate_keys) else {
        return Err(overflow);
    };
    let Some(output_words) = morph_cuda::output_words(candidates, max_candidate_keys) else {
        return Err(overflow);
    };
    let agreements: [(u32, usize, usize); 12] = [
        (
            morph_cuda::REFUSAL_CONTROL_CANDIDATE_WORDS,
            morph_cuda::CANDIDATE_WORDS,
            control[morph_cuda::CONTROL_CANDIDATE_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_CANDIDATE_TOTAL_WORDS,
            candidate_total_words,
            control[morph_cuda::CONTROL_CANDIDATE_TOTAL_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_DEPOSIT_ROW_WORDS,
            deposit_row_words,
            control[morph_cuda::CONTROL_DEPOSIT_ROW_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_DEPOSIT_TOTAL_WORDS,
            deposit_total_words,
            control[morph_cuda::CONTROL_DEPOSIT_TOTAL_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_KEY_ROW_WORDS,
            key_row_words,
            control[morph_cuda::CONTROL_KEY_ROW_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_KEY_ROW_TOTAL_WORDS,
            key_row_total_words,
            control[morph_cuda::CONTROL_KEY_ROW_TOTAL_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_OUTPUT_ROW_WORDS,
            candidate_row_words,
            control[morph_cuda::CONTROL_OUTPUT_ROW_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CONTROL_OUTPUT_TOTAL_WORDS,
            output_words,
            control[morph_cuda::CONTROL_OUTPUT_TOTAL_WORDS] as usize,
        ),
        (
            morph_cuda::REFUSAL_CANDIDATE_SHEET_EXTENT,
            candidate_total_words,
            candidate_words_len,
        ),
        (
            morph_cuda::REFUSAL_DEPOSIT_SHEET_EXTENT,
            deposit_total_words,
            deposit_words_len,
        ),
        (
            morph_cuda::REFUSAL_KEY_ROW_SHEET_EXTENT,
            key_row_total_words,
            key_row_words_len,
        ),
        (
            morph_cuda::REFUSAL_OUTPUT_SHEET_EXTENT,
            output_words,
            output_words_len,
        ),
    ];
    let mut at = 0usize;
    while at < agreements.len() {
        let (cause, declared, found) = agreements[at];
        if declared != found {
            return Err(morphological_shape_refusal(cause, declared, found));
        }
        at += 1;
    }
    Ok(MorphologicalConductShape {
        epoch: control[morph_cuda::CONTROL_EPOCH],
        candidates,
        deposits,
        key_rows,
        key_words,
        max_candidate_keys,
        deposit_row_words,
        key_row_words,
        candidate_row_words,
        output_words,
    })
}

#[inline(always)]
fn morphological_deposit_key(
    deposits: &[u32],
    shape: MorphologicalConductShape,
    deposit: usize,
) -> &[u32] {
    let at = deposit * shape.deposit_row_words + morph_cuda::DEPOSIT_KEY_AT;
    &deposits[at..at + shape.key_words]
}

#[inline(always)]
fn morphological_key_row_key(
    key_rows: &[u32],
    shape: MorphologicalConductShape,
    row: usize,
) -> &[u32] {
    let at = row * shape.key_row_words + morph_cuda::KEY_ROW_KEY_AT;
    &key_rows[at..at + shape.key_words]
}

#[inline(always)]
fn condition_u64(words: &[u32], low: usize) -> u64 {
    words[low] as u64 | ((words[low + 1] as u64) << 32)
}

#[inline(always)]
fn condition_put_u64(words: &mut [u32], low: usize, value: u64) {
    words[low] = value as u32;
    words[low + 1] = (value >> 32) as u32;
}

#[inline(always)]
fn suffix_state_at(state: usize, field: usize) -> Option<usize> {
    state
        .checked_mul(morph_condition_cuda::SUFFIX_STATE_WORDS)?
        .checked_add(field)
}

#[inline(always)]
fn suffix_transition_at(transition: usize, field: usize) -> Option<usize> {
    transition
        .checked_mul(morph_condition_cuda::SUFFIX_TRANSITION_WORDS)?
        .checked_add(field)
}

#[inline(always)]
fn suffix_find_transition(
    states: &[u32],
    transitions: &[u32],
    state: usize,
    symbol: u32,
    reads: &mut u64,
) -> Option<(usize, u32)> {
    let mut edge = states
        [suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_TRANSITION_HEAD)?]
        as usize;
    while edge != morph_condition_cuda::OPEN as usize {
        *reads = reads.wrapping_add(1);
        let symbol_at = suffix_transition_at(edge, morph_condition_cuda::SUFFIX_TRANSITION_SYMBOL)?;
        if *transitions.get(symbol_at)? == symbol {
            let target = *transitions.get(suffix_transition_at(
                edge,
                morph_condition_cuda::SUFFIX_TRANSITION_TARGET,
            )?)?;
            return Some((edge, target));
        }
        edge = *transitions.get(suffix_transition_at(
            edge,
            morph_condition_cuda::SUFFIX_TRANSITION_NEXT,
        )?)? as usize;
    }
    None
}

#[inline(always)]
fn suffix_add_transition(
    states: &mut [u32],
    transitions: &mut [u32],
    transition_count: &mut usize,
    state: usize,
    symbol: u32,
    target: u32,
) -> bool {
    let edge = *transition_count;
    let Some(base) = suffix_transition_at(edge, 0) else {
        return false;
    };
    if base > transitions.len()
        || morph_condition_cuda::SUFFIX_TRANSITION_WORDS > transitions.len() - base
    {
        return false;
    }
    let Some(head_at) = suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_TRANSITION_HEAD)
    else {
        return false;
    };
    transitions[base + morph_condition_cuda::SUFFIX_TRANSITION_STATE] = state as u32;
    transitions[base + morph_condition_cuda::SUFFIX_TRANSITION_SYMBOL] = symbol;
    transitions[base + morph_condition_cuda::SUFFIX_TRANSITION_TARGET] = target;
    transitions[base + morph_condition_cuda::SUFFIX_TRANSITION_NEXT] = states[head_at];
    states[head_at] = edge as u32;
    *transition_count += 1;
    true
}

#[inline(always)]
fn suffix_init_state(states: &mut [u32], state: usize, maximum_length: u32, suffix: u32) -> bool {
    let Some(base) = suffix_state_at(state, 0) else {
        return false;
    };
    if base > states.len() || morph_condition_cuda::SUFFIX_STATE_WORDS > states.len() - base {
        return false;
    }
    states[base + morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH] = maximum_length;
    states[base + morph_condition_cuda::SUFFIX_STATE_SUFFIX] = suffix;
    states[base + morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_LO] = 0;
    states[base + morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_HI] = 0;
    states[base + morph_condition_cuda::SUFFIX_STATE_TRANSITION_HEAD] = morph_condition_cuda::OPEN;
    states[base + morph_condition_cuda::SUFFIX_STATE_DIRECT_SOURCE] = morph_condition_cuda::OPEN;
    states[base + morph_condition_cuda::SUFFIX_STATE_SPAN_START] = 0;
    states[base + morph_condition_cuda::SUFFIX_STATE_SPAN_LEN] = 0;
    true
}

/// Found one generalized suffix ecology on the resident card.
///
/// One invocation owns the chart because extension chronology is constitutive.  Parallelism is
/// across the five co-present charts at the cpu launch surface, not invented inside one path.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn morphological_suffix_condition(
    control_words: *const u32,
    control_words_len: usize,
    input_words: *const u32,
    input_words_len: usize,
    state_words: *mut u32,
    state_words_len: usize,
    transition_words: *mut u32,
    transition_words_len: usize,
    occurrence_sources: *mut u32,
    occurrence_sources_len: usize,
    scratch_words: *mut u32,
    scratch_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
) {
    let (x, y) = unsafe { global_xy() };
    if x != 0 || y != 0 || output_words_len < morph_condition_cuda::SUFFIX_OUTPUT_WORDS {
        return;
    }
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    output[morph_condition_cuda::SUFFIX_OUTPUT_VERSION] = morph_condition_cuda::LAYOUT_VERSION;
    if control_words_len != morph_condition_cuda::SUFFIX_CONTROL_WORDS {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let control = unsafe { slice::from_raw_parts(control_words, control_words_len) };
    let inputs = control[morph_condition_cuda::SUFFIX_CONTROL_INPUTS] as usize;
    let material_symbols = control[morph_condition_cuda::SUFFIX_CONTROL_MATERIAL_SYMBOLS] as usize;
    let state_capacity = control[morph_condition_cuda::SUFFIX_CONTROL_STATE_CAPACITY] as usize;
    let transition_capacity =
        control[morph_condition_cuda::SUFFIX_CONTROL_TRANSITION_CAPACITY] as usize;
    let occurrence_capacity =
        control[morph_condition_cuda::SUFFIX_CONTROL_OCCURRENCE_CAPACITY] as usize;
    let expected_scratch = control[morph_condition_cuda::SUFFIX_CONTROL_SCRATCH_WORDS] as usize;
    let Some(input_extent) = inputs.checked_mul(morph_condition_cuda::SUFFIX_INPUT_WORDS) else {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    };
    let Some(state_extent) = state_capacity.checked_mul(morph_condition_cuda::SUFFIX_STATE_WORDS)
    else {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    };
    let Some(transition_extent) =
        transition_capacity.checked_mul(morph_condition_cuda::SUFFIX_TRANSITION_WORDS)
    else {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    };
    let Some(required_scratch) = inputs.checked_add(1).and_then(|count| {
        state_capacity
            .checked_mul(6)
            .and_then(|states| count.checked_add(states))
    }) else {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    };
    if inputs == 0
        || material_symbols == 0
        || state_capacity < 2
        || input_words_len != input_extent
        || state_words_len != state_extent
        || transition_words_len != transition_extent
        || occurrence_sources_len != occurrence_capacity
        || scratch_words_len != expected_scratch
        || expected_scratch != required_scratch
        || control[morph_condition_cuda::SUFFIX_CONTROL_VERSION]
            != morph_condition_cuda::LAYOUT_VERSION
    {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let input = unsafe { slice::from_raw_parts(input_words, input_words_len) };
    let states = unsafe { slice::from_raw_parts_mut(state_words, state_words_len) };
    let transitions = unsafe { slice::from_raw_parts_mut(transition_words, transition_words_len) };
    let occurrences =
        unsafe { slice::from_raw_parts_mut(occurrence_sources, occurrence_sources_len) };
    let scratch = unsafe { slice::from_raw_parts_mut(scratch_words, scratch_words_len) };
    let mut state_count = 1usize;
    let mut transition_count = 0usize;
    let mut material_occurrences = 0usize;
    let mut clones = 0u32;
    let mut suffix_crosses = 0u64;
    let mut transition_reads = 0u64;
    if !suffix_init_state(states, 0, 0, morph_condition_cuda::OPEN) {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let mut last = 0usize;
    let mut input_at = 0usize;
    while input_at < inputs {
        let row = input_at * morph_condition_cuda::SUFFIX_INPUT_WORDS;
        let symbol = input[row + morph_condition_cuda::SUFFIX_INPUT_SYMBOL];
        let source = input[row + morph_condition_cuda::SUFFIX_INPUT_SOURCE];
        let material = input[row + morph_condition_cuda::SUFFIX_INPUT_MATERIAL];
        if material > 1
            || (material == 1
                && (symbol as usize >= material_symbols || source == morph_condition_cuda::OPEN))
            || (material == 0
                && ((symbol as usize) < material_symbols || source != morph_condition_cuda::OPEN))
            || state_count >= state_capacity
        {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        }
        let current = state_count;
        state_count += 1;
        let Some(current_length) =
            states[suffix_state_at(last, morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH)
                .unwrap_or(usize::MAX)]
            .checked_add(1)
        else {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        };
        if !suffix_init_state(states, current, current_length, morph_condition_cuda::OPEN) {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        }
        let mut cursor = last as u32;
        loop {
            if cursor == morph_condition_cuda::OPEN {
                states[suffix_state_at(current, morph_condition_cuda::SUFFIX_STATE_SUFFIX)
                    .unwrap()] = 0;
                break;
            }
            let state = cursor as usize;
            if let Some((_, target)) =
                suffix_find_transition(states, transitions, state, symbol, &mut transition_reads)
            {
                let next_length = states[suffix_state_at(
                    state,
                    morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH,
                )
                .unwrap()]
                .wrapping_add(1);
                let target_length = states[suffix_state_at(
                    target as usize,
                    morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH,
                )
                .unwrap()];
                if next_length == target_length {
                    states[suffix_state_at(current, morph_condition_cuda::SUFFIX_STATE_SUFFIX)
                        .unwrap()] = target;
                } else {
                    if state_count >= state_capacity {
                        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                            morph_condition_cuda::STATUS_INVALID;
                        return;
                    }
                    let clone = state_count;
                    state_count += 1;
                    clones = clones.wrapping_add(1);
                    let target_suffix = states[suffix_state_at(
                        target as usize,
                        morph_condition_cuda::SUFFIX_STATE_SUFFIX,
                    )
                    .unwrap()];
                    if !suffix_init_state(states, clone, next_length, target_suffix) {
                        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                            morph_condition_cuda::STATUS_INVALID;
                        return;
                    }
                    let mut edge = states[suffix_state_at(
                        target as usize,
                        morph_condition_cuda::SUFFIX_STATE_TRANSITION_HEAD,
                    )
                    .unwrap()];
                    while edge != morph_condition_cuda::OPEN {
                        let edge_at = edge as usize;
                        let edge_symbol = transitions[suffix_transition_at(
                            edge_at,
                            morph_condition_cuda::SUFFIX_TRANSITION_SYMBOL,
                        )
                        .unwrap()];
                        let edge_target = transitions[suffix_transition_at(
                            edge_at,
                            morph_condition_cuda::SUFFIX_TRANSITION_TARGET,
                        )
                        .unwrap()];
                        if !suffix_add_transition(
                            states,
                            transitions,
                            &mut transition_count,
                            clone,
                            edge_symbol,
                            edge_target,
                        ) {
                            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                                morph_condition_cuda::STATUS_INVALID;
                            return;
                        }
                        edge = transitions[suffix_transition_at(
                            edge_at,
                            morph_condition_cuda::SUFFIX_TRANSITION_NEXT,
                        )
                        .unwrap()];
                    }
                    let mut rewrite = cursor;
                    while rewrite != morph_condition_cuda::OPEN {
                        suffix_crosses = suffix_crosses.wrapping_add(1);
                        let Some((edge, found)) = suffix_find_transition(
                            states,
                            transitions,
                            rewrite as usize,
                            symbol,
                            &mut transition_reads,
                        ) else {
                            break;
                        };
                        if found != target {
                            break;
                        }
                        transitions[suffix_transition_at(
                            edge,
                            morph_condition_cuda::SUFFIX_TRANSITION_TARGET,
                        )
                        .unwrap()] = clone as u32;
                        rewrite = states[suffix_state_at(
                            rewrite as usize,
                            morph_condition_cuda::SUFFIX_STATE_SUFFIX,
                        )
                        .unwrap()];
                    }
                    states[suffix_state_at(
                        target as usize,
                        morph_condition_cuda::SUFFIX_STATE_SUFFIX,
                    )
                    .unwrap()] = clone as u32;
                    states[suffix_state_at(current, morph_condition_cuda::SUFFIX_STATE_SUFFIX)
                        .unwrap()] = clone as u32;
                }
                break;
            }
            if !suffix_add_transition(
                states,
                transitions,
                &mut transition_count,
                state,
                symbol,
                current as u32,
            ) {
                output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                    morph_condition_cuda::STATUS_INVALID;
                return;
            }
            suffix_crosses = suffix_crosses.wrapping_add(1);
            cursor =
                states[suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_SUFFIX).unwrap()];
        }
        last = current;
        if material == 1 {
            states[suffix_state_at(current, morph_condition_cuda::SUFFIX_STATE_DIRECT_SOURCE)
                .unwrap()] = source;
            states[suffix_state_at(current, morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_LO)
                .unwrap()] = 1;
            material_occurrences += 1;
        }
        input_at += 1;
    }

    // Counting sort states by (maximum_length, state). Reversing the ascending order reproduces
    // the exact cpu law's (Reverse(maximum_length), Reverse(state)) propagation.
    let count_len = inputs + 1;
    let order_base = count_len;
    let first_base = order_base + state_capacity;
    let next_base = first_base + state_capacity;
    let stack_state_base = next_base + state_capacity;
    let stack_child_base = stack_state_base + state_capacity;
    let stack_start_base = stack_child_base + state_capacity;
    let mut at = 0usize;
    while at < count_len {
        scratch[at] = 0;
        at += 1;
    }
    at = 0;
    while at < state_count {
        let length = states
            [suffix_state_at(at, morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH).unwrap()]
            as usize;
        scratch[length] = scratch[length].wrapping_add(1);
        at += 1;
    }
    at = 1;
    while at < count_len {
        scratch[at] = scratch[at].wrapping_add(scratch[at - 1]);
        at += 1;
    }
    at = state_count;
    while at > 0 {
        at -= 1;
        let length = states
            [suffix_state_at(at, morph_condition_cuda::SUFFIX_STATE_MAXIMUM_LENGTH).unwrap()]
            as usize;
        scratch[length] -= 1;
        let slot = scratch[length] as usize;
        scratch[order_base + slot] = at as u32;
    }
    at = state_count;
    while at > 1 {
        at -= 1;
        let state = scratch[order_base + at] as usize;
        let suffix = states
            [suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_SUFFIX).unwrap()]
            as usize;
        if suffix >= state_count {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        }
        let state_base = suffix_state_at(state, 0).unwrap();
        let suffix_base = suffix_state_at(suffix, 0).unwrap();
        let carried = condition_u64(
            states,
            state_base + morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_LO,
        );
        let standing = condition_u64(
            states,
            suffix_base + morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_LO,
        );
        let Some(total) = standing.checked_add(carried) else {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        };
        condition_put_u64(
            states,
            suffix_base + morph_condition_cuda::SUFFIX_STATE_MULTIPLICITY_LO,
            total,
        );
    }

    // The suffix-link tree's exact descendant order and source spans.
    at = 0;
    while at < state_capacity {
        scratch[first_base + at] = morph_condition_cuda::OPEN;
        scratch[next_base + at] = morph_condition_cuda::OPEN;
        at += 1;
    }
    at = 1;
    while at < state_count {
        let parent = states[suffix_state_at(at, morph_condition_cuda::SUFFIX_STATE_SUFFIX).unwrap()]
            as usize;
        if parent >= state_count || parent == at {
            output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        }
        scratch[next_base + at] = scratch[first_base + parent];
        scratch[first_base + parent] = at as u32;
        at += 1;
    }
    let mut occurrence_count = 0usize;
    let mut depth = 1usize;
    scratch[stack_state_base] = 0;
    scratch[stack_child_base] = scratch[first_base];
    scratch[stack_start_base] = 0;
    while depth > 0 {
        let slot = depth - 1;
        let child = scratch[stack_child_base + slot];
        if child != morph_condition_cuda::OPEN {
            let child_at = child as usize;
            scratch[stack_child_base + slot] = scratch[next_base + child_at];
            let direct =
                states[suffix_state_at(child_at, morph_condition_cuda::SUFFIX_STATE_DIRECT_SOURCE)
                    .unwrap()];
            let child_start = occurrence_count;
            if direct != morph_condition_cuda::OPEN {
                if occurrence_count >= occurrence_capacity {
                    output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] =
                        morph_condition_cuda::STATUS_INVALID;
                    return;
                }
                occurrences[occurrence_count] = direct;
                occurrence_count += 1;
            }
            scratch[stack_state_base + depth] = child;
            scratch[stack_child_base + depth] = scratch[first_base + child_at];
            scratch[stack_start_base + depth] = child_start as u32;
            depth += 1;
        } else {
            let state = scratch[stack_state_base + slot] as usize;
            let start = scratch[stack_start_base + slot];
            states
                [suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_SPAN_START).unwrap()] =
                start;
            states[suffix_state_at(state, morph_condition_cuda::SUFFIX_STATE_SPAN_LEN).unwrap()] =
                occurrence_count as u32 - start;
            depth -= 1;
        }
    }
    if occurrence_count != material_occurrences {
        output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let mut material_transitions = 0u32;
    at = 0;
    while at < transition_count {
        if (transitions
            [suffix_transition_at(at, morph_condition_cuda::SUFFIX_TRANSITION_SYMBOL).unwrap()]
            as usize)
            < material_symbols
        {
            material_transitions = material_transitions.wrapping_add(1);
        }
        at += 1;
    }
    output[morph_condition_cuda::SUFFIX_OUTPUT_STATE_COUNT] = state_count as u32;
    output[morph_condition_cuda::SUFFIX_OUTPUT_TRANSITION_COUNT] = transition_count as u32;
    output[morph_condition_cuda::SUFFIX_OUTPUT_OCCURRENCE_COUNT] = occurrence_count as u32;
    output[morph_condition_cuda::SUFFIX_OUTPUT_MATERIAL_TRANSITIONS] = material_transitions;
    output[morph_condition_cuda::SUFFIX_OUTPUT_EXTENSIONS] = inputs as u32;
    output[morph_condition_cuda::SUFFIX_OUTPUT_CLONES] = clones;
    condition_put_u64(
        output,
        morph_condition_cuda::SUFFIX_OUTPUT_SUFFIX_CROSSES_LO,
        suffix_crosses,
    );
    condition_put_u64(
        output,
        morph_condition_cuda::SUFFIX_OUTPUT_TRANSITION_READS_LO,
        transition_reads,
    );
    output[morph_condition_cuda::SUFFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_COMPLETE;
}

#[inline(always)]
fn prefix_node_at(node: usize, field: usize) -> Option<usize> {
    node.checked_mul(morph_condition_cuda::PREFIX_NODE_WORDS)?
        .checked_add(field)
}

/// Found the boundary-anchored question-prefix incidence on the resident card.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn morphological_prefix_condition(
    control_words: *const u32,
    control_words_len: usize,
    path_words: *const u32,
    path_words_len: usize,
    token_words: *const u32,
    token_words_len: usize,
    node_words: *mut u32,
    node_words_len: usize,
    support_words: *mut u32,
    support_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
) {
    let (x, y) = unsafe { global_xy() };
    if x != 0 || y != 0 || output_words_len < morph_condition_cuda::PREFIX_OUTPUT_WORDS {
        return;
    }
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    output[morph_condition_cuda::PREFIX_OUTPUT_VERSION] = morph_condition_cuda::LAYOUT_VERSION;
    if control_words_len != morph_condition_cuda::PREFIX_CONTROL_WORDS {
        output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let control = unsafe { slice::from_raw_parts(control_words, control_words_len) };
    let paths = control[morph_condition_cuda::PREFIX_CONTROL_PATHS] as usize;
    let tokens = control[morph_condition_cuda::PREFIX_CONTROL_TOKENS] as usize;
    let node_capacity = control[morph_condition_cuda::PREFIX_CONTROL_NODE_CAPACITY] as usize;
    let support_capacity = control[morph_condition_cuda::PREFIX_CONTROL_SUPPORT_CAPACITY] as usize;
    if control[morph_condition_cuda::PREFIX_CONTROL_VERSION] != morph_condition_cuda::LAYOUT_VERSION
        || path_words_len != paths.saturating_mul(morph_condition_cuda::PREFIX_PATH_WORDS)
        || token_words_len != tokens
        || node_words_len != node_capacity.saturating_mul(morph_condition_cuda::PREFIX_NODE_WORDS)
        || support_words_len
            != support_capacity.saturating_mul(morph_condition_cuda::PREFIX_SUPPORT_WORDS)
        || node_capacity == 0
    {
        output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_INVALID;
        return;
    }
    let path_rows = unsafe { slice::from_raw_parts(path_words, path_words_len) };
    let token_rows = unsafe { slice::from_raw_parts(token_words, token_words_len) };
    let nodes = unsafe { slice::from_raw_parts_mut(node_words, node_words_len) };
    let supports = unsafe { slice::from_raw_parts_mut(support_words, support_words_len) };
    let mut field = 0usize;
    while field < morph_condition_cuda::PREFIX_NODE_WORDS {
        nodes[field] = if field == morph_condition_cuda::PREFIX_NODE_PARENT
            || field == morph_condition_cuda::PREFIX_NODE_TOKEN
            || field == morph_condition_cuda::PREFIX_NODE_FIRST_CHILD
            || field == morph_condition_cuda::PREFIX_NODE_NEXT_SIBLING
            || field == morph_condition_cuda::PREFIX_NODE_FIRST_CONTINUATION
        {
            morph_condition_cuda::OPEN
        } else {
            0
        };
        field += 1;
    }
    let mut node_count = 1usize;
    let mut support_count = 0usize;
    let mut crossings = 0u64;
    let mut legacy_clones = 0u64;
    let mut edge_reads = 0u64;
    let mut path = 0usize;
    while path < paths {
        let row = path * morph_condition_cuda::PREFIX_PATH_WORDS;
        let start = path_rows[row + morph_condition_cuda::PREFIX_PATH_START] as usize;
        let len = path_rows[row + morph_condition_cuda::PREFIX_PATH_LEN] as usize;
        let source = path_rows[row + morph_condition_cuda::PREFIX_PATH_SOURCE];
        if len < 2 || start > tokens || len > tokens - start || source == morph_condition_cuda::OPEN
        {
            output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] =
                morph_condition_cuda::STATUS_INVALID;
            return;
        }
        let mut node = 0usize;
        let mut depth = 0usize;
        while depth + 1 < len {
            let token = token_rows[start + depth];
            let continuation = token_rows[start + depth + 1];
            let mut child =
                nodes[prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_FIRST_CHILD).unwrap()];
            let mut found = morph_condition_cuda::OPEN;
            while child != morph_condition_cuda::OPEN {
                edge_reads = edge_reads.wrapping_add(1);
                if nodes[prefix_node_at(child as usize, morph_condition_cuda::PREFIX_NODE_TOKEN)
                    .unwrap()]
                    == token
                {
                    found = child;
                    break;
                }
                child = nodes[prefix_node_at(
                    child as usize,
                    morph_condition_cuda::PREFIX_NODE_NEXT_SIBLING,
                )
                .unwrap()];
            }
            if found == morph_condition_cuda::OPEN {
                if node_count >= node_capacity {
                    output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] =
                        morph_condition_cuda::STATUS_INVALID;
                    return;
                }
                let new_node = node_count;
                node_count += 1;
                let base = prefix_node_at(new_node, 0).unwrap();
                nodes[base + morph_condition_cuda::PREFIX_NODE_PARENT] = node as u32;
                nodes[base + morph_condition_cuda::PREFIX_NODE_TOKEN] = token;
                nodes[base + morph_condition_cuda::PREFIX_NODE_FIRST_CHILD] =
                    morph_condition_cuda::OPEN;
                nodes[base + morph_condition_cuda::PREFIX_NODE_NEXT_SIBLING] = nodes
                    [prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_FIRST_CHILD).unwrap()];
                nodes[base + morph_condition_cuda::PREFIX_NODE_OCCURRENCES] = 0;
                nodes[base + morph_condition_cuda::PREFIX_NODE_FIRST_CONTINUATION] =
                    morph_condition_cuda::OPEN;
                nodes[base + morph_condition_cuda::PREFIX_NODE_DIVERGENT] = 0;
                nodes[base + morph_condition_cuda::PREFIX_NODE_ACTIVE] = 0;
                nodes[prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_FIRST_CHILD)
                    .unwrap()] = new_node as u32;
                found = new_node as u32;
            }
            node = found as usize;
            let occurrences_at =
                prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_OCCURRENCES).unwrap();
            nodes[occurrences_at] = nodes[occurrences_at].wrapping_add(1);
            let continuation_at =
                prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_FIRST_CONTINUATION).unwrap();
            if nodes[continuation_at] == morph_condition_cuda::OPEN {
                nodes[continuation_at] = continuation;
            } else if nodes[continuation_at] != continuation {
                nodes[prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_DIVERGENT).unwrap()] =
                    1;
            }
            if support_count >= support_capacity {
                output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] =
                    morph_condition_cuda::STATUS_INVALID;
                return;
            }
            let support_at = support_count * morph_condition_cuda::PREFIX_SUPPORT_WORDS;
            supports[support_at + morph_condition_cuda::PREFIX_SUPPORT_NODE] = node as u32;
            supports[support_at + morph_condition_cuda::PREFIX_SUPPORT_SOURCE] = source;
            support_count += 1;
            crossings = crossings.wrapping_add(1);
            legacy_clones = legacy_clones.wrapping_add((depth + 1) as u64);
            depth += 1;
        }
        path += 1;
    }
    let mut returned_tokens = 0u64;
    let mut node = 1usize;
    while node < node_count {
        let active = nodes
            [prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_OCCURRENCES).unwrap()]
            >= 2
            && nodes[prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_DIVERGENT).unwrap()]
                == 1;
        if active {
            nodes[prefix_node_at(node, morph_condition_cuda::PREFIX_NODE_ACTIVE).unwrap()] = 1;
            let mut depth = 0u64;
            let mut cursor = node as u32;
            while cursor != 0 {
                depth = depth.wrapping_add(1);
                cursor = nodes[prefix_node_at(
                    cursor as usize,
                    morph_condition_cuda::PREFIX_NODE_PARENT,
                )
                .unwrap()];
            }
            returned_tokens = returned_tokens.wrapping_add(depth);
        }
        node += 1;
    }
    output[morph_condition_cuda::PREFIX_OUTPUT_NODE_COUNT] = node_count as u32;
    output[morph_condition_cuda::PREFIX_OUTPUT_SUPPORT_COUNT] = support_count as u32;
    condition_put_u64(
        output,
        morph_condition_cuda::PREFIX_OUTPUT_CROSSINGS_LO,
        crossings,
    );
    condition_put_u64(
        output,
        morph_condition_cuda::PREFIX_OUTPUT_LEGACY_CLONES_LO,
        legacy_clones,
    );
    condition_put_u64(
        output,
        morph_condition_cuda::PREFIX_OUTPUT_RETURNED_TOKENS_LO,
        returned_tokens,
    );
    condition_put_u64(
        output,
        morph_condition_cuda::PREFIX_OUTPUT_EDGE_READS_LO,
        edge_reads,
    );
    output[morph_condition_cuda::PREFIX_OUTPUT_STATUS] = morph_condition_cuda::STATUS_COMPLETE;
}

/// Read the recurrence shadow of raw material without retaining or interpreting its surfaces.
///
/// One lane owns one passage.  Equality is the sole surface relation: at each position the lane
/// returns the distance to the immediately preceding equal octet.  A bijection of every octet
/// therefore leaves the complete field and key unchanged.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn material_shadow_read(
    descriptors: *const u32,
    descriptors_len: usize,
    material_words: *const u32,
    material_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    shadow_words: *mut u32,
    shadow_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if descriptors_len % material_shadow_cuda::INPUT_WORDS != 0
        || output_words_len % material_shadow_cuda::OUTPUT_WORDS != 0
    {
        return;
    }
    let rows = descriptors_len / material_shadow_cuda::INPUT_WORDS;
    if output_words_len / material_shadow_cuda::OUTPUT_WORDS != rows || lane >= rows {
        return;
    }
    let descriptors = unsafe { slice::from_raw_parts(descriptors, descriptors_len) };
    let material = unsafe { slice::from_raw_parts(material_words, material_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    let shadows = unsafe { slice::from_raw_parts_mut(shadow_words, shadow_words_len) };
    let input_at = lane * material_shadow_cuda::INPUT_WORDS;
    let output_at = lane * material_shadow_cuda::OUTPUT_WORDS;
    output[output_at + material_shadow_cuda::OUTPUT_VERSION] =
        material_shadow_cuda::LAYOUT_VERSION;
    let offset = descriptors[input_at + material_shadow_cuda::INPUT_OFFSET] as usize;
    let extent = descriptors[input_at + material_shadow_cuda::INPUT_EXTENT] as usize;
    let shadow_offset =
        descriptors[input_at + material_shadow_cuda::INPUT_SHADOW_OFFSET] as usize;
    if extent == 0
        || offset > material.len()
        || extent > material.len() - offset
        || shadow_offset > shadows.len()
        || extent > shadows.len() - shadow_offset
    {
        output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
            material_shadow_cuda::STATUS_INVALID;
        return;
    }
    let mut distinct = 0u32;
    let mut recurrent = 0u32;
    let mut adjacent_equal = 0u32;
    let mut forward = material_shadow_cuda::FNV_OFFSET;
    let mut position = 0usize;
    while position < extent {
        let surface = material[offset + position];
        let mut prior = position;
        let mut gap = 0usize;
        while prior > 0 {
            prior -= 1;
            if material[offset + prior] == surface {
                gap = position - prior;
                break;
            }
        }
        let Ok(gap_word) = u32::try_from(gap) else {
            output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
                material_shadow_cuda::STATUS_INVALID;
            return;
        };
        shadows[shadow_offset + position] = gap_word;
        if gap == 0 {
            let Some(next) = distinct.checked_add(1) else {
                output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
                    material_shadow_cuda::STATUS_INVALID;
                return;
            };
            distinct = next;
        } else {
            let Some(next) = recurrent.checked_add(1) else {
                output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
                    material_shadow_cuda::STATUS_INVALID;
                return;
            };
            recurrent = next;
            if gap == 1 {
                let Some(next) = adjacent_equal.checked_add(1) else {
                    output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
                        material_shadow_cuda::STATUS_INVALID;
                    return;
                };
                adjacent_equal = next;
            }
        }
        forward = material_shadow_cuda::hash_step(forward, gap_word);
        position += 1;
    }
    let mut reverse = material_shadow_cuda::FNV_OFFSET;
    let mut remaining = extent;
    while remaining > 0 {
        remaining -= 1;
        reverse = material_shadow_cuda::hash_step(reverse, shadows[shadow_offset + remaining]);
    }
    let summary_at = output_at + material_shadow_cuda::OUTPUT_SUMMARY_AT;
    output[summary_at] = extent as u32;
    output[summary_at + 1] = distinct;
    output[summary_at + 2] = recurrent;
    output[summary_at + 3] = adjacent_equal;
    output[summary_at + 4] = forward as u32;
    output[summary_at + 5] = (forward >> 32) as u32;
    output[summary_at + 6] = reverse as u32;
    output[summary_at + 7] = (reverse >> 32) as u32;
    output[output_at + material_shadow_cuda::OUTPUT_STATUS] =
        material_shadow_cuda::STATUS_COMPLETE;
}

/// Found one exact local bi-affine law from a complete rectangular intervention face.
///
/// One lane owns one founding row. The card returns the Newton coefficients and the lattice chart;
/// no section name, operation tag, or later query crosses this entry.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn recurrent_law_found(
    input_words: *const u32,
    input_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if input_words_len % recurrent_law_cuda::FOUND_INPUT_WORDS != 0
        || output_words_len % recurrent_law_cuda::FOUND_OUTPUT_WORDS != 0
    {
        return;
    }
    let rows = input_words_len / recurrent_law_cuda::FOUND_INPUT_WORDS;
    if output_words_len / recurrent_law_cuda::FOUND_OUTPUT_WORDS != rows || lane >= rows {
        return;
    }
    let input = unsafe { slice::from_raw_parts(input_words, input_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    let input_at = lane * recurrent_law_cuda::FOUND_INPUT_WORDS;
    let output_at = lane * recurrent_law_cuda::FOUND_OUTPUT_WORDS;
    output[output_at + recurrent_law_cuda::FOUND_OUTPUT_VERSION] =
        recurrent_law_cuda::LAYOUT_VERSION;
    let mut values = [0i64; recurrent_law_cuda::FOUND_VALUES];
    let mut value = 0usize;
    while value < values.len() {
        let Some(decoded) =
            recurrent_read_i64(input, input_at + value * recurrent_law_cuda::I64_WORDS)
        else {
            output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        };
        values[value] = decoded;
        value += 1;
    }
    let [x0, x1, y0, y1, f00, f10, f01, f11] = values;
    let Some(dx) = x1.checked_sub(x0) else {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(dy) = y1.checked_sub(y0) else {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    if dx == 0 || dy == 0 {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    let Some(cx) = f10.checked_sub(f00) else {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(cy) = f01.checked_sub(f00) else {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(cxy) = f11
        .checked_sub(f10)
        .and_then(|v| v.checked_sub(f01))
        .and_then(|v| v.checked_add(f00))
    else {
        output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let law = [x0, y0, dx, dy, f00, cx, cy, cxy];
    let mut coordinate = 0usize;
    while coordinate < law.len() {
        if !recurrent_write_i64(
            output,
            output_at
                + recurrent_law_cuda::FOUND_OUTPUT_LAW_AT
                + coordinate * recurrent_law_cuda::I64_WORDS,
            law[coordinate],
        ) {
            output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        }
        coordinate += 1;
    }
    output[output_at + recurrent_law_cuda::FOUND_OUTPUT_STATUS] =
        recurrent_law_cuda::STATUS_COMPLETE;
}

/// Evaluate a remounted exact local law at a later lattice coordinate.
///
/// One lane owns one query. Every multiplication and addition is checked; an off-lattice query or
/// finite-carrier overflow remains a returned obstruction.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn recurrent_law_evaluate(
    input_words: *const u32,
    input_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if input_words_len % recurrent_law_cuda::EVALUATE_INPUT_WORDS != 0
        || output_words_len % recurrent_law_cuda::EVALUATE_OUTPUT_WORDS != 0
    {
        return;
    }
    let rows = input_words_len / recurrent_law_cuda::EVALUATE_INPUT_WORDS;
    if output_words_len / recurrent_law_cuda::EVALUATE_OUTPUT_WORDS != rows || lane >= rows {
        return;
    }
    let input = unsafe { slice::from_raw_parts(input_words, input_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    let input_at = lane * recurrent_law_cuda::EVALUATE_INPUT_WORDS;
    let output_at = lane * recurrent_law_cuda::EVALUATE_OUTPUT_WORDS;
    output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_VERSION] =
        recurrent_law_cuda::LAYOUT_VERSION;
    let mut values = [0i64; recurrent_law_cuda::LAW_VALUES + 2];
    let mut coordinate = 0usize;
    while coordinate < values.len() {
        let Some(decoded) =
            recurrent_read_i64(input, input_at + coordinate * recurrent_law_cuda::I64_WORDS)
        else {
            output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        };
        values[coordinate] = decoded;
        coordinate += 1;
    }
    let [x0, y0, dx, dy, c0, cx, cy, cxy, query_x, query_y] = values;
    if dx == 0 || dy == 0 {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    let Some(relative_x) = query_x.checked_sub(x0) else {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(relative_y) = query_y.checked_sub(y0) else {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    if relative_x.checked_rem(dx) != Some(0) || relative_y.checked_rem(dy) != Some(0) {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OUTSIDE_LATTICE;
        return;
    }
    let Some(u) = relative_x.checked_div(dx) else {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(v) = relative_y.checked_div(dy) else {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    let Some(value) = u
        .checked_mul(cx)
        .and_then(|x_term| {
            v.checked_mul(cy)
                .and_then(|y_term| x_term.checked_add(y_term))
        })
        .and_then(|linear| {
            u.checked_mul(v)
                .and_then(|uv| uv.checked_mul(cxy))
                .and_then(|mixed| linear.checked_add(mixed))
        })
        .and_then(|delta| c0.checked_add(delta))
    else {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_OVERFLOW;
        return;
    };
    if !recurrent_write_i64(
        output,
        output_at + recurrent_law_cuda::EVALUATE_OUTPUT_VALUE_AT,
        value,
    ) {
        output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    output[output_at + recurrent_law_cuda::EVALUATE_OUTPUT_STATUS] =
        recurrent_law_cuda::STATUS_COMPLETE;
}

/// Enact one exact local law repeatedly over a later current and return the complete world-line.
///
/// One lane owns one passage. The cpu supplies the law deposit, initial standing, and current
/// sheet; it never receives a chance to replay the recurrence between events.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn recurrent_law_fold(
    input_words: *const u32,
    input_words_len: usize,
    current_words: *const u32,
    current_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    trace_words: *mut u32,
    trace_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if input_words_len % recurrent_law_cuda::FOLD_INPUT_WORDS != 0
        || output_words_len % recurrent_law_cuda::FOLD_OUTPUT_WORDS != 0
    {
        return;
    }
    let rows = input_words_len / recurrent_law_cuda::FOLD_INPUT_WORDS;
    if output_words_len / recurrent_law_cuda::FOLD_OUTPUT_WORDS != rows || lane >= rows {
        return;
    }
    let input = unsafe { slice::from_raw_parts(input_words, input_words_len) };
    let currents = unsafe { slice::from_raw_parts(current_words, current_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };
    let traces = unsafe { slice::from_raw_parts_mut(trace_words, trace_words_len) };
    let input_at = lane * recurrent_law_cuda::FOLD_INPUT_WORDS;
    let output_at = lane * recurrent_law_cuda::FOLD_OUTPUT_WORDS;
    output[output_at + recurrent_law_cuda::FOLD_OUTPUT_VERSION] =
        recurrent_law_cuda::LAYOUT_VERSION;
    let current_offset =
        input[input_at + recurrent_law_cuda::FOLD_INPUT_CURRENT_OFFSET] as usize;
    let current_extent =
        input[input_at + recurrent_law_cuda::FOLD_INPUT_CURRENT_EXTENT] as usize;
    let trace_offset = input[input_at + recurrent_law_cuda::FOLD_INPUT_TRACE_OFFSET] as usize;
    let Some(current_end) = current_offset.checked_add(current_extent) else {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    };
    let Some(trace_extent) = current_extent.checked_add(1) else {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    };
    let Some(trace_end) = trace_offset.checked_add(trace_extent) else {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    };
    if current_end > current_words_len / recurrent_law_cuda::I64_WORDS
        || trace_end > trace_words_len / recurrent_law_cuda::I64_WORDS
    {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    let mut law = [0i64; recurrent_law_cuda::LAW_VALUES];
    let mut coordinate = 0usize;
    while coordinate < law.len() {
        let Some(value) = recurrent_read_i64(
            input,
            input_at
                + recurrent_law_cuda::FOLD_INPUT_LAW_AT
                + coordinate * recurrent_law_cuda::I64_WORDS,
        ) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        };
        law[coordinate] = value;
        coordinate += 1;
    }
    let Some(mut standing) = recurrent_read_i64(
        input,
        input_at + recurrent_law_cuda::FOLD_INPUT_INITIAL_AT,
    ) else {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    };
    if !recurrent_write_i64(
        traces,
        trace_offset * recurrent_law_cuda::I64_WORDS,
        standing,
    ) {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    let [x0, y0, dx, dy, c0, cx, cy, cxy] = law;
    if dx == 0 || dy == 0 {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    let mut event = 0usize;
    while event < current_extent {
        let Some(current) = recurrent_read_i64(
            currents,
            (current_offset + event) * recurrent_law_cuda::I64_WORDS,
        ) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        };
        let Some(relative_x) = standing.checked_sub(x0) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OVERFLOW;
            return;
        };
        let Some(relative_y) = current.checked_sub(y0) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OVERFLOW;
            return;
        };
        if relative_x.checked_rem(dx) != Some(0) || relative_y.checked_rem(dy) != Some(0) {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OUTSIDE_LATTICE;
            return;
        }
        let Some(u) = relative_x.checked_div(dx) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OVERFLOW;
            return;
        };
        let Some(v) = relative_y.checked_div(dy) else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OVERFLOW;
            return;
        };
        let Some(next) = u
            .checked_mul(cx)
            .and_then(|x_term| {
                v.checked_mul(cy)
                    .and_then(|y_term| x_term.checked_add(y_term))
            })
            .and_then(|linear| {
                u.checked_mul(v)
                    .and_then(|uv| uv.checked_mul(cxy))
                    .and_then(|mixed| linear.checked_add(mixed))
            })
            .and_then(|delta| c0.checked_add(delta))
        else {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_OVERFLOW;
            return;
        };
        standing = next;
        if !recurrent_write_i64(
            traces,
            (trace_offset + event + 1) * recurrent_law_cuda::I64_WORDS,
            standing,
        ) {
            output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
                recurrent_law_cuda::STATUS_INVALID;
            return;
        }
        event += 1;
    }
    output[output_at + recurrent_law_cuda::FOLD_OUTPUT_TRACE_OFFSET] = trace_offset as u32;
    output[output_at + recurrent_law_cuda::FOLD_OUTPUT_TRACE_EXTENT] = trace_extent as u32;
    if !recurrent_write_i64(
        output,
        output_at + recurrent_law_cuda::FOLD_OUTPUT_VALUE_AT,
        standing,
    ) {
        output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
            recurrent_law_cuda::STATUS_INVALID;
        return;
    }
    output[output_at + recurrent_law_cuda::FOLD_OUTPUT_STATUS] =
        recurrent_law_cuda::STATUS_COMPLETE;
}

/// **The card's own decision: which deposit, if any, carries this exact key.**
///
/// A binary search over the validated ascending deposit sheet. The cpu ships two independently
/// assembled key sheets and never the answer; this function is where membership is decided.
#[inline(always)]
fn morphological_deposit_of_key(
    deposits: &[u32],
    shape: MorphologicalConductShape,
    key: &[u32],
) -> Option<usize> {
    let mut low = 0usize;
    let mut high = shape.deposits;
    while low < high {
        let middle = low + (high - low) / 2;
        let candidate = morphological_deposit_key(deposits, shape, middle);
        if morph_cuda::key_equals(candidate, key) {
            return Some(middle);
        }
        if morph_cuda::key_precedes(candidate, key) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    None
}

/// Attach candidate fronts to the exact deposits whose transport keys they carry.
///
/// Lane zero validates that both key sheets are strictly ascending in their declared order — the
/// property the search relies on, refused rather than assumed — counts the active deposits, and
/// returns the header. Each later lane owns one candidate, binary-searches the deposit sheet for
/// each of that candidate's keys, and writes only the ordinals it found. No relation sheet enters
/// and none returns.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn morphological_conduct_group(
    control_words: *const u32,
    control_words_len: usize,
    candidate_words: *const u32,
    candidate_words_len: usize,
    deposit_words: *const u32,
    deposit_words_len: usize,
    key_row_words: *const u32,
    key_row_words_len: usize,
    output_words: *mut u32,
    output_words_len: usize,
    x_stride: u32,
) {
    let (x, y) = unsafe { global_xy() };
    let lane = x as usize + y as usize * x_stride as usize;
    if control_words_len != morph_cuda::CONTROL_WORDS
        || output_words_len < morph_cuda::OUTPUT_HEADER_WORDS
    {
        return;
    }
    let control = unsafe { slice::from_raw_parts(control_words, control_words_len) };
    let shape = match morphological_conduct_shape(
        control,
        candidate_words_len,
        deposit_words_len,
        key_row_words_len,
        output_words_len,
    ) {
        Ok(shape) => shape,
        Err(refusal) => {
            if lane == 0 {
                let output = unsafe {
                    slice::from_raw_parts_mut(output_words, morph_cuda::OUTPUT_HEADER_WORDS)
                };
                // The version is written even on the decline path, so a cpu can tell "the card
                // refused" from "the card did not write" instead of reporting the first unwritten
                // header word as the disagreement.
                output[morph_cuda::OUTPUT_VERSION] = morph_cuda::LAYOUT_VERSION;
                output[morph_cuda::OUTPUT_REFUSAL_CAUSE] = refusal.cause;
                output[morph_cuda::OUTPUT_REFUSAL_DECLARED] = refusal.declared;
                output[morph_cuda::OUTPUT_REFUSAL_FOUND] = refusal.found;
                output[morph_cuda::OUTPUT_INVALID_KEY_ROW] = morph_cuda::OPEN_KEY_ROW;
                output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
            }
            return;
        }
    };
    let work = match 1usize.checked_add(shape.candidates) {
        Some(work) => work,
        None => return,
    };
    if lane >= work {
        return;
    }

    let candidates = unsafe { slice::from_raw_parts(candidate_words, candidate_words_len) };
    let deposits = unsafe { slice::from_raw_parts(deposit_words, deposit_words_len) };
    let key_rows = unsafe { slice::from_raw_parts(key_row_words, key_row_words_len) };
    let output = unsafe { slice::from_raw_parts_mut(output_words, output_words_len) };

    if lane == 0 {
        output[morph_cuda::OUTPUT_VERSION] = morph_cuda::LAYOUT_VERSION;
        output[morph_cuda::OUTPUT_EPOCH] = shape.epoch;
        output[morph_cuda::OUTPUT_CANDIDATES] = shape.candidates as u32;
        output[morph_cuda::OUTPUT_DEPOSITS] = shape.deposits as u32;
        output[morph_cuda::OUTPUT_KEY_ROWS] = shape.key_rows as u32;
        output[morph_cuda::OUTPUT_MAX_CANDIDATE_KEYS] = shape.max_candidate_keys as u32;
        output[morph_cuda::OUTPUT_CANDIDATE_ROW_WORDS] = shape.candidate_row_words as u32;
        output[morph_cuda::OUTPUT_CANDIDATE_ROWS_AT] = morph_cuda::OUTPUT_HEADER_WORDS as u32;
        output[morph_cuda::OUTPUT_TOTAL_WORDS] = shape.output_words as u32;
        output[morph_cuda::OUTPUT_INVALID_KEY_ROW] = morph_cuda::OPEN_KEY_ROW;
        output[morph_cuda::OUTPUT_REFUSAL_CAUSE] = morph_cuda::REFUSAL_NONE;
        output[morph_cuda::OUTPUT_REFUSAL_DECLARED] = 0;
        output[morph_cuda::OUTPUT_REFUSAL_FOUND] = 0;

        let mut active = 0u32;
        let mut deposit = 0usize;
        while deposit < shape.deposits {
            let at = deposit * shape.deposit_row_words;
            if deposits[at + morph_cuda::DEPOSIT_ACTIVE] > 1 {
                output[morph_cuda::OUTPUT_REFUSAL_CAUSE] =
                    morph_cuda::REFUSAL_DEPOSIT_ACTIVITY_WORD;
                output[morph_cuda::OUTPUT_REFUSAL_FOUND] = deposit as u32;
                output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                return;
            }
            if deposit > 0 {
                let earlier = morphological_deposit_key(deposits, shape, deposit - 1);
                let here = morphological_deposit_key(deposits, shape, deposit);
                if !morph_cuda::key_precedes(earlier, here) {
                    output[morph_cuda::OUTPUT_REFUSAL_CAUSE] =
                        morph_cuda::REFUSAL_DEPOSIT_SHEET_UNSORTED;
                    output[morph_cuda::OUTPUT_REFUSAL_FOUND] = deposit as u32;
                    output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                    return;
                }
            }
            if deposits[at + morph_cuda::DEPOSIT_ACTIVE] == 1 {
                active = match active.checked_add(1) {
                    Some(next) => next,
                    None => {
                        output[morph_cuda::OUTPUT_REFUSAL_CAUSE] =
                            morph_cuda::REFUSAL_ACTIVE_DEPOSIT_OVERFLOW;
                        output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                        return;
                    }
                };
            }
            deposit += 1;
        }
        let mut candidate = 0usize;
        while candidate < shape.candidates {
            if candidates[candidate * morph_cuda::CANDIDATE_WORDS + morph_cuda::CANDIDATE_FACE]
                == morph_cuda::OPEN_FACE
            {
                output[morph_cuda::OUTPUT_REFUSAL_CAUSE] = morph_cuda::REFUSAL_CANDIDATE_FACE_OPEN;
                output[morph_cuda::OUTPUT_REFUSAL_FOUND] = candidate as u32;
                output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                return;
            }
            candidate += 1;
        }
        output[morph_cuda::OUTPUT_ACTIVE_DEPOSITS] = active;

        let mut row = 0usize;
        while row < shape.key_rows {
            let at = row * shape.key_row_words;
            let owner = key_rows[at + morph_cuda::KEY_ROW_CANDIDATE] as usize;
            if owner >= shape.candidates {
                output[morph_cuda::OUTPUT_INVALID_KEY_ROW] = row as u32;
                output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                return;
            }
            if row > 0 {
                let earlier_at = (row - 1) * shape.key_row_words;
                let earlier_owner = key_rows[earlier_at + morph_cuda::KEY_ROW_CANDIDATE] as usize;
                let ascending = if earlier_owner == owner {
                    morph_cuda::key_precedes(
                        morphological_key_row_key(key_rows, shape, row - 1),
                        morphological_key_row_key(key_rows, shape, row),
                    )
                } else {
                    earlier_owner < owner
                };
                if !ascending {
                    output[morph_cuda::OUTPUT_INVALID_KEY_ROW] = row as u32;
                    output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_INVALID;
                    return;
                }
            }
            row += 1;
        }
        output[morph_cuda::OUTPUT_STATUS] = morph_cuda::STATUS_COMPLETE;
        return;
    }

    let candidate = lane - 1;
    let row_at = morph_cuda::OUTPUT_HEADER_WORDS + candidate * shape.candidate_row_words;
    output[row_at + morph_cuda::CANDIDATE_EPOCH] = shape.epoch;
    output[row_at + morph_cuda::CANDIDATE_ORDINAL] = candidate as u32;
    let candidate_face =
        candidates[candidate * morph_cuda::CANDIDATE_WORDS + morph_cuda::CANDIDATE_FACE];
    output[row_at + morph_cuda::CANDIDATE_OUTPUT_FACE] = candidate_face;
    let mut slot = 0usize;
    while slot < shape.max_candidate_keys {
        output[row_at + morph_cuda::CANDIDATE_MATCH_AT + slot] = morph_cuda::OPEN_DEPOSIT;
        slot += 1;
    }

    let mut invalid = candidate_face == morph_cuda::OPEN_FACE;
    let mut seen_key_rows = 0u32;
    let mut matched = 0usize;
    let mut previous = morph_cuda::OPEN_DEPOSIT;
    // The key sheet is validated ascending by owner, so this lane's block is contiguous and its
    // start is found rather than scanned to. Without this every lane reads the whole sheet and the
    // front costs `candidates × key_rows`, which is the cost law the by-extent cover exists to
    // avoid one level up.
    let mut low = 0usize;
    let mut high = shape.key_rows;
    while low < high {
        let middle = low + (high - low) / 2;
        if (key_rows[middle * shape.key_row_words + morph_cuda::KEY_ROW_CANDIDATE] as usize)
            < candidate
        {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    let mut row = low;
    while row < shape.key_rows {
        let at = row * shape.key_row_words;
        if key_rows[at + morph_cuda::KEY_ROW_CANDIDATE] as usize != candidate {
            break;
        }
        seen_key_rows = match seen_key_rows.checked_add(1) {
            Some(next) => next,
            None => {
                invalid = true;
                seen_key_rows
            }
        };
        let key = morphological_key_row_key(key_rows, shape, row);
        if let Some(deposit) = morphological_deposit_of_key(deposits, shape, key) {
            let deposit_at = deposit * shape.deposit_row_words;
            if deposits[deposit_at + morph_cuda::DEPOSIT_ACTIVE] == 1 {
                // The key sheet is validated ascending per candidate and the deposit sheet is
                // validated ascending, so a later key can only land on a later deposit. A match
                // that does not advance is a violated invariant, not a duplicate to absorb.
                if previous != morph_cuda::OPEN_DEPOSIT && deposit as u32 <= previous {
                    invalid = true;
                } else if matched < shape.max_candidate_keys {
                    output[row_at + morph_cuda::CANDIDATE_MATCH_AT + matched] = deposit as u32;
                    matched += 1;
                    previous = deposit as u32;
                } else {
                    invalid = true;
                }
            }
        }
        row += 1;
    }
    output[row_at + morph_cuda::CANDIDATE_KEY_ROWS] = seen_key_rows;
    output[row_at + morph_cuda::CANDIDATE_ACTIVE_DEPOSITS] = matched as u32;
    output[row_at + morph_cuda::CANDIDATE_STATUS] = if invalid {
        morph_cuda::STATUS_INVALID
    } else {
        morph_cuda::STATUS_COMPLETE
    };
}
