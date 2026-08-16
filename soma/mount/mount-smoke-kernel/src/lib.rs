//! The PTX payload — two `extern "ptx-kernel"` entries proving the launch path end to end.
//! Pure integer work; no floats, no dice. Global invocation index is `block_idx*block_dim + thread_idx`.
//! The law crates are untouched; nothing here is engine law.
#![no_std]
#![feature(abi_ptx, stdarch_nvptx)]

use core::arch::nvptx;
use core::sync::atomic::{AtomicU64, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// The global invocation index of the calling thread.
#[inline(always)]
unsafe fn global_index() -> u32 {
    (nvptx::_block_idx_x() * nvptx::_block_dim_x() + nvptx::_thread_idx_x()) as u32
}

/// Each thread writes its own global invocation index into `out[i]`.
/// After a full grid over `n` cells, `out[i] == i` exactly.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn fill_identity(out: *mut u32) {
    let i = global_index();
    *out.offset(i as isize) = i;
}

/// The odd constant folded once per thread by `atomic_fold`. Fixed and odd by construction
/// so the exact cpu check `add_cell == count * FOLD_CONSTANT` cannot alias an even overlap.
pub const FOLD_CONSTANT: u64 = 2_305_843_009_213_693_951; // 2^61 - 1 (a Mersenne prime, odd)

/// Each thread folds `FOLD_CONSTANT` into `add_cell` (atomic add) and its own index into
/// `max_cell` (atomic max). After a grid of `count` threads:
///   `*add_cell == count * FOLD_CONSTANT`  and  `*max_cell == count - 1`.
#[no_mangle]
pub unsafe extern "ptx-kernel" fn atomic_fold(add_cell: *mut u64, max_cell: *mut u64) {
    let i = global_index() as u64;
    AtomicU64::from_ptr(add_cell).fetch_add(FOLD_CONSTANT, Ordering::Relaxed);
    AtomicU64::from_ptr(max_cell).fetch_max(i, Ordering::Relaxed);
}
