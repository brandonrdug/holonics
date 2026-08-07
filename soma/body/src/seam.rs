//! seam — THE SWING'S substrate read-face.
//!
//! A packed construction grounds one scalar word at a time through this exact two-operation
//! boundary. Layout remains with the construction that owns it; the seam supplies no remapping,
//! cache, ordering, or law semantics. Whole-row readers prove their extent once, then every word
//! crosses this mouth without a second checked-index spelling.

#[cfg(target_arch = "spirv")]
use spirv_std::arch::IndexUnchecked;

/// The two-operation substrate seam. Implementations spell exactly `words[at]`.
///
/// # Safety
///
/// The caller guarantees `at < words.len()`. The implementation must access exactly that aligned
/// `u32` slot. Mutable spans are invocation-exclusive before they reach this boundary; a substrate
/// may therefore use its relaxed/none atomic store spelling, but correctness comes from the span's
/// single writer rather than atomic arbitration.
pub unsafe trait WordSeam {
    unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32;
    unsafe fn store_u32_unchecked(words: &mut [u32], at: usize, value: u32);
}

/// The ordinary Rust slice realization. Composite public readers establish a whole row before
/// selecting this unchecked mouth, so a short row has one structural absence face rather than a
/// field-by-field zero extension.
pub struct SliceWordSeam;

unsafe impl WordSeam for SliceWordSeam {
    #[inline(always)]
    unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
        #[cfg(target_arch = "spirv")]
        {
            *words.index_unchecked(at)
        }
        #[cfg(not(target_arch = "spirv"))]
        {
            *words.get_unchecked(at)
        }
    }

    #[inline(always)]
    unsafe fn store_u32_unchecked(words: &mut [u32], at: usize, value: u32) {
        #[cfg(target_arch = "spirv")]
        {
            *words.index_unchecked_mut(at) = value;
        }
        #[cfg(not(target_arch = "spirv"))]
        {
            *words.get_unchecked_mut(at) = value;
        }
    }
}

/// Prove one complete packed row without overflow-prone end arithmetic.
#[inline(always)]
pub fn row_fits(words: &[u32], at: usize, extent: usize) -> bool {
    at <= words.len() && extent <= words.len() - at
}

/// Safe scalar face for public boundary readers whose enclosing row is not already proved.
#[inline]
pub fn read_u32_with<S: WordSeam>(words: &[u32], at: usize) -> u32 {
    if at < words.len() {
        unsafe { S::read_u32_unchecked(words, at) }
    } else {
        0
    }
}

#[inline]
pub fn read_u32(words: &[u32], at: usize) -> u32 {
    read_u32_with::<SliceWordSeam>(words, at)
}
