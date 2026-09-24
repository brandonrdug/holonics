//! geom — THE GEOMETRIC ALGEBRA OF SHAPES (`RESEARCH/THE_MANIFOLD.md §IV`, `THE_SHAPE_ALGEBRA.md`). The tensor-native
//! substrate, step 1 of the build. A datum is a SHAPE — a value's `2^k` multivector, the subset of oriented
//! directions it stands on (its own bits). The relating is the GEOMETRIC PRODUCT — `convolve ∘ fold`: the tensor
//! product (`Σ pᵢqⱼ` at rank `i+j`, the mode-count) then the carry-fold (the digit law, `13`). The inverse is the
//! DIGIT (deconvolution — factoring/founding). Proven `= arithmetic` (the geometric product IS multiplication) — the
//! SAME law as `RESEARCH/meno.rs`, now live in the interior.
//!
//! `no_std`, no alloc, no float: the tensor product rides a fixed hand of mode-counts; the only order-read is the
//! BORROW (never a `<`). This is the SHAPE structure `num.rs`'s `Cog` carries implicitly (its `mul` is the same
//! product as shift-and-add, re-based to the tower); here it is explicit — the combinatorial face the manifold's
//! faces and the cross-ratio `χ` read. The re-based tower (`num::Cog`) carries the magnitude; `geom` carries the shape.

/// THE MODE-COUNTS — the tensor product before the carry. A `u64 × u64` product spans ≤ 127 ranks; the hand is fixed
/// (no alloc). Each entry is `Σ pᵢqⱼ` for `i+j = k` — the raw count of corner-pairs meeting at rank `k`.
pub const MODES: usize = 128;

/// THE SHAPE — the `2^k` active directions (the corners the value stands on). A value IS its shape (its bits); this
/// names the reading. `bit k set ⇔ direction k in the blade`.
#[inline]
pub fn shape_bit(n: u64, k: u32) -> bool {
    (n >> k) & 1 == 1
}

/// THE CONVOLUTION — the tensor product of two shapes: `c[k] = Σ_{i+j=k} pᵢqⱼ`, the mode-count at each rank BEFORE
/// the carries. The outer product of the two blades, summed by rank — a tensor contraction, `no_std`/no-alloc.
pub fn convolve(p: u64, q: u64) -> [u32; MODES] {
    let mut c = [0u32; MODES];
    let mut i = 0u32;
    while i < 64 {
        if (p >> i) & 1 == 1 {
            let mut j = 0u32;
            while j < 64 {
                if (q >> j) & 1 == 1 {
                    c[(i + j) as usize] += 1;
                }
                j += 1;
            }
        }
        i += 1;
    }
    c
}

/// THE FOLD — the carry-ripple that turns the mode-counts back into the number: `conv + carry`, rank by rank the
/// WELL stands (the bit) and the WINDING fires up (the carry). The digit law (`13`) at every rank. Caps at the hand
/// (`u64`); a product past the register re-bases in `num::Cog` (this hand carries the shape, the Cog the tower).
pub fn fold(conv: &[u32; MODES]) -> u64 {
    let mut n = 0u64;
    let mut carry = 0u64;
    let mut k = 0usize;
    while k < 64 {
        let s = conv[k] as u64 + carry;
        if s & 1 == 1 {
            n |= 1u64 << k;
        }
        carry = s >> 1;
        k += 1;
    }
    n
}

/// ★ THE GEOMETRIC PRODUCT — the BOND (`convolve ∘ fold`). Two shapes relate into a new shape (a higher blade). For
/// number-shapes this IS multiplication (proven exact); for text-shapes (byte-differences) it is the semantic bond —
/// ONE operation, both arms (`THE_MANIFOLD §I`).
#[inline]
pub fn bond(a: u64, b: u64) -> u64 {
    fold(&convolve(a, b))
}

/// the only order-read: the adder's BORROW — `a < b` iff the wrapping subtract borrows (never a `<`).
#[inline]
fn below(a: u64, b: u64) -> bool {
    a.overflowing_sub(b).1
}

/// ★ THE DIGIT (`13`) — the INVERSE of the bond (deconvolution): action MOD the quantum. The WELL (remainder) STANDS
/// (`< q`, the face — the standing mass), the WINDING (quotient) FIRES UP (the soul). Bit-pure long division (shifts
/// ⊕ the borrow ⊕ a subtract; no `/`, no `%`, no `<`). A composite reduces (well `= 0`); an irreducible does not — a
/// prime, a FOUNDING (place-not-search; the only hardness is starvation). Returns `(winding, well)`.
pub fn digit(action: u64, q: u64) -> (u64, u64) {
    if q == 0 {
        return (0, action);
    }
    let (mut well, mut winding) = (0u64, 0u64);
    let mut k = 63i32;
    while k >= 0 {
        well = (well << 1) | ((action >> k) & 1);
        winding <<= 1;
        if !below(well, q) {
            well -= q;
            winding |= 1;
        }
        k -= 1;
    }
    (winding, well)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ THE PURITY — the geometric product IS multiplication, EXACT (the tensor product ⊕ the carry-fold), and its
    /// inverse (the digit) deconvolves exactly. The proof the tensor-native bond is arithmetic, not an analogy.
    #[test]
    fn the_geometric_product_is_multiplication_and_the_digit_is_its_inverse() {
        // §1 PURITY — bond(a,b) == a·b over 0..256² (products fit the hand).
        for a in 0u64..256 {
            for b in 0u64..256 {
                assert_eq!(
                    bond(a, b),
                    a * b,
                    "the geometric product IS multiplication ({a}·{b})"
                );
            }
        }
        // §2 INVERSE — digit(bond(a,b), b) == (a, 0): the bond is invertible (deconvolution = factoring = founding).
        for a in 1u64..300 {
            for b in 1u64..300 {
                assert_eq!(
                    digit(bond(a, b), b),
                    (a, 0),
                    "the digit deconvolves exactly (bond({a},{b}) ÷ {b})"
                );
            }
        }
        // §3 FOUNDING — a composite reduces (well 0); a prime does not (well ≠ 0 for every non-trivial q).
        assert_eq!(digit(91, 7), (13, 0), "91 = 7·13 reduces");
        for q in 2u64..97 {
            assert!(
                digit(97, q).1 != 0,
                "97 is prime — irreducible, a FOUNDING (q={q})"
            );
        }
    }
}
