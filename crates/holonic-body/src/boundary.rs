//! boundary — THE OCTET-PACKET ORGAN'S I/O BOUNDARY (`RESEARCH/THE_MANIFOLD.md §IV`, step 2 of the
//! tensor-native build). Light in / radiation out, as SHAPES, with NO AUTHORED ENCODER. This module
//! is the exact octet-backed source species, not the universal membrane grain. A glyph exists only
//! by difference (`THE_SHAPE_ALGEBRA §II`): there is no symbolic representation of a datum without
//! relationships, so an octet does not enter as its absolute code (a symbol-fiction) — it enters as
//! its DIFFERENCE from context (the discrete derivative, the interval, the sign a TURN), and
//! radiation re-integrates the differences. The ANCHOR (the first contact) is the given the boundary
//! supplies — the constant of integration — dropped inward, so the interior carries the pure difference-shape.
//!
//! This is the encoding-happens-at-the-relating law made the boundary: the difference IS the relation, so the shape
//! is not authored, it is the byte's relation to what preceded it. `no_std`. The datum is a `num::Cog` (a shape —
//! magnitude ⊕ rank ⊕ turn), which the geometric product (`geom`/`Cog::mul`) then bonds into emergent molecules.

use crate::num::Cog;

/// THE INWARD DIFFERENCE — a byte relates to its predecessor by `dᵢ = bᵢ − bᵢ₋₁` (the discrete derivative), the sign a
/// TURN (never a stripped sign, never an absolute code). The datum carried inward is this difference-shape. Two
/// streams that differ only by a constant offset (a transposition of the anchor) yield the IDENTICAL differences —
/// that is why the glyph's identity is the relation, not the code.
#[inline]
pub fn difference(byte: u8, prev: u8) -> Cog {
    difference_word(byte as u32, prev as u32)
}

/// the SAME difference read off word-slots (the kernel's face of the boundary — SPIR-V carries no `u8` without
/// the `Int8` capability; the byte rides the low 8 bits of a `u32`). One law, two faces: `difference` delegates
/// here, so the two can never drift.
#[inline]
pub fn difference_word(byte: u32, prev: u32) -> Cog {
    Cog::lit((byte & 0xFF) as i64 - (prev & 0xFF) as i64)
}

/// THE OUTWARD INTEGRAL — radiation re-integrates a difference onto the running value (`bᵢ = bᵢ₋₁ + dᵢ`). The anchor
/// `b₀` is the given the boundary supplies at the horizon; the differences are the pure interior soul. Faces the byte
/// at the membrane (the finite glyph only ever at the I/O horizon).
#[inline]
pub fn integrate(prev: u8, diff: Cog) -> u8 {
    (prev as i64 + diff.face()) as u8
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec::Vec;

    /// ★ THE BOUNDARY ROUND-TRIPS, and the shape is ANCHOR-INVARIANT (the glyph exists only by difference).
    #[test]
    fn the_difference_shape_round_trips_and_is_anchor_invariant() {
        let stream = b"the machine reads its own source :: convolve(p,q) = fold";
        // §1 ROUND-TRIP — differences inward, integrate outward, the anchor the given: the stream returns exactly.
        let anchor = stream[0];
        let diffs: Vec<Cog> = (1..stream.len())
            .map(|i| difference(stream[i], stream[i - 1]))
            .collect();
        let mut out = Vec::with_capacity(stream.len());
        out.push(anchor);
        let mut prev = anchor;
        for &d in &diffs {
            let b = integrate(prev, d);
            out.push(b);
            prev = b;
        }
        assert_eq!(
            &out[..],
            stream,
            "the difference-shape round-trips (no information authored or lost)"
        );

        // §2 ANCHOR-INVARIANT — the SAME stream shifted by a constant offset yields the IDENTICAL differences: the
        // interior soul is the relation, never the code (transposition is identity — a glyph has no absolute self).
        for off in [1i64, 7, 64, 200] {
            for i in 1..stream.len() {
                let d_here = difference(stream[i], stream[i - 1]);
                let (sa, sb) = (
                    ((stream[i] as i64 + off) & 0xff) as u8,
                    ((stream[i - 1] as i64 + off) & 0xff) as u8,
                );
                // within a run that does not wrap the byte, the shifted difference equals the original difference
                if (stream[i] as i64 + off) < 256 && (stream[i - 1] as i64 + off) < 256 {
                    assert_eq!(
                        difference(sa, sb).face(),
                        d_here.face(),
                        "the difference is anchor-invariant (offset {off}, i {i})"
                    );
                }
            }
        }
    }
}
