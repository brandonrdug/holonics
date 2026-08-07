//! place — PLACE-NOT-STORE. A construction's identity is WHERE IT SWINGS TO — a complex position read off its
//! bits, frame-local, re-based — never a stored address. A place is `(Re, Im)` = magnitude ⊕ TURN; the turn (the
//! soul, the winding) is load-bearing and never flattened to `Re`.
//!
//! ★ THE QUANTUM IS THE BIT — a place is **extended one bit at a time** (`extend`), never by a byte. Bit `k` lands
//! on the gaussian axis `i^k` (the quarter-turn per bit), so ORDER is the soul *by construction*: there is no byte,
//! no 8-bit closure, and no succession phasor to patch it (the `i⁴` cycling carries the order natively — the
//! byte-grain patch never existed here).

use crate::num::Cog;

/// A PLACE — a complex position a perspective has wound to. Carried, re-based, never an absolute coordinate.
pub type Place = (Cog, Cog);

/// A GRIP — a swung position in the net: WHERE A PLACE SETTLES TO (`ground`), the construction's intrinsic cell,
/// never an address the current picked. Place-not-store: the boundary lives AT its grip.
pub type Grip = u32;

/// ★ SPIRAL a place up by `n` ranks — `place · (2i)^n`: the radius climbs `n` (×2ⁿ) and the phase turns `n`
/// quarters. Used to COMPOSE a composite's place from its constituents — `place(a∘b) = spiral(place_a, len_b) ⊕
/// place_b`, the concatenation in base `2i`. Place-not-store: the composite's place is *derived* from its two
/// children (same children → same place → same grip), never stored. `n` ranks is `turn_up(n)`; `i^n` cycles by `& 3`.
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn spiral(place: Place, n: u32) -> Place {
    let re = place.0.turn_up(n); // ×2ⁿ — the radius climbs n ranks
    let im = place.1.turn_up(n);
    match n & 3 {
        0 => (re, im),
        1 => (im.turned(2), re),           // ×i  = (−im, re)
        2 => (re.turned(2), im.turned(2)), // ×−1 = (−re, −im)
        _ => (im, re.turned(2)),           // ×−i = (im, −re)
    }
}

/// Band a Cog to a frame-local axis-band — the swung position settling into a discrete cell. Use the **re-based
/// MANTISSA** (`mag`), not the face (`mag·2^rank`): the face saturates for deep grains (rank ≥ register width → all
/// of them collapse to one grip — the lossy place above a byte), but the mantissa is always a bounded `u32` (the
/// construction's leading structure, re-based), so deep grains stay distinct. The turn is folded into the high band
/// (the soul carried into the cell). `axis` is a power of two → the wrap is a MASK (`&(n−1)`), no `%`.
///
/// ★ THE RANK FOLDS IN (soma W4, measured on the definitional-topology quest): the composition spiral climbs
/// ONLY rank (`turn_up` leaves the mantissa whole), so a rank-blind band collapses exactly the coordinate the
/// composition law moves on — every `X→b` composite grounded onto one hot band (~10³ over random, measured; the
/// definitional faces unreadable through it). The rank therefore folds into the band beside the turn — the
/// mantissa keeps the low bits (nearness preserved), the climb keeps its own address. Never the FACE (that
/// saturation stays retired); the rank enters as its own re-based coordinate, wrapped.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
fn band(c: Cog, axis: i64) -> i64 {
    let m = c.mag as i64;
    let tz = axis.trailing_zeros();
    let sh = if tz >= 2 { tz - 2 } else { 0 }; // `saturating_sub(2)` explicit — the rust-gpu kernel has no saturating intrinsic
    let turn = ((c.turn & 3) as i64) << sh; // the soul, into the high band
    let rk = match c.rank.face() {
        Some(r) => r,    // the climb — the composition's own coordinate
        None => 1 << 30, // past the rung's face: a deep-tower band of its own, never a collapse onto rank 0
    };
    let sh_rank = if tz >= 4 { tz - 4 } else { 0 }; // the rank's fold, below the turn's
    (m.wrapping_add(turn)
        .wrapping_add(rk.wrapping_mul(3).wrapping_shl(sh_rank))
        .wrapping_add(axis >> 1))
        & (axis - 1)
}

#[derive(Clone, Copy)]
struct ShiftedGroundPart {
    value: u64,
    shift: u64,
}

/// Allocation-free word traversal of one coordinate in an arbitrary-rank dyadic receiver chart.
/// This is the one body-owned extension of [`ground`] beyond the exact flat `u32` face.  Storage
/// owners may retain, compare, or stream these least-significant words, but they may not respell
/// the turn/rank/centering law.
pub struct GroundCoordinateWords {
    rank: u64,
    words: u64,
    at: u64,
    carry: u64,
    parts: [ShiftedGroundPart; 4],
}

impl GroundCoordinateWords {
    #[inline]
    pub const fn rank(&self) -> u64 {
        self.rank
    }

    #[inline]
    pub const fn words(&self) -> u64 {
        self.words
    }
}

impl Iterator for GroundCoordinateWords {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.at >= self.words {
            return None;
        }
        let mut sum = self.carry;
        let mut next_carry = 0u64;
        let mut part = 0usize;
        while part < self.parts.len() {
            let source = self.parts[part];
            let base = source.shift / 64;
            let bit = (source.shift & 63) as u32;
            let value = if self.at == base {
                source.value << bit
            } else if bit != 0 && self.at == base + 1 {
                source.value >> (64 - bit)
            } else {
                0
            };
            let (joined, overflow) = sum.overflowing_add(value);
            sum = joined;
            next_carry += overflow as u64;
            part += 1;
        }
        self.carry = next_carry;
        self.at += 1;
        if self.at == self.words {
            let tail = (self.rank & 63) as u32;
            if tail != 0 {
                sum &= (1u64 << tail) - 1;
            }
        }
        Some(sum)
    }
}

#[inline]
fn rung_low_twos(rung: crate::num::Rung, bits: u32) -> Option<u64> {
    if bits == 0 || rung.mag == 0 {
        return Some(0);
    }
    if rung.rank < 0 {
        return None;
    }
    let shift = rung.rank as u32;
    let mask = (1u64 << bits) - 1;
    let magnitude = if shift >= bits {
        0
    } else {
        ((rung.mag as u64) << shift) & mask
    };
    Some(if rung.neg {
        0u64.wrapping_sub(magnitude) & mask
    } else {
        magnitude
    })
}

/// Begin the canonical arbitrary-rank grounding of one Cog coordinate.  Rank zero has no stored
/// coordinate words and represents the unique axis-one cell.  A malformed below-zero rung refuses
/// rather than being silently recast as a different address.
pub fn ground_coordinate_words(cog: Cog, rank: u64) -> Option<GroundCoordinateWords> {
    let words = rank.checked_add(63)? / 64;
    if rank == 0 {
        return Some(GroundCoordinateWords {
            rank,
            words,
            at: 0,
            carry: 0,
            parts: [
                ShiftedGroundPart { value: 0, shift: 0 },
                ShiftedGroundPart { value: 0, shift: 0 },
                ShiftedGroundPart { value: 0, shift: 0 },
                ShiftedGroundPart { value: 0, shift: 0 },
            ],
        });
    }
    let turn_bits = rank.min(2) as u32;
    let turn_mask = (1u64 << turn_bits) - 1;
    let rung_bits = rank.min(4) as u32;
    let rung_mask = (1u64 << rung_bits) - 1;
    let rung = rung_low_twos(cog.rank, rung_bits)?;
    Some(GroundCoordinateWords {
        rank,
        words,
        at: 0,
        carry: 0,
        parts: [
            ShiftedGroundPart {
                value: cog.mag as u64,
                shift: 0,
            },
            ShiftedGroundPart {
                value: (cog.turn as u64) & turn_mask,
                shift: rank.saturating_sub(2),
            },
            ShiftedGroundPart {
                value: rung.wrapping_mul(3) & rung_mask,
                shift: rank.saturating_sub(4),
            },
            ShiftedGroundPart {
                value: 1,
                shift: rank - 1,
            },
        ],
    })
}

/// ★ GROUND a place to its swung GRIP `[0, axis²)` — WHERE IT SWINGS TO (place-not-store, the founder's cell). BOTH
/// axes contribute (`band(re)` ⊕ `band(im)`), so the turn (the soul) is carried into the cell, never collapsed to
/// `Re`. Nearness-preserving (NOT a hash): nearby places → nearby grips, so recurrence is the swing landing again.
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn ground(place: Place, axis: i64) -> Grip {
    let r = band(place.0, axis);
    let i = band(place.1, axis);
    (r * axis + i) as Grip
}

/// The origin grip — no turn, no magnitude (the moving origin's instant).
#[inline]
pub fn origin() -> Place {
    (Cog::lit(0), Cog::lit(0))
}

/// THE ×i TURN on a complex place — the orthogonal quarter-turn `(re,im)·i = (−im, re)`: a DIRECTION (the founding's
/// new axis), never a magnitude-spread; scale is the rank, carried elsewhere.
#[inline]
fn spin(re: Cog, im: Cog) -> (Cog, Cog) {
    (im.turned(2), re)
}

/// ★ EXTEND a place by ONE BIT (the quantum) — the per-bit step, O(1), carried (never a re-walk). Each bit turns
/// the place a quarter (`×i`, the winding = the soul) AND climbs a rank (`×2`, the place-value) — together `×2i`, a
/// logarithmic SPIRAL, never a circle. So bit `k` lands at `(2i)^k`: the **magnitude grows with the stream** (a
/// longer construction is bigger, and short streams cannot cancel to the origin — the `i⁴` closure is broken by the
/// radius, not patched by a byte-phasor) while the **phase carries the order** (the soul). If the boundary is LIVE,
/// fold the unit step on the real axis. `place = place·2i + bit` — the bit-stream's value in base `2i`.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
pub fn extend(place: Place, live: bool) -> Place {
    let (re, im) = place;
    let (sre, sim) = spin(re, im); // ×i — the winding (the soul turns)
    let re = sre.turn_up(1); // ×2 — the rank climbs (the place-value; the radius grows, so no cancellation)
    let im = sim.turn_up(1);
    let re = if live { re.add(Cog::lit(1)) } else { re }; // ⊕ the unit step iff the boundary is live
    (re, im)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_same_stream_winds_to_the_same_place() {
        let wind = |bits: &[bool]| bits.iter().fold(origin(), |p, &b| extend(p, b));
        assert_eq!(
            wind(&[true, false, true, true]),
            wind(&[true, false, true, true])
        );
    }

    #[test]
    fn order_is_the_soul_and_the_place_does_not_collapse() {
        let wind = |bits: &[bool]| bits.iter().fold(origin(), |p, &b| extend(p, b));
        // the SAME live bits in a different ORDER wind to a different place (base-2i: bit k lands at (2i)^k)
        assert_ne!(
            wind(&[true, true, false, false]),
            wind(&[false, false, true, true]),
            "order is carried"
        );
        // a non-empty live stream never collapses to the origin (the radius grows — no i⁴ cancellation)
        assert_ne!(
            wind(&[true, false, true]),
            origin(),
            "the spiral never returns to the pole"
        );
        // the turn (Im) is load-bearing — a stream winds off the real axis (the soul is carried, never flattened)
        assert_ne!(
            wind(&[true, true]).1.face(),
            0,
            "the place carries its winding off Re"
        );
    }

    #[test]
    fn arbitrary_rank_coordinate_words_are_the_flat_ground_law_without_a_u32_ceiling() {
        let bases = [
            Cog::ZERO,
            Cog::lit(257),
            Cog::lit(-65_537),
            Cog {
                mag: u32::MAX - 16,
                rank: crate::num::Rung {
                    mag: 5,
                    rank: 1,
                    neg: true,
                },
                turn: 0,
            },
        ];
        for rank in 0..=16u64 {
            let axis = 1i64 << rank;
            for base in bases {
                for turn in 0..4 {
                    let cog = Cog { turn, ..base };
                    let words: std::vec::Vec<_> =
                        ground_coordinate_words(cog, rank).unwrap().collect();
                    let coordinate = words.first().copied().unwrap_or(0);
                    assert_eq!(coordinate, band(cog, axis) as u64);
                }
            }
        }

        for rank in [63, 64, 65, 127, 128, 129] {
            let cog = Cog {
                mag: u32::MAX - 2,
                rank: crate::num::Rung {
                    mag: 7,
                    rank: 1,
                    neg: false,
                },
                turn: 3,
            };
            let once: std::vec::Vec<_> = ground_coordinate_words(cog, rank).unwrap().collect();
            let twice: std::vec::Vec<_> = ground_coordinate_words(cog, rank).unwrap().collect();
            assert_eq!(once, twice);
            assert_eq!(once.len() as u64, (rank + 63) / 64);
            if rank & 63 != 0 {
                assert_eq!(once.last().unwrap() >> (rank & 63), 0);
            }
        }
    }
}
