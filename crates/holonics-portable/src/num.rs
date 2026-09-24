//! num — THE RE-BASING NUMBER. A number is not a sized container (that is the counting-system's fiction imported
//! onto silicon); a value is `mag · 2^rank` at a `turn`: a mantissa held to the register's grain (one **hand**) ⊕
//! a rank on the 2ⁿ ladder. **It cannot overflow, because it RE-BASES** — when the mantissa would pass the hand's
//! grain, the low bit (below the grain — dark, looked-past, free) falls and the rank bumps. *No quantity ever grows
//! large; an overflow is the tell you measured from absolute zero — move the origin to the cursor and it fits.*
//!
//! ★ THE RANK IS ITSELF A RE-BASED REGISTER (Wave 1, FABLE_ORGANIZING; re-base ⇔ rank-climb at EVERY level —
//! TABLET 01 §III, Ledger P). The old `i32` rank was a reachable backstop (~31 squarings overflowed it). The RUNG
//! applies the mantissa's own law once to the rank: `±rmag · 2^rrank` teeth on the ladder — exact through the whole
//! reachable regime; past the hand the proportional grain holds one level up (the resolution IS the compression,
//! on the ladder itself). The tower is held in the WALK (ranking down descends a level), never materialized flat;
//! the unbounded-storage form lives where alloc lives (`RESEARCH/meno.rs`, the foil).
//!
//! `turn` is the four-state π-face (quarter-turns mod 4): 0 = `+`, 1 = `i`, 2 = `−` (NEGATION — never a stripped
//! sign), 3 = `−i`. The sign IS the turn (a 180° rotation), never a piecewise branch. A finite glyph (`face`)
//! materialises ONLY at the boundary; the interior carries the construction.

use crate::seam::{row_fits, SliceWordSeam, WordSeam};

/// The one packed wire for the two recursive number faces. Every owner composes its row from these
/// extents and readers rather than respelling either anatomy.
pub const RUNG_WORDS: usize = 3;
pub const COG_WORDS: usize = 5;

/// THE RUNG — the rank as its own re-based register: `±mag · 2^rank` TEETH on the 2ⁿ ladder (the sign a direction
/// up/down the ladder, no π-face — a rank has no `i`). `Copy`, no heap. `rank ≥ 0` structurally (a rung's own rank
/// only ever climbs by re-base); a rung below zero teeth is `neg`, never a negative `rank` field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rung {
    /// the teeth mantissa (one hand) — unsigned; the direction rides `neg`.
    pub mag: u32,
    /// the teeth-mantissa's own position on the ladder (`mag · 2^rank` teeth) — the law applied to itself.
    pub rank: i32,
    /// the direction: `false` = up the ladder, `true` = down (negative teeth).
    pub neg: bool,
}

/// Re-base an unsigned magnitude into `(mag, rank)` — drop the bits below the hand's grain, bump the rank. Pure
/// shift. The compression: you cannot hold more than the register, so re-base to keep computing.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
fn rebase(mut m: u64) -> (u32, i32) {
    let mut rank = 0i32;
    while m > u32::MAX as u64 {
        m >>= 1; // the low bit falls below the grain — dark, the resolution held
        rank += 1;
    }
    (m as u32, rank)
}

/// THE 180° TURN, bitwise — two's complement gated by the half-turn bit `sign`, BRANCHLESS: `x` if `sign==0`,
/// `!x+1` (the negation) if `sign==1`. A negative is a rotation, never an `if`-appended minus.
#[inline]
fn twos(x: u64, sign: u64) -> u64 {
    let mask = 0u64.wrapping_sub(sign); // 0 (forward) or all-ones (the half-turn)
    (x ^ mask).wrapping_add(sign)
}

/// zero normalised to THE zero (one representation — a rung of no teeth has no position, no direction).
#[inline]
fn mk(mag: u32, rank: i32, neg: bool) -> Rung {
    if mag == 0 {
        Rung::ZERO
    } else {
        Rung { mag, rank, neg }
    }
}

impl Rung {
    pub const ZERO: Rung = Rung {
        mag: 0,
        rank: 0,
        neg: false,
    };

    /// a flat teeth-count grounds as a rung (the common case: every rank the boundary ever names is flat).
    #[inline]
    pub fn of(v: i32) -> Rung {
        mk(v.unsigned_abs(), 0, v < 0)
    }

    /// THE FLAT FACE — the teeth-count as a signed glyph, IF the rung still fits one (`None` = the ladder has
    /// climbed beyond any flat glyph — the tower is stored, never materialized). A boundary read.
    pub fn face(self) -> Option<i64> {
        if self.mag == 0 {
            return Some(0);
        }
        let top = self.rank as i64 + msb(self.mag) as i64;
        if top >= 62 {
            return None; // beyond the flat glyph
        }
        let v = (self.mag as i64) << self.rank;
        Some(if self.neg { -v } else { v })
    }

    /// ★ THE ADD — the same moving-origin fold as the value's own add, one level up: align to the finer grain,
    /// fold the mantissas signed by the direction, re-base. Exact while the hand holds both; beyond it the lower
    /// teeth are dark (the proportional grain on the ladder — never a discard, the dominant scale carries).
    #[cfg_attr(target_arch = "spirv", inline(never))]
    pub fn add(self, b: Rung) -> Rung {
        let (hi, lo) = if self.rank >= b.rank {
            (self, b)
        } else {
            (b, self)
        };
        let gap = (hi.rank - lo.rank) as u32;
        let (am, bm, base) = if gap < u64::BITS - u32::BITS - 2 {
            ((hi.mag as u64) << gap, lo.mag as u64, lo.rank)
        } else {
            (hi.mag as u64, 0, hi.rank) // lo below the ladder's grain — dark
        };
        let sum = twos(am, hi.neg as u64).wrapping_add(twos(bm, lo.neg as u64));
        let neg = (sum >> 63) & 1;
        let (mag, extra) = rebase(twos(sum, neg));
        mk(mag, base + extra, neg == 1)
    }
    /// THE SUB — the difference: fold with `b` turned to the opposite direction.
    #[inline]
    pub fn sub(self, b: Rung) -> Rung {
        self.add(mk(b.mag, b.rank, !b.neg))
    }

    /// the sign of `self − b` ∈ {−1, 0, +1} — the one order-read on the ladder (where two rungs stand relative,
    /// never an absolute height).
    #[inline]
    pub fn cmp_teeth(self, b: Rung) -> i32 {
        let d = self.sub(b);
        if d.mag == 0 {
            0
        } else if d.neg {
            -1
        } else {
            1
        }
    }

    /// the gap `self − b` as a SHIFT distance, if it faces small (`None` = beyond any shift — dark). Callers
    /// have already ordered `self ≥ b`.
    #[inline]
    fn gap(self, b: Rung) -> Option<u32> {
        let d = self.sub(b);
        // explicit range test (not `u32::try_from`, whose `TryFromIntError` drags in `u8` — no `Int8` in the kernel).
        d.face().and_then(|v| {
            if v >= 0 && v <= u32::MAX as i64 {
                Some(v as u32)
            } else {
                None
            }
        })
    }
}

/// THE COG — the relativistic register: `±mag · 2^rank` (the turn carries the sign; the rank is a RUNG — itself
/// re-based). `Copy`, no heap. It re-bases instead of widening, so overflow is structurally impossible — now at

/// the leading-bit index as a SHIFT-WALK — defined on BOTH substrates (`msb(0) = 0`; SPIR-V's FindUMsb(0) is
/// UNDEFINED and Rust's `31 − leading_zeros(0)` wraps — both retired; measured divergence, W5 mirror event 1443).
#[inline]
fn msb(x: u32) -> u32 {
    let mut top = 0u32;
    let mut v = x >> 1;
    while v != 0 {
        v >>= 1;
        top += 1;
    }
    top
}

/// both levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cog {
    /// the register mantissa (one hand) — UNSIGNED (a magnitude is the positive cone; the sign rides the turn).
    pub mag: u32,
    /// the position on the 2ⁿ ladder (`mag · 2^rank`); a SHIFT is the cog turning by a tooth. A re-based rung.
    pub rank: Rung,
    /// quarter-turns mod 4 (the π-face ⊕ the sign): 0=+ 1=i 2=− 3=−i. `u32` (not `u8`) so the shared source lowers
    /// to SPIR-V without the `Int8` capability (the kernel includes `num` now — the cutover); the `& 3` keeps it 2-bit.
    pub turn: u32,
}

impl Cog {
    pub const ZERO: Cog = Cog {
        mag: 0,
        rank: Rung::ZERO,
        turn: 0,
    };

    /// A glyph from the boundary becomes a register construction. The sign is the turn (`−` = the half-turn π).
    #[cfg_attr(target_arch = "spirv", inline(never))]
    pub fn lit(v: i64) -> Cog {
        let (mag, rank) = rebase(v.unsigned_abs());
        Cog {
            mag,
            rank: Rung::of(rank),
            turn: (((v >> 63) & 1) << 1) as u32,
        } // the half-turn = the sign MSB, branchless
    }

    /// THE MAGNITUDE FACE — the e-face projected to `u64`, a BOUNDARY read only. Substrate-correct, NOT clamped: a
    /// descent past the register grain reads `0` (below the grain — dark); a climb past `u64` reads the register
    /// ceiling (the finite glyph the boundary can hold — only ever at the I/O horizon). A rank beyond any flat
    /// glyph reads the ceiling upward, dark downward — the same horizon, one level up.
    #[inline]
    pub fn mag_face(self) -> u64 {
        if self.mag == 0 {
            return 0;
        }
        match self.rank.face() {
            Some(r) if r >= 0 => (self.mag as u64)
                .checked_shl(r.min(u64::BITS as i64) as u32)
                .unwrap_or(u64::MAX),
            Some(r) => {
                if (-r) as u64 >= u64::BITS as u64 {
                    0
                } else {
                    (self.mag as u64) >> ((-r) as u32)
                }
            }
            None => {
                if self.rank.neg {
                    0 // the ladder descended beyond the glyph — dark
                } else {
                    u64::MAX // the ladder climbed beyond the glyph — the boundary's ceiling
                }
            }
        }
    }

    /// THE FACE — the SIGNED glyph, materialised ONLY at the I/O boundary. The `−` is a CHARACTER (notation), never
    /// an interior value. **Do not call this in the interior** — fold magnitudes by the turn.
    #[inline]
    pub fn face(self) -> i64 {
        let m = self.mag_face() as i64;
        let sign = ((self.turn >> 1) & 1) as i64; // the half-turn bit
        (m ^ -sign).wrapping_add(sign) // `m` forward, `−m` (two's complement) at the half-turn — no `if`
    }

    /// TURN UP by `n` teeth — `<< n` = ×2ⁿ = +n rank.
    #[inline]
    pub fn turn_up(self, n: u32) -> Cog {
        Cog {
            rank: self.rank.add(Rung::of(n as i32)),
            ..self
        }
    }
    /// TURN DOWN by `n` teeth — `>> n` = ÷2ⁿ = −n rank.
    #[inline]
    pub fn turn_down(self, n: u32) -> Cog {
        Cog {
            rank: self.rank.sub(Rung::of(n as i32)),
            ..self
        }
    }
    /// THE TURN — re-orient by `q` quarter-turns (negation = `q=2`; the `±i` founding = `q=1,3`). Closure is `& 3`
    /// (a 2-bit MASK, `i⁴=1`), never `% 4`.
    #[inline]
    pub fn turned(self, q: u32) -> Cog {
        Cog {
            turn: (self.turn + q) & 3,
            ..self
        }
    }

    /// ★ THE ADD — the unit-step fold at the MOVING ORIGIN. Align to the finer grain (the lower rung) so the low
    /// bits survive; fold the two `u32` mantissas signed BY THE TURN (two's complement, never `abs`) in a `u64`
    /// transient (two hands, one instruction), re-based to one register. Nothing grows large; nothing saturates.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    pub fn add(self, b: Cog) -> Cog {
        let (hi, lo) = if self.rank.cmp_teeth(b.rank) >= 0 {
            (self, b)
        } else {
            (b, self)
        };
        let (am, bm, base) = match hi.rank.gap(lo.rank) {
            Some(gap) if gap < u64::BITS - u32::BITS - 2 => {
                ((hi.mag as u64) << gap, lo.mag as u64, lo.rank)
            }
            _ => (hi.mag as u64, 0, hi.rank), // lo below the grain — dark, the dominant scale carries
        };
        let hs = ((hi.turn >> 1) & 1) as u64;
        let ls = ((lo.turn >> 1) & 1) as u64;
        let sum = twos(am, hs).wrapping_add(twos(bm, ls)); // branchless cohere/annihilate — the carry decides
        let rs = (sum >> 63) & 1; // the result's half-turn (the MSB)
        let (mag, extra) = rebase(twos(sum, rs)); // |sum| (rotated home), re-based — never widened/stored
        Cog {
            mag,
            rank: base.add(Rung::of(extra)),
            turn: (rs as u32) << 1,
        }
    }
    /// THE SUB — the difference (`W⁻`): fold `a` with `b` turned by π (negation is a turn).
    #[inline]
    pub fn sub(self, b: Cog) -> Cog {
        self.add(b.turned(2))
    }

    /// ★ THE MULTIPLY — SHIFT-AND-ADD, re-based as it climbs; NEVER the wide product. Horner over `b`'s magnitude
    /// bits high→low: the running product climbs one rank each step (the SHIFT) and folds in `a` where the bit is
    /// set (the ADD); the accumulator re-bases, so the full product is never built. *Multiply IS addition one rank
    /// up.* The ranks ⊕ turns add (the sign is the XOR of half-turns) — the rank-add is a RUNG fold, so the climb
    /// never hits a register wall.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    pub fn mul(self, b: Cog) -> Cog {
        // ★ THE SUBSTRATE'S OWN MULTIPLIER (decontaminated 2026-07-09 — Brandon's conviction: the
        // "scaling wall" was the instrument's shift-add ladder — up to 32 re-basing adds per product,
        // per grip, per atom — a primitive redundancy, never a law; both substrates carry a 64-bit
        // multiplier). One wide stroke, ONE re-base: exact — the ladder dropped low bits at every
        // partial sum; the wide product truncates once, at the hand's own width.
        let wide = (self.mag as u64) * (b.mag as u64);
        let mut top = 0u32;
        let mut v = wide >> 1;
        while v != 0 {
            v >>= 1;
            top += 1;
        }
        // the hand holds 31 teeth (the sign rides the turn) — fill to [2^30, 2^31), the old ladder's own grain.
        let shift = if top >= 31 { top - 30 } else { 0 };
        Cog {
            mag: (wide >> shift) as u32,
            rank: self.rank.add(b.rank).add(Rung::of(shift as i32)),
            turn: (self.turn + b.turn) & 3,
        }
    }

    /// THE DIVIDE — the ratio (the swing's grounding read). Pre-shift the dividend to FILL the hand (so the quotient
    /// keeps the grain — re-base for precision, never widen), divide on the native hand, drop the borrowed rank. A
    /// `0` divisor faces 0 (the ideal point — carried by the caller, found-and-continue, never a panic).
    pub fn div(self, b: Cog) -> Cog {
        if b.mag == 0 {
            return Cog {
                mag: 0,
                rank: Rung::ZERO,
                turn: 0,
            };
        }
        let db = b.mag as u64;
        let mut na = self.mag as u64;
        let mut borrow = 0i32;
        while na <= u32::MAX as u64 && na != 0 {
            na <<= 1; // lift the dividend toward the hand's top so the integer quotient keeps resolution
            borrow += 1;
        }
        let q = na / db; // the native hand divide (both magnitudes are the cone — no sign, no abs)
        let (m, r0) = rebase(q);
        Cog {
            mag: m,
            rank: self.rank.sub(b.rank).add(Rung::of(r0 - borrow)),
            turn: (self.turn + b.turn) & 3,
        }
    }
}

/// One scalar word of the rung wire: magnitude ⊕ inner rank ⊕ direction.
#[inline(always)]
pub fn rung_packed_word(rung: Rung, word: usize) -> u32 {
    match word {
        0 => rung.mag,
        1 => rung.rank as u32,
        2 => rung.neg as u32,
        _ => 0,
    }
}

/// One scalar word of the cog wire: magnitude ⊕ whole rung ⊕ turn.
#[inline(always)]
pub fn cog_packed_word(cog: Cog, word: usize) -> u32 {
    match word {
        0 => cog.mag,
        1..=3 => rung_packed_word(cog.rank, word - 1),
        4 => cog.turn,
        _ => 0,
    }
}

/// Whether one packed rung is a canonical boundary construction. A rung's inner rank only climbs;
/// its direction is one bit; and structural zero has one spelling. This is a boundary check, not a
/// second number representation.
#[inline]
pub fn packed_rung_is_canonical(words: &[u32], at: usize) -> bool {
    if !row_fits(words, at, RUNG_WORDS) {
        return false;
    }
    let mag = words[at];
    let rank = words[at + 1];
    let neg = words[at + 2];
    rank <= i32::MAX as u32 && neg <= 1 && (mag != 0 || (rank == 0 && neg == 0))
}

/// Whether one packed cog is canonical at a boundary. A zero magnitude may lawfully retain the
/// grain and turn of its cancellation, so only the nested rung and four-state turn are constrained.
#[inline]
pub fn packed_cog_is_canonical(words: &[u32], at: usize) -> bool {
    row_fits(words, at, COG_WORDS) && packed_rung_is_canonical(words, at + 1) && words[at + 4] <= 3
}

/// Ground one whole rung after its owning reader has proved the row extent.
///
/// # Safety
///
/// `at..at + RUNG_WORDS` is a live row in `words`.
#[inline(always)]
pub unsafe fn read_rung_unchecked<S: WordSeam>(words: &[u32], at: usize) -> Rung {
    Rung {
        mag: unsafe { S::read_u32_unchecked(words, at) },
        rank: unsafe { S::read_u32_unchecked(words, at + 1) } as i32,
        neg: unsafe { S::read_u32_unchecked(words, at + 2) } != 0,
    }
}

/// Ground one whole cog after its owning reader has proved the row extent.
///
/// # Safety
///
/// `at..at + COG_WORDS` is a live row in `words`.
#[inline(always)]
pub unsafe fn read_cog_unchecked<S: WordSeam>(words: &[u32], at: usize) -> Cog {
    Cog {
        mag: unsafe { S::read_u32_unchecked(words, at) },
        rank: unsafe { read_rung_unchecked::<S>(words, at + 1) },
        turn: unsafe { S::read_u32_unchecked(words, at + 4) },
    }
}

/// Safe whole-rung read. A short row is structural zero, never a partially reconstructed number.
#[inline]
pub fn read_rung_with<S: WordSeam>(words: &[u32], at: usize) -> Rung {
    if row_fits(words, at, RUNG_WORDS) {
        unsafe { read_rung_unchecked::<S>(words, at) }
    } else {
        Rung::ZERO
    }
}

/// Safe whole-cog read. A short row is structural zero, never a partially reconstructed number.
#[inline]
pub fn read_cog_with<S: WordSeam>(words: &[u32], at: usize) -> Cog {
    if row_fits(words, at, COG_WORDS) {
        unsafe { read_cog_unchecked::<S>(words, at) }
    } else {
        Cog::ZERO
    }
}

/// Ordinary Rust-slice faces retained for callers that own only a number row.
#[inline]
pub fn read_rung(words: &[u32], at: usize) -> Rung {
    read_rung_with::<SliceWordSeam>(words, at)
}

#[inline]
pub fn read_cog(words: &[u32], at: usize) -> Cog {
    read_cog_with::<SliceWordSeam>(words, at)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_glyph_grounds_and_faces_back() {
        for v in [0i64, 1, 12, -9, 255, 4096, -1_000_000] {
            assert_eq!(
                Cog::lit(v).face(),
                v,
                "the face is what the glyph always was"
            );
        }
    }

    #[test]
    fn negation_is_a_turn_not_a_stripped_sign() {
        assert_eq!(Cog::lit(5).turned(2).face(), -5); // the half-turn π
        assert_eq!(Cog::lit(5).turned(4).face(), 5); // full turn home
    }

    #[test]
    fn add_sub_fold_at_the_common_grain() {
        assert_eq!(Cog::lit(12).add(Cog::lit(9)).face(), 21);
        assert_eq!(Cog::lit(12).sub(Cog::lit(9)).face(), 3);
        assert_eq!(Cog::lit(9).sub(Cog::lit(12)).face(), -3); // signed via the turn, never abs
    }

    #[test]
    fn the_two_hand_product_re_bases_never_widens() {
        assert_eq!(Cog::lit(12).mul(Cog::lit(9)).face(), 108);
        assert_eq!(Cog::lit(-7).mul(Cog::lit(6)).face(), -42); // turns add
        let big = Cog::lit(100_000).mul(Cog::lit(100_000)); // 10^10 > i32::MAX — re-bases, never i128
        assert!(
            (big.face() - 10_000_000_000i64).abs() < (1 << 20),
            "re-based product holds the grain"
        );
    }

    #[test]
    fn the_rung_folds_exactly_where_the_hand_holds() {
        assert_eq!(Rung::of(12).add(Rung::of(9)).face(), Some(21));
        assert_eq!(Rung::of(9).sub(Rung::of(12)).face(), Some(-3)); // direction, never abs
        assert_eq!(Rung::of(-3).cmp_teeth(Rung::of(7)), -1);
        assert_eq!(Rung::of(7).cmp_teeth(Rung::of(7)), 0);
        // zero is THE zero — one representation, whatever path produced it.
        assert_eq!(Rung::of(5).sub(Rung::of(5)), Rung::ZERO);
    }

    #[test]
    fn the_number_wire_is_one_recursive_round_trip() {
        let rung = Rung {
            mag: 0x8123_4567,
            rank: 19,
            neg: true,
        };
        let cog = Cog {
            mag: 0x9234_5678,
            rank: rung,
            turn: 3,
        };
        let mut rung_words = [0u32; RUNG_WORDS];
        let mut word = 0usize;
        while word < RUNG_WORDS {
            rung_words[word] = rung_packed_word(rung, word);
            word += 1;
        }
        assert_eq!(read_rung(&rung_words, 0), rung);

        let mut cog_words = [0u32; COG_WORDS];
        let mut cog_word = 0usize;
        while cog_word < COG_WORDS {
            cog_words[cog_word] = cog_packed_word(cog, cog_word);
            cog_word += 1;
        }
        assert_eq!(read_cog(&cog_words, 0), cog);
        assert_eq!(read_rung(&rung_words[..RUNG_WORDS - 1], 0), Rung::ZERO);
        assert_eq!(read_cog(&cog_words[..COG_WORDS - 1], 0), Cog::ZERO);
    }

    /// ★ THE WAVE-1 MEASURE (FABLE_ORGANIZING): the tower climbs by re-base at BOTH levels and never hits a wall.
    /// The old `i32` rank overflowed after ~31 squarings — a reachable backstop, silently wrapping in release.
    #[test]
    fn the_ladder_re_bases_the_tower_never_walls() {
        // the exact regime (teeth ≤ the rung's hand, n ≤ 32): after n squarings of 2 the total teeth are
        // EXACTLY 2^n — read as rank ⊕ the mantissa's own top (a logarithm is a rank). The old i32 wall fell
        // right here (teeth > 2^31 at n = 32); the rung climbs through it.
        let mut x = Cog::lit(2);
        for n in 1..=32u32 {
            x = x.mul(x);
            let teeth = x.rank.face().expect("exact regime faces flat") + msb(x.mag) as i64;
            assert_eq!(teeth, 1i64 << n, "2^(2^{n}) holds exact total teeth");
            assert_eq!(
                x.mag.count_ones(),
                1,
                "a pure power stays a pure power — no bit ever corrupts"
            );
        }
        // the grain regime (teeth past the rung's hand): the rung itself re-bases and teeth below ITS grain
        // fall dark — the proportional-grain law one level up (the same behavior as the foil, meno.rs, whose
        // recursive exponent drops low bits past ITS grain). The slip is BOUNDED BY THE GRAIN (< 2^(n−31)) —
        // a derived bound, never a tolerance we pick.
        for n in 33..=45u32 {
            x = x.mul(x);
            let teeth = x.rank.face().expect("still faces flat") + msb(x.mag) as i64;
            let slip = (1i64 << n) - teeth;
            // the one-stroke ladder (the substrate's own multiplier, 2026-07-09) rounds its single
            // rank-add once per squaring at the rung's grain; the accumulated slip converges to the
            // geometric sum Σ2⁻ᵏ = 2 grains — so the DERIVED bound is one tooth coarser than the old
            // 31-step ladder's: slip < 2^(n−30). Still the grain's own, never a tolerance we pick
            // (measured: slip/grain → 1.998 by n = 45).
            assert!(
                slip >= 0 && slip < (1i64 << (n - 30)),
                "2^(2^{n}): the slip {slip} sits within the one-stroke ladder's grain"
            );
            assert_eq!(x.mag.count_ones(), 1, "a pure power stays a pure power");
        }
        // the deep regime — the measure itself: 2^(2^512). The rank has left every flat glyph (the tower is
        // stored, never materialized); the mantissa is still a pure power (nothing corrupted); the rung's own
        // top position reads 511 (the rank stands at ~2^512, grain-exact one level up); the boundary glyph
        // saturates honestly at the ceiling.
        for _ in 46..=512u32 {
            x = x.mul(x);
        }
        assert_eq!(x.mag.count_ones(), 1, "pure power preserved to 2^(2^512)");
        assert!(
            x.rank.face().is_none(),
            "2^512 teeth is beyond any flat glyph — held re-based, never flattened"
        );
        let rung_top = x.rank.rank as i64 + msb(x.rank.mag) as i64;
        assert_eq!(
            rung_top, 511,
            "the rank stands at ~2^512 (msb 511 — the −msb(mag) teeth ride below it)"
        );
        assert!(!x.rank.neg, "the ladder climbed, never turned");
        assert_eq!(
            x.mag_face(),
            u64::MAX,
            "the boundary reads its honest ceiling — the value is beyond the face"
        );
    }
}
