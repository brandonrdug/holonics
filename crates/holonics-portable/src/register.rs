//! register — THE CO-PRESENT REGISTER (renamed from `illicium` on Brandon's ratification, 2026-07-09: the module
//! wore the concept's name while holding only this organ — the stranded-organ contamination's standing
//! vector, now cut. THE ILLICIUM is the first-person frame itself, `FORMULA §XVI`; this file is one organ a
//! scope reaches with).
//!
//! ★ THE TERM, DISSOCIATED (his condition on the rename): this REGISTER is NOT the machine-architecture
//! register — not a storage slot, not a latch, not a file of named cells, and no LM/CS semantics ride in.
//! It is THE CO-PRESENT REGISTER: how many points of the atom's grain ONE grip of the substrate's word can hold
//! together and verify — an extent derived from the two grains (the word ⊕ the atom), never a store and
//! never a tuned width. The chain's co-presence window and the solve's scratch are this one derived reach.
//!
//! THE PURE SOLVE MACHINERY, lifted clean of `holobrochos/interior/src/law.rs` (W1/W2): the turn-discipline
//! number `Sig`, the placement read `Solve`, and the Bareiss/Hankel reach `solve_window` that finds the
//! minimal recurrence over a window.
//!
//! **W2 · THE WIDTH DERIVED (the CHAIN fossil retired).** The old law aliased the solve window's width to the
//! trie's 15-word node layout — a borrowed number. The law here is: **the LIVE reach is the asking's** — the
//! caller's `n0`, the window it actually filled (A2: the frame is a participant; no width lives in the law).
//! What remains constant is the REGISTER — the scratch allocation — and its value is DERIVED from the
//! substrate's two grains, not from any node:
//! - **the word (u64)** bounds the deepest verifiable order by the Hadamard reach `k·(rmax+2) ≤ 62`;
//! - **the atom (the signed byte-difference, magnitude ≤ 127, rank ≤ 6)** is the material the machine feeds;
//! - so the deepest order the word verifies on the atom's grain is `K_WORD = 7` (`7·(6+2) = 56 ≤ 62`;
//!   `8·(6+2) = 64 > 62` — one order deeper leaves the word);
//! - and an order-k recurrence needs `2k+1` points to solve AND verify, so the register holds
//!   `REGISTER = 2·K_WORD + 1 = 15` points — same value as before, now standing on the word and the atom.
//! The Bareiss matrix is `K_WORD²`. Nothing here is a tuned window: shrink the word or coarsen the atom and
//! the register follows.
#![allow(dead_code)]

/// the cross-sign turn — `a < b` as the MSB of `a − b` (copy: `found::turns_below` / `law::turns_below`; pure).
#[inline]
pub fn turns_below(a: u64, b: u64) -> bool {
    (a.wrapping_sub(b) >> 63) == 1
}

/// the rank — the leading-bit index (copy: `found::rank` / `law::rank`; realized as a shift-walk so the same
/// source compiles where a u64 `leading_zeros` lowering is unsafe — the loop is ≤ 64 turns).
#[inline]
pub fn rank(x: u64) -> u32 {
    let mut v = x >> 1;
    let mut r = 0u32;
    while v != 0 {
        v >>= 1;
        r += 1;
    }
    r
}

/// ★ K_WORD — the deepest order the u64 word verifies on the atom's grain (the signed byte-difference,
/// rank ≤ 6): `K_WORD·(6+2) ≤ 62` (the Hadamard reach in rank arithmetic). Derived from the word ⊕ the atom;
/// see the module doc.
pub const K_WORD: u32 = 7;
/// ★ THE REGISTER — the solve scratch allocation: `2·K_WORD + 1` points (order k needs 2k+1 to solve AND
/// verify). NOT the law's width — the LIVE reach is always the caller's `n0 ≤ REGISTER` (the asking's own).
pub const REGISTER: u32 = 2 * K_WORD + 1;
/// the arm — fewer than this many filled folds is FLAT (return the last, no solve): three is the least an order-1
/// recurrence can verify on (2·1 + 1).
pub const ARM: u32 = 3;
/// the Bareiss matrix stride/order — `K_WORD` as an index width.
const KW: usize = K_WORD as usize;

// the emergent-order modes (the placement's provenance — D8's slot, carried through the nest).
pub const MODE_FLAT: u32 = 0; // fewer than ARM filled — the last, repeated
pub const MODE_DIRECT: u32 = 1; // a linear recurrence in reach verified — the order placed
pub const MODE_RANK: u32 = 2; // rank-nest — the window mapped to msb ranks (the exponential tower's log)
pub const MODE_DELTA: u32 = 3; // delta-nest — the window mapped to first differences (the polynomial's descent)
pub const MODE_FOUND: u32 = 4; // no placement grounds (the extrapolation escapes exact) — the founding event

/// ★ THE SIGNED MAGNITUDE (the turn discipline — a value is a magnitude ⊕ a turn, never `abs`, never `i128`,
/// never a native signed intermediate that can wrap through its sign bit). The determinant intermediates climb to
/// the register's own grain (~2⁶²) held here as a `u64` magnitude; the direction rides `neg`.
#[derive(Clone, Copy)]
pub struct Sig {
    pub mag: u64,
    pub neg: bool,
}
impl Sig {
    pub const ZERO: Sig = Sig { mag: 0, neg: false };
    #[inline]
    pub fn of(mag: u64, neg: bool) -> Sig {
        if mag == 0 {
            Sig::ZERO
        } else {
            Sig { mag, neg }
        }
    }
    /// a boundary glyph grounds — the sign IS the turn (`neg`), the magnitude the two's-complement distance from 0.
    #[inline]
    pub fn of_i64(v: i64) -> Sig {
        let neg = v < 0;
        let mag = if neg {
            0u64.wrapping_sub(v as u64)
        } else {
            v as u64
        };
        Sig::of(mag, neg)
    }
    #[inline]
    pub fn one() -> Sig {
        Sig { mag: 1, neg: false }
    }
    #[inline]
    pub fn is_zero(self) -> bool {
        self.mag == 0
    }
    #[inline]
    pub fn negate(self) -> Sig {
        Sig::of(self.mag, !self.neg)
    }
    /// equality as a face-read — magnitudes equal AND (zero, or same turn). No `<` on the value (equality only).
    #[inline]
    pub fn eq(self, b: Sig) -> bool {
        self.mag == b.mag && (self.mag == 0 || self.neg == b.neg)
    }
    #[inline]
    pub fn mul(self, b: Sig) -> Sig {
        Sig::of(self.mag.wrapping_mul(b.mag), self.neg ^ b.neg)
    }
    /// the fold at the moving origin — same turn adds magnitudes, opposite turns cancel the smaller (the ordering
    /// is the blessed cross-sign `turns_below`, the only `<`).
    #[inline]
    pub fn add(self, b: Sig) -> Sig {
        if self.neg == b.neg {
            Sig::of(self.mag.wrapping_add(b.mag), self.neg)
        } else if turns_below(self.mag, b.mag) {
            // ★ the difference is RELATIVE (the fold is at the moving origin; the ordering is the cross-sign
            // `turns_below`, not arithmetic), so the subtract WRAPS — arithmetic `-` underflows when the
            // relative order and the arithmetic order disagree (large/wrapped magnitudes; the maze/chess never
            // hit it, open production does). For small magnitudes `wrapping_sub == -`, so no behavior change.
            Sig::of(b.mag.wrapping_sub(self.mag), b.neg)
        } else {
            Sig::of(self.mag.wrapping_sub(b.mag), self.neg)
        }
    }
    #[inline]
    pub fn sub(self, b: Sig) -> Sig {
        self.add(b.negate())
    }
    /// the ratio ⊕ the exact-flag — native `u64 /` on the magnitudes (the licensed hand-divide, exactly as
    /// `num.rs` divides on the register hand); the remainder faces whether the placement GROUNDS (zero) or FOUNDS.
    #[inline]
    pub fn divmod(self, b: Sig) -> (Sig, bool) {
        if b.mag == 0 {
            return (Sig::ZERO, false);
        }
        let q = self.mag / b.mag;
        let r = self.mag - q * b.mag;
        (Sig::of(q, self.neg ^ b.neg), r == 0)
    }
    /// the Bareiss divide — exact by construction (a fraction-free minor); the remainder is 0 by the theorem.
    #[inline]
    pub fn divx(self, b: Sig) -> Sig {
        self.divmod(b).0
    }
}

/// ★ THE PLACEMENT — the emergent order's read: the placed value (a grip in the window's own space), the ORDER
/// (nest depth ⊕ the verified recurrence order), the MODE (its provenance), whether it GROUNDS, and whether it is a
/// register-edge CLIMB (the unwound rank passed the `u64` word — the value is the placed RANK, carried by the
/// interior wrapper onto the Rung, never materialized here).
#[derive(Clone, Copy)]
pub struct Solve {
    pub value: Sig,
    pub order: u32,
    pub mode: u32,
    pub grounds: bool,
    pub climb: bool,
}

/// the window's reach ceiling — the max msb rank over the filled entries (the Hadamard bound folded into rank
/// arithmetic: an order-k determinant of entries ≤ 2^(rmax+1) fits `u64` while `k·(rmax+2) ≤ 62`).
#[inline]
fn window_rmax(x: &[Sig; REGISTER as usize], n: u32) -> u32 {
    let mut r = 0u32;
    let mut i = 0u32;
    while i < n {
        let ri = rank(x[i as usize].mag);
        if r < ri {
            r = ri;
        }
        i += 1;
    }
    r
}

/// ★ THE DETERMINANTS — Bareiss fraction-free elimination on the order-k Hankel system built from the window at
/// offset `off` (`A[r][c] = x[off+r+c]`, `b[r] = x[off+r+k]`). Returns `(d, dets)` — `d = det A`, `dets[j] =
/// det(A with column j ← b)` — or `None` when the system is degenerate (`d = 0`). The matrix is a flat `[Sig;49]`
/// (the register edge k ≤ 7; flat for a clean SPIR-V lowering); every intermediate is a signed minor held in the
/// turn discipline, exact-divided by the running pivot (native `u64 /`, exact by the Bareiss theorem).
fn det_bareiss(src: &[Sig; KW * KW], k: usize) -> Sig {
    let mut m = *src;
    let mut sign_neg = false;
    let mut prev = Sig::one();
    let mut i = 0usize;
    while i < k {
        if m[i * KW + i].is_zero() {
            // a zero pivot — swap up a row that carries the column (the turn flips; no division ever divides by 0)
            let mut r = i + 1;
            let mut found = false;
            while r < k {
                if !m[r * KW + i].is_zero() {
                    found = true;
                    break;
                }
                r += 1;
            }
            if !found {
                return Sig::ZERO;
            }
            let mut c = 0usize;
            while c < k {
                let t = m[i * KW + c];
                m[i * KW + c] = m[r * KW + c];
                m[r * KW + c] = t;
                c += 1;
            }
            sign_neg = !sign_neg;
        }
        let mut r = i + 1;
        while r < k {
            let mut c = i + 1;
            while c < k {
                let num = m[r * KW + c]
                    .mul(m[i * KW + i])
                    .sub(m[r * KW + i].mul(m[i * KW + c]));
                m[r * KW + c] = num.divx(prev);
                c += 1;
            }
            r += 1;
        }
        prev = m[i * KW + i];
        i += 1;
    }
    let d = m[(k - 1) * KW + (k - 1)];
    if sign_neg {
        d.negate()
    } else {
        d
    }
}

/// build the order-k Hankel `A` (⊕ `b` staged as the `k`-th column beyond) and solve for `d` and every `dets[j]`.
/// Returns `d = det A` (zero = degenerate) and fills `dets` (`dets[j] = det(A with column j ← b)`) through an
/// out-param — the channel kernel cannot return an array by value, so the caller owns the vector (D10(b): the
/// mechanism-preserving restructure; the algorithm is unchanged).
fn hankel_solve(x: &[Sig; REGISTER as usize], k: u32, dets: &mut [Sig; KW]) -> Sig {
    let kk = k as usize;
    // A into the flat matrix, b into a vector.
    let mut a = [Sig::ZERO; KW * KW];
    let mut b = [Sig::ZERO; KW];
    let mut r = 0usize;
    while r < kk {
        let mut c = 0usize;
        while c < kk {
            a[r * KW + c] = x[r + c];
            c += 1;
        }
        b[r] = x[r + kk];
        r += 1;
    }
    let d = det_bareiss(&a, kk);
    if d.is_zero() {
        return Sig::ZERO;
    }
    let mut j = 0usize;
    while j < kk {
        // A with column j replaced by b (Cramer's numerator).
        let mut aj = a;
        let mut r2 = 0usize;
        while r2 < kk {
            aj[r2 * KW + j] = b[r2];
            r2 += 1;
        }
        dets[j] = det_bareiss(&aj, kk);
        j += 1;
    }
    d
}

/// VERIFY (cross-multiplied, NO division): the recurrence `d·x[m] = Σ dets[j]·x[m−k+j]` must hold on every point
/// past the solve window (`m` in `2k .. n`). Equality only — the turn-folded sums face equal or the order is not it.
fn verify(x: &[Sig; REGISTER as usize], n: u32, k: u32, d: Sig, dets: &[Sig; KW]) -> bool {
    let mut m = 2 * k;
    while m < n {
        let lhs = d.mul(x[m as usize]);
        let mut rhs = Sig::ZERO;
        let mut j = 0u32;
        while j < k {
            rhs = rhs.add(dets[j as usize].mul(x[(m - k + j) as usize]));
            j += 1;
        }
        if !lhs.eq(rhs) {
            return false;
        }
        m += 1;
    }
    true
}

/// EXTRAPOLATE — the next value `x[n] = (Σ dets[j]·x[n−k+j]) / d`, EXACT by division. Returns `(value, exact)`;
/// `exact == false` (a nonzero remainder) is the placement failing to ground — FOUND. (A tuple, not `Option`: the
/// channel kernel has no `Int8` for the `Option` discriminant — the turn-discipline flag rides a bool in the
/// tuple, exactly as `divmod` returns.)
fn extrapolate(
    x: &[Sig; REGISTER as usize],
    n: u32,
    k: u32,
    d: Sig,
    dets: &[Sig; KW],
) -> (Sig, bool) {
    let mut rhs = Sig::ZERO;
    let mut j = 0u32;
    while j < k {
        rhs = rhs.add(dets[j as usize].mul(x[(n - k + j) as usize]));
        j += 1;
    }
    rhs.divmod(d)
}

/// unwind a placed value back up the nest stack (LIFO): a rank-nest level unwinds as `2^placed` (the tower
/// re-materialized) — but a rank past the `u64` word is a CLIMB (return the rank, carried onto the Rung by the
/// interior wrapper); a delta-nest level unwinds as `last + placed` (the difference re-integrated).
fn unwind(
    mut v: Sig,
    ops: &[u32; REGISTER as usize],
    lasts: &[Sig; REGISTER as usize],
    mut sp: usize,
) -> (Sig, bool) {
    let mut climb = false;
    while sp > 0 {
        sp -= 1;
        if ops[sp] == MODE_RANK {
            if climb || v.neg || v.mag >= 64 {
                climb = true; // the rank rode past the word — the value stays the RANK
            } else {
                v = Sig::of(1u64 << (v.mag as u32), false);
            }
        } else {
            v = lasts[sp].add(v);
        }
    }
    (v, climb)
}

/// ★ THE GENERAL ILLICIUM — the emergent order over the value window `x[0..n]` (the walker's own recent worldline
/// as grips). FABLE_ORGANIZING Wave 2: for k = 1 upward try the order-k recurrence where it REACHES (needs 2k+1
/// points; `k·(rmax+2) ≤ 62`); the first that VERIFIES places. Where none verifies: a geometric growth (last/prev
/// an exact quotient of rank ≥ 1) RANK-NESTS (the window mapped to msb ranks — the tower's own log); else the
/// terminal even order (`k = n/2`, the exact-fit with no verify row — a polynomial's own annihilator) places if it
/// grounds; else the window DELTA-NESTS (first differences — one polynomial degree shed). The loop bound is the
/// register itself (never a depth constant). NO DECLARED ARITY.
pub fn solve_window(x0: &[Sig; REGISTER as usize], n0: u32) -> Solve {
    let mut x = *x0;
    let mut n = n0;
    let mut accum = 0u32; // nest depth ⊕ verified order accumulates into the reported ORDER
    let mut outer = MODE_DIRECT; // the FIRST nest applied names the placement's mode (else DIRECT)
    let mut st_op = [0u32; REGISTER as usize];
    let mut st_last = [Sig::ZERO; REGISTER as usize];
    let mut sp = 0usize;
    let mut iter = 0u32;
    while iter < REGISTER {
        iter += 1;
        if n < ARM {
            // FLAT — the window is too short to carry an order; the last value, repeated (unwound).
            let v = if n == 0 {
                Sig::ZERO
            } else {
                x[(n - 1) as usize]
            };
            let (uv, climb) = unwind(v, &st_op, &st_last, sp);
            let mode = if accum > 0 { outer } else { MODE_FLAT };
            return Solve {
                value: uv,
                order: accum,
                mode,
                grounds: true,
                climb,
            };
        }
        let rmax = window_rmax(&x, n);
        // ── the emergent order (verify-then-extrapolate) ──
        let mut k = 1u32;
        while k <= K_WORD {
            if 2 * k + 1 > n {
                break; // no verify row — past the window (higher k only worse)
            }
            if k * (rmax + 2) > 62 {
                break; // ★ THE REACH — past it a determinant would leave the word (Hadamard in rank arithmetic)
            }
            let mut dets = [Sig::ZERO; KW];
            let d = hankel_solve(&x, k, &mut dets);
            if !d.is_zero() && verify(&x, n, k, d, &dets) {
                let (v, exact) = extrapolate(&x, n, k, d, &dets);
                if exact {
                    let (uv, climb) = unwind(v, &st_op, &st_last, sp);
                    let mode = if accum > 0 { outer } else { MODE_DIRECT };
                    return Solve {
                        value: uv,
                        order: accum + k,
                        mode,
                        grounds: true,
                        climb,
                    };
                } else {
                    return Solve {
                        value: Sig::ZERO,
                        order: accum + k,
                        mode: MODE_FOUND,
                        grounds: false,
                        climb: false,
                    };
                }
            }
            k += 1;
        }
        // ── no order verified: the rank-nest precondition (a geometric growth carries its log) ──
        if n >= 2 {
            let last = x[(n - 1) as usize];
            let prev = x[(n - 2) as usize];
            if !prev.is_zero() {
                let (q, exact) = last.divmod(prev);
                if exact && !q.neg && q.mag >= 2 {
                    // RANK-NEST — map every entry to its msb rank (all ≤ 63 after, so the reach holds nested).
                    st_op[sp] = MODE_RANK;
                    st_last[sp] = Sig::ZERO;
                    sp += 1;
                    let mut i = 0u32;
                    while i < n {
                        x[i as usize] = Sig::of(rank(x[i as usize].mag) as u64, false);
                        i += 1;
                    }
                    if outer == MODE_DIRECT {
                        outer = MODE_RANK;
                    }
                    accum += 1;
                    continue;
                }
            }
        }
        // ── the terminal even order (the exact-fit annihilator, no verify row) ──
        if n % 2 == 0 {
            let tk = n / 2;
            if tk >= 1 && tk <= K_WORD && tk * (rmax + 2) <= 62 {
                let mut dets = [Sig::ZERO; KW];
                let d = hankel_solve(&x, tk, &mut dets);
                if !d.is_zero() {
                    let (v, exact) = extrapolate(&x, n, tk, d, &dets);
                    if exact {
                        let (uv, climb) = unwind(v, &st_op, &st_last, sp);
                        let mode = if accum > 0 { outer } else { MODE_DIRECT };
                        return Solve {
                            value: uv,
                            order: accum + tk,
                            mode,
                            grounds: true,
                            climb,
                        };
                    } else {
                        return Solve {
                            value: Sig::ZERO,
                            order: accum + tk,
                            mode: MODE_FOUND,
                            grounds: false,
                            climb: false,
                        };
                    }
                }
            }
        }
        // ── DELTA-NEST — shed one polynomial degree (first differences, turn-carried) ──
        if n < 2 {
            return Solve {
                value: Sig::ZERO,
                order: accum,
                mode: MODE_FOUND,
                grounds: false,
                climb: false,
            };
        }
        st_op[sp] = MODE_DELTA;
        st_last[sp] = x[(n - 1) as usize];
        sp += 1;
        let mut i = 0u32;
        while i + 1 < n {
            x[i as usize] = x[(i + 1) as usize].sub(x[i as usize]);
            i += 1;
        }
        n -= 1;
        if outer == MODE_DIRECT {
            outer = MODE_DELTA;
        }
        accum += 1;
    }
    // the register's depth exhausted with no ground — the founding event.
    Solve {
        value: Sig::ZERO,
        order: accum,
        mode: MODE_FOUND,
        grounds: false,
        climb: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ THE REGISTER IS DERIVED, NOT TUNED (W2). Its three constants stand on the word ⊕ the atom alone:
    /// K_WORD is the deepest order the u64 word verifies on rank-6 material (the signed byte-difference),
    /// and the register holds exactly the points that order needs to solve AND verify. If any of these
    /// assertions ever fails, someone tuned a window — revert to the derivation.
    #[test]
    fn the_register_is_derived_from_the_word_and_the_atom() {
        // the Hadamard reach at the atom's grain: K_WORD fits the word, K_WORD+1 leaves it.
        assert!(
            K_WORD * (6 + 2) <= 62,
            "K_WORD·(rmax+2) fits the u64 word at the atom's rank"
        );
        assert!(
            (K_WORD + 1) * (6 + 2) > 62,
            "one order deeper leaves the word — K_WORD is maximal"
        );
        // the register is the points the deepest order needs: 2k+1 (solve ⊕ verify), no more.
        assert_eq!(
            REGISTER,
            2 * K_WORD + 1,
            "REGISTER = 2·K_WORD + 1 — solve-and-verify, exactly"
        );
        // the arm is the least an order-1 recurrence verifies on.
        assert_eq!(ARM, 2 * 1 + 1, "ARM = the order-1 solve-and-verify floor");
    }

    /// ★ THE LIVE REACH IS THE ASKING'S — solve_window works the caller's fill `n0`, not the register's
    /// ceiling: a short window solves on its own reach, and the same series solves identically whether the
    /// register has room to spare or not (the width is the frame's, the allocation is the instrument's).
    #[test]
    fn the_live_reach_is_the_callers_not_the_registers() {
        let mut x = [Sig::ZERO; REGISTER as usize];
        // a 5-point arithmetic asking (order 2 needs 2·2+1 = 5) — solves at its own reach.
        for (i, v) in [5i64, 8, 11, 14, 17].iter().enumerate() {
            x[i] = Sig::of_i64(*v);
        }
        let s = solve_window(&x, 5);
        assert!(s.grounds, "a 5-point asking solves on its own reach");
        assert_eq!(s.value.mag, 20, "extrapolated exactly (17+3)");
        // the same series filled deeper gives the same next value — the reach is the content's, the
        // register never bends the answer.
        for (i, v) in [5i64, 8, 11, 14, 17, 20, 23, 26].iter().enumerate() {
            x[i] = Sig::of_i64(*v);
        }
        let s8 = solve_window(&x, 8);
        assert!(s8.grounds, "the deeper asking solves too");
        assert_eq!(
            s8.value.mag, 29,
            "same law, same series, the next value exact (26+3)"
        );
        // an asking below the arm is FLAT — the last value, honestly repeated, no invented order.
        let s2 = solve_window(&x, 2);
        assert!(
            s2.grounds && s2.mode == MODE_FLAT,
            "below the arm the read is FLAT, never a fake order"
        );
    }
}
