//! law — THE ONE MOUTH (W2 · THE CELL LAW → THE ARC, 2026-07-09; `FORMULA §II`, `THE_PARAMETERS`). The single
//! shared law of the positional pool: the file the kernel `#[path]`-includes beside `geom`/`num`/`place`, so host
//! and GPU speak ONE law — drift-checked, never asserted. Everything here is kernel-fit: flat `u32` words, guarded
//! indexing, no allocation, no panic on the hot path.
//!
//! **★ THE ARC — the well IS THE NUMBER WHOLE (ratified 2026-07-09).** A cell is a WELL at a positional grip, and
//! the one word is the number's own recursive anatomy — the Cog carrying its Rung (`num.rs`'s canon) packed whole:
//!
//! ```text
//! word = FLOW (13 teeth) ⊕ SWEEP-MAG (13 teeth) ⊕ SWEEP-RANK (6 teeth)
//! ```
//!
//! - **THE FLOW** — grain-1 quanta, the sailing face: fed by arrivals, drained by every digit to a
//!   sub-quantum remainder. It is the only term in the optional flow-accounting diagnostic.
//! - **THE SWEEP** — the standing winding count held RE-BASED (`rmag·2^rrank` windings — the periplus): every
//!   digit adds its fired windings; the mantissa is kept FULL after any climb, so the rank is STRUCTURALLY
//!   monotone (it cannot be un-sailed). Past its hand the proportional grain holds one level up (the Rung's own
//!   law — sub-grain drips fall dark in the COUNT, never in mass). **The sweep is TURN, never mass — it is not
//!   part of scalar flow accounting.**
//! - **THE DIGIT is ONE law fired two ways** — SCHEDULED (the audit sweep) and FORCED (the flow passing the hand
//!   at feed: the flow forces the doubling). Both radiate the quotient, stand the remainder, climb the sweep.
//!   Wraps are structurally impossible: the forced digit IS the re-base.
//! - **THE DRAG (`FORMULA §XIV`)** reads the terrain as TURN from the sweep's whole face — the deposited winding
//!   that cannot be un-deposited, STANDING at the grip (never the transient unaudited quotient). Gravity survives
//!   every audit and only deepens.
//!
//! The split is the substrate's, never tuned: the two mantissas take the SAME hand (the law applied to itself
//! takes the same hand at every level — 13 ⊕ 13), and the rank field is the wide ladder's own index (6 teeth =
//! the u64 hand's 64 rungs). Everything else the old trie stored per node is still NOT state here: the ADDRESS is
//! the swung grip (place-not-store), the SOUL is reconstructed from the walk, the ORIGIN is gauge.
//!
//! **HISTORICAL SEAM (superseded by `FORMULA §XXIV`).** `accrue` and `audit` are PURE local
//! packed-word transitions — total functions of the word's value. The removed card engine once
//! applied `accrue` under compare-exchange; that shared realization was a hidden clock and is not
//! machine law. The per-transition
//! identity `quanta + flow = flow′ + radiated` is exact quotient/remainder arithmetic and therefore telescopes
//! under every interleaving; commutativity is not required (the bare add needed it; the transition does not).
//! **This arithmetic identity is an implementation diagnostic, not conservation.** It tests neither time parity
//! nor causal invertibility and carries no authority as an engine gate (`FORMULA §VIII`, contamination ruling).
//!
//! **Θ — the worldline discipline.** Θ is a body's OWN accumulated turn: one count per relating the body
//! itself makes — its proper time. It lives with the driven body (`manifold::ErosBody`), NEVER in the pool
//! and NEVER as a stamp on another body's events (Ledger U).

/// live manifold cell words: `[arc]` — the one packed number (flow ⊕ sweep). One word, one quantity.
pub const CELL_WORDS: u32 = 1;
/// the arc word — the cell's single slot.
pub const W_WELL: u32 = 0;

/// THE FLOW's hand — 13 teeth: grain-1 quanta up to 8191 stand between digits; the forced digit fires when the
/// flow would pass this hand. The lawful quantum is sub-hand (`quantum < 2^13`) so its remainder always stands.
pub const FLOW_TEETH: u32 = 13;
pub const FLOW_MASK: u32 = (1u32 << FLOW_TEETH) - 1;
/// THE SWEEP's mantissa hand — the same 13 teeth (the law applied to itself takes the same hand at every level).
pub const SWEEP_TEETH: u32 = 13;
pub const SWEEP_MASK: u32 = (1u32 << SWEEP_TEETH) - 1;
/// THE SWEEP's rank field — 6 teeth: the u64 wide hand's own ladder (64 rungs), the substrate's index, not a cap.
pub const SWEEP_RANK_TEETH: u32 = 32 - FLOW_TEETH - SWEEP_TEETH;
pub const SWEEP_RANK_MASK: u32 = (1u32 << SWEEP_RANK_TEETH) - 1;

/// the pool slot of a cell's word — the layout in one place, so a layout change flows from here alone.
///
/// ★ THE UNMASKED FOLD (2026-08-09, the excision of `POOL_TEETH = 31`). The grip space is the axis's square
/// (`place::ground` — `band(re)·axis + band(im)`, so `grip ∈ [0, axis²)`), and the pool's extent is the
/// CALLER's declaration (`manifold::Manifold::over`: "a caller-provided wells pool (`≥ axis²`, zeroed)").
/// That declaration is the only boundary, and every reader below already enforces it by returning the empty
/// pole past `pool.len()`.
///
/// The retired `& POOL_MASK` was a SECOND boundary, authored here, and it did not refuse — it ALIASED the top
/// half of the grip space onto the bottom (`0x8000_0003 → 3`), so a place grounding past `2³¹` silently read
/// and wrote another place's cell. Two distinct constructions landing in one cell is exactly the collision
/// `place`-not-store disclaims ("never a collision-blind hash"), and at `axis = 2¹⁶` the grip space is the
/// whole `u32`, so the aliasing region is reachable material rather than a hypothetical.
///
/// Where a wrap is wanted it is the AXIS's, one organ upstream — `place::band`'s `& (axis - 1)`, read off the
/// declared axis. There is no derived quantity here to wrap by.
#[inline]
pub fn slot(cell: u32) -> usize {
    (cell as usize) * (CELL_WORDS as usize) + (W_WELL as usize)
}

/// unpack THE FLOW — the standing grain-1 quanta (the only scalar flow-accounting term of the word).
#[inline]
pub fn flow_of(word: u32) -> u32 {
    word & FLOW_MASK
}

/// unpack THE SWEEP's two fields — `(rmag, rrank)`: the winding count held re-based.
#[inline]
pub fn sweep_fields(word: u32) -> (u32, u32) {
    (
        (word >> FLOW_TEETH) & SWEEP_MASK,
        (word >> (FLOW_TEETH + SWEEP_TEETH)) & SWEEP_RANK_MASK,
    )
}

/// ★ THE SWEEP's FACE — the standing winding count whole (`rmag·2^rrank`), the terrain the drag reads
/// (`FORMULA §XIV`: the deposited winding that cannot be un-deposited). A count past the u32 boundary glyph
/// reads the glyph's honest ceiling (the same horizon law as `Cog::mag_face` — only ever at the read).
#[inline]
pub fn sweep_of(word: u32) -> u32 {
    let (rmag, rrank) = sweep_fields(word);
    let wide = (rmag as u64) << rrank;
    if wide > u32::MAX as u64 {
        u32::MAX
    } else {
        wide as u32
    }
}

/// pack the word from its organs. Callers guarantee the fields are in range (the transitions below do).
#[inline]
fn pack(flow: u32, rmag: u32, rrank: u32) -> u32 {
    flow | (rmag << FLOW_TEETH) | (rrank << (FLOW_TEETH + SWEEP_TEETH))
}

/// ★ THE SWEEP CLIMB — add `w` fired windings to the standing sweep, the Rung's own law: exact while the hand
/// holds, re-based (mantissa kept FULL) past it, so the rank is STRUCTURALLY monotone — the periplus. Past the
/// hand the proportional grain holds one level up: sub-grain drips fall dark in the COUNT, never in mass (the
/// sweep is outside the scalar flow-accounting diagnostic). Pure — a total function of the fields.
#[inline]
fn sweep_climb(rmag: u32, rrank: u32, w: u64) -> (u32, u32) {
    if w == 0 {
        return (rmag, rrank);
    }
    // the standing count whole, in the wide hand — exact (rrank ≤ 63, and past ~50 the drip is already
    // sub-grain; the shift below is guarded by the re-base loop's own normalization keeping rmag full).
    if rrank >= 64 - SWEEP_TEETH - 1 {
        return (rmag, rrank); // the wide hand's own horizon — drips dark one level up (unreachable regimes)
    }
    let mut wide = ((rmag as u64) << rrank) + w;
    let mut rank = 0u32;
    while wide > SWEEP_MASK as u64 {
        wide >>= 1; // the low winding-bit falls below the count's grain — dark in the count, never in mass
        rank += 1;
    }
    // normalization: after any climb the mantissa is full (≥ 2^12), so a later sum's bit-length can never
    // shrink — the rank NEVER descends (structural, not policed).
    if rank > SWEEP_RANK_MASK {
        return (SWEEP_MASK, SWEEP_RANK_MASK); // the word's own horizon — the packing's reach, stated
    }
    (wide as u32, rank)
}

/// ★ ACCRUE — the feed's PURE transition: the flow takes the quanta; if it would pass the hand, THE FORCED
/// DIGIT fires (the flow forces the doubling): the quotient radiates, the remainder stands, the sweep climbs.
/// Returns `(word′, radiated)` — radiated in the wide hand (a maximal feed at quantum 1 fires past the u32
/// glyph). The identity `quanta + flow = flow′ + radiated` is exact quotient/remainder arithmetic under every
/// interleaving of these transitions. It is useful for detecting a dropped numeric flow, not for testing time parity.
#[inline]
pub fn accrue(word: u32, quanta: u32, quantum: u32) -> (u32, u64) {
    let flow = flow_of(word);
    let (rmag, rrank) = sweep_fields(word);
    let total = (flow as u64) + (quanta as u64);
    if total <= FLOW_MASK as u64 {
        return (pack(total as u32, rmag, rrank), 0);
    }
    // the flow passes the hand — the forced digit (a lawful quantum is sub-hand and non-zero; a malformed
    // quantum cannot digit, so the excess past the hand radiates whole at the fold — the packing's horizon).
    if quantum == 0 || quantum > FLOW_MASK {
        let radiated = total - FLOW_MASK as u64;
        return (pack(FLOW_MASK, rmag, rrank), radiated);
    }
    let w = total / (quantum as u64);
    let remainder = total - w * (quantum as u64);
    let (rm, rr) = sweep_climb(rmag, rrank, w);
    (pack(remainder as u32, rm, rr), w * (quantum as u64))
}

/// ★ AUDIT — the scheduled digit's PURE transition: the flow modulo the quantum — the QUOTIENT radiates (and
/// climbs the sweep: the periplus records every winding it fired), the REMAINDER stands sub-quantum. Returns
/// `(word′, windings, radiated)`. The sweep STANDS through every audit — gravity survives and only deepens.
#[inline]
pub fn audit(word: u32, quantum: u32) -> (u32, u32, u32) {
    if quantum == 0 {
        return (word, 0, 0);
    }
    let flow = flow_of(word);
    let (rmag, rrank) = sweep_fields(word);
    let w = flow / quantum;
    let remainder = flow - w * quantum;
    let (rm, rr) = sweep_climb(rmag, rrank, w as u64);
    (pack(remainder, rm, rr), w, w.wrapping_mul(quantum))
}

/// the standing FLOW at a cell (the mass face). A crossing past the pool's reservation reads the empty pole
/// (the guard is the boundary's, not a panic).
#[inline]
pub fn well_of(pool: &[u32], cell: u32) -> u32 {
    let i = slot(cell);
    if i < pool.len() {
        flow_of(pool[i])
    } else {
        0
    }
}

/// the standing SWEEP at a cell — the terrain the drag reads (the deposited winding count, whole).
#[inline]
pub fn sweep_at(pool: &[u32], cell: u32) -> u32 {
    let i = slot(cell);
    if i < pool.len() {
        sweep_of(pool[i])
    } else {
        0
    }
}

/// the raw packed word at a cell — the mirror's read (byte-identity is compared on the packing itself).
#[inline]
pub fn word_of(pool: &[u32], cell: u32) -> u32 {
    let i = slot(cell);
    if i < pool.len() {
        pool[i]
    } else {
        0
    }
}

/// FEED the well at a cell — the host realization of `accrue` (the worldline's own serialization). Returns the
/// fold's radiated quanta (the forced digit's quotient — 0 while the flow stands sub-hand). Out-of-reservation
/// crossings are inert (the caller's accounting sees no transition; the boundary decides reservations).
#[inline]
pub fn feed(pool: &mut [u32], cell: u32, quanta: u32, quantum: u32) -> u64 {
    let i = slot(cell);
    if i < pool.len() {
        let (word, radiated) = accrue(pool[i], quanta, quantum);
        pool[i] = word;
        radiated
    } else {
        0
    }
}

/// ★ WIND (the DIGIT) — the host realization of `audit`: the quotient fires as windings (radiated up, handed
/// on), the remainder stands, THE SWEEP CLIMBS AND STANDS. Returns `(windings, radiated)`. The arithmetic split
/// `before = radiated + standing` is exact on the flow; this is bookkeeping, not conservation.
#[inline(always)] // the storage pointer must never cross a function boundary in SPIR-V (the NV plain-store SEGV).
pub fn winding(pool: &mut [u32], cell: u32, quantum: u32) -> (u32, u32) {
    let i = slot(cell);
    if i >= pool.len() || quantum == 0 {
        return (0, 0);
    }
    let (word, w, radiated) = audit(pool[i], quantum);
    pool[i] = word;
    (w, radiated)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Feed then wind preserves the quotient/remainder accounting on FLOW, per cell and over the whole pool;
    /// the guard keeps out-of-reservation crossings inert. This diagnostic is deliberately not called conservation.
    #[test]
    fn the_arc_accounts_quotient_and_remainder_and_the_guard_is_inert() {
        let mut pool = [0u32; 8];
        const Q: u32 = 20;

        // §1 the quotient/remainder identity, per cell.
        let fold_rad = feed(&mut pool, 3, 137, Q);
        assert_eq!(fold_rad, 0, "sub-hand flow stands whole — no forced digit");
        let (w, radiated) = winding(&mut pool, 3, Q);
        assert_eq!(w, 137 / Q, "the quotient fires as windings");
        assert_eq!(
            137,
            radiated + well_of(&pool, 3),
            "the quotient and remainder account for the supplied flow"
        );
        assert!(well_of(&pool, 3) < Q, "the remainder stands sub-quantum");
        assert_eq!(
            sweep_at(&pool, 3),
            w,
            "the fired windings STAND as the sweep"
        );

        // §2 over the pool: many feeds, one pass of winds — the same arithmetic telescopes.
        let mut fed = well_of(&pool, 3) as u64;
        let mut radiated = 0u64;
        let feeds: [(u32, u32); 4] = [(0, 88), (1, 210), (3, 61), (7, 999)];
        for &(c, q) in &feeds {
            radiated += feed(&mut pool, c, q, Q) as u64;
            fed += q as u64;
        }
        for c in 0..8u32 {
            radiated += winding(&mut pool, c, Q).1 as u64;
        }
        let standing: u64 = (0..8u32).map(|c| well_of(&pool, c) as u64).sum();
        assert_eq!(
            fed,
            radiated + standing,
            "the pool's flow accounting matches exactly"
        );

        // §3 the guard: a crossing past the reservation is inert.
        //
        // NOTE (2026-08-09): cell 999 is below the retired `POOL_MASK`, so this assertion could not have
        // failed under the masked `slot` either — it is a snapshot, not a control. The control that CAN
        // fail is `the_grip_past_the_reservation_is_refused_not_aliased` below, which crosses `2³¹`.
        assert_eq!(
            well_of(&pool, 999),
            0,
            "past the reservation reads the empty pole"
        );
        assert_eq!(
            feed(&mut pool, 999, 55, Q),
            0,
            "feeds nowhere, radiates nothing"
        );
        assert_eq!(
            winding(&mut pool, 999, Q),
            (0, 0),
            "and winds nothing (inert, no panic)"
        );
        assert_eq!(winding(&mut pool, 0, 0), (0, 0), "a zero quantum is inert");
    }

    /// ★ THE FORCED DIGIT — the flow passing the hand fires the digit AT THE FEED (the flow forces the
    /// doubling): the quotient radiates, the remainder stands sub-quantum, the sweep climbs. Wraps are
    /// structurally impossible; the transition identity `quanta + flow = flow′ + radiated` holds exactly.
    #[test]
    fn the_flow_forces_the_digit_and_wraps_are_impossible() {
        let mut pool = [0u32; 4];
        const Q: u32 = 20;
        let mut fed = 0u64;
        let mut radiated = 0u64;
        // hammer one cell far past the old wrap regime (the old accounting drift's shape, in miniature).
        for _ in 0..100_000 {
            radiated += feed(&mut pool, 2, 137, Q) as u64;
            fed += 137;
        }
        assert!(
            well_of(&pool, 2) <= FLOW_MASK,
            "the flow never passes the hand"
        );
        assert_eq!(
            fed,
            radiated + well_of(&pool, 2) as u64,
            "13.7M quanta through a 13-tooth flow — exact (the forced digit is the re-base)"
        );
        assert!(
            sweep_at(&pool, 2) > 0,
            "the sweep stands — the periplus recorded the sailing"
        );
    }

    /// ★ THE SWEEP NEVER DESCENDS AND SURVIVES THE AUDIT — the ratified gate's own pin: gravity (the standing
    /// sweep) is monotone through feeds and audits; the audit drains the flow and leaves the sweep standing.
    #[test]
    fn the_sweep_survives_the_audit_and_never_descends() {
        let mut pool = [0u32; 2];
        const Q: u32 = 20;
        let mut last_sweep = 0u32;
        for round in 0..200 {
            feed(&mut pool, 1, 137, Q);
            let s = sweep_at(&pool, 1);
            assert!(s >= last_sweep, "the sweep never descends (round {round})");
            last_sweep = s;
            if round % 7 == 0 {
                winding(&mut pool, 1, Q); // the scheduled audit
                let after = sweep_at(&pool, 1);
                assert!(after >= last_sweep, "the audit only deepens the sweep");
                assert!(
                    well_of(&pool, 1) < Q,
                    "the audit drains the flow sub-quantum"
                );
                last_sweep = after;
            }
        }
        assert!(
            last_sweep > 100,
            "two hundred feeds of 137/20 stand as a deep sweep"
        );
    }

    /// ★ THE GRIP PAST THE RESERVATION IS REFUSED, NEVER ALIASED — the control the retired `POOL_MASK`
    /// made unfailable. The mask's only effect was on cells `≥ 2³¹`; the module's own guard assertion uses
    /// cell 999, which is below it, so no configuration of THAT material could have caught the aliasing.
    ///
    /// The material here is `place::ground` at `axis = 2¹⁶`, where the grip space `[0, axis²)` is the whole
    /// `u32` and the top half is therefore reachable from honest places. Two distinct places whose grips
    /// differ by exactly `2³¹` are the distinguishing word: the retired mask sent both to ONE slot.
    #[test]
    fn the_grip_past_the_reservation_is_refused_not_aliased() {
        use crate::num::Cog;
        use crate::place;

        /// the excised level, reproduced here as the thing under test (`law.rs:70`, deleted 2026-08-09).
        const RETIRED_POOL_MASK: u32 = (1u32 << 31) - 1;
        /// the one axis at which `axis²` covers the whole `u32` grip space — read off `place::ground`,
        /// not chosen: `band` returns `[0, axis)` and `ground` returns `band(re)·axis + band(im)`.
        const AXIS: i64 = 1 << 16;

        // §1 the layout is injective on the whole grip space; the retired mask was not.
        assert_eq!(slot(3), 3);
        assert_eq!(slot(0x8000_0003), 0x8000_0003);
        assert_ne!(
            slot(0x8000_0003),
            slot(3),
            "distinct cells occupy distinct slots"
        );
        assert_eq!(
            0x8000_0003u32 & RETIRED_POOL_MASK,
            3,
            "the retired mask aliased the top half onto the bottom"
        );

        // §2 the aliasing region is REACHED by real places. Scan every literal the band can distinguish at
        // this axis — `axis` of them, the extent read off the axis rather than chosen — and key each grip
        // by the slot the retired mask would have handed it.
        let mut past_reservation = 0usize;
        let mut colliding: Option<(i64, i64, u32, u32)> = None;
        let mut seen = std::collections::BTreeMap::<u32, (i64, u32)>::new();
        for a in 0..AXIS {
            let grip = place::ground((Cog::lit(a), Cog::lit(0)), AXIS);
            if grip > RETIRED_POOL_MASK {
                past_reservation += 1;
            }
            match seen.insert(grip & RETIRED_POOL_MASK, (a, grip)) {
                Some((prior_lit, prior_grip)) if prior_grip != grip && colliding.is_none() => {
                    colliding = Some((prior_lit, a, prior_grip, grip));
                }
                _ => {}
            }
        }
        assert!(
            past_reservation > 0,
            "at axis 2^16 the grip space reaches past 2^31 from honest places"
        );
        let (low_lit, high_lit, low_grip, high_grip) =
            colliding.expect("two places whose grips differ by exactly 2^31");
        // THE ORBIT, stated rather than narrated: over the `axis` literals the real part bands to every
        // value in `[0, axis)` exactly once, so the grip's bit 31 — which IS the real band's bit 15 — is
        // set on exactly half of them, and the retired mask collapsed the grip space exactly 2:1.
        // Measured 2026-08-09: `lit(0)` (the ORIGIN) grounds to grip 2_147_516_416 and `lit(32768)` to
        // grip 32_768; both were handed slot 32_768.
        assert_eq!(
            past_reservation,
            (AXIS as usize) / 2,
            "half of every place at this axis grounds past the retired mask"
        );
        assert_eq!(
            seen.len(),
            (AXIS as usize) / 2,
            "which the retired mask folded 2:1 onto the bottom half"
        );
        assert_ne!(low_lit, high_lit);
        assert_ne!(
            low_grip, high_grip,
            "the two places ground to distinct grips"
        );
        assert_eq!(
            low_grip & RETIRED_POOL_MASK,
            high_grip & RETIRED_POOL_MASK,
            "and the retired mask sent both to ONE slot"
        );

        // §3 the orbit: feed the in-reservation grip, then read the aliased one. Under the retired mask
        // this returned the OTHER place's standing flow; under the caller-declared boundary it is refused.
        let (inside, outside) = if low_grip < high_grip {
            (low_grip, high_grip)
        } else {
            (high_grip, low_grip)
        };
        let mut pool = vec![0u32; (inside as usize) + 1];
        const Q: u32 = 20;
        feed(&mut pool, inside, 137, Q);
        assert_eq!(
            well_of(&pool, inside),
            137,
            "the reserved cell took the feed"
        );
        assert_eq!(
            well_of(&pool, outside),
            0,
            "the crossing past the reservation reads the empty pole, not the other place's well"
        );
        assert_eq!(
            (outside & RETIRED_POOL_MASK),
            inside,
            "which is exactly the slot the retired mask would have handed it"
        );

        // and the write direction: an out-of-reservation feed is inert rather than corrupting `inside`.
        assert_eq!(feed(&mut pool, outside, 999, Q), 0, "feeds nowhere");
        assert_eq!(
            well_of(&pool, inside),
            137,
            "the reserved cell is untouched by the crossing"
        );
        assert_eq!(winding(&mut pool, outside, Q), (0, 0), "and winds nothing");
    }

    /// Every interleaving of accrue transitions preserves the same scalar flow accounting. This says nothing
    /// about identical construction or time parity; byte equality is a separate mirror claim.
    #[test]
    fn every_interleaving_of_accrue_accounts_for_flow() {
        const Q: u32 = 20;
        let a: [u32; 6] = [137, 999, 61, 137, 4000, 88];
        let b: [u32; 6] = [210, 137, 137, 8000, 5, 137];
        let orders: [[usize; 12]; 3] = [
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], // a then b
            [0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11], // alternating
            [6, 7, 8, 0, 1, 9, 10, 2, 3, 4, 11, 5], // scrambled
        ];
        let fed_total: u64 = a.iter().chain(b.iter()).map(|&q| q as u64).sum();
        for order in &orders {
            let mut word = 0u32;
            let mut radiated = 0u64;
            for &k in order {
                let q = if k < 6 { a[k] } else { b[k - 6] };
                let (w2, rad) = accrue(word, q, Q);
                word = w2;
                radiated += rad as u64;
            }
            assert_eq!(
                fed_total,
                radiated + flow_of(word) as u64,
                "quotient/remainder accounting telescopes under this serialization"
            );
        }
    }
}
