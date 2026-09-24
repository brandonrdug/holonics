//! medium — THE CLIPPED FIELD's own law (`FORMULA §XXVI` ⊕ the FELT SERIES, `LEDGER` 2026-07-09).
//! Many faces from one point IS the illicium and friction: the sweep FEELS every triangle face of
//! the instantaneous local interaction, and the felt faces stand in DIFFERENT DIRECTIONS. The
//! regional form at one place is a SERIES' PARTIAL SUM held re-based (`Θ = C/r` as a series; re-base
//! is the lawful tolerance, §XXVI): the DIRECTED RESULTANT of the felt second-order pairs ⊕ the
//! WINDING FIBER per hand.
//!
//! Within one lineage, `deposit` follows that current's ordered worldline and may re-base after each
//! term. Across co-present lineages no such order exists: `integrate` performs one two-pass
//! configuration fold at the light's end, with one declared grain and no sequential binary fold
//! (CAS stays dead; the storm stays dissolved). Aligned faces compose ballistically (the groove);
//! scattered faces at half-rank (the background) — the razor and the 2⁻¹ seam are LINK's own
//! composition law (`§XXVI`, `§XXVII`).
//!
//! PURE LAW — types and total transitions only. No pool, no body wiring: the ratified receiving edge
//! (`§XXVIII`) is installed by the membrane, which calls this module's configuration product.

use crate::arrow::Arrow;
use crate::channel::WindingQuantum;
use crate::manifold::{self, Face};
use crate::num::{Cog, Rung};
use crate::soul::Chi;

#[path = "medium/codec.rs"]
mod codec;
pub use codec::{
    CompactFormError, LegacyFormError, COMPACT_FORM_LAYOUT_VERSION, COMPACT_FORM_WORDS,
    LEGACY_FORM_WORDS,
};

/// The additive origin on the register ladder — no mag, no rank, no turn. The starting point, base
/// of the series (`§XXVI`: zero is wherever the frame thinks it is, nothing more).
const COG_ZERO: Cog = Cog {
    mag: 0,
    rank: Rung::ZERO,
    turn: 0,
};

/// ONE DEED's lawful crossing into regional form. Only the transported soul `χ` ⊕ the oriented
/// winding cross a horizon after the deed (`§XXIV`); the deed's frame-local Flow stays with its
/// lineage. A felt term is exactly that crossing pair — nothing of the interior comes with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeltTerm {
    pub chi: Chi,
    pub winding: WindingQuantum,
}

/// THE REGIONAL FORM — a place's clipped field. `same`/`other` are the DIRECTED RESULTANT (the felt
/// second-order pairs accumulated whole: THE SAME face ⊕ THE DIFFERENT face — signed, never
/// normalized, never divided). `this_way`/`that_way` are the two NON-CANCELLING winding arms: a
/// circuit followed by its opposite remains two deposited passages, never a return to zero (mirrors
/// `channel::OrientedWinding`). Deposit-only: the arms and the resultant grow through `deposit`; a
/// read never mutates them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegionalForm {
    same: Cog,
    other: Cog,
    this_way: Rung,
    that_way: Rung,
    /// A founded grip remains founded even when its directed resultant cancels exactly. This is
    /// the grip face of `grip ⊕ RegionalForm`, not a founder, identity key, or history list.
    occupied: bool,
}

impl RegionalForm {
    /// THE UNBORN place — the series' empty partial sum. Lawful (unlike the channel's horizon): a
    /// place with no felt term reads as no drag, no fiber. All-zero, and the all-zero seam row
    /// unpacks straight back to it.
    pub const UNBORN: RegionalForm = RegionalForm {
        same: COG_ZERO,
        other: COG_ZERO,
        this_way: Rung::ZERO,
        that_way: Rung::ZERO,
        occupied: false,
    };

    /// ONE LINEAGE'S ORDERED DEPOSIT. The resultant folds the felt pair component-wise (`Cog::add`
    /// re-bases at the current hand — the series' partial sum at the lawful tolerance, `§XXVI`); the
    /// fiber deposits one unit on the term's arm, `None` deposits none. This order is the lineage's
    /// worldline and is lawful. It is NOT the cross-lineage product: sequential re-base is not
    /// associative, so co-present forms meet only through `integrate` at the light's end.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    #[cfg_attr(not(target_arch = "spirv"), inline)]
    pub fn deposit(self, term: FeltTerm) -> RegionalForm {
        let (this_way, that_way) = match term.winding {
            WindingQuantum::None => (self.this_way, self.that_way),
            WindingQuantum::ThisWay => (self.this_way.add(Rung::of(1)), self.that_way),
            WindingQuantum::ThatWay => (self.this_way, self.that_way.add(Rung::of(1))),
        };
        RegionalForm {
            same: self.same.add(term.chi.same),
            other: self.other.add(term.chi.other),
            this_way,
            that_way,
            occupied: true,
        }
    }

    /// ★ THE DIRECTED DRAG (`§XIV` generalized by the felt series). A later lineage's meeting is
    /// dragged by the standing resultant READ AT THE MEETING'S OWN HAND (`§XXV-b` THE TIP'S GRAIN):
    /// the enclosure's interior scale is gauge, so `rebase_pair` strips the resultant's accumulated
    /// common rank before it enters the relating — the standing form arrives at the content's grain
    /// and can NEVER swamp the content (the collapse conviction, `§XXV-b`).
    ///
    /// THE ALGEBRA. The resultant `(same, other)` is a rotor face — `same` the scalar/cohere real
    /// part, `other` the bivector/different imaginary part (the `Chi` convention). Composing the
    /// meeting rotor `M = aim + i·cross` with the standing rotor `S = same' + i·other'` (`'` = the
    /// re-based pair) is the complex product `M·S`:
    ///
    /// ```text
    /// aim'   = aim·same' − cross·other'
    /// cross' = cross·same' + aim·other'
    /// ```
    ///
    /// `reach` is untouched (the frame-free mass face does not compose). If the resultant is zero
    /// (UNBORN, or a direction exactly cancelled) the meeting returns unchanged — the dark is free,
    /// no torque from nothing.
    ///
    /// IT REDUCES TO `Face::dragged_by` EXACTLY. `dragged_by` composes with the terrain rotor
    /// `(1, −w)`: `aim' = aim + cross·w`, `cross' = cross − aim·w`. Set `same' = 1`, `other' = −w`
    /// (`rebase_pair` leaves a rank-0 pair untouched): `aim·1 − cross·(−w) = aim + cross·w` and
    /// `cross·1 + aim·(−w) = cross − aim·w`. The Cog operations coincide term for term, so the
    /// result is BYTE-IDENTICAL, not merely equal in face — the precession is the single-winding
    /// case of the felt resultant. (The reduction gate pins it.)
    #[cfg_attr(target_arch = "spirv", inline(never))]
    #[cfg_attr(not(target_arch = "spirv"), inline)]
    pub fn drag(self, meeting: Face) -> Face {
        // THE COHERENCE FACE — the resultant's rotor composes where it stands (the built term).
        let faced = if self.same.mag == 0 && self.other.mag == 0 {
            meeting
        } else {
            let (same, other) = manifold::rebase_pair(self.same, self.other);
            let aim = meeting.arrow.aim;
            let cross = meeting.arrow.cross;
            Face {
                arrow: Arrow {
                    reach: meeting.arrow.reach,
                    aim: aim.mul(same).sub(cross.mul(other)),
                    cross: cross.mul(same).add(aim.mul(other)),
                },
            }
        };
        // ★ THE CURVATURE FACE (`FORMULA §XXXIV` — one drag reads the WHOLE form, always; no
        // switch, no predicate): whatever winding stands here curves the trajectory of the
        // arriving inertia relative to it — dark or dressed alike. The two arms compose as the
        // Gaussian terrain rotor `(1,−t)·(1,+a) = (1 + t·a, a − t)`, which reduces BYTE-EXACTLY
        // to the ratified §XIV precession `(1,−w)` when one arm stands alone (the reduction
        // gate). The arm pair strips its common rank first (§XXV-b — scale re-based to the
        // content's grain; the bend's DIRECTION crosses whole).
        if self.this_way.mag == 0 && self.that_way.mag == 0 {
            return faced;
        }
        let arm_cog = |arm: Rung| Cog {
            mag: arm.mag,
            rank: Rung::of(arm.rank),
            turn: 0,
        };
        let (t, a) = manifold::rebase_pair(arm_cog(self.this_way), arm_cog(self.that_way));
        let aim = faced.arrow.aim;
        let cross = faced.arrow.cross;
        let (aim, cross) = if a.mag == 0 {
            // one arm: EXACTLY the §XIV precession `(1,−w)` — the reduction is by construction
            (aim.add(cross.mul(t)), cross.sub(aim.mul(t)))
        } else if t.mag == 0 {
            // the other hand: the mirrored rotor `(1,+w)`
            (aim.sub(cross.mul(a)), cross.add(aim.mul(a)))
        } else {
            // both sides of the boundary: `(1,−t)·(1,+a) = (1 + t·a, a − t)`
            let re = Cog::lit(1).add(t.mul(a));
            let im = a.sub(t);
            (
                aim.mul(re).sub(cross.mul(im)),
                cross.mul(re).add(aim.mul(im)),
            )
        };
        Face {
            arrow: Arrow {
                reach: faced.arrow.reach,
                aim,
                cross,
            },
        }
    }

    /// ★ THE JOIN (`§XXVIII` — a reader's whole past cone: PRE-LIGHT STANDING ⊕ ITS OWN DEPOSITS). The
    /// two already-formed regions fold component-wise (same+same, other+other, arm+arm). The pair fits
    /// the wide hand whole, so the read commutes and the cone never depends on which region is named
    /// first. It is intentionally binary and must never be repeated over a configuration.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    #[cfg_attr(not(target_arch = "spirv"), inline)]
    pub fn join(self, other: RegionalForm) -> RegionalForm {
        RegionalForm {
            same: self.same.add(other.same),
            other: self.other.add(other.other),
            this_way: self.this_way.add(other.this_way),
            that_way: self.that_way.add(other.that_way),
            occupied: self.occupied || other.occupied,
        }
    }

    /// Whether this grip has been founded. Unlike the resultant, this direction cannot cancel: a
    /// later arrival may deepen an occupied grip but cannot make it unborn.
    #[inline]
    pub fn occupied(self) -> bool {
        self.occupied
    }

    /// The receiving edge has observed at least one founded cast at this grip. Its numeric form may
    /// be exactly zero; occupancy is the construction's positional face.
    #[inline]
    pub fn occupy(mut self) -> RegionalForm {
        self.occupied = true;
        self
    }

    /// THE WINDING FIBER — the two non-cancelling arms `(this_way, that_way)`. The direction spread
    /// is felt HERE, not as a scalar count.
    #[inline]
    pub fn fiber(self) -> (Rung, Rung) {
        (self.this_way, self.that_way)
    }

    /// THE DIRECTED RESULTANT — the felt pairs' partial sum `(same, other)`, held whole (never
    /// divided). A boundary read of the raw accumulation, before any grain re-base.
    #[inline]
    pub fn resultant(self) -> (Cog, Cog) {
        (self.same, self.other)
    }
}

/// `RegionalForm`'s active canonical seam extent. Generic Cog/Rung, carrier, and K layouts remain
/// unchanged; only this place-local form uses the direct eleven-word codec in `medium::codec`.
pub const FORM_WORDS: usize = COMPACT_FORM_WORDS;

impl RegionalForm {
    /// Re-form the four exact components after the configuration fold's one final re-base. The
    /// constructor is the card/cpu shared mouth; it performs no additional fold or normalization.
    #[inline]
    pub fn from_components(same: Cog, other: Cog, this_way: Rung, that_way: Rung) -> RegionalForm {
        let occupied = same.mag != 0 || other.mag != 0 || this_way.mag != 0 || that_way.mag != 0;
        RegionalForm {
            same,
            other,
            this_way,
            that_way,
            occupied,
        }
    }
}

/// The unsigned midpoint of the card grain order. Zero stands here; positive rungs rise above it
/// and negative rungs descend below it. One `atomic_u_max` can therefore declare exactly the same
/// grain as `Rung::cmp_teeth` without flattening the whole rung to its inner `rank` field.
const GRAIN_ZERO: u64 = 1u64 << 63;
const GRAIN_FRACTION: u64 = (1u64 << 31) - 1;

/// THE WHOLE-RUNG GRAIN KEY — an order-preserving, canonical boundary face of a `Rung`. Engine-born
/// rungs have one representation: flat values use `rank == 0`; a re-based rung has `rank > 0` and
/// its mantissa's high bit set. `top-tooth ⊕ normalized mantissa` therefore round-trips that whole
/// construction in 63 magnitude bits. The upper/lower half carries its direction. This is a card
/// realization of `cmp_teeth`, never a replacement number system.
#[inline]
pub fn grain_key(r: Rung) -> u64 {
    if r.mag == 0 {
        return GRAIN_ZERO;
    }
    let mut top_bit = 0u32;
    let mut v = r.mag >> 1;
    while v != 0 {
        v >>= 1;
        top_bit += 1;
    }
    // `Rung.rank >= 0` is structural (`num::Rung`); the top stays below 2^32 and the composed
    // magnitude below 2^63 across the entire representable hand.
    let top = r.rank as u64 + top_bit as u64;
    let normalized = (r.mag as u64) << (31 - top_bit);
    let magnitude = (top << 31) | (normalized & GRAIN_FRACTION);
    if r.neg {
        GRAIN_ZERO - (magnitude + 1)
    } else {
        GRAIN_ZERO + (magnitude + 1)
    }
}

/// The exact canonical `Rung` carried by a grain key. Equivalent non-canonical boundary spellings
/// return to the one engine representation, so equal grains cannot retain a first-lane tie-break.
#[inline]
pub fn grain_from_key(key: u64) -> Rung {
    if key == GRAIN_ZERO {
        return Rung::ZERO;
    }
    let (negative, magnitude) = if key < GRAIN_ZERO {
        (true, GRAIN_ZERO - key - 1)
    } else {
        (false, key - GRAIN_ZERO - 1)
    };
    let top = magnitude >> 31;
    let normalized = (1u32 << 31) | (magnitude as u32 & GRAIN_FRACTION as u32);
    if top <= 31 {
        Rung {
            mag: normalized >> (31 - top as u32),
            rank: 0,
            neg: negative,
        }
    } else {
        Rung {
            mag: normalized,
            rank: (top - 31) as i32,
            neg: negative,
        }
    }
}

/// One Cog contribution re-based exactly once to the configuration's declared grain. The half-turn
/// remains the high bit of a two's-complement `u64` hand; no signed scalar is interposed between the
/// turn and the fold. This is also the exact bit-face consumed by the card's integer atomic add.
#[inline]
pub fn cog_at_grain(c: Cog, grain: Rung) -> u64 {
    if c.mag == 0 {
        return 0;
    }
    let drop = grain.sub(c.rank);
    let m = match drop.face() {
        Some(d) if d >= 32 => 0u32,
        Some(d) if d >= 0 => c.mag >> d,
        _ => 0, // a rank above the declared grain cannot exist
    };
    let sign = ((c.turn >> 1) & 1) as u64;
    ((m as u64) ^ 0u64.wrapping_sub(sign)).wrapping_add(sign)
}

/// The Cog configuration sum's ONE final re-base at its already-declared grain.
#[inline]
pub fn cog_from_sum(grain: Rung, sum: u64) -> Cog {
    if sum == 0 {
        return Cog::lit(0);
    }
    let sign = (sum >> 63) & 1;
    let mut mag = (sum ^ 0u64.wrapping_sub(sign)).wrapping_add(sign);
    let mut climb = 0u32;
    while mag > u32::MAX as u64 {
        mag >>= 1;
        climb += 1;
    }
    Cog {
        mag: mag as u32,
        rank: grain.add(Rung::of(climb as i32)),
        turn: (sign as u32) << 1,
    }
}

/// One unsigned winding-arm contribution at the declared arm grain.
#[inline]
pub fn arm_at_grain(arm: Rung, grain: i32) -> u64 {
    if arm.mag == 0 {
        return 0;
    }
    let drop = grain - arm.rank;
    if drop >= 0 && drop < 32 {
        (arm.mag >> drop) as u64
    } else {
        0
    }
}

/// The winding-arm configuration sum's ONE final re-base.
#[inline]
pub fn arm_from_sum(grain: i32, sum: u64) -> Rung {
    let mut mag = sum;
    let mut climb = 0i32;
    while mag > u32::MAX as u64 {
        mag >>= 1;
        climb += 1;
    }
    Rung {
        mag: mag as u32,
        rank: grain + climb,
        neg: false,
    }
}

/// ★ THE CONFIGURATION FOLD (ratified 2026-07-09 — Sol's associativity conviction answered): the
/// CROSS-LANE product is ONE fold at the light's end, two passes, both order-free. PASS 1 — THE
/// GRAIN DECLARES ITSELF: the deepest hand present per component (max of ranks — associative,
/// commutative, idempotent; a pure function of the multiset, never authored, never order-chosen).
/// PASS 2 — THE EXACT SUM AT THE GRAIN: each contribution re-based ONCE to the declared grain,
/// summed exactly in a wide hand, ONE re-base of the result. Sub-grain contributions fall dark
/// UNIFORMLY (the declared tolerance — every observer agrees which fell; the sweep's own
/// "sub-grain drips fall dark" law). Repeated binary folds are NOT the regional product: re-base
/// after every fold is commutative but not associative — the accumulation order would decide which
/// co-present differences cohere before the grain is taken, the hidden chronology one layer
/// beneath CAS. `join` remains lawful ONLY as the cone's single two-term read (exact for two —
/// the pair fits the wide hand whole); it is never folded over a configuration.
/// Card realization: pass 1 is an atomic max, pass 2 an atomic add — nothing to race (§XXVIII).
pub fn integrate(forms: &[RegionalForm]) -> RegionalForm {
    RegionalForm {
        same: fold_cogs(forms, false),
        other: fold_cogs(forms, true),
        this_way: fold_arms(forms, false),
        that_way: fold_arms(forms, true),
        occupied: forms.iter().any(|form| form.occupied),
    }
}

/// One Cog component's two-pass fold. The sign rides the half-turn bit; contributions are
/// real-signed faces (the medium's components carry no quarter-turn — the direction lives in the
/// (same, other) PAIR, never in one component's imaginary axis).
fn fold_cogs(forms: &[RegionalForm], other_face: bool) -> Cog {
    let pick = |f: &RegionalForm| if other_face { f.other } else { f.same };
    // PASS 1 — the grain declares itself: the deepest hand present.
    let mut grain: Option<u64> = None;
    let mut i = 0usize;
    while i < forms.len() {
        let c = pick(&forms[i]);
        if c.mag != 0 {
            let key = grain_key(c.rank);
            grain = Some(match grain {
                None => key,
                Some(g) if key > g => key,
                Some(g) => g,
            });
        }
        i += 1;
    }
    let Some(grain_key) = grain else {
        return Cog::lit(0);
    };
    let grain = grain_from_key(grain_key);
    // PASS 2 — the exact sum at the grain: each contribution re-based ONCE, wide-hand exact.
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < forms.len() {
        acc = acc.wrapping_add(cog_at_grain(pick(&forms[i]), grain));
        i += 1;
    }
    cog_from_sum(grain, acc)
}

/// One winding arm's two-pass fold — the same law on the unsigned count face (arms never cancel,
/// never carry a sign; `neg` rungs cannot enter an arm by construction).
fn fold_arms(forms: &[RegionalForm], that_face: bool) -> Rung {
    let pick = |f: &RegionalForm| if that_face { f.that_way } else { f.this_way };
    let mut grain: Option<i32> = None;
    let mut i = 0usize;
    while i < forms.len() {
        let r = pick(&forms[i]);
        if r.mag != 0 {
            grain = Some(match grain {
                None => r.rank,
                Some(g) if r.rank > g => r.rank,
                Some(g) => g,
            });
        }
        i += 1;
    }
    let Some(grain) = grain else {
        return Rung::ZERO;
    };
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < forms.len() {
        acc = acc.wrapping_add(arm_at_grain(pick(&forms[i]), grain));
        i += 1;
    }
    arm_from_sum(grain, acc)
}

/// HISTORICAL FOSSIL — the superseded §XXXIV-c projected-identity scan. §XXXV-b quarantines this
/// mechanism from every production mouth: it is compiled only for the historical reproduction
/// below and must never select, merge, depart, or narrow a live body. Its old transition remains
/// intact so the 63-settles record stays reproducible while the lawful seam runs fold → archive.
#[cfg(test)]
pub(crate) fn settle_standing(
    standing: &mut [u32],
    axis_in: i64,
    register_in: crate::chart::Register,
) -> (i64, crate::chart::Register, u64, u32) {
    let mut axis = axis_in;
    let mut register = register_in;
    let mut settled_cells = 0u64;
    let mut retired = 0u32;
    loop {
        let side = axis as usize;
        let mut borrowed = false;
        let mut pass_settled = 0u64;
        let mut by = 0usize;
        while by + 1 < side || (side == 1 && by == 0) {
            if side == 1 {
                break;
            }
            let mut bx = 0usize;
            while bx + 1 < side || bx == 0 {
                if bx + 1 >= side {
                    break;
                }
                let block = [
                    by * side + bx,
                    by * side + bx + 1,
                    (by + 1) * side + bx,
                    (by + 1) * side + bx + 1,
                ];
                let mut live: [Option<usize>; 4] = [None; 4];
                let mut live_count = 0usize;
                for (slot, &grip) in block.iter().enumerate() {
                    if RegionalForm::unpack(standing, grip * FORM_WORDS).occupied() {
                        live[slot] = Some(grip);
                        live_count += 1;
                    }
                }
                if live_count >= 2 {
                    // THE IDENTITY READ AT THE HAND (§XXXIV-c): the block's own declared grain —
                    // the deepest hand present, the fold's own law — is the measurement's
                    // resolution. Forms whose faces are EQUAL AT THAT GRAIN are indistinguishable
                    // to this measurement (the observer effect): one circulating structure,
                    // encountered k times. Sub-grain detail falls dark uniformly in the fold —
                    // the declared tolerance, never a threshold.
                    let mut forms = [RegionalForm::UNBORN; 4];
                    let mut n = 0usize;
                    for &slot in live.iter().flatten() {
                        forms[n] = RegionalForm::unpack(standing, slot * FORM_WORDS);
                        n += 1;
                    }
                    let live_forms = &forms[..live_count];
                    let mut g_same = 0u64;
                    let mut g_other = 0u64;
                    let mut g_tw = 0u32;
                    let mut g_ta = 0u32;
                    for f in live_forms {
                        let (same, other) = f.resultant();
                        let (tw, ta) = f.fiber();
                        if same.mag != 0 {
                            g_same = g_same.max(grain_key(same.rank));
                        }
                        if other.mag != 0 {
                            g_other = g_other.max(grain_key(other.rank));
                        }
                        if tw.mag != 0 {
                            g_tw = g_tw.max(tw.rank as u32 + 1);
                        }
                        if ta.mag != 0 {
                            g_ta = g_ta.max(ta.rank as u32 + 1);
                        }
                    }
                    // THE HALF-RANK RAZOR IS THE MEASUREMENT'S CERTAINTY (§XXVI/§XXVII): the
                    // seam reads FAR standing form, and a far read more certain than half-rank
                    // has smuggled an absolute frame — the razor's own words. The identity is
                    // therefore read on the TOP HALF of the mantissa at the declared grain
                    // (aim-rank = ½·reach-rank; the 2⁻¹ seam; the mantissa's tolerance — one
                    // law). Arithmetic shift keeps the sign whole.
                    const HALF_RANK: u32 = 16;
                    let face_at_hand = |f: &RegionalForm| {
                        let (same, other) = f.resultant();
                        let (tw, ta) = f.fiber();
                        (
                            if g_same != 0 {
                                (cog_at_grain(same, grain_from_key(g_same)) as i64) >> HALF_RANK
                            } else {
                                0
                            },
                            if g_other != 0 {
                                (cog_at_grain(other, grain_from_key(g_other)) as i64) >> HALF_RANK
                            } else {
                                0
                            },
                            if g_tw != 0 {
                                (arm_at_grain(tw, g_tw as i32 - 1) >> HALF_RANK) as i64
                            } else {
                                0
                            },
                            if g_ta != 0 {
                                (arm_at_grain(ta, g_ta as i32 - 1) >> HALF_RANK) as i64
                            } else {
                                0
                            },
                        )
                    };
                    let reference = face_at_hand(&live_forms[0]);
                    let mut identical = true;
                    for f in &live_forms[1..] {
                        if face_at_hand(f) != reference {
                            identical = false;
                            break;
                        }
                    }
                    if identical {
                        // the k encounters cross the ONE configuration fold — the actual forms,
                        // sub-grain detail falling dark uniformly at the declared grain
                        let settled = integrate(live_forms).occupy();
                        // vacate the block, then land the settled structure at the section cell
                        for &slot in live.iter().flatten() {
                            let at = slot * FORM_WORDS;
                            let mut w = 0usize;
                            while w < FORM_WORDS {
                                standing[at + w] = 0;
                                w += 1;
                            }
                        }
                        settled.pack(standing, block[0] * FORM_WORDS);
                        let mut departs = live_count - 1;
                        while departs > 0 {
                            let (next, b) = register.depart();
                            register = next;
                            borrowed |= b;
                            departs -= 1;
                        }
                        pass_settled += (live_count - 1) as u64;
                    }
                }
                bx += 2;
            }
            by += 2;
        }
        settled_cells += pass_settled;
        // the narrow, exactly the breath's law: only when the borrow fired and every live cell
        // sits on the retiring digit's zero section — lossless, never a merge of its own.
        let mut narrowed = false;
        if borrowed && axis > 1 {
            let new_axis = axis >> 1;
            let cells = (axis * axis) as usize;
            let mut clean = true;
            let mut grip = 0usize;
            while grip < cells {
                if RegionalForm::unpack(standing, grip * FORM_WORDS).occupied()
                    && crate::chart::zero_extended_source(grip as u32, new_axis as u32, axis as u32)
                        .is_none()
                {
                    clean = false;
                    break;
                }
                grip += 1;
            }
            if clean {
                let mut grip = 0usize;
                while grip < cells {
                    let at = grip * FORM_WORDS;
                    if RegionalForm::unpack(standing, at).occupied() {
                        let moved = crate::chart::zero_extended_source(
                            grip as u32,
                            new_axis as u32,
                            axis as u32,
                        )
                        .expect("a clean section narrows losslessly")
                            as usize
                            * FORM_WORDS;
                        if moved != at {
                            let mut w = 0usize;
                            while w < FORM_WORDS {
                                standing[moved + w] = standing[at + w];
                                standing[at + w] = 0;
                                w += 1;
                            }
                        }
                    }
                    grip += 1;
                }
                axis = new_axis;
                register = register.digit_retired();
                retired += 1;
                narrowed = true;
            }
        }
        if pass_settled == 0 && !narrowed {
            break;
        }
    }
    (axis, register, settled_cells, retired)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::seam::WordSeam;

    struct MirrorWordSeam;

    unsafe impl WordSeam for MirrorWordSeam {
        unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
            *words.get_unchecked(at)
        }

        unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
            panic!("the form fixture never stores through its read face")
        }
    }

    struct TrapWordSeam;

    unsafe impl WordSeam for TrapWordSeam {
        unsafe fn read_u32_unchecked(_words: &[u32], _at: usize) -> u32 {
            panic!("a short form must not enter the seam")
        }

        unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
            panic!("a short form must not enter the seam")
        }
    }
    use crate::manifold::StandingWinding;

    fn term(same: i64, other: i64, winding: WindingQuantum) -> FeltTerm {
        FeltTerm {
            chi: Chi {
                same: Cog::lit(same),
                other: Cog::lit(other),
            },
            winding,
        }
    }

    fn deposit_all(terms: &[FeltTerm]) -> RegionalForm {
        let mut form = RegionalForm::UNBORN;
        for &t in terms {
            form = form.deposit(t);
        }
        form
    }

    fn meeting(aim: i64, cross: i64) -> Face {
        Face {
            arrow: Arrow {
                reach: Cog::lit(1),
                aim: Cog::lit(aim),
                cross: Cog::lit(cross),
            },
        }
    }

    /// the total-teeth position of a Cog on the ladder — rank position ⊕ the mantissa's own top.
    fn total_rank(c: Cog) -> i64 {
        if c.mag == 0 {
            return 0;
        }
        let mut top = 0i64;
        let mut v = c.mag >> 1;
        while v != 0 {
            v >>= 1;
            top += 1;
        }
        c.rank.face().unwrap_or(1 << 40) + top
    }

    /// A LANE'S CHRONOLOGY IS REAL. Re-based deposit is a left fold over that worldline; the known
    /// H ⊕ u ⊕ u witness lands differently when its chronology is reversed. This negative pin keeps
    /// `deposit` from being mistaken for the co-present product; `integrate` alone drops lane order.
    #[test]
    fn a_lane_deposits_in_its_own_worldline_order() {
        let h = FeltTerm {
            chi: Chi {
                same: Cog::lit(1 << 30).turn_up(2),
                other: Cog::lit(0),
            },
            winding: WindingQuantum::None,
        };
        let u = term(1, 0, WindingQuantum::None);
        assert_ne!(
            deposit_all(&[h, u, u]),
            deposit_all(&[u, u, h]),
            "the lane's worldline survives its sequential re-base; only the configuration fold drops cross-lane order"
        );
    }

    /// THE CONE JOINS THE TWO REGIONS ORDER-FREE (`§XXVIII`). Standing ⊕ own commute; the join of two
    /// forms is one exact binary read at their already-declared grains; the unborn region adds
    /// nothing. This is the two-region cone's own permutation gate.
    #[test]
    fn the_cone_joins_the_two_regions_in_any_order() {
        let standing = deposit_all(&[
            term(3, 5, WindingQuantum::ThisWay),
            term(-2, 7, WindingQuantum::ThatWay),
        ]);
        let own = deposit_all(&[
            term(11, -4, WindingQuantum::None),
            term(6, 6, WindingQuantum::ThisWay),
        ]);
        assert_eq!(
            standing.join(own),
            own.join(standing),
            "the cone is order-free — standing ⊕ own commute"
        );
        assert_eq!(
            RegionalForm::UNBORN.join(own),
            own,
            "the unborn region adds nothing"
        );
        assert_eq!(
            own.join(RegionalForm::UNBORN),
            own,
            "either side unborn is the identity"
        );
    }

    /// TOOTH 3 — SAME-FACE / DIFFERENT-SOUL SEPARATION. Two aligned deposits vs two opposed ones,
    /// each carrying a winding arm. Opposed χ SHRINKS the resultant toward zero WHILE the fiber
    /// records the spread across BOTH arms — the direction spread IS the felt fiber. A scalar count
    /// of deposits (2 either way) cannot tell these apart; the (fiber, resultant) pair does.
    #[test]
    fn the_direction_spread_is_felt_as_fiber_not_lost() {
        let aligned = deposit_all(&[
            term(3, 4, WindingQuantum::ThisWay),
            term(3, 4, WindingQuantum::ThisWay),
        ]);
        let opposed = deposit_all(&[
            term(3, 4, WindingQuantum::ThisWay),
            term(-3, -4, WindingQuantum::ThatWay),
        ]);

        // the opposed fiber holds both arms without cancelling — a circuit and its opposite are two
        // deposited passages, never a return to zero.
        assert_eq!(opposed.fiber().0.face(), Some(1));
        assert_eq!(opposed.fiber().1.face(), Some(1));

        // the resultant shrinks under opposition (to the base) while it stands under alignment.
        let (as_, ao) = aligned.resultant();
        let (os, oo) = opposed.resultant();
        assert_ne!(as_.mag, 0, "aligned faces compose — the resultant stands");
        assert_ne!(ao.mag, 0);
        assert_eq!(
            os.mag, 0,
            "opposed faces cancel in the resultant — the spread"
        );
        assert_eq!(oo.mag, 0);

        // the same scalar count (2 deposits) yields DIFFERENT forms — the fiber distinguishes.
        assert_ne!(
            aligned.fiber(),
            opposed.fiber(),
            "one arm twice vs two arms once — the felt spread, not a count"
        );
        assert_ne!(aligned, opposed);
    }

    /// THE TWO ARMS NEVER CANCEL. ThisWay then ThatWay — both arms stand at one, and the form is no
    /// longer UNBORN even though the (zero) resultant did not move.
    #[test]
    fn the_two_arms_never_cancel() {
        let form = RegionalForm::UNBORN
            .deposit(term(0, 0, WindingQuantum::ThisWay))
            .deposit(term(0, 0, WindingQuantum::ThatWay));
        assert_eq!(form.fiber().0.face(), Some(1));
        assert_eq!(form.fiber().1.face(), Some(1));
        assert_ne!(
            form,
            RegionalForm::UNBORN,
            "a deposited passage is not nothing"
        );
    }

    /// THE DIRECTED DRAG READS DIRECTION. Deposits aligned one way vs opposed drag the SAME meeting
    /// to different faces; the UNBORN form drags nothing (the dark is free).
    #[test]
    fn the_directed_drag_reads_direction() {
        let m = meeting(5, 2);
        let one_way = deposit_all(&[
            term(4, 6, WindingQuantum::None),
            term(4, 6, WindingQuantum::None),
        ]);
        let other_way = deposit_all(&[
            term(4, 6, WindingQuantum::None),
            term(4, -6, WindingQuantum::None),
        ]);
        assert_ne!(
            one_way.drag(m),
            other_way.drag(m),
            "the standing direction bends the passing frame — deflection gains an axis"
        );
        assert_eq!(
            RegionalForm::UNBORN.drag(m),
            m,
            "no resultant, no torque — the dark is free"
        );
    }

    /// THE DRAG IS THE PRECESSION'S FELT-SERIES GENERALIZATION. A single winding resultant
    /// `(1, −w)` reduces the felt drag to `Face::dragged_by` byte-for-byte (§XIV is the one-term
    /// case of §XXVI's series).
    #[test]
    fn the_drag_reduces_to_the_precession_at_a_single_winding() {
        let w = 3i64;
        let form = RegionalForm::UNBORN.deposit(term(1, -w, WindingQuantum::None));
        let m = meeting(5, 2);
        assert_eq!(
            form.drag(m),
            m.dragged_by(StandingWinding::at_boundary(w)),
            "the felt resultant (1,−w) IS the terrain rotor of the precession"
        );
    }

    /// TOOTH 6 — THE HALF-RANK RAZOR, AS PHYSICS. Aligned faces compose BALLISTICALLY: the
    /// resultant's rank grows with the count's rank (`2·rank ≥ rank-of-count`). Scattered (opposed)
    /// faces compose DIFFUSELY: the resultant's rank stays at/below half the count's rank
    /// (`2·rank ≤ rank-of-count`) — the 2⁻¹ seam, LINK's own composition law (§XXVI/§XXVII). Written
    /// with exact constructed terms, no dice.
    #[test]
    fn aligned_faces_compose_ballistically_scattered_at_half_rank() {
        let count = total_rank(Cog::lit(64));

        // 64 aligned deposits of the unit resultant → 64, rank == count (ballistic).
        let mut ballistic = RegionalForm::UNBORN;
        let mut i = 0;
        while i < 64 {
            ballistic = ballistic.deposit(term(1, 0, WindingQuantum::None));
            i += 1;
        }
        let (bs, _) = ballistic.resultant();
        assert_eq!(bs.face(), 64, "the groove sums whole");
        assert!(
            2 * total_rank(bs) >= count,
            "aligned: 2·{} ≥ {}",
            total_rank(bs),
            count
        );

        // 64 deposits in opposed pairs (directions alternating) → the diffuse walk cancels to the
        // base; its rank sits at/below half the count's (half-rank).
        let mut diffuse = RegionalForm::UNBORN;
        let mut j = 0;
        while j < 64 {
            let dir = if j & 1 == 0 { 1 } else { -1 };
            diffuse = diffuse.deposit(term(dir, 0, WindingQuantum::None));
            j += 1;
        }
        let (ds, _) = diffuse.resultant();
        assert!(
            2 * total_rank(ds) <= count,
            "scattered: 2·{} ≤ {}",
            total_rank(ds),
            count
        );
    }

    /// THE SEAM ROUND-TRIPS. A form built from several deposits crosses pack→unpack byte-exact at a
    /// shifted offset; the all-zero row unpacks straight to UNBORN.
    #[test]
    fn the_form_crosses_the_seam_byte_exact() {
        let form = deposit_all(&[
            term(7, -3, WindingQuantum::ThisWay),
            term(-11, 5, WindingQuantum::ThatWay),
            term(2, 2, WindingQuantum::ThisWay),
        ]);
        let mut row = [9u32; FORM_WORDS + 3];
        form.pack(&mut row, 2);
        assert_eq!(
            RegionalForm::unpack(&row, 2),
            form,
            "the clipped field crosses whole"
        );
        assert_eq!(
            RegionalForm::unpack_with::<MirrorWordSeam>(&row, 2),
            form,
            "the canonical form reader crosses the supplied seam"
        );

        let unborn = [0u32; FORM_WORDS];
        assert_eq!(
            RegionalForm::unpack(&unborn, 0),
            RegionalForm::UNBORN,
            "the all-zero row is the unborn place"
        );

        let short = [u32::MAX; FORM_WORDS - 1];
        assert_eq!(
            RegionalForm::unpack_with::<TrapWordSeam>(&short, 0),
            RegionalForm::UNBORN,
            "a short nonzero prefix is one structural absence"
        );
        assert_eq!(
            RegionalForm::unpack_with::<TrapWordSeam>(&short, usize::MAX),
            RegionalForm::UNBORN,
            "extent arithmetic cannot wrap a short row into presence"
        );
    }

    /// THE DRAG HOLDS THE MEETING'S GRAIN (the collapse conviction, §XXV-b). A standing resultant of
    /// HUGE rank drags a small meeting WITHOUT swamping it: `rebase_pair` strips the enclosure's
    /// interior scale, so the dragged components stay within a bounded number of ranks of the
    /// original rather than being lifted to the terrain's ~200-rank scale.
    #[test]
    fn the_drag_never_swamps_the_content() {
        let huge = RegionalForm::UNBORN.deposit(FeltTerm {
            chi: Chi {
                same: Cog::lit(3).turn_up(200),
                other: Cog::lit(5).turn_up(202),
            },
            winding: WindingQuantum::None,
        });
        let (hs, _) = huge.resultant();
        assert!(
            total_rank(hs) >= 200,
            "the standing resultant really is huge"
        );

        let m = meeting(5, 2);
        let dragged = huge.drag(m);
        assert!(
            total_rank(dragged.arrow.aim) < 64,
            "the dragged aim stays at the content's grain, not the terrain's ({})",
            total_rank(dragged.arrow.aim)
        );
        assert!(
            total_rank(dragged.arrow.cross) < 64,
            "the dragged cross stays at the content's grain ({})",
            total_rank(dragged.arrow.cross)
        );
    }

    /// ★ THE CONFIGURATION FOLD IS ORDER-FREE AT THE GRAIN EDGE (Sol's witness shape, 2026-07-09):
    /// one huge-rank contribution beside units whose coherence would be order-dependent under
    /// repeated binary folding. The fold's two passes (the grain declares itself; the exact sum at
    /// it) return ONE form for every permutation — including the arms.
    #[test]
    fn the_configuration_fold_is_order_free_at_the_grain_edge() {
        // H: a deep-rank form; u: unit forms — Sol's exact shape (H ⊕ u ⊕ u).
        let h = RegionalForm::UNBORN.deposit(FeltTerm {
            chi: Chi {
                same: Cog::lit(1 << 30).turn_up(2),
                other: Cog::lit(3),
            },
            winding: WindingQuantum::ThisWay,
        });
        let u = RegionalForm::UNBORN.deposit(term(1, 1, WindingQuantum::ThatWay));
        let configs: [&[RegionalForm]; 3] = [&[h, u, u], &[u, u, h], &[u, h, u]];
        let folded = integrate(configs[0]);
        assert_eq!(folded, integrate(configs[1]), "H last = H first");
        assert_eq!(folded, integrate(configs[2]), "H middle = H first");
        // the arms sum exactly across the fold (1 + 1 + 1 of ThisWay/ThatWay split):
        assert_eq!(folded.fiber().0.face(), Some(1), "one ThisWay arm");
        assert_eq!(folded.fiber().1.face(), Some(2), "two ThatWay arms");
        // and the empty configuration is the unborn place:
        assert_eq!(integrate(&[]), RegionalForm::UNBORN);
    }

    /// M4'S WHOLE-RUNG GRAIN FACE. The key round-trips every canonical rung shape used by the
    /// engine and orders them exactly as `cmp_teeth`. Two equivalent boundary spellings collapse to
    /// the same canonical key, so an equal maximum cannot retain a first-lane representation.
    #[test]
    fn the_whole_rung_grain_key_is_exact_and_order_preserving() {
        let rungs = [
            Rung::of(-19),
            Rung::of(-1),
            Rung::ZERO,
            Rung::of(1),
            Rung::of(19),
            Rung {
                mag: 1u32 << 31,
                rank: 1,
                neg: false,
            },
            Rung {
                mag: u32::MAX,
                rank: 117,
                neg: false,
            },
            Rung {
                mag: u32::MAX,
                rank: 117,
                neg: true,
            },
            Rung {
                mag: u32::MAX,
                rank: i32::MAX,
                neg: false,
            },
        ];
        for &r in &rungs {
            assert_eq!(
                grain_from_key(grain_key(r)),
                r,
                "the whole rung round-trips"
            );
        }
        for &a in &rungs {
            for &b in &rungs {
                assert_eq!(
                    grain_key(a).cmp(&grain_key(b)),
                    a.cmp_teeth(b).cmp(&0),
                    "the atomic key and the native rung order are one order"
                );
            }
        }

        let flat_two = Rung::of(2);
        let same_two = Rung {
            mag: 1,
            rank: 1,
            neg: false,
        };
        assert_eq!(flat_two.cmp_teeth(same_two), 0);
        assert_eq!(grain_key(flat_two), grain_key(same_two));
        assert_eq!(grain_from_key(grain_key(same_two)), flat_two);

        let a = RegionalForm::from_components(
            Cog {
                mag: 5,
                rank: flat_two,
                turn: 0,
            },
            Cog::lit(0),
            Rung::ZERO,
            Rung::ZERO,
        );
        let b = RegionalForm::from_components(
            Cog {
                mag: 7,
                rank: same_two,
                turn: 0,
            },
            Cog::lit(0),
            Rung::ZERO,
            Rung::ZERO,
        );
        assert_eq!(
            integrate(&[a, b]),
            integrate(&[b, a]),
            "equal-valued grain spellings cannot leak lane order"
        );
    }

    /// The card's first M4 crossing caught a direct `u32 → i64` lowering being sign-extended. The
    /// configuration hand therefore keeps the half-turn in unsigned two's-complement bits whole.
    #[test]
    fn the_wide_configuration_hand_never_interposes_a_signed_mantissa() {
        let grain = Rung::of(7);
        let forward = Cog {
            mag: u32::MAX,
            rank: grain,
            turn: 0,
        };
        let backward = Cog { turn: 2, ..forward };
        assert_eq!(cog_at_grain(forward, grain), u32::MAX as u64);
        assert_eq!(
            cog_at_grain(backward, grain),
            0u64.wrapping_sub(u32::MAX as u64)
        );
        assert_eq!(
            cog_from_sum(
                grain,
                cog_at_grain(forward, grain).wrapping_add(cog_at_grain(backward, grain)),
            ),
            Cog::lit(0),
            "opposite half-turns cancel without changing the positive mantissa's sign"
        );
    }

    /// The fold's declared grain is uniform: contributions below the deepest hand fall dark for
    /// EVERY permutation identically (the honest tolerance), never order-dependently.
    #[test]
    fn sub_grain_contributions_fall_dark_uniformly() {
        let deep = RegionalForm::UNBORN.deposit(FeltTerm {
            chi: Chi {
                same: Cog::lit(1).turn_up(40), // rank 40 — the declared grain
                other: Cog::lit(0),
            },
            winding: WindingQuantum::None,
        });
        let shallow = RegionalForm::UNBORN.deposit(term(3, 0, WindingQuantum::None)); // rank ~0
        let a = integrate(&[deep, shallow, shallow]);
        let b = integrate(&[shallow, deep, shallow]);
        assert_eq!(
            a, b,
            "the drop below the grain is a pure function of the multiset"
        );
        assert_eq!(
            a.resultant().0,
            deep.resultant().0,
            "rank-0 units stand 40 ranks below the declared grain — dark in the fold, uniformly"
        );
    }

    /// HISTORICAL REPRODUCTION: preserve the projected-identity scan's recorded fold, departure,
    /// narrowing, and idempotence after §XXXV-b removes it from production.
    #[test]
    fn the_superseded_identity_settling_reproduces_its_historical_transition() {
        use crate::chart::Register;
        let kin = deposit_all(&[term(3, 4, WindingQuantum::ThisWay)]);
        let axis = 4i64;
        let mut standing = std::vec![0u32; (axis * axis) as usize * FORM_WORDS];
        // four identical kin structures scattered across one section block (grips 0,1,4,5)
        for grip in [0usize, 1, 4, 5] {
            kin.pack(&mut standing, grip * FORM_WORDS);
        }
        // one distinct structure elsewhere — it must survive untouched
        let lone = deposit_all(&[term(7, -2, WindingQuantum::None)]);
        lone.pack(&mut standing, 10 * FORM_WORDS);
        let register = Register {
            axis: axis as u32,
            occupancy: 5,
        };
        let (axis1, reg1, settled, retired) = settle_standing(&mut standing, axis, register);
        assert_eq!(
            settled, 3,
            "four identical kin settle to one — three depart"
        );
        assert_eq!(
            reg1.occupancy, 2,
            "the register's occupancy is the settled count"
        );
        let settled_form = RegionalForm::unpack(&standing, 0);
        assert_eq!(
            settled_form,
            integrate(&[kin, kin, kin, kin]).occupy(),
            "the settled structure is the one configuration fold of the k encounters"
        );
        let (tw, _) = settled_form.fiber();
        assert_eq!(
            tw.face(),
            Some(4),
            "fibers add — winding is never un-deposited"
        );
        for grip in [1usize, 4, 5] {
            assert!(
                !RegionalForm::unpack(
                    &standing,
                    grip * FORM_WORDS * (axis1 as usize * axis1 as usize >= grip + 1) as usize
                )
                .occupied()
                    || axis1 < 4,
                "vacated cells stand empty"
            );
        }
        assert!(
            RegionalForm::unpack(&standing, {
                // the lone survivor transported to the current gauge
                let mut grip = 10u32;
                let mut a = 4u32;
                while a > axis1 as u32 {
                    grip = crate::chart::zero_extended_source(grip, a >> 1, a)
                        .expect("the lone cell sits on the section");
                    a >>= 1;
                }
                grip as usize * FORM_WORDS
            })
            .occupied(),
            "the distinct structure survives the settling whole"
        );
        let _ = retired;
        // IDEMPOTENCE — the same measurement read twice is the same body
        let snapshot = standing[..(axis1 * axis1) as usize * FORM_WORDS].to_vec();
        let (axis2, reg2, settled2, retired2) = settle_standing(&mut standing, axis1, reg1);
        assert_eq!(axis2, axis1);
        assert_eq!(reg2, reg1);
        assert_eq!(settled2, 0, "a settled body settles to itself");
        assert_eq!(retired2, 0);
        assert_eq!(
            &standing[..(axis2 * axis2) as usize * FORM_WORDS],
            snapshot.as_slice(),
            "byte-identical — the settling is a measurement, never a trigger"
        );
    }

    /// §XXXIV gate: the whole drag's curvature face reduces BYTE-EXACTLY to the ratified §XIV
    /// precession rotor when one arm stands alone — and a faceless form (dark: no coherence with
    /// relative differences) still curves the arriving inertia. No switch exists: both faces
    /// read always, by content.
    #[test]
    fn the_whole_drag_reads_curvature_and_reduces_to_the_precession() {
        use crate::manifold::{face, wind, StandingWinding};
        let meeting = face(
            wind(b"the arriving inertia"),
            wind(b"its pole"),
            wind(b"its frame"),
        );
        // a dark form: resultant exactly cancelled, one standing arm — pure curvature
        let dark = deposit_all(&[
            term(5, 7, WindingQuantum::ThisWay),
            term(-5, -7, WindingQuantum::None),
        ]);
        let (ds, do_) = dark.resultant();
        assert_eq!((ds.mag, do_.mag), (0, 0), "the resultant cancelled exactly");
        let bent = dark.drag(meeting);
        assert_ne!(
            (bent.arrow.aim, bent.arrow.cross),
            (meeting.arrow.aim, meeting.arrow.cross),
            "a dark place curves the passing inertia — it is not inert"
        );
        // the single-arm reduction: byte-exact to §XIV's dragged_by rotor (1, −w)
        let reduction = meeting.dragged_by(StandingWinding::at_boundary(1));
        assert_eq!(
            (bent.arrow.aim, bent.arrow.cross, bent.arrow.reach),
            (
                reduction.arrow.aim,
                reduction.arrow.cross,
                reduction.arrow.reach
            ),
            "one standing arm IS the ratified precession — the reduction gate"
        );
        // both arms standing: the composed terrain rotor (1+t·a, a−t); symmetric spread bends
        // by its product face while the difference face cancels — the two sides of one boundary
        let spread = deposit_all(&[
            term(5, 7, WindingQuantum::ThisWay),
            term(-5, -7, WindingQuantum::ThatWay),
        ]);
        let spread_bent = spread.drag(meeting);
        assert_ne!(
            (spread_bent.arrow.aim, spread_bent.arrow.cross),
            (meeting.arrow.aim, meeting.arrow.cross),
            "an opposed spread still holds curvature — the boundary's two sides"
        );
    }

    /// FIBER-R0 F2 (declared `RESEARCH/2026-07-10_FIBER-R0.md`): HAND-EXCHANGE IS CONJUGATION.
    /// Exchanging the two arms' hands conjugates the fiber rotor — `re = 1 + t·a` is symmetric,
    /// `im = a − t` flips sign — read as exact face relations, never by re-implementing the
    /// branch: the two drags' aim-sum and cross-sum carry only the scalar face (the turned face
    /// cancels), and their differences carry only the turned face (the scalar cancels). The pair
    /// holds no preferred arm; the hand of the read is the reader's — the fiber's palindrome.
    #[test]
    fn the_fiber_conjugates_under_hand_exchange() {
        let m = meeting(3, 4);
        // arms (2,1) and (1,2), resultants exactly cancelled — the fiber face isolated.
        let forward = deposit_all(&[
            term(1, 2, WindingQuantum::ThisWay),
            term(4, -1, WindingQuantum::ThisWay),
            term(-5, -1, WindingQuantum::ThatWay),
        ]);
        let exchanged = deposit_all(&[
            term(1, 2, WindingQuantum::ThatWay),
            term(4, -1, WindingQuantum::ThatWay),
            term(-5, -1, WindingQuantum::ThisWay),
        ]);
        assert_eq!(
            (forward.resultant().0.mag, forward.resultant().1.mag),
            (0, 0)
        );
        assert_eq!(
            (forward.fiber().0.face(), forward.fiber().1.face()),
            (Some(2), Some(1))
        );
        assert_eq!(
            (exchanged.fiber().0.face(), exchanged.fiber().1.face()),
            (Some(1), Some(2))
        );
        let f = forward.drag(m);
        let x = exchanged.drag(m);
        // scalar face only: aim_f + aim_x = 2·re·aim and cross_f + cross_x = 2·re·cross (re = 3)
        assert_eq!(
            f.arrow.aim.add(x.arrow.aim).face(),
            m.arrow.aim.mul(Cog::lit(6)).face(),
            "the aim-sum carries only the symmetric scalar face"
        );
        assert_eq!(
            f.arrow.cross.add(x.arrow.cross).face(),
            m.arrow.cross.mul(Cog::lit(6)).face(),
            "the cross-sum carries only the symmetric scalar face"
        );
        // turned face only: aim_f − aim_x = 2·cross and cross_x − cross_f = 2·aim (im = ∓1)
        assert_eq!(
            f.arrow.aim.sub(x.arrow.aim).face(),
            m.arrow.cross.mul(Cog::lit(2)).face(),
            "the aim-difference is the turned face — sign-flipped by the exchange"
        );
        assert_eq!(
            x.arrow.cross.sub(f.arrow.cross).face(),
            m.arrow.aim.mul(Cog::lit(2)).face(),
            "the cross-difference is the turned face — conjugation exact"
        );
    }

    /// FIBER-R0 F3 (declared `RESEARCH/2026-07-10_FIBER-R0.md`): THE SYMMETRIC FACE IS AIM-NULL.
    /// Equal arms compose to `(1 + t², 0)` — a pure positive scalar: common projective scale,
    /// no aim bend. The direction crosses unchanged, a pure-aim meeting stays pure-aim, and
    /// reach is untouched. The machine's NEUTRAL FORM (`§XXXVI`): mass without alignment —
    /// deepening without deflecting.
    #[test]
    fn the_symmetric_fiber_is_aim_null() {
        // arms (2,2), resultant exactly cancelled: the neutral form.
        let neutral = deposit_all(&[
            term(1, 2, WindingQuantum::ThisWay),
            term(4, -1, WindingQuantum::ThisWay),
            term(-2, -3, WindingQuantum::ThatWay),
            term(-3, 2, WindingQuantum::ThatWay),
        ]);
        assert_eq!(
            (neutral.resultant().0.mag, neutral.resultant().1.mag),
            (0, 0)
        );
        assert_eq!(
            (neutral.fiber().0.face(), neutral.fiber().1.face()),
            (Some(2), Some(2))
        );
        let m = meeting(3, 4);
        let bent = neutral.drag(m);
        // the direction is untouched exactly: cross'·aim = aim'·cross (the projective identity)
        assert_eq!(
            bent.arrow.cross.mul(m.arrow.aim).face(),
            bent.arrow.aim.mul(m.arrow.cross).face(),
            "no aim bend — the direction crosses the neutral form unchanged"
        );
        // the whole action is the scalar face: 1 + t·a = 5 at arms (2,2)
        assert_eq!(bent.arrow.aim.face(), m.arrow.aim.mul(Cog::lit(5)).face());
        assert_eq!(
            bent.arrow.cross.face(),
            m.arrow.cross.mul(Cog::lit(5)).face()
        );
        // a pure-aim meeting stays pure-aim: the neutral form deflects nothing in-plane
        let pure = meeting(3, 0);
        let pure_bent = neutral.drag(pure);
        assert_eq!(
            pure_bent.arrow.cross.mag, 0,
            "no cross appears from a neutral fiber"
        );
        assert_eq!(
            pure_bent.arrow.reach, pure.arrow.reach,
            "reach is never the drag's to touch"
        );
    }
}
