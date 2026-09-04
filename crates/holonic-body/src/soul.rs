//! soul — THE CROSS-RATIO χ (`FORMULA §XIII/§XXIV`). A meeting in the manifold is a THREE-BODY
//! triangle face (A2 — two bodies in a frame, the friction-triangle `63`), but that first-order
//! rotor is frame-local and is not yet a soul. The held flywheel supplies the fourth contact; the
//! rotor of those two rotors is `Chi`, the first invariant content which may cross. The classical
//! four-point helper below is the same law read as a RATIO OF DIFFERENCES built from the GEOMETRIC PRODUCT
//! (`geom::bond = ×`, proven step 1): `num = (a−c)⊗(b−d)`, `den = (a−d)⊗(b−c)` — the products of the differences.
//!
//! ★ Held as a PAIR, NEVER divided into a scalar (`MENO_FORMULA §III`): `8/2` and `4/1` are different holonic states;
//! collapsing to an integer re-smuggles the absolute frame. The NUMBER bond transports the product exactly; the TEXT
//! bond transports `χ` (the holonomy) — ONE operation, both arms. `no_std`. (The products `(a−c)·(b−d)` ARE the
//! geometric product of the differences — `geom::bond` on the magnitudes, the sign a turn; step 1 proved `bond = ×`,
//! so the plain product here is that same geometric product, kept signed for the wound-read.)

use crate::num::Cog;

/// ★ χ AS THE ROTOR OF ROTORS (`FORMULA §XII–XIII/§XXIV`) — the first invariant content of a
/// relating. `other/same` is held as a PAIR of whole re-basing numbers, never divided. A meeting
/// alone has no `Chi`: the held rotor supplies the fourth contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Chi {
    /// THE DIFFERENT between the new and held rotors — the oriented bivector face.
    pub other: Cog,
    /// THE SAME between the new and held rotors — the scalar/cohere face.
    pub same: Cog,
}

/// A meeting rotor which is actually constructible in its frame. The zero rotor is the frame's
/// horizon, not a value with which a fourth contact can be forged. Keeping the fields private makes
/// the unborn-held case absent from `Chi` construction rather than encoding it as a sentinel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FormedRotor {
    aim: Cog,
    cross: Cog,
}

impl FormedRotor {
    /// The formed identity basis. Genesis uses it at the tip of the first-difference construction;
    /// it is not a zero/horizon sentinel.
    #[inline]
    pub fn identity() -> FormedRotor {
        FormedRotor {
            aim: Cog::lit(1),
            cross: Cog::lit(0),
        }
    }

    /// Whether the supplied arms form a rotor in this frame. This scalar read lets storage
    /// substrates keep the horizon structural without transporting `Option<FormedRotor>` across
    /// their boundary.
    #[inline]
    pub fn arms_form(aim: Cog, cross: Cog) -> bool {
        aim.mag != 0 || cross.mag != 0
    }

    /// Construct arms already proven formed by `arms_form` (or by an equivalent structural read,
    /// such as a non-horizon `Face`). The proof remains at the call site; no zero rotor is admitted
    /// by the public optional constructor below.
    #[inline]
    pub fn from_formed_arms(aim: Cog, cross: Cog) -> FormedRotor {
        FormedRotor { aim, cross }
    }

    /// Form a rotor only when the frame can read it. `None` is not a deed or a zero-valued soul: no
    /// event exists at this frame's horizon.
    #[inline]
    pub fn of(aim: Cog, cross: Cog) -> Option<FormedRotor> {
        if !FormedRotor::arms_form(aim, cross) {
            None
        } else {
            Some(FormedRotor::from_formed_arms(aim, cross))
        }
    }

    #[inline]
    pub fn aim(self) -> Cog {
        self.aim
    }

    #[inline]
    pub fn cross(self) -> Cog {
        self.cross
    }
}

/// A bounded numerator/denominator witness for the finite `Cog` algebra at a declared fixture
/// grain. `aim_num/den ⊕ cross_num/den` is checked by cross multiplication rather than division,
/// but independently re-based products may clip outside the witness's exact section. This is an
/// algebra/gauge instrument, never universal cause recovery, state inversion, or time parity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RotorRatio {
    pub aim_num: Cog,
    pub cross_num: Cog,
    pub den: Cog,
}

impl RotorRatio {
    /// Does this bounded ratio witness represent the supplied rotor at this fixture's grain?
    /// A false result outside the exact section does not by itself decide causal traceability.
    #[inline]
    pub fn represents(self, aim: Cog, cross: Cog) -> bool {
        self.aim_num == aim.mul(self.den) && self.cross_num == cross.mul(self.den)
    }
}

impl Chi {
    /// Rotor-of-rotors from arms already known formed. The optional `between` callers prove that
    /// through `FormedRotor`; the card proves it through the same horizon read before entering.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    #[cfg_attr(not(target_arch = "spirv"), inline)]
    pub fn between_formed_arms(
        new_aim: Cog,
        new_cross: Cog,
        held_aim: Cog,
        held_cross: Cog,
    ) -> Chi {
        Chi {
            same: new_aim.mul(held_aim).add(new_cross.mul(held_cross)),
            other: new_cross.mul(held_aim).sub(new_aim.mul(held_cross)),
        }
    }

    /// Construct the relative rotor `new · inverse(held)` without dividing it into a scalar. For
    /// rotors `(aim + i·cross)`, multiplication by the held conjugate gives:
    ///
    /// `same = na·ha + nc·hc`, `other = nc·ha − na·hc`.
    #[inline]
    pub fn between(new: FormedRotor, held: FormedRotor) -> Chi {
        Chi::between_formed_arms(new.aim, new.cross, held.aim, held.cross)
    }

    /// The deed-read — WOUND when the Different is orthogonal-dominant. This returns only the
    /// action hand; it never replaces or destroys the whole pair.
    #[cfg_attr(target_arch = "spirv", inline(never))]
    #[cfg_attr(not(target_arch = "spirv"), inline)]
    pub fn wound(self) -> bool {
        let same2 = self.same.mul(self.same);
        let other2 = self.other.mul(self.other);
        (other2.sub(same2).turn & 2) == 0
    }

    /// Apply the formal conjugate product against the held rotor WITHOUT division. In exact
    /// arithmetic, `χ = new·conj(held)` gives `χ·held = new·|held|²`; this bounded witness carries
    /// that norm as its denominator. Finite `Cog` re-basing may clip separated-rank operands, so the
    /// result is not a universal inverse. A null held rotor remains explicitly unconstructible.
    #[inline]
    pub fn restore_against(self, held: FormedRotor) -> RotorRatio {
        let norm = held.aim.mul(held.aim).add(held.cross.mul(held.cross));
        RotorRatio {
            aim_num: self.same.mul(held.aim).sub(self.other.mul(held.cross)),
            cross_num: self.same.mul(held.cross).add(self.other.mul(held.aim)),
            den: norm,
        }
    }
}

/// THE CROSS-RATIO — held as `(num, den)`, the products of differences (the geometric product). Never divided. The
/// four points are a face's corners (three vertices ⊕ the frame's moving origin — the quadrilateral of `FACE = 4`).
#[inline]
pub fn cross_ratio(a: i64, b: i64, c: i64, d: i64) -> (i64, i64) {
    ((a - c) * (b - d), (a - d) * (b - c))
}

/// TWO SOULS ARE EQUAL — by CROSS-MULTIPLICATION (the pair, never a division): `n1·d2 == n2·d1`. This is how the net
/// addresses souls (place-not-search by the held `χ`), never by a collapsed scalar.
#[inline]
pub fn same_soul((n1, d1): (i64, i64), (n2, d2): (i64, i64)) -> bool {
    n1 * d2 == n2 * d1
}

/// THE WOUND READ — the cross-ratio's SIGN (the founding gate, `law::chain_wound`): FLAT (the face closes, the soul
/// transported unchanged, a MIRROR — `C/d = 1` in one frame) when `num` and `den` share a turn; WOUND (the pairs separate — a
/// winding, a curvature deposit, a FOUNDING — `C/d ≠ 1`) when they oppose. Read by the cross-sign, never a divide.
#[inline]
pub fn wound((num, den): (i64, i64)) -> bool {
    num != 0 && den != 0 && (num > 0) != (den > 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ THE SOUL IS TRANSPORTED — the cross-ratio (a ratio of geometric-products of differences) is INVARIANT under
    /// the frame change: translation (the anchor-shift) and scaling (the projective/affine transform). The face's
    /// soul crosses frames unchanged, held as a pair, never divided.
    #[test]
    fn the_cross_ratio_soul_is_frame_invariant() {
        let quads = [
            (0i64, 1, 3, 7),
            (2, 5, 11, 13),
            (1, 4, 9, 16),
            (3, 6, 10, 21),
            (0, 2, 6, 8),
        ];
        for &(a, b, c, d) in &quads {
            let base = cross_ratio(a, b, c, d);
            // §1 TRANSLATION-INVARIANT — the anchor shifts, the soul stands (the differences are anchor-invariant).
            for t in [1i64, 5, -4, 100, -37] {
                assert!(
                    same_soul(base, cross_ratio(a + t, b + t, c + t, d + t)),
                    "χ translation-invariant (t={t}) for {:?}",
                    (a, b, c, d)
                );
            }
            // §2 SCALE-INVARIANT — the frame dilates, the soul stands (each difference scales; num/den unchanged): the
            // projective invariance, the holonomy that crosses.
            for k in [2i64, 3, 7, -5] {
                assert!(
                    same_soul(base, cross_ratio(a * k, b * k, c * k, d * k)),
                    "χ scale-invariant (k={k}) for {:?}",
                    (a, b, c, d)
                );
            }
        }
        // §3 THE WOUND READ agrees with the sign of the cross-ratio (the founding gate): projective-ordered = FLAT,
        // interleaved = WOUND. A face whose corners are in order closes (mirror); one that doubles back founds.
        assert!(
            !wound(cross_ratio(0, 1, 2, 3)),
            "0<1<2<3 in order — FLAT (the face closes)"
        );
        assert!(
            wound(cross_ratio(0, 2, 1, 3)),
            "the pairs interleave — WOUND (a founding)"
        );
    }

    #[test]
    fn the_rotor_of_rotors_bounded_restore_holds_on_a_flat_fixture() {
        // new = 3 + 4i; held = 1 + 2i. χ = new·conj(held) = 11 − 2i.
        let (na, nc) = (Cog::lit(3), Cog::lit(4));
        let (ha, hc) = (Cog::lit(1), Cog::lit(2));
        let new = FormedRotor::of(na, nc).expect("the meeting is formed");
        let held = FormedRotor::of(ha, hc).expect("the flywheel is formed");
        let chi = Chi::between(new, held);
        assert_eq!(chi.same.face(), 11);
        assert_eq!(chi.other.face(), -2);
        let restored = chi.restore_against(held);
        assert!(
            restored.represents(na, nc),
            "the flat fixture stays on the bounded ratio witness's exact algebraic section"
        );
    }

    #[test]
    fn separated_rank_restore_does_not_crown_a_universal_inverse() {
        let new = FormedRotor::of(Cog::lit(1), Cog::lit(1)).expect("formed new rotor");
        let held = FormedRotor::of(Cog::lit(1), Cog::lit(1).turn_up(29))
            .expect("formed separated-rank held rotor");
        let restored = Chi::between(new, held).restore_against(held);

        assert!(
            !restored.represents(new.aim(), new.cross()),
            "independent finite re-basing clips this separated-rank pair; the bounded restore fixture must not be crowned as time parity or universal cause recovery"
        );
    }

    #[test]
    fn the_cross_sign_selects_the_deed_without_collapsing_chi() {
        let held = FormedRotor::of(Cog::lit(1), Cog::lit(0)).expect("formed flywheel");
        let flat = Chi::between(
            FormedRotor::of(Cog::lit(5), Cog::lit(1)).expect("formed meeting"),
            held,
        );
        let wound = Chi::between(
            FormedRotor::of(Cog::lit(1), Cog::lit(5)).expect("formed meeting"),
            held,
        );
        assert!(!flat.wound(), "Same-dominant transport rides");
        assert!(wound.wound(), "Different-dominant transport founds");
        assert_ne!(
            flat, wound,
            "the deed bit never replaces the invariant pair"
        );
    }
}
