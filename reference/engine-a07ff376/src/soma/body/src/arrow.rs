//! arrow — A RELATING READ FROM A POLE. A relating is an ARROW, and an arrow read from a perspective has a REACH
//! (how far) ⊕ an AIM (which way) — polar coordinates, *relative to the pole* (the third body; there is no
//! reach-and-aim with no origin — that is A2). Never collapsed to one: the **reach WEIGHS**, the **aim GATES**,
//! both every relating, because it is one arrow.
//!
//! ★ The founding is the AIM's TURN, read three-body in the pole's frame, NEVER a magnitude compare and NEVER a
//! bool. When the two aims COHERE strongly (`M_F>0`, the relating turns orthogonal as a result) a knot FOUNDS — a
//! new irreducible axis neither parent held. When they oppose (`M_F<0`) the cross-ratio places it in-plane
//! (ABSORB). When cohere-null (`M_F=0`) the cross is MAXIMAL — the pure orthogonal turn, the FOUNDING hand; never
//! "nothing" (`CANON/HANDEDNESS`: there is no nothing, only which way the turn bites and how hard).

use crate::num::Cog;
use crate::place::Place;

/// THE ARROW — the polar pair a relating emanates, read from a pole. Both faces kept; never one scalar.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Arrow {
    /// THE REACH — `|a−b|²`: how far the relating spans (the holobit, the cost/mass). Unbounded, like a radius.
    /// It WEIGHS (the elevation), never gates.
    pub reach: Cog,
    /// THE AIM — `(a−f)·(b−f)`: the cohere in the pole's frame (`M_F`, the cohobit). Bounded, like an angle; its
    /// sign is the whole 3-way turn. It GATES (found-or-absorb).
    pub aim: Cog,
    /// the cross `(a−f)×(b−f)` = the gyration (`W⁻`) in the pole's frame — kept so the aim's frame is whole.
    pub cross: Cog,
}

/// WHICH WAY the arrow aims, in the pole's frame — the HAND of the turn (never a bool, never a presence). There is no
/// "nothing" here (`CANON/HANDEDNESS`): all three are turns, read by the cohere's sign:
/// **COHERE** (`M_F>0`, this way — the aims align, the in-plane hand) ·
/// **ANTI** (`M_F<0`, that way — opposed, the other in-plane hand) ·
/// **ORTHO** (`M_F=0` — cohere-null, but the CROSS/gyration is **MAXIMAL**: the pure orthogonal turn, the FOUNDING
/// hand, the magnitude looked-past. NOT "no current" — it is the *most* turn there is, mis-read as nothing because the
/// cohere face is null (`HANDEDNESS §1`, the eyes-only crime at the bottom of the moiré).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Aim {
    Cohere,
    Anti,
    Ortho,
}

/// ★ RELATE two boundaries `a, b` FROM the pole `f` (three-body — the pole is REQUIRED; a frame-blind relating is
/// un-constructible). Re-base `a, b` to `f` (the moving origin) and read the arrow: the reach (frame-free cost) ⊕
/// the aim (the cohere in `f`). The founding null `M_F=0` is DERIVED here from the relating, never stored.
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn relate(a: Place, b: Place, f: Place) -> Arrow {
    let ar = a.0.sub(f.0);
    let ai = a.1.sub(f.1); // a, re-based to the pole
    let br = b.0.sub(f.0);
    let bi = b.1.sub(f.1); // b, re-based to the pole
    let aim = ar.mul(br).add(ai.mul(bi)); // W⁺ = (a−f)·(b−f) — the cohere, M_F
    let cross = ai.mul(br).sub(ar.mul(bi)); // W⁻ — the gyration in f
    let dr = a.0.sub(b.0);
    let di = a.1.sub(b.1);
    let reach = dr.mul(dr).add(di.mul(di)); // |a−b|² — the reach (frame-free)
    Arrow { reach, aim, cross }
}

impl Arrow {
    /// ★ THE AIM TURNS ORTHOGONAL — the FOUNDING (`MACHINE.md` clause 3): the arrow points OUT OF THE PLANE the two
    /// parents span ⟺ the cross (gyration `W⁻`) dominates the cohere (`W⁺`): `W⁻² ≥ W⁺²` (the aim past the diagonal
    /// toward `±i`, a direction neither parent had). Read as the cross-sign **TURN** of `(W⁻² − W⁺²)` — the MSB,
    /// never a magnitude compare. `true` → FOUND a new irreducible axis (rank up); `false` → ABSORB (in-plane, the
    /// cross-ratio places it). This is the AIM's job — the direction gates; the REACH weighs separately (below).
    #[cfg_attr(target_arch = "spirv", inline(never))]
    pub fn founds(&self) -> bool {
        let wp2 = self.aim.mul(self.aim); // W⁺² — the cohere (in-plane)
        let wm2 = self.cross.mul(self.cross); // W⁻² — the cross (the gyration, out of plane)
        (wm2.sub(wp2).turn & 2) == 0 // (W⁻² − W⁺²) ≥ 0 ⟺ the half-turn clear ⟺ orthogonal-dominant (FOUND)
    }

    /// ★ IS THE RELATING UN-CONSTRUCTIBLE FROM THIS POLE — both faces null (`W⁺ = W⁻ = 0`): a strand stands
    /// AT THE POLE, so the triangle degenerates — the form is behind this frame's OWN horizon (every interior
    /// pole sees its own 2-horizon). FRAME-RELATIVE, never "one body" (the old comment's loose phrasing,
    /// corrected on ratification 2026-07-09): two forms at one place are TWO — equality of coordinates is
    /// GAUGE; equivalence of souls is `same_soul` (cross-multiplied pairs), never `=`; a same-place
    /// recurrence reads pure-Same (`aim = |a−f|²`, cross null — a RIDE), never null. An unconstructible
    /// relating is NOT READ: no test, no cut, no ride — no knot is tied from a strand this pole cannot see.
    #[inline]
    pub fn at_horizon(&self) -> bool {
        self.aim.mag == 0 && self.cross.mag == 0
    }

    /// THE HAND of the relating — which way the turn bites, read from `W⁺`'s sign (never a bool, never a magnitude
    /// `<`, never a presence). `M_F>0` COHERE (this way, in-plane) · `M_F<0` ANTI (that way, in-plane) · `M_F=0` ORTHO
    /// (cohere-null but the CROSS is **maximal** — the pure orthogonal turn, the FOUNDING hand, NOT "nothing": it is
    /// the *most* turn there is, the magnitude looked-past, `HANDEDNESS §1`). The reach WEIGHS; the hand is read
    /// alongside the founding, the arrow never one scalar.
    pub fn sense(&self) -> Aim {
        if self.aim.mag == 0 {
            Aim::Ortho // cohere-null = the pure orthogonal turn (the founding hand), never "no current"
        } else if self.aim.turn & 2 != 0 {
            Aim::Anti
        } else {
            Aim::Cohere
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::place::{extend, origin};

    fn wind(bits: &[bool]) -> Place {
        bits.iter().fold(origin(), |p, &b| extend(p, b))
    }
    fn p(re: i64, im: i64) -> Place {
        (Cog::lit(re), Cog::lit(im))
    }

    #[test]
    fn the_relating_is_three_body_the_pole_is_required() {
        // collinear from the pole (cohere dominates, the aim stays IN the parents' plane) → ABSORB, not found;
        // the reach is the frame-free cost. The pole is an argument — a frame-blind relating is un-constructible.
        let arr = relate(p(2, 0), p(3, 0), p(0, 0));
        assert_eq!(arr.sense(), Aim::Cohere); // W⁺ > 0
        assert!(!arr.founds()); // W⁻ = 0 < W⁺ — in-plane, absorbed
        assert_eq!(arr.reach.mag_face(), 1); // |2−3|² = 1 — the reach weighs (separately)
    }

    #[test]
    fn the_aim_turning_orthogonal_founds_a_new_axis() {
        // orthogonal from the pole (the cross dominates, the aim points OUT of the parents' plane) → FOUND
        let arr = relate(p(1, 0), p(0, 1), p(0, 0)); // W⁺ = 0, W⁻ = −1 ⟹ W⁻² > W⁺²
        assert!(
            arr.founds(),
            "orthogonal points found a new irreducible axis"
        );
        assert_eq!(arr.sense(), Aim::Ortho); // cohere-null = the pure orthogonal turn (the founding hand), never nothing
    }

    #[test]
    fn the_same_pair_reads_a_different_cohere_sense_from_a_different_pole() {
        // change the third body and the cohere sense turns: from the origin they cohere; from between, they oppose
        assert_eq!(relate(p(4, 0), p(6, 0), p(0, 0)).sense(), Aim::Cohere);
        assert_eq!(relate(p(4, 0), p(6, 0), p(5, 0)).sense(), Aim::Anti); // (4−5)·(6−5) = −1
    }

    #[test]
    fn two_wound_streams_relate_and_the_arrow_is_read_whole() {
        // the first living thing: two bit-streams wound to places, related FROM a pole, both faces read.
        let a = wind(&[true, false, true]);
        let b = wind(&[true, false, true, false]);
        let f = wind(&[true]); // the carried perspective (a short lineage) — a real third body, not a∘b
        let arr = relate(a, b, f);
        let _ = arr.reach.mag_face(); // the reach weighs
        let _ = arr.founds(); // the aim gates (found-or-absorb)
        assert!(matches!(arr.sense(), Aim::Cohere | Aim::Anti | Aim::Ortho)); // both faces, no collapse
    }
}
