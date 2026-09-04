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

/// ★ THE CAUSAL CLASS — which face of the relating dominates, read as a cone rather than a
/// threshold. `aim` is what STANDS (the cohere; the stored face) and `cross` is what FLOWS (the
/// gyration; the transported face), so `W⁻² − W⁺²` is an indefinite form of signature (1,1) and its
/// sign is a causal character. Formal names, for the record and never as the label: timelike, null,
/// spacelike.
///
/// **THE FORM HAS AN EXACT RATIONAL OWNER OUTSIDE THIS CRATE.** `holonic-engine`'s
/// `model_surface::ExactReading::HarmonicReal` computes `re² − im²`, which for `z = aim + i·cross`
/// is `Re(z²) = aim² − cross²` — this form with the hand reversed — so `founds()` is
/// `HarmonicReal ≤ 0` and the three classes below are its three signs. `crates/holonic-body` has zero
/// dependencies and does not import it; the correspondence is carried by `model_surface`'s test
/// `the_harmonic_real_is_the_arrows_founding_form`, which re-derives `(aim, cross)` from this
/// module's own four declared points over `Rat`.
///
/// **The causal class is `sense()` composed with squaring** — squaring doubles the phase, which is
/// why this wall sits at a quarter turn while the scalar's sign flips at a half.
///
/// **But it is STRICTLY SHARPER than any single reading off `z²`, and that boundary is the point:**
/// squaring sends the whole wall to zero along with the origin, so `Re(z²) = 0` cannot tell
/// `Balanced` from `Unread`. Only `at_horizon()`, which reads the **pair** rather than the square,
/// separates the honest point `[0:1]` from the non-point `[0:0]`.
///
/// **INSIDE THE CONE** (`|cross| > |aim|`, *timelike*) — transport dominates storage; this is the
/// FOUND band. **ON THE CONE** (`|cross| = |aim|`, *null*) — the wall, at a quarter of the half
/// turn. **OUTSIDE THE CONE** (`|cross| < |aim|`, *spacelike*) — storage dominates; the RIDE band.
/// **UNREAD** — the relating is behind this pole's own horizon and has no causal character at all;
/// it is the non-point of the projective line, never a class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Causal {
    TransportDominant,
    Balanced,
    StorageDominant,
    Unread,
}

/// ★ WHY A RELATING READ NOTHING — the distinction the Information Chemistry vocabulary requires and
/// which no reader in this tree has ever made. Its own definition of ANNIHILATION is *"opposed
/// contributions in one declared fiber actually compose to zero"*, and adds that *"a flat, inactive,
/// equal, absent, or **uncontacted** relation is not thereby annihilated."*
///
/// The two are not interchangeable and they carry opposite evidence. Stationary phase REQUIRES a
/// large annihilating population — that is how non-surviving paths are removed without any chooser.
/// An uncontacted population says the opposite: nothing was ever put into the sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NullSpecies {
    /// Both arms stand and their contributions actually cancelled. This is a real event.
    Annihilated,
    /// A strand stands at the pole, so one arm is null. Nothing was contacted, nothing cancelled.
    Uncontacted,
}

/// ★ WHICH SPECIES OF NULL — computable only from the relata, because `Arrow` retains the faces and
/// not the arms. Returns `None` when the relating is not null at all.
#[inline]
pub fn null_species(a: Place, b: Place, f: Place) -> Option<NullSpecies> {
    let arrow = relate(a, b, f);
    if !arrow.at_horizon() {
        return None;
    }
    let alpha_null = a.0.sub(f.0).mag == 0 && a.1.sub(f.1).mag == 0;
    let beta_null = b.0.sub(f.0).mag == 0 && b.1.sub(f.1).mag == 0;
    if alpha_null || beta_null {
        Some(NullSpecies::Uncontacted)
    } else {
        Some(NullSpecies::Annihilated)
    }
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

    /// ★ THE CAUSAL CLASS of a relating — the three-way species `founds()` collapses into a bool.
    ///
    /// `founds()` tests `W⁻² − W⁺² ≥ 0`, which is an **indefinite form of signature (1,1)** on the
    /// `(aim, cross)` plane with the cross timelike. That is a causal classification and always was:
    /// the founding band is a CONE, not a threshold, and its wall sits at `|cross| = |aim|` — the
    /// quarter-of-a-half-turn locus, `c = 1` in the plane's own units.
    ///
    /// Note this reading is strictly sharper than `founds()`, which returns `true` on a horizon
    /// arrow because `ZERO − ZERO` carries no half-turn. `Unread` separates the non-point `[0:0]`
    /// from the honest point `[0:1]`; `founds()` cannot.
    #[inline]
    pub fn causal_class(&self) -> Causal {
        if self.at_horizon() {
            return Causal::Unread;
        }
        let wp2 = self.aim.mul(self.aim); // W⁺² — the cohere, the STORED face
        let wm2 = self.cross.mul(self.cross); // W⁻² — the gyration, the TRANSPORTED face
        let difference = wm2.sub(wp2);
        if difference.mag == 0 {
            Causal::Balanced
        } else if difference.turn & 2 == 0 {
            Causal::TransportDominant
        } else {
            Causal::StorageDominant
        }
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

    /// CONSTRUCTION 1 — the causal class must be a species and must not be vacuous. A reading that
    /// only ever returns one class has classified nothing, so all three classes plus the horizon are
    /// exhibited here on declared material, and the cone wall is shown to be reachable exactly.
    #[test]
    fn the_founding_band_is_a_cone_and_all_three_classes_are_reachable() {
        // |cross| > |aim|: orthogonal from the pole -- transport dominates.
        let inside = relate(p(1, 0), p(0, 1), p(0, 0));
        assert_eq!(inside.causal_class(), Causal::TransportDominant);
        assert_eq!(inside.sense(), Aim::Ortho);
        // |cross| = |aim|: the wall. (2,0) and (1,1) from the origin -> aim 2, cross 2.
        let wall = relate(p(2, 0), p(1, 1), p(0, 0));
        assert_eq!(wall.aim.mag_face(), 2);
        assert_eq!(wall.cross.mag_face(), 2);
        assert_eq!(wall.causal_class(), Causal::Balanced);
        // |cross| < |aim|: collinear from the pole -- storage dominates, nothing founds.
        let outside = relate(p(2, 0), p(3, 0), p(0, 0));
        assert_eq!(outside.causal_class(), Causal::StorageDominant);
        assert!(!outside.founds());
        // the horizon is NOT a class: a strand stands at the pole.
        let horizon = relate(p(1, 0), p(0, 1), p(1, 0));
        assert!(horizon.at_horizon());
        assert_eq!(horizon.causal_class(), Causal::Unread);
        // and this is strictly sharper than `founds()`, which cannot separate the two.
        assert!(
            horizon.founds(),
            "founds() returns true on a horizon arrow; causal_class does not, which is the point"
        );
    }

    /// CONSTRUCTION 3 — annihilation and non-contact are different events and the vocabulary forbids
    /// reading one as the other. Both must be exhibited, or the census cannot separate them.
    #[test]
    fn a_null_relating_is_annihilated_or_uncontacted_and_they_are_not_the_same_event() {
        // UNCONTACTED: a strand stands at the pole, so one arm is null. Nothing cancelled.
        let uncontacted = null_species(p(4, 0), p(6, 0), p(4, 0));
        assert_eq!(uncontacted, Some(NullSpecies::Uncontacted));
        // ANNIHILATED: both arms stand, and the faces actually cancel. From the origin, a = (1,1)
        // and b = (1,-1): aim = 1-1 = 0, cross = 1*1 - 1*(-1)... exhibited rather than asserted.
        let a = p(1, 1);
        let b = p(1, -1);
        let f = p(0, 0);
        let arr = relate(a, b, f);
        assert_eq!(
            arr.aim.mag, 0,
            "the cohere face cancelled from two standing arms"
        );
        // Not at horizon: the gyration survives, so this is ORTHO and not a null relating at all.
        assert!(!arr.at_horizon());
        assert_eq!(arr.sense(), Aim::Ortho);
        assert_eq!(
            null_species(a, b, f),
            None,
            "not null: only one face cancelled"
        );
        // A relating is annihilated only when BOTH faces cancel from standing arms.
        assert_eq!(
            null_species(p(2, 0), p(2, 0), p(0, 0)),
            None,
            "a same-place recurrence reads pure-Same, never null"
        );
    }

    /// THE GAUGE ORBIT. The pole enters by RE-BASE, never by projection, so the receiver acts on
    /// construction space by the affine group `z -> p z + q`. Its invariants on three points are
    /// the ratio and the predicates built from it; every magnitude the arrow carries is a receiver
    /// coordinate. Both arms are required: the hand and the founding must be UNMOVED and at least
    /// one magnitude must MOVE, because a gauge whose group acts trivially on the declared material
    /// has gauged nothing and agreement through it is not evidence.
    fn affine(z: Place, scale: Place, shift: Place) -> Place {
        // (x + iy)(u + iv) + (s + it) -- the complex product, then the translation.
        let re = z.0.mul(scale.0).sub(z.1.mul(scale.1)).add(shift.0);
        let im = z.0.mul(scale.1).add(z.1.mul(scale.0)).add(shift.1);
        (re, im)
    }

    #[test]
    fn the_hand_and_the_founding_survive_the_affine_gauge_while_the_magnitudes_move() {
        // scale = 1 + i, so |p|^2 = 2 and every magnitude must double; shift = 3 - 2i.
        let scale = p(1, 1);
        let shift = p(3, -2);
        // Declared material: one cohere, one anti, one ortho, one at the pole's own horizon.
        let material = [
            (p(2, 0), p(3, 0), p(0, 0)),
            (p(4, 0), p(6, 0), p(5, 0)),
            (p(1, 0), p(0, 1), p(0, 0)),
            (p(1, 0), p(0, 1), p(1, 0)),
        ];
        let mut a_magnitude_moved = false;
        for (a, b, f) in material {
            let here = relate(a, b, f);
            let there = relate(
                affine(a, scale, shift),
                affine(b, scale, shift),
                affine(f, scale, shift),
            );
            assert_eq!(
                here.sense(),
                there.sense(),
                "the hand is an affine invariant"
            );
            assert_eq!(
                here.founds(),
                there.founds(),
                "the founding band is an affine invariant"
            );
            assert_eq!(
                here.at_horizon(),
                there.at_horizon(),
                "the horizon is an affine invariant"
            );
            // |p|^2 = 2, so each magnitude doubles exactly. This is the anti-vacuity arm.
            assert_eq!(there.aim.mag_face(), here.aim.mag_face() * 2);
            assert_eq!(there.cross.mag_face(), here.cross.mag_face() * 2);
            assert_eq!(there.reach.mag_face(), here.reach.mag_face() * 2);
            if here.reach.mag_face() != 0 {
                a_magnitude_moved = true;
            }
        }
        assert!(
            a_magnitude_moved,
            "the gauge must act non-trivially on the declared material, or agreement is not evidence"
        );
    }
}
