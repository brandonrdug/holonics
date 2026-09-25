//! **The logarithm of an undivided ratio, carried with its winding.**
//!
//! [definition] The Rust face of `Objects/Ratio.logFibre`: a lift of `log(num : den)` is the pair
//! and the whole turns of the lift, never evaluated; the principal lift of the divided ratio is one
//! of them (`Physics/Fluid/Singularity.principal_mem_logFibre`). Two lifts of one ratio differ by whole turns
//! (`logFibre_torsor`); a zero comparand has no logarithm (`logFibre_eq_empty_of_den_eq_zero`,
//! `logFibre_zero_zero`). The real part is half the base-two log of the quadrance ratio, an exact
//! form over the primes ([`SymbolicSurprisal`]); the imaginary part is the ratio's direction plus
//! the winding in turns.
//!
//! [proved-derived; implemented-exact] **Continuation is path lifting.** Along a polygonal path of
//! the ratio's chart that avoids zero, the lift continues by counting the signed crossings of the
//! principal cut, the negative real axis ([`LogRatio::continued`]): each counterclockwise crossing
//! advances the winding by one turn, each clockwise crossing returns it. Around a closed path the
//! winding advances by the path's winding number about zero, the exact polygonal face of lifting
//! through `exp` (Lean `Physics/Fluid/Body.siteLift`, `siteLift_advance`, `winding`).

use num_traits::{Signed, Zero};

use super::Rat;
use super::exponentiated::exponentiate;
use super::gaussian::{GaussianError, GaussianRat};
use super::surprisal::SymbolicSurprisal;

/// [definition] **A lift of `log(num : den)`**: the undivided pair and the whole turns of the lift
/// above the principal branch `Arg ∈ (−π, π]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogRatio {
    pub numerator: GaussianRat,
    pub denominator: GaussianRat,
    pub winding: i64,
}

impl LogRatio {
    /// A lift of `(num : den)`, refused when either comparand is zero (no logarithm: Lean
    /// `logFibre_eq_empty_of_den_eq_zero`, `logFibre_zero_zero`).
    pub fn new(
        numerator: GaussianRat,
        denominator: GaussianRat,
        winding: i64,
    ) -> Result<Self, GaussianError> {
        if numerator.is_zero() || denominator.is_zero() {
            return Err(GaussianError::ZeroDivisor {
                what: "a comparand of the logarithm's ratio",
            });
        }
        Ok(Self {
            numerator,
            denominator,
            winding,
        })
    }

    /// The fractional chart `num / den`.
    pub fn chart(&self) -> Result<GaussianRat, GaussianError> {
        self.numerator.div(&self.denominator)
    }

    /// `log₂(|num|²/|den|²)`, exactly, as a symbolic form over the primes.
    pub fn modulus_log2(&self) -> Result<SymbolicSurprisal, GaussianError> {
        Ok(SymbolicSurprisal::log2_of_ratio(
            &(self.numerator.norm_sq() / self.denominator.norm_sq()),
        )?)
    }

    /// The quadrance ratio `|num|²/|den|²` back through the chart transition
    /// (`ratio::exponentiated::exponentiate`).
    pub fn modulus(&self) -> Result<Rat, GaussianError> {
        exponentiate(&self.modulus_log2()?).map_err(|_| GaussianError::ModulusNotRational)
    }

    /// The same lift advanced by whole turns.
    pub fn advanced(&self, turns: i64) -> Self {
        Self {
            winding: self.winding + turns,
            ..self.clone()
        }
    }

    /// [proved-derived; implemented-exact] **Two lifts of one ratio differ by whole turns** (Lean
    /// `logFibre_torsor`): the turns from `other` to `self`, or `None` when the ratios differ.
    pub fn turns_from(&self, other: &Self) -> Result<Option<i64>, GaussianError> {
        Ok((self.chart()? == other.chart()?).then_some(self.winding - other.winding))
    }

    /// [proved-derived; implemented-exact] **The lift continued along a polygonal path** of the
    /// chart, from the current chart value through each vertex of `path` in turn: the winding
    /// changes by the signed crossings of the principal cut, and the returned lift sits at the last
    /// vertex over the same denominator. Refused at a segment through zero, where no logarithm
    /// exists. Around a closed path the winding advances by the path's winding number about zero.
    pub fn continued(&self, path: &[GaussianRat]) -> Result<Self, GaussianError> {
        let mut here = self.chart()?;
        let mut winding = self.winding;
        for (segment, next) in path.iter().enumerate() {
            winding += cut_crossing(&here, next).ok_or(GaussianError::ThroughZero { segment })?;
            here = next.clone();
        }
        Self::new(
            here.mul(&self.denominator),
            self.denominator.clone(),
            winding,
        )
    }
}

/// On the principal cut or in the upper half-plane: the closed side of `Arg ∈ (−π, π]` at `π`.
fn upper(w: &GaussianRat) -> bool {
    w.im.is_positive() || (w.im.is_zero() && w.re.is_negative())
}

/// The change of the lift's winding along the segment `a → b`: `+1` for a counterclockwise
/// crossing of the negative real axis, `−1` for a clockwise one, `0` otherwise; `None` when the
/// segment meets zero (`a × b = 0` and `a · b ≤ 0`).
fn cut_crossing(a: &GaussianRat, b: &GaussianRat) -> Option<i64> {
    let cross = &a.re * &b.im - &a.im * &b.re;
    let dot = &a.re * &b.re + &a.im * &b.im;
    if cross.is_zero() && !dot.is_positive() {
        return None;
    }
    // Where the segment meets the real axis, if it crosses it: `x = (a × b)/(Im a − Im b)`.
    let crosses_the_cut = |from: &GaussianRat, to: &GaussianRat| {
        from.im.is_zero() || {
            let x = (&from.re * &to.im - &from.im * &to.re) / (&to.im - &from.im);
            x.is_negative()
        }
    };
    Some(if upper(a) && b.im.is_negative() {
        i64::from(crosses_the_cut(a, b))
    } else if a.im.is_negative() && upper(b) {
        -i64::from(crosses_the_cut(b, a))
    } else {
        0
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn g(re: i64, im: i64) -> GaussianRat {
        GaussianRat::from_i64(re, im)
    }

    /// `Objects/Ratio.logFibre_torsor`: two lifts of one ratio differ by whole turns; a zero
    /// comparand has no logarithm; the modulus is carried as an exact log form and returns through
    /// the chart transition.
    #[test]
    fn two_lifts_of_one_ratio_differ_by_whole_turns() {
        let lift = LogRatio::new(g(3, 1), g(1, -2), 0).unwrap();
        assert_eq!(lift.advanced(3).turns_from(&lift).unwrap(), Some(3));
        let other = LogRatio::new(g(6, 2), g(2, -4), 5).unwrap();
        assert_eq!(other.turns_from(&lift).unwrap(), Some(5));
        let elsewhere = LogRatio::new(g(1, 0), g(1, 0), 0).unwrap();
        assert_eq!(elsewhere.turns_from(&lift).unwrap(), None);
        assert_eq!(lift.modulus().unwrap(), rat(10, 5));
        assert!(LogRatio::new(g(0, 0), g(1, 0), 0).is_err());
    }

    /// Path lifting: around a closed square about zero the lift advances by one turn per
    /// counterclockwise circuit and returns by one per clockwise circuit; a square beside zero
    /// winds nothing; a path through zero is refused.
    #[test]
    fn a_closed_path_advances_the_lift_by_its_winding_number() {
        let start = LogRatio::new(g(1, 0), GaussianRat::one(), 0).unwrap();
        let counterclockwise = [g(1, 1), g(-1, 1), g(-1, -1), g(1, -1), g(1, 0)];
        let once = start.continued(&counterclockwise).unwrap();
        assert_eq!(once.turns_from(&start).unwrap(), Some(1));
        let twice = once.continued(&counterclockwise).unwrap();
        assert_eq!(twice.winding, 2);
        let clockwise: Vec<GaussianRat> = counterclockwise.iter().map(GaussianRat::conj).collect();
        assert_eq!(start.continued(&clockwise).unwrap().winding, -1);
        let beside = LogRatio::new(g(3, 0), GaussianRat::one(), 0).unwrap();
        let away = [g(4, 1), g(2, 1), g(2, -1), g(4, -1), g(3, 0)];
        assert_eq!(beside.continued(&away).unwrap().winding, 0);
        assert_eq!(
            start.continued(&[g(-1, 0)]),
            Err(GaussianError::ThroughZero { segment: 0 })
        );
        // Vertices on the cut: arriving from below returns a turn, leaving downward advances it.
        let onto = LogRatio::new(g(-1, -1), GaussianRat::one(), 0).unwrap();
        assert_eq!(onto.continued(&[g(-2, 0)]).unwrap().winding, -1);
        let off = LogRatio::new(g(-2, 0), GaussianRat::one(), 0).unwrap();
        assert_eq!(off.continued(&[g(-1, -1)]).unwrap().winding, 1);
        assert_eq!(
            off.continued(&[g(-1, -1), g(-2, 0)]).unwrap().winding,
            0,
            "down and back up across the cut returns"
        );
        // The denominator is kept: the lift of `(z : 2)` around zero.
        let halved = LogRatio::new(g(2, 0), GaussianRat::real(integer(2)), 0).unwrap();
        let back = halved.continued(&counterclockwise).unwrap();
        assert_eq!(back.numerator, g(2, 0));
        assert_eq!(back.winding, 1);
    }

    /// A unimodular ratio has modulus one and a zero log form.
    #[test]
    fn the_modulus_is_one_on_the_unit_ratio() {
        let unit = LogRatio::new(g(3, 4), g(5, 0), 0).unwrap();
        assert_eq!(unit.modulus().unwrap(), integer(1));
        assert!(unit.modulus_log2().unwrap().is_zero());
    }
}
