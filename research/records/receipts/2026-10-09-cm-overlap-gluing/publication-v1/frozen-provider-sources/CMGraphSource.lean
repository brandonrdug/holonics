import CMCurveCore
import CMCoordinateRingOnly
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An algebraic source for the square-lattice egg's graph

Isolated proof unit, 2026-09-30. Existing source: Geometry/EggModular.
The egg's lambda=1/2 face has j=1728. This file constructs the automorphism
on the *actual Weierstrass affine coordinate ring*, not an assumed cycle lift.
The next geometric gap is extension to the smooth projective curve, its graph
as a divisor on E x E, and the comparison with the rational cycle-class map.
Neither the Hodge conjecture nor a complete primitive basis is asserted.

The helical pair interaction stays attached through its phase/relative-graph
receiver: the touched general objects are navigator faces, cell holonomy and
tube transport. No inference about a generic family's monodromy is made.
agent-inferred: select this source rather than another abstract surjectivity
interface; the recorded failure would be a receiver law with no source map.
-/

noncomputable section

namespace Holonics.Hodge.CMGraphSource

open Polynomial
open scoped Polynomial.Bivariate

abbrev CurveRing := squareCurve.toAffine.CoordinateRing

def u : CurveRing := AdjoinRoot.of squareCurve.toAffine.polynomial X
def v : CurveRing := AdjoinRoot.root squareCurve.toAffine.polynomial

theorem squarePolynomial : squareCurve.toAffine.polynomial = Y ^ 2 - C (X ^ 3 - X) := by
  simp [WeierstrassCurve.Affine.polynomial, squareCurve, sub_eq_add_neg]

theorem curve_relation : v ^ 2 = u ^ 3 - u := by
  have h := AdjoinRoot.eval₂_root squareCurve.toAffine.polynomial
  conv at h => arg 1; arg 3; rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_sub, map_pow] at h
  exact sub_eq_zero.mp h

/-- The coefficient pullback u -> -u, fixing the coefficient field. -/
def coefficientPullback : ℂ[X] →ₐ[ℂ] CurveRing := aeval (-u)

theorem phase_relation (q : ℂ) (hq : q ^ 2 = -1) :
    squareCurve.toAffine.polynomial.eval₂ coefficientPullback (q • v) = 0 := by
  conv_lhs => arg 3; rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_sub, map_pow]
  simp only [coefficientPullback, AlgHom.coe_toRingHom, aeval_X]
  rw [smul_pow, hq, neg_one_smul, curve_relation]
  ring

/-- A polynomial algebra map descended through the Weierstrass equation. -/
def phasePullback (q : ℂ) (hq : q ^ 2 = -1) : CurveRing →ₐ[ℂ] CurveRing :=
  AdjoinRoot.liftAlgHom squareCurve.toAffine.polynomial coefficientPullback
    (q • v) (phase_relation q hq)

@[simp] theorem phasePullback_u (q : ℂ) (hq : q ^ 2 = -1) :
    phasePullback q hq u = -u := by
  simp [phasePullback, u, coefficientPullback]

@[simp] theorem phasePullback_v (q : ℂ) (hq : q ^ 2 = -1) :
    phasePullback q hq v = q • v := by
  simp [phasePullback, v]

/-- Algebra maps out of the actual curve ring are determined by u and v. -/
theorem curveRing_hom_ext {A : Type*} [CommRing A] [Algebra ℂ A]
    {f g : CurveRing →ₐ[ℂ] A} (hu : f u = g u) (hv : f v = g v) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hu
  · exact hv

def iota : CurveRing →ₐ[ℂ] CurveRing := phasePullback Complex.I Complex.I_sq
def iotaInverse : CurveRing →ₐ[ℂ] CurveRing :=
  phasePullback (-Complex.I) (by simp)

theorem iota_inverse_comp : iotaInverse.comp iota = AlgHom.id ℂ CurveRing := by
  apply curveRing_hom_ext
  · simp [iota, iotaInverse]
  · simp [iota, iotaInverse, smul_smul]

theorem iota_comp_inverse : iota.comp iotaInverse = AlgHom.id ℂ CurveRing := by
  apply curveRing_hom_ext
  · simp [iota, iotaInverse]
  · simp [iota, iotaInverse, smul_smul]

/-- The addressed CM algebraic automorphism, with its actual inverse. -/
def iotaEquiv : CurveRing ≃ₐ[ℂ] CurveRing :=
  AlgEquiv.ofAlgHom iota iotaInverse iota_comp_inverse iota_inverse_comp

theorem iota_fourth : iota.comp (iota.comp (iota.comp iota)) = AlgHom.id ℂ CurveRing := by
  apply curveRing_hom_ext
  · simp [iota]
  · simp [iota, smul_smul]

#print axioms squareCurve_discriminant
#print axioms curve_relation
#print axioms phase_relation
#print axioms phasePullback
#print axioms curveRing_hom_ext
#print axioms iotaEquiv
#print axioms iota_fourth

end Holonics.Hodge.CMGraphSource
