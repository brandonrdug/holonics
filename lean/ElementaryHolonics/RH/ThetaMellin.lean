import ElementaryHolonics.Millennium.LandenFlow
import ElementaryHolonics.RH.Statement
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic

/-!
# The Landen theta kernel is the Mellin source of completed zeta

`LandenLattice.T3` is the theta leg transported by the exact dyadic scale flow.
Mathlib constructs the completed Riemann zeta function from the same series,
presented as `HurwitzZeta.evenKernel 0`, through a weak functional-equation
pair and its Mellin transform.  This file joins those two existing owners.

The main theorem is stated in the half-plane of absolute Mellin convergence.
Analytic continuation and reflection remain the existing completed-zeta
functional equation; they are not rederived here.
-/

noncomputable section

namespace Soma.Holonics.RH

open Complex MeasureTheory Real Set
open HurwitzZeta
open Soma.Holonics.Millennium.LandenLattice

/-- On positive scale, the Landen `T3` leg is exactly Mathlib's even theta
kernel at the zero additive character. -/
theorem landenT3_eq_evenKernel_zero {t : ℝ} (ht : 0 < t) :
    T3 t = evenKernel 0 t := by
  simpa [T3] using (hasSum_int_evenKernel 0 ht).tsum_eq

/--
In the half-plane `1 < re s`, the actual completed Riemann zeta function is
the Mellin receiver of the normalized Landen `T3` current.  This is an exact
pullback to `completedRiemannZeta`, not a comparison with a separate theta
model.
-/
theorem completedRiemannZeta_hasMellin_T3 {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ => (((T3 t : ℝ) : ℂ) - 1) / 2) (s / 2)
      (completedRiemannZeta s) := by
  let P := hurwitzEvenFEPair 0
  have hs' : P.k < (s / 2).re := by
    dsimp [P, hurwitzEvenFEPair]
    rw [div_ofNat_re]
    linarith
  have hM := P.hasMellin hs'
  change MellinConvergent _ (s / 2) ∧ mellin _ (s / 2) = completedRiemannZeta s
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      (((T3 t : ℝ) : ℂ) - 1) / 2 = (((evenKernel 0 t : ℝ) : ℂ) - 1) / 2 := by
    intro t ht
    rw [landenT3_eq_evenKernel_zero ht]
  have hPpoint : ∀ t : ℝ,
      (((evenKernel 0 t : ℝ) : ℂ) - 1) / 2 = (P.f t - P.f₀) / 2 := by
    intro t
    dsimp [P, hurwitzEvenFEPair]
    simp
  have hmellin :
      mellin (fun t : ℝ => (((T3 t : ℝ) : ℂ) - 1) / 2) (s / 2) =
      mellin (fun t : ℝ => (((evenKernel 0 t : ℝ) : ℂ) - 1) / 2) (s / 2) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hpoint t ht]
  constructor
  · unfold MellinConvergent at hM ⊢
    have hbase := hM.1.div_const (2 : ℂ)
    unfold MellinConvergent at hbase
    exact (integrableOn_congr_fun (fun t ht => by
      dsimp only
      rw [hpoint t ht, hPpoint t]) measurableSet_Ioi).mpr hbase
  · rw [hmellin]
    simp_rw [hPpoint]
    rw [mellin_div_const, hM.2]
    change P.Λ (s / 2) / 2 = P.Λ (s / 2) / 2
    rfl

#print axioms landenT3_eq_evenKernel_zero
#print axioms completedRiemannZeta_hasMellin_T3

end Soma.Holonics.RH
