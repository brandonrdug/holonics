import ElementaryHolonics.Millennium.HolonicYangMillsHessian

/-!
# The abelian reduction: the Yang--Mills flow is the heat flow of the curvature

When the algebra commutes every bracket vanishes: the covariant derivative is the differential,
the curvature is `dA`, the Ricci identity is the symmetry of second derivatives, and the
Weitzenböck evolution along the Yang--Mills direction is the heat equation

```text
(D_A G)_ij = Σ_k ∂_k ∂_k F_ij.
```

The Hessian loses its curvature coupling and becomes the free form `∫ Σ B(dB, dB)`.  Read against
the fluid: with the velocity as an abelian connection the curvature is the vorticity, the abelian
flow is the Stokes heat flow of the vorticity, and the nonabelian commutator `2 [F_ik, F_kj]` that
the abelian case discards is the gauge twin of the vortex stretching.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.HolonicYangMillsAbelian

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
open Soma.Holonics.Millennium.HolonicYangMillsDescent
open Soma.Holonics.Millennium.HolonicYangMillsHessian

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

section Commutative

variable (hcomm : ∀ x y : 𝔤, x * y = y * x)
include hcomm

omit [NormedAlgebra ℝ 𝔤] in
theorem bracket_eq_zero (x y : 𝔤) : bracket x y = 0 := by
  simp [bracket, hcomm x y]

/-- In a commutative algebra the covariant derivative is the differential. -/
theorem covariantDerivative_eq_differential (A : Connection n 𝔤) (i : Fin n) (X : Base n → 𝔤) :
    covariantDerivative A i X = differential i X := by
  funext x
  simp [covariantDerivative, bracket_eq_zero hcomm]

/-- In a commutative algebra the curvature is `dA`. -/
theorem curvature_eq_differential (A : Connection n 𝔤) (i j : Fin n) (x : Base n) :
    curvature A i j x = differential i (A j) x - differential j (A i) x := by
  simp [curvature, bracket_eq_zero hcomm]

/-- **The abelian Weitzenböck evolution is the heat equation of the curvature.** -/
theorem covariantVariation_yangMillsDirection_eq_laplacian (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 3 (A i)) (i j : Fin n) (x : Base n) :
    covariantVariation A (yangMillsDirection A) i j x =
      ∑ k, differential k (differential k (curvature A i j)) x := by
  rw [covariantVariation_yangMillsDirection A hA i j x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bracket_eq_zero hcomm, covariantDerivative_eq_differential hcomm,
    covariantDerivative_eq_differential hcomm]
  simp

/-- **The abelian Hessian is the free form** `∫ Σ B(dB, dB)`. -/
theorem hessian_eq_free (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤) :
    hessian P A B = ∫ x in unitBox (n + 1), ∑ i, ∑ j,
      P.B (differential i (B j) x - differential j (B i) x)
        (differential i (B j) x - differential j (B i) x) := by
  unfold hessian
  refine setIntegral_congr_fun isCompact_Icc.measurableSet fun x _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [covariantVariation, covariantDerivative_eq_differential hcomm, bracket_eq_zero hcomm]

end Commutative

section Audit

#print axioms covariantVariation_yangMillsDirection_eq_laplacian
#print axioms hessian_eq_free

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsAbelian
