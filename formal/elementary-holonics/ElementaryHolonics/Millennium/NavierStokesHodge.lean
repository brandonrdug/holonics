import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ElementaryHolonics.Millennium.NavierStokesVorticity

/-!
# Local Hodge faces of Navier--Stokes

Every local velocity jet is first split exactly into transpose-symmetric and transpose-skew faces.
The symmetric face is the complete local kernel population of curl; the skew face is reconstructed
canonically from vorticity and carries the entire curl return.

The pressure part of the momentum current is then constructed as the exterior derivative of the
pressure zero-form on the actual Euclidean fluid carrier.  Mathlib's `d² = 0` theorem proves that
this exact one-form is closed.  The Euclidean musical identification is explicit: the exact
one-form is precisely the inner-product lowering of the pressure gradient; its negative is the
pressure-force covector used by momentum.

This supplies the first genuine de Rham/Hodge port for the fluid track.  A subsequent global Hodge
decomposition may split admitted one-forms into exact, coexact, and harmonic populations; the
pressure occurrence already lands in the exact population.  A subsequent realized codifferential
must transport incompressibility into the co-closed receiver for velocity.
-/

noncomputable section

open ContinuousAlternatingMap InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesHodge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## 1. The local symmetric/skew jet split -/

/-- The transpose-symmetric face of a local velocity Jacobian. -/
def symmetricJacobianPart (J : Matrix3) : Matrix3 :=
  (2 : ℝ)⁻¹ • (J + J.transpose)

/-- The transpose-skew face of a local velocity Jacobian. -/
def skewJacobianPart (J : Matrix3) : Matrix3 :=
  (2 : ℝ)⁻¹ • (J - J.transpose)

/-- Every local jet is exactly the sum of its symmetric and skew faces. -/
theorem jacobian_eq_symmetricPart_add_skewPart (J : Matrix3) :
    J = symmetricJacobianPart J + skewJacobianPart J := by
  ext i j
  simp [symmetricJacobianPart, skewJacobianPart]
  ring

/-- The first face really belongs to the kernel population of local curl. -/
theorem symmetricJacobianPart_isSymmetric (J : Matrix3) :
    IsSymmetricJacobian (symmetricJacobianPart J) := by
  intro i j
  simp [symmetricJacobianPart, add_comm]

/-- Curl is carried entirely by the skew face of the local jet. -/
theorem curlFromJacobian_skewJacobianPart (J : Matrix3) :
    curlFromJacobian (skewJacobianPart J) = curlFromJacobian J := by
  ext i
  fin_cases i <;> simp [curlFromJacobian, skewJacobianPart] <;> ring

/-- The canonical skew chart reconstructed from one vorticity vector. -/
def skewFromVorticity (ω : Space) : Matrix3 :=
  !![0, -(ω 2) / 2, (ω 1) / 2;
    (ω 2) / 2, 0, -(ω 0) / 2;
    -(ω 1) / 2, (ω 0) / 2, 0]

/-- The reconstructed skew chart returns exactly its source vorticity. -/
theorem curlFromJacobian_skewFromVorticity (ω : Space) :
    curlFromJacobian (skewFromVorticity ω) = ω := by
  ext i
  fin_cases i <;> simp [curlFromJacobian, skewFromVorticity] <;> ring

/-- The skew face of every jet is exactly the canonical reconstruction of its curl. -/
theorem skewJacobianPart_eq_skewFromVorticity (J : Matrix3) :
    skewJacobianPart J = skewFromVorticity (curlFromJacobian J) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewJacobianPart, skewFromVorticity, curlFromJacobian] <;> ring

/-! ## 2. Exact pressure as a de Rham form -/

/-- Differential `n`-forms on the spatial fluid carrier. -/
abbrev SpatialForm (n : ℕ) := Space → Space [⋀^Fin n]→L[ℝ] ℝ

/-- A scalar pressure field presented as a spatial zero-form. -/
def pressureZeroForm (pressure : Space → ℝ) : SpatialForm 0 :=
  fun x => constOfIsEmpty ℝ Space (Fin 0) (pressure x)

/-- The exact pressure one-form `d p`. -/
def pressureExactOneForm (pressure : Space → ℝ) : SpatialForm 1 :=
  extDeriv (pressureZeroForm pressure)

/-- The pressure gradient lowered by the Euclidean metric and bundled as a one-form. -/
def loweredPressureGradientOneForm (pressure : Space → ℝ) : SpatialForm 1 :=
  fun x => ofSubsingleton ℝ Space ℝ (0 : Fin 1) (innerSL ℝ (gradient pressure x))

/-- **The de Rham and metric presentations agree.**  At a differentiable pressure occurrence,
`d p` is exactly the Euclidean lowering of `grad p`. -/
theorem pressureExactOneForm_eq_loweredGradient
    (pressure : Space → ℝ) (x : Space) (hpressure : DifferentiableAt ℝ pressure x) :
    pressureExactOneForm pressure x = loweredPressureGradientOneForm pressure x := by
  change extDeriv (fun y => constOfIsEmpty ℝ Space (Fin 0) (pressure y)) x = _
  rw [extDeriv_constOfIsEmpty]
  change (ofSubsingleton ℝ Space ℝ (0 : Fin 1)) (fderiv ℝ pressure x) =
    (ofSubsingleton ℝ Space ℝ (0 : Fin 1)) (innerSL ℝ (gradient pressure x))
  apply congrArg (ofSubsingleton ℝ Space ℝ (0 : Fin 1))
  ext v
  exact inner_gradient_left.symm

/-- **Exact pressure is closed.**  The second exterior derivative of every `C²` pressure zero-form
vanishes at the addressed event. -/
theorem pressureExactOneForm_closed
    (pressure : Space → ℝ) (x : Space) (hpressure : ContDiffAt ℝ 2 pressure x) :
    extDeriv (pressureExactOneForm pressure) x = 0 := by
  apply extDeriv_extDeriv_apply
  · exact (constOfIsEmptyLIE ℝ Space ℝ (Fin 0)).contDiff.contDiffAt.comp x hpressure
  · simp

/-- The official smooth solution places its positive-time pressure occurrence in the exact and
closed one-form population. -/
theorem smoothSolution_pressureExactOneForm_closed
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    extDeriv (pressureExactOneForm (fun y => pressure y t)) x = 0 := by
  apply Soma.Holonics.Millennium.NavierStokesHodge.pressureExactOneForm_closed
  exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
    solution.pressureSmooth ht).of_le (WithTop.coe_le_coe.mpr le_top)

/-- The same admitted pressure occurrence is the lowered gradient used by momentum. -/
theorem smoothSolution_pressureExactOneForm_eq_loweredGradient
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    pressureExactOneForm (fun y => pressure y t) x =
      loweredPressureGradientOneForm (fun y => pressure y t) x := by
  apply Soma.Holonics.Millennium.NavierStokesHodge.pressureExactOneForm_eq_loweredGradient
  exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
    solution.pressureSmooth ht).differentiableAt (by simp)

section Audit

#print axioms pressureExactOneForm_eq_loweredGradient
#print axioms pressureExactOneForm_closed
#print axioms smoothSolution_pressureExactOneForm_closed
#print axioms jacobian_eq_symmetricPart_add_skewPart
#print axioms skewJacobianPart_eq_skewFromVorticity

end Audit

end Soma.Holonics.Millennium.NavierStokesHodge
