import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart
import ElementaryHolonics.Millennium.NavierStokesViscousSwirlBalance
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A factorized anisotropic Cartesian frame

This owner records the diagonal method chart with horizontal factor `r` and axial factor `z`.
All inverse, metric, rate, and reconstruction statements retain their nonzero-factor hypotheses.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped Laplacian Pointwise

namespace Soma.Holonics.Millennium.NavierStokesAnisotropicFrame

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance

def diagonalFrame (r z : ℝ) : Space →L[ℝ] Space :=
  ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] Space).comp
    (ContinuousLinearMap.pi (fun i : Fin 3 ↦
      if i = 0 then r • coordinateProjection 0
      else if i = 1 then r • coordinateProjection 1
      else z • coordinateProjection 2))

@[simp] theorem coordinateProjection_basisFun (i j : Fin 3) :
    coordinateProjection i (EuclideanSpace.basisFun (Fin 3) ℝ j) = if i = j then 1 else 0 := by
  simp [coordinateProjection, EuclideanSpace.basisFun_apply, PiLp.proj_apply, PiLp.single_apply]

@[simp] theorem coordinateProjection_apply (i : Fin 3) (x : Space) :
    coordinateProjection i x = x i := rfl

theorem diagonalFrame_apply (r z : ℝ) (x : Space) :
    diagonalFrame r z x = assemble (r * x 0) (r * x 1) (z * x 2) := by
  ext i
  fin_cases i <;>
    simp [diagonalFrame, assemble, coordinateProjection_apply]

theorem diagonalFrame_scalar (a : ℝ) :
    diagonalFrame a a = a • ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The complete fibre is retained even when one spatial factor vanishes. -/
theorem diagonalFrame_fibre (r z : ℝ) (x y : Space) :
    diagonalFrame r z x = diagonalFrame r z y ↔
      r * (x 0 - y 0) = 0 ∧ r * (x 1 - y 1) = 0 ∧ z * (x 2 - y 2) = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Space ↦ v 0) h
    have h1 := congrArg (fun v : Space ↦ v 1) h
    have h2 := congrArg (fun v : Space ↦ v 2) h
    simp only [diagonalFrame_apply, assemble_zero, assemble_one, assemble_two] at h0 h1 h2
    constructor
    · nlinarith
    constructor <;> nlinarith
  · rintro ⟨h0, h1, h2⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change r * x 0 = r * y 0
      nlinarith
    · change r * x 1 = r * y 1
      nlinarith
    · change z * x 2 = z * y 2
      nlinarith

theorem diagonalFrame_det (r z : ℝ) :
    LinearMap.det (diagonalFrame r z).toLinearMap = r ^ 2 * z := by
  have hm : NavierStokesVorticity.jacobianMatrix (diagonalFrame r z) =
      Matrix.diagonal ![r, r, z] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [NavierStokesVorticity.jacobianMatrix_apply, diagonalFrame, Matrix.diagonal]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  change Matrix.det (NavierStokesVorticity.jacobianMatrix (diagonalFrame r z)) = _
  rw [hm, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, pow_two, mul_assoc]

theorem diagonalFrame_hasDerivAt
    (r z : ℝ → ℝ) (rJet zJet : ℝ) (t : ℝ)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t) :
    HasDerivAt (fun τ ↦ diagonalFrame (r τ) (z τ))
      (diagonalFrame rJet zJet) t := by
  have h0 := hr.smul_const ((coordinateProjection 0).smulRight
    (EuclideanSpace.basisFun (Fin 3) ℝ 0))
  have h1 := hr.smul_const ((coordinateProjection 1).smulRight
    (EuclideanSpace.basisFun (Fin 3) ℝ 1))
  have h2 := hz.smul_const ((coordinateProjection 2).smulRight
    (EuclideanSpace.basisFun (Fin 3) ℝ 2))
  convert (h0.add h1).add h2 using 1 <;> try rfl
  · funext τ
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [diagonalFrame, coordinateProjection_apply]
  · apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [diagonalFrame, coordinateProjection_apply]

def inverseFrame (r z : ℝ) : Space →L[ℝ] Space := diagonalFrame r⁻¹ z⁻¹

theorem inverseFrame_hasDerivAt
    (r z : ℝ → ℝ) (rJet zJet t : ℝ)
    (hr : HasDerivAt r rJet t) (hz : HasDerivAt z zJet t)
    (hr0 : r t ≠ 0) (hz0 : z t ≠ 0) :
    HasDerivAt (fun τ ↦ inverseFrame (r τ) (z τ))
      (-((inverseFrame (r t) (z t)).comp (diagonalFrame rJet zJet)).comp
        (inverseFrame (r t) (z t))) t := by
  have hri := hr.inv hr0
  have hzi := hz.inv hz0
  have hframe := diagonalFrame_hasDerivAt (fun τ ↦ (r τ)⁻¹) (fun τ ↦ (z τ)⁻¹)
    (-rJet / r t ^ 2) (-zJet / z t ^ 2) t hri hzi
  change HasDerivAt (fun τ ↦ diagonalFrame (r τ)⁻¹ (z τ)⁻¹) _ t
  convert hframe using 1
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [inverseFrame, diagonalFrame_apply, diagonalFrame, assemble, hr0, hz0]
  · field_simp [hr0]
  · field_simp [hr0]
  · field_simp [hz0]

theorem inverseFrame_comp_diagonalFrame (r z : ℝ) (hr : r ≠ 0) (hz : z ≠ 0) :
    (inverseFrame r z).comp (diagonalFrame r z) = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro x
  change diagonalFrame r⁻¹ z⁻¹ (diagonalFrame r z x) = x
  rw [diagonalFrame_apply, diagonalFrame_apply]
  ext i
  fin_cases i <;> simp [assemble, coordinateProjection_apply] <;> field_simp [hr, hz]

theorem diagonalFrame_comp_inverseFrame (r z : ℝ) (hr : r ≠ 0) (hz : z ≠ 0) :
    (diagonalFrame r z).comp (inverseFrame r z) = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro x
  change diagonalFrame r z (diagonalFrame r⁻¹ z⁻¹ x) = x
  rw [diagonalFrame_apply, diagonalFrame_apply]
  ext i
  fin_cases i <;> simp [assemble, coordinateProjection_apply] <;> field_simp [hr, hz]

theorem diagonalFrame_adjoint (r z : ℝ) :
    (diagonalFrame r z).adjoint = diagonalFrame r z := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [PiLp.inner_apply]
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ, diagonalFrame, coordinateProjection_apply]
  ring

def metricFrame (r z : ℝ) : Space →L[ℝ] Space := inverseFrame r z |>.comp (inverseFrame r z).adjoint

theorem metricFrame_apply (r z : ℝ) (x : Space) :
    metricFrame r z x = assemble (r⁻¹ ^ 2 * x 0) (r⁻¹ ^ 2 * x 1) (z⁻¹ ^ 2 * x 2) := by
  have hadj : (inverseFrame r z).adjoint = inverseFrame r z := by
    simp [inverseFrame, diagonalFrame_adjoint]
  unfold metricFrame
  rw [hadj]
  ext i
  fin_cases i <;>
    simp [metricFrame, inverseFrame, diagonalFrame_apply, diagonalFrame, assemble]
  · ring
  · ring
  · ring

theorem diagonalFrame_comp_adjoint (r z : ℝ) :
    (diagonalFrame r z).comp (diagonalFrame r z).adjoint =
      diagonalFrame (r ^ 2) (z ^ 2) := by
  rw [diagonalFrame_adjoint]
  ext x i
  fin_cases i <;>
    simp [diagonalFrame_apply, diagonalFrame, assemble]
  · ring
  · ring
  · ring

def gridRate (r z r' z' : ℝ) : Space →L[ℝ] Space :=
  (inverseFrame r z).comp (diagonalFrame r' z')

theorem gridRate_apply (r z r' z' : ℝ) (hr : r ≠ 0) (hz : z ≠ 0) (x : Space) :
    gridRate r z r' z' x = assemble (r' / r * x 0) (r' / r * x 1) (z' / z * x 2) := by
  ext i
  fin_cases i <;>
    simp [gridRate, inverseFrame, diagonalFrame_apply, diagonalFrame, assemble, hr, hz]
  · field_simp
  · field_simp
  · field_simp

def physicalReconstruction (b r z : ℝ) (u : Space → Space) : Space → Space :=
  fun y ↦ b⁻¹ • diagonalFrame r z (u y)

theorem physicalAngularReconstruction (b r z : ℝ) (u : Space → Space) (y v : Space) :
    cartesianAngularMomentum (diagonalFrame r z y)
        (physicalReconstruction b r z u v) =
      (r ^ 2 / b) * cartesianAngularMomentum y (u v) := by
  simp [physicalReconstruction, diagonalFrame_apply, assemble, cartesianAngularMomentum]
  ring

def kineticMetric (r z : ℝ) (U : Space) : ℝ :=
  r ^ 2 * (U 0 ^ 2 + U 1 ^ 2) + z ^ 2 * U 2 ^ 2

theorem kineticMetric_eq_norm_sq (r z : ℝ) (U : Space) :
    kineticMetric r z U = ‖diagonalFrame r z U‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [kineticMetric, diagonalFrame, diagonalFrame_apply, Fin.sum_univ_succ]
  ring

theorem radialViscosity_reconstructionFactor
    (nu b r : ℝ) (hr : r ≠ 0) (hb : b ≠ 0) :
    (nu * b / r ^ 2) * r ^ 2 / b = nu := by
  field_simp

theorem reconstructionFactor_logDerivative
    (r b r' b' : ℝ) (hr : r ≠ 0) (hb : b ≠ 0) :
    (2 * r' / r - b' / b) = (2 * r' * b - b' * r) / (r * b) := by
  field_simp

theorem reconstructionFactor_hasDerivAt
    (r b : ℝ → ℝ) (rJet bJet t : ℝ)
    (hr : HasDerivAt r rJet t) (hb : HasDerivAt b bJet t)
    (hr0 : r t ≠ 0) (hb0 : b t ≠ 0) :
    HasDerivAt (fun τ ↦ r τ ^ 2 / b τ)
      (((2 * rJet / r t) - (bJet / b t)) * (r t ^ 2 / b t)) t := by
  have h := (hr.pow 2).div hb hb0
  convert h using 1 <;> try rfl
  field_simp [hr0, hb0]
  simp only [Pi.pow_apply, pow_two]
  ring

#print axioms diagonalFrame_apply
#print axioms diagonalFrame_fibre
#print axioms diagonalFrame_det
#print axioms diagonalFrame_hasDerivAt
#print axioms inverseFrame_comp_diagonalFrame
#print axioms diagonalFrame_comp_inverseFrame
#print axioms inverseFrame_hasDerivAt
#print axioms diagonalFrame_adjoint
#print axioms metricFrame_apply
#print axioms gridRate_apply
#print axioms physicalAngularReconstruction
#print axioms kineticMetric_eq_norm_sq
#print axioms radialViscosity_reconstructionFactor
#print axioms reconstructionFactor_logDerivative
#print axioms reconstructionFactor_hasDerivAt

end Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
