import ElementaryHolonics.Millennium.NavierStokesExteriorTorque
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Pressure torque on a Cartesian circle

The pressure is an arbitrary Cartesian `C¹` field.  Restricting it to a closed horizontal circle
gives an actual one-variable function, so Rolle's theorem supplies a point with zero angular
derivative.  The argument retains the full Cartesian pressure field and does not use
axisymmetry or periodicity.
-/

noncomputable section

open ContDiff Set InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesPressureCircle

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesExteriorTorque

/-- The horizontal Cartesian circle of radius `r` at height `z`. -/
def circlePath (r z : ℝ) (theta : ℝ) : Space :=
  assemble (r * Real.cos theta) (r * Real.sin theta) z

/-- Pressure restricted to the actual horizontal circle. -/
def circlePressure (P : Space → ℝ) (r z : ℝ) (theta : ℝ) : ℝ :=
  P (circlePath r z theta)

theorem continuous_circlePath (r z : ℝ) :
    Continuous (circlePath r z) := by
  have hcos : Continuous (fun theta : ℝ ↦ r * Real.cos theta) :=
    continuous_const.mul Real.continuous_cos
  have hsin : Continuous (fun theta : ℝ ↦ r * Real.sin theta) :=
    continuous_const.mul Real.continuous_sin
  have hthird : Continuous (fun _ : ℝ ↦
      (z • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space)) :=
    continuous_const
  exact ((hcos.smul continuous_const).add
    (hsin.smul continuous_const)).add
    hthird

theorem circlePath_hasDerivAt (r z theta : ℝ) :
    HasDerivAt (circlePath r z)
      (rotationGenerator (circlePath r z theta)) theta := by
  have hcos : HasDerivAt (fun s : ℝ ↦ r * Real.cos s) (-r * Real.sin theta) theta :=
    by simpa [mul_neg] using (Real.hasDerivAt_cos theta).const_mul r
  have hsin : HasDerivAt (fun s : ℝ ↦ r * Real.sin s) (r * Real.cos theta) theta :=
    (Real.hasDerivAt_sin theta).const_mul r
  have hpath := ((hcos.smul_const
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)).add
    (hsin.smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space))).add
    ((hasDerivAt_const theta z).smul_const
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space))
  change HasDerivAt (circlePath r z) _ theta at hpath
  convert hpath using 1
  simp [circlePath, rotationGenerator, assemble]

theorem circlePressure_hasDerivAt
    (P : Space → ℝ) (hP : ContDiff ℝ 1 P) (r z theta : ℝ) :
    HasDerivAt (circlePressure P r z)
      (pressureTorque P (circlePath r z theta)) theta := by
  have hPdiff : DifferentiableAt ℝ P (circlePath r z theta) :=
    (hP.differentiable (by norm_num)) (circlePath r z theta)
  have hcomp := hPdiff.hasFDerivAt.comp_hasDerivAt theta
    (circlePath_hasDerivAt r z theta)
  change HasDerivAt (circlePressure P r z) _ theta at hcomp
  convert hcomp using 1
  exact pressureTorque_eq_angular_derivative P (circlePath r z theta)

theorem circlePressure_endpoints (P : Space → ℝ) (r z : ℝ) :
    circlePressure P r z 0 = circlePressure P r z (2 * Real.pi) := by
  unfold circlePressure
  apply congrArg P
  ext i
  fin_cases i <;> simp [circlePath]

/-- Every `C¹` Cartesian pressure has a zero actual pressure torque on the closed circle. -/
theorem exists_pressureTorque_eq_zero_on_circle
    (P : Space → ℝ) (hP : ContDiff ℝ 1 P) (r z : ℝ) :
    ∃ theta ∈ Icc (0 : ℝ) (2 * Real.pi),
      pressureTorque P (circlePath r z theta) = 0 := by
  have hrolle := exists_hasDerivAt_eq_zero
    (f := circlePressure P r z)
    (f' := fun theta ↦ pressureTorque P (circlePath r z theta))
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (by positivity)
    ((hP.continuous.comp (continuous_circlePath r z)).continuousOn)
    (circlePressure_endpoints P r z)
    (fun theta _ ↦ circlePressure_hasDerivAt P hP r z theta)
  obtain ⟨theta, htheta, hzero⟩ := hrolle
  exact ⟨theta, ⟨le_of_lt htheta.1, le_of_lt htheta.2⟩, hzero⟩

/-- A uniform bound on a decomposed angular residual bounds its circle-constant part. -/
theorem abs_circle_constant_le_of_abs_residual_le
    (P : Space → ℝ) (hP : ContDiff ℝ 1 P) (r z constant epsilon : ℝ)
    (residual : ℝ → ℝ)
    (hdecomp : ∀ theta, residual theta =
      constant + pressureTorque P (circlePath r z theta))
    (hbound : ∀ theta ∈ Icc (0 : ℝ) (2 * Real.pi), |residual theta| ≤ epsilon) :
    |constant| ≤ epsilon := by
  obtain ⟨theta, htheta, hzero⟩ :=
    exists_pressureTorque_eq_zero_on_circle P hP r z
  have h := hbound theta htheta
  rw [hdecomp theta, hzero, add_zero] at h
  exact h

#print axioms circlePath_hasDerivAt
#print axioms circlePressure_hasDerivAt
#print axioms exists_pressureTorque_eq_zero_on_circle
#print axioms abs_circle_constant_le_of_abs_residual_le

end Soma.Holonics.Millennium.NavierStokesPressureCircle
