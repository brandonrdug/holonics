import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart
import ElementaryHolonics.Millennium.NavierStokesPeriodicEnergy
import ElementaryHolonics.Millennium.NavierStokesPeriodicCubeInterpolation

/-!
# Quartic pressure currents

These are literal homogeneous quartic harmonic pressure polynomials.  Their negative gradients
are cubic currents and therefore vanish to first order at the origin.
-/

noncomputable section

open ContDiff Function Set Topology InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesQuarticPressureCurrent

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicCubeInterpolation
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesVorticity

private theorem coordinate_fderiv (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space ↦ y i) x = EuclideanSpace.proj i := by
  convert (EuclideanSpace.proj i : Space →L[ℝ] ℝ).fderiv (x := x) using 1 <;> rfl

def radiusSq (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

def Hax (x : Space) : ℝ :=
  x 2 ^ 4 - 3 * radiusSq x * x 2 ^ 2 + (3 / 8) * radiusSq x ^ 2

def Hcos (x : Space) : ℝ := x 0 ^ 4 - 6 * x 0 ^ 2 * x 1 ^ 2 + x 1 ^ 4

def Hsin (x : Space) : ℝ := x 0 * x 1 * (x 0 ^ 2 - x 1 ^ 2)

def quarticPressure (a b c : ℝ) (x : Space) : ℝ :=
  a * Hax x + b * Hcos x + c * Hsin x

def quarticPressureCurrent (a b c : ℝ) : InitialVelocity :=
  fun x ↦ -gradient (quarticPressure a b c) x

theorem quarticPressure_contDiff (a b c : ℝ) :
    ContDiff ℝ ∞ (quarticPressure a b c) := by
  unfold quarticPressure Hax Hcos Hsin radiusSq
  fun_prop

theorem quarticPressure_fderiv (a b c : ℝ) (x : Space) :
    fderiv ℝ (quarticPressure a b c) x =
      (a * (-6 * x 0 * x 2 ^ 2 + (3 / 2) * x 0 * radiusSq x) +
          b * (4 * x 0 ^ 3 - 12 * x 0 * x 1 ^ 2) +
          c * (3 * x 0 ^ 2 * x 1 - x 1 ^ 3)) • coordinateProjection 0 +
      (a * (-6 * x 1 * x 2 ^ 2 + (3 / 2) * x 1 * radiusSq x) +
          b * (4 * x 1 ^ 3 - 12 * x 0 ^ 2 * x 1) +
          c * (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2)) • coordinateProjection 1 +
      (a * (4 * x 2 ^ 3 - 6 * radiusSq x * x 2)) • coordinateProjection 2 := by
  unfold quarticPressure Hax Hcos Hsin radiusSq
  ext direction
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_pow,
    coordinate_fderiv, fderiv_const]
  simp [coordinateProjection]
  ring

theorem gradient_quarticPressure (a b c : ℝ) (x : Space) :
    gradient (quarticPressure a b c) x =
      assemble
        (a * (-6 * x 0 * x 2 ^ 2 + (3 / 2) * x 0 * radiusSq x) +
          b * (4 * x 0 ^ 3 - 12 * x 0 * x 1 ^ 2) +
          c * (3 * x 0 ^ 2 * x 1 - x 1 ^ 3))
        (a * (-6 * x 1 * x 2 ^ 2 + (3 / 2) * x 1 * radiusSq x) +
          b * (4 * x 1 ^ 3 - 12 * x 0 ^ 2 * x 1) +
          c * (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2))
        (a * (4 * x 2 ^ 3 - 6 * radiusSq x * x 2)) := by
  apply ext_inner_right ℝ
  intro direction
  rw [inner_gradient_left]
  rw [quarticPressure_fderiv]
  simp [assemble, inner_add_left, real_inner_smul_left, PiLp.inner_apply, Fin.sum_univ_three, coordinateProjection]
  ring

theorem divergence_quarticGradient (a b c : ℝ) (x : Space) :
    divergence (gradient (quarticPressure a b c)) x = 0 := by
  have hg : ContDiff ℝ 1 (gradient (quarticPressure a b c)) :=
    (gradient_contDiff (quarticPressure_contDiff a b c)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [← divergenceFromJacobian_velocityJacobianAt]
  simp only [divergenceFromJacobian, Fin.sum_univ_three, velocityJacobianAt, jacobianMatrix_apply]
  rw [← fderiv_component_apply _ hg x _ 0, ← fderiv_component_apply _ hg x _ 1,
    ← fderiv_component_apply _ hg x _ 2]
  simp_rw [gradient_quarticPressure]
  simp only [assemble, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, Fin.reduceFinMk, ite_true, ite_false, zero_mul,
    mul_zero, add_zero, zero_add, mul_one]
  unfold radiusSq
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, coordinate_fderiv, fderiv_const]
  simp [EuclideanSpace.basisFun_apply]
  ring

theorem quarticPressure_harmonic (a b c : ℝ) (x : Space) :
    Δ (quarticPressure a b c) x = 0 := by
  rw [← divergence_gradient_eq_laplacian (quarticPressure a b c)
    ((quarticPressure_contDiff a b c).of_le (WithTop.coe_le_coe.mpr le_top)) x]
  exact divergence_quarticGradient a b c x

theorem divergence_quarticPressureCurrent (a b c : ℝ) (x : Space) :
    divergence (quarticPressureCurrent a b c) x = 0 := by
  have h := congrArg (fun r : ℝ ↦ -r) (divergence_quarticGradient a b c x)
  unfold quarticPressureCurrent divergence
  rw [fderiv_fun_neg]
  simpa [divergence] using h

theorem quarticPressureCurrent_contDiff (a b c : ℝ) :
    ContDiff ℝ ∞ (quarticPressureCurrent a b c) := by
  unfold quarticPressureCurrent
  exact (gradient_contDiff (quarticPressure_contDiff a b c)).neg

theorem quarticPressure_gradient_zero (a b c : ℝ) :
    gradient (quarticPressure a b c) 0 = 0 := by
  rw [gradient_quarticPressure]
  simp [assemble, radiusSq]

theorem quarticPressureCurrent_zero (a b c : ℝ) :
    quarticPressureCurrent a b c 0 = 0 := by
  unfold quarticPressureCurrent
  rw [quarticPressure_gradient_zero]
  simp

theorem quarticPressureCurrent_fderiv_zero (a b c : ℝ) :
    fderiv ℝ (quarticPressureCurrent a b c) 0 = 0 := by
  have hg : ContDiff ℝ 1 (quarticPressureCurrent a b c) :=
    (quarticPressureCurrent_contDiff a b c).of_le (WithTop.coe_le_coe.mpr le_top)
  ext direction component
  change (fderiv ℝ (quarticPressureCurrent a b c) 0 direction) component = 0
  rw [← fderiv_component_apply _ hg 0 direction component]
  simp_rw [quarticPressureCurrent, gradient_quarticPressure]
  fin_cases component <;>
    simp (disch := fun_prop) [assemble, radiusSq, fderiv_fun_neg, fderiv_fun_add,
      fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_pow, coordinate_fderiv, fderiv_const] <;> norm_num

/-- The zero first jet does not identify these currents: the complete polynomial receiver
has exactly the zero coefficient triple as its null fibre. -/
theorem quarticPressureCurrent_eq_zero_iff (a b c : ℝ) :
    quarticPressureCurrent a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun f : InitialVelocity ↦ f (assemble 0 0 1) 2) h
    have hx := congrArg (fun f : InitialVelocity ↦ f (assemble 1 0 0) 0) h
    have hy := congrArg (fun f : InitialVelocity ↦ f (assemble 1 0 0) 1) h
    simp [quarticPressureCurrent, gradient_quarticPressure, assemble, radiusSq] at hz hx hy
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext x
    simp [quarticPressureCurrent, gradient_quarticPressure, assemble]

#print axioms quarticPressure_contDiff
#print axioms gradient_quarticPressure
#print axioms quarticPressure_harmonic
#print axioms divergence_quarticPressureCurrent
#print axioms quarticPressureCurrent_contDiff
#print axioms quarticPressureCurrent_zero
#print axioms quarticPressureCurrent_fderiv_zero
#print axioms quarticPressureCurrent_eq_zero_iff

end Soma.Holonics.Millennium.NavierStokesQuarticPressureCurrent
