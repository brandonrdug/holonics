import ElementaryHolonics.Millennium.NavierStokesFramedHorizontalMean
import ElementaryHolonics.Millennium.NavierStokesPressureMean
import ElementaryHolonics.Millennium.NavierStokesAnisotropicViscousClock

/-!
# Anisotropic pressure mean

The actual pressure mean and vertical velocity-square mean remain joined after a diagonal
horizontal transport.  The aspect factor and the radial clock make the two transported terms
carry the same coefficient, while the framed mean retains the moving cell.
-/

noncomputable section

open ContDiff Function Set MeasureTheory
open scoped Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesAnisotropicPressureMean

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesHorizontalMean
open Soma.Holonics.Millennium.NavierStokesPressureMean
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
open Soma.Holonics.Millennium.NavierStokesAnisotropicViscousClock
open Soma.Holonics.Millennium.NavierStokesFramedHorizontalMean

theorem anisotropic_pressure_mean_add_vertical_square_mean_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (centre : Space) (r zScale K ζ w : ℝ)
    (hr : r ≠ 0) (hz : zScale ≠ 0) (hK : K ≠ 0) :
    aspect r zScale *
        framedHorizontalMean r centre
          (fun y ↦ (r / K) ^ 2 * pressure (centre + diagonalFrame r zScale y) t.1) ζ +
        framedHorizontalMean r centre
          (fun y ↦ ((clockRate K r / zScale) *
            (velocity (centre + diagonalFrame r zScale y) t.1 2)) ^ 2) ζ =
      aspect r zScale *
        framedHorizontalMean r centre
          (fun y ↦ (r / K) ^ 2 * pressure (centre + diagonalFrame r zScale y) t.1) w +
        framedHorizontalMean r centre
          (fun y ↦ ((clockRate K r / zScale) *
            (velocity (centre + diagonalFrame r zScale y) t.1 2)) ^ 2) w := by
  let p : Space → ℝ := fun x ↦ pressure x t.1
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let q : Space → ℝ := verticalVelocitySquare u
  have hp ζ' := framedHorizontalMean_affine_transport r zScale ((r / K) ^ 2) hr
    centre p ζ'
  have hq ζ' := framedHorizontalMean_affine_transport r zScale
    ((clockRate K r / zScale) ^ 2) hr centre q ζ'
  have hq' (ζ' : ℝ) :
      framedHorizontalMean r centre
          (fun y ↦ ((clockRate K r / zScale) *
            (u (centre + diagonalFrame r zScale y) 2)) ^ 2) ζ' =
        (clockRate K r / zScale) ^ 2 *
          horizontalMean q (centre 2 + zScale * ζ') := by
    have hfun :
        (fun y ↦ ((clockRate K r / zScale) *
          (u (centre + diagonalFrame r zScale y) 2)) ^ 2) =
          (fun y ↦ (clockRate K r / zScale) ^ 2 *
            q (centre + diagonalFrame r zScale y)) := by
      funext y
      dsimp [q, verticalVelocitySquare]
      ring
    rw [hfun]
    exact hq ζ'
  have hmean := pressure_mean_add_vertical_square_mean_eq solution t
    (centre 2 + zScale * ζ) (centre 2 + zScale * w)
  have hmean' :
      horizontalMean p (centre 2 + zScale * ζ) +
          horizontalMean q (centre 2 + zScale * ζ) =
        horizontalMean p (centre 2 + zScale * w) +
          horizontalMean q (centre 2 + zScale * w) := by
    simpa [p, u, q] using hmean
  rw [hq' ζ, hq' w]
  rw [hp ζ, hp w]
  have hcoef :
      aspect r zScale * (r / K) ^ 2 = (clockRate K r / zScale) ^ 2 := by
    unfold aspect clockRate
    field_simp [hK, hz]
  rw [← mul_assoc, hcoef, ← mul_assoc, hcoef]
  rw [← mul_add, hmean', mul_add]

/-- Actual reduced pressure read through the transported horizontal cell. -/
def radialPressureMean (r zScale K : ℝ) (centre : Space) (p : Space → ℝ) : ℝ → ℝ :=
  framedHorizontalMean r centre (fun y ↦ (r / K) ^ 2 * p (centre + diagonalFrame r zScale y))

/-- The quadratic vertical population is retained before averaging. -/
def radialVerticalSquareMean (r zScale K : ℝ) (centre : Space) (u : InitialVelocity) : ℝ → ℝ :=
  framedHorizontalMean r centre (fun y ↦
    ((clockRate K r / zScale) * u (centre + diagonalFrame r zScale y) 2) ^ 2)

theorem radialPressureMean_hasDerivAt
    (r zScale K : ℝ) (hr : r ≠ 0) (centre : Space) (p : Space → ℝ)
    (hp : ContDiff ℝ 2 p) (ζ : ℝ) :
    HasDerivAt (radialPressureMean r zScale K centre p)
      ((r / K) ^ 2 * zScale * horizontalMean (fun x ↦ fderiv ℝ p x
        (EuclideanSpace.single (2 : Fin 3) 1)) (centre 2 + zScale * ζ)) ζ :=
  framedHorizontalMean_affine_transport_hasDerivAt r zScale ((r / K) ^ 2) hr centre p hp ζ

theorem radialVerticalSquareMean_hasDerivAt
    (r zScale K : ℝ) (hr : r ≠ 0) (centre : Space) (u : InitialVelocity)
    (hu : ContDiff ℝ ∞ u) (ζ : ℝ) :
    HasDerivAt (radialVerticalSquareMean r zScale K centre u)
      ((clockRate K r / zScale) ^ 2 * zScale * horizontalMean
        (fun x ↦ fderiv ℝ (verticalVelocitySquare u) x
          (EuclideanSpace.single (2 : Fin 3) 1)) (centre 2 + zScale * ζ)) ζ := by
  have heq : radialVerticalSquareMean r zScale K centre u =
      framedHorizontalMean r centre (fun y ↦ (clockRate K r / zScale) ^ 2 *
        verticalVelocitySquare u (centre + diagonalFrame r zScale y)) := by
    unfold radialVerticalSquareMean
    congr 1
    funext y
    simp only [verticalVelocitySquare, mul_pow]
  rw [heq]
  exact framedHorizontalMean_affine_transport_hasDerivAt r zScale
    ((clockRate K r / zScale) ^ 2) hr centre (verticalVelocitySquare u)
    ((verticalVelocitySquare_contDiff u hu).of_le (WithTop.coe_le_coe.mpr le_top)) ζ

/-- The actual axial mean pressure force remains coupled to the complete quadratic source.
The derivative is spatial at the selected physical time, with the chart frozen there. -/
theorem anisotropic_pressure_mean_deriv_eq_neg_vertical_square_mean_deriv
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (centre : Space) (r zScale K ζ : ℝ)
    (hr : r ≠ 0) (hz : zScale ≠ 0) (hK : K ≠ 0) :
    aspect r zScale * deriv (radialPressureMean r zScale K centre (fun x ↦ pressure x t.1)) ζ =
      -deriv (radialVerticalSquareMean r zScale K centre (fun x ↦ velocity x t.1)) ζ := by
  rw [(radialPressureMean_hasDerivAt r zScale K hr centre _
      ((openPeriodicSolutionOn_pressureSlice_contDiff solution t.2).of_le
        (WithTop.coe_le_coe.mpr le_top)) ζ).deriv,
    (radialVerticalSquareMean_hasDerivAt r zScale K hr centre _
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2) ζ).deriv]
  rw [horizontalMean_pressure_axialDerivative_eq_neg_vertical_square_axialDerivative
    solution t (centre 2 + zScale * ζ)]
  have hc : aspect r zScale * (r / K) ^ 2 = (clockRate K r / zScale) ^ 2 := by
    unfold aspect clockRate
    field_simp [hz, hK]
  rw [← mul_assoc, ← mul_assoc, hc]
  ring

/-- A nonzero aspect factor quantifies the exact pressure-gradient amplification. This identity
does not assert a nonzero lower bound for any concentrating family. -/
theorem anisotropic_pressure_mean_abs_deriv_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (centre : Space) (r zScale K ζ : ℝ)
    (hr : r ≠ 0) (hz : zScale ≠ 0) (hK : K ≠ 0) :
    |deriv (radialPressureMean r zScale K centre (fun x ↦ pressure x t.1)) ζ| =
      |deriv (radialVerticalSquareMean r zScale K centre (fun x ↦ velocity x t.1)) ζ| /
        aspect r zScale := by
  have h := congrArg (fun x : ℝ ↦ |x|) (anisotropic_pressure_mean_deriv_eq_neg_vertical_square_mean_deriv
    solution t centre r zScale K ζ hr hz hK)
  have hpos : 0 < aspect r zScale := sq_pos_of_ne_zero (div_ne_zero hr hz)
  rw [abs_mul, abs_of_pos hpos, abs_neg] at h
  apply (eq_div_iff hpos.ne').mpr
  simpa only [mul_comm] using h

#print axioms anisotropic_pressure_mean_add_vertical_square_mean_eq
#print axioms radialPressureMean_hasDerivAt
#print axioms radialVerticalSquareMean_hasDerivAt
#print axioms anisotropic_pressure_mean_deriv_eq_neg_vertical_square_mean_deriv
#print axioms anisotropic_pressure_mean_abs_deriv_eq

end Soma.Holonics.Millennium.NavierStokesAnisotropicPressureMean
