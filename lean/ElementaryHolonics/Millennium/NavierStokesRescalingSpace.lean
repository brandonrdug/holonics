import ElementaryHolonics.Millennium.NavierStokesParabolicRebase

/-!
# The MFR1 spatial pullback

This file carries the spatial part of the moving-frame chart.  The chart is addressed by its
centre and scale; no chronology or solution carrier is introduced here.  In particular, the
inverse and the changed period retain the nonzero-scale obligation instead of treating a collapsed
chart as an inverse.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped Laplacian Pointwise

namespace Soma.Holonics.Millennium.NavierStokesRescalingSpace

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesParabolicRebase

/-! ## The addressed spatial chart -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar-amplitude pullback through the translated dilation `y ↦ centre + scale • y`. -/
def spatialPullback (amplitude scale : ℝ) (centre : Space) (field : Space → E) : Space → E :=
  fun y ↦ amplitude • field (centre + scale • y)

@[simp]
theorem spatialPullback_apply
    (amplitude scale : ℝ) (centre : Space) (field : Space → E) (y : Space) :
    spatialPullback amplitude scale centre field y = amplitude • field (centre + scale • y) := rfl

/-- The scalar-amplitude velocity chart `U(y) = a⁻¹ u(c + ell y)`. -/
def velocitySpatialPullback
    (a ell : ℝ) (centre : Space) (velocity : Space → Space) : Space → Space :=
  spatialPullback a⁻¹ ell centre velocity

/-- The scalar-amplitude pressure chart `P(y) = a⁻² p(c + ell y)`. -/
def pressureSpatialPullback
    (a ell : ℝ) (centre : Space) (pressure : Space → ℝ) : Space → ℝ :=
  spatialPullback (a⁻¹ ^ 2) ell centre pressure

/-! ## First-order transport -/

/-- The translated dilation contributes one incoming spatial scale and one amplitude scale. -/
theorem fderiv_spatialPullback
    (amplitude scale : ℝ) (centre : Space) (field : Space → E) (y : Space) :
    fderiv ℝ (spatialPullback amplitude scale centre field) y =
      amplitude • (scale • fderiv ℝ field (centre + scale • y)) := by
  unfold spatialPullback
  rw [show (fun z : Space ↦ amplitude • field (centre + scale • z)) =
      amplitude • (fun z : Space ↦ field (centre + scale • z)) by
    funext z
    rfl]
  rw [congrFun (fderiv_const_smul_field amplitude) y]
  simp only [Pi.smul_apply]
  have hcomp :
      fderiv ℝ (fun z : Space ↦ field (centre + scale • z)) y =
        scale • fderiv ℝ field (centre + scale • y) := by
    simpa only [Function.comp_def, fderiv_comp_add_left] using
      (fderiv_comp_smul (f := fun z : Space ↦ field (centre + z)) (x := y) scale)
  rw [hcomp]

/-! ## Navier--Stokes receivers -/

/-- The divergence receiver transports with the product of amplitude and spatial scale. -/
theorem divergence_spatialPullback
    (amplitude scale : ℝ) (centre : Space) (velocity : Space → Space) (y : Space) :
    divergence (spatialPullback amplitude scale centre velocity) y =
      (amplitude * scale) * divergence velocity (centre + scale • y) := by
  unfold divergence
  rw [fderiv_spatialPullback]
  simp [mul_assoc]

/-- The advective receiver transports with two amplitude copies and one spatial copy. -/
theorem advection_spatialPullback
    (amplitude scale : ℝ) (centre : Space) (velocity : Space → Space) (y : Space) :
    fderiv ℝ (spatialPullback amplitude scale centre velocity) y
        (spatialPullback amplitude scale centre velocity y) =
      (amplitude ^ 2 * scale) •
        fderiv ℝ velocity (centre + scale • y) (velocity (centre + scale • y)) := by
  rw [fderiv_spatialPullback]
  unfold spatialPullback
  simp only [smul_apply]
  rw [map_smul, smul_smul]
  rw [smul_smul]
  congr 1
  ring

/-- The gradient receiver for a scalar field transports with one pressure and one spatial copy. -/
theorem gradient_spatialPullback
    (amplitude scale : ℝ) (centre : Space) (pressure : Space → ℝ) (y : Space) :
    gradient (spatialPullback amplitude scale centre pressure) y =
      (amplitude * scale) • gradient pressure (centre + scale • y) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, fderiv_spatialPullback]
  simp [smul_eq_mul, mul_assoc]

/-- The velocity Laplacian transports with one amplitude copy and two spatial copies.

The dilation part reuses `laplacian_comp_parabolicSpaceMap`; the only new step is the translated
field, which is a chart change and contributes no derivative factor.
-/
theorem laplacian_spatialPullback
    (amplitude scale : ℝ) (centre : Space) (velocity : Space → Space)
    (hvelocity : ContDiff ℝ 2 velocity) (y : Space) :
    Δ (spatialPullback amplitude scale centre velocity) y =
      (amplitude * scale ^ 2) • Δ velocity (centre + scale • y) := by
  let translated : Space → Space := fun z ↦ velocity (centre + z)
  have htranslated : ContDiff ℝ 2 translated := by
    simpa [translated, Function.comp_def] using
      hvelocity.comp (contDiff_const.add contDiff_id)
  have hcomp :
      (fun z : Space ↦ translated (scale • z)) =
        (fun z : Space ↦ velocity (centre + scale • z)) := by
    funext z
    rfl
  have hlap := laplacian_comp_parabolicSpaceMap scale translated htranslated y
  have htrans : Δ translated (scale • y) = Δ velocity (centre + scale • y) := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis translated) (scale • y),
      congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis velocity)
        (centre + scale • y)]
    simp [translated, iteratedFDeriv_comp_add_left]
  unfold spatialPullback
  rw [show (fun z : Space ↦ amplitude • velocity (centre + scale • z)) =
      amplitude • (fun z : Space ↦ velocity (centre + scale • z)) by
    funext z
    rfl]
  rw [laplacian_smul amplitude]
  · rw [hcomp, hlap, htrans]
    rw [smul_smul]
  · exact (hvelocity.comp
      (contDiff_const.add (contDiff_id.const_smul scale))).contDiffAt

/-! ## Specialized frozen MFR1 fields -/

theorem fderiv_velocitySpatialPullback
    (a ell : ℝ) (centre : Space) (velocity : Space → Space) (y : Space) :
    fderiv ℝ (velocitySpatialPullback a ell centre velocity) y =
      (a⁻¹ * ell) • fderiv ℝ velocity (centre + ell • y) := by
  rw [show velocitySpatialPullback a ell centre velocity =
      spatialPullback a⁻¹ ell centre velocity by rfl,
    fderiv_spatialPullback]
  rw [smul_smul]

theorem divergence_velocitySpatialPullback
    (a ell : ℝ) (centre : Space) (velocity : Space → Space) (y : Space) :
    divergence (velocitySpatialPullback a ell centre velocity) y =
      (a⁻¹ * ell) * divergence velocity (centre + ell • y) := by
  rw [show velocitySpatialPullback a ell centre velocity =
      spatialPullback a⁻¹ ell centre velocity by rfl,
    divergence_spatialPullback]
theorem advection_velocitySpatialPullback
    (a ell : ℝ) (centre : Space) (velocity : Space → Space) (y : Space) :
    fderiv ℝ (velocitySpatialPullback a ell centre velocity) y
        (velocitySpatialPullback a ell centre velocity y) =
      (a⁻¹ ^ 2 * ell) •
        fderiv ℝ velocity (centre + ell • y) (velocity (centre + ell • y)) := by
  rw [show velocitySpatialPullback a ell centre velocity =
      spatialPullback a⁻¹ ell centre velocity by rfl,
    advection_spatialPullback]
theorem gradient_pressureSpatialPullback
    (a ell : ℝ) (centre : Space) (pressure : Space → ℝ) (y : Space) :
    gradient (pressureSpatialPullback a ell centre pressure) y =
      (a⁻¹ ^ 2 * ell) • gradient pressure (centre + ell • y) := by
  rw [show pressureSpatialPullback a ell centre pressure =
      spatialPullback (a⁻¹ ^ 2) ell centre pressure by rfl,
    gradient_spatialPullback]
theorem laplacian_velocitySpatialPullback
    (a ell : ℝ) (centre : Space) (velocity : Space → Space)
    (hvelocity : ContDiff ℝ 2 velocity) (y : Space) :
    Δ (velocitySpatialPullback a ell centre velocity) y =
      (a⁻¹ * ell ^ 2) • Δ velocity (centre + ell • y) := by
  rw [show velocitySpatialPullback a ell centre velocity =
      spatialPullback a⁻¹ ell centre velocity by rfl,
    laplacian_spatialPullback a⁻¹ ell centre velocity hvelocity]
/-! ## Inverse chart and reconstruction -/

/-- The inverse spatial chart, with its inverse amplitude and inverse scale visible. -/
def spatialPushforward (amplitude scale : ℝ) (centre : Space) (field : Space → E) : Space → E :=
  fun x ↦ amplitude • field (scale • (x - centre))

@[simp]
theorem spatialPushforward_apply
    (amplitude scale : ℝ) (centre : Space) (field : Space → E) (x : Space) :
    spatialPushforward amplitude scale centre field x =
      amplitude • field (scale • (x - centre)) := rfl

theorem spatialPushforward_spatialPullback
    (amplitude scale : ℝ) (hamplitude : amplitude ≠ 0) (hscale : scale ≠ 0)
    (centre : Space) (field : Space → E) :
    spatialPushforward amplitude⁻¹ scale⁻¹ centre
        (spatialPullback amplitude scale centre field) = field := by
  funext x
  unfold spatialPushforward spatialPullback
  simp [smul_smul, smul_sub, mul_inv_cancel₀ hscale, inv_mul_cancel₀ hamplitude]

theorem spatialPullback_spatialPushforward
    (amplitude scale : ℝ) (hamplitude : amplitude ≠ 0) (hscale : scale ≠ 0)
    (centre : Space) (field : Space → E) :
    spatialPullback amplitude⁻¹ scale⁻¹ centre
        (spatialPushforward amplitude scale centre field) = field := by
  funext y
  unfold spatialPullback spatialPushforward
  simp [smul_smul, mul_inv_cancel₀ hscale, inv_mul_cancel₀ hamplitude]

theorem velocitySpatialPullback_reconstruct
    {a ell : ℝ} (ha : a ≠ 0) (hell : ell ≠ 0) (centre : Space)
    (velocity : Space → Space) :
    (fun x ↦ a • velocitySpatialPullback a ell centre velocity
      (ell⁻¹ • (x - centre))) = velocity := by
  funext x
  unfold velocitySpatialPullback spatialPullback
  simp [smul_smul, mul_inv_cancel₀ ha, mul_inv_cancel₀ hell, add_sub_cancel]

/-! ## The transported period -/

theorem spatialPullback_isPeriodic
    (amplitude scale : ℝ) (hscale : scale ≠ 0) (centre : Space)
    {field : Space → E} (hperiodic : IsOnePeriodic field) :
    ∀ y i, spatialPullback amplitude scale centre field
      (y + scale⁻¹ • EuclideanSpace.single i 1) =
      spatialPullback amplitude scale centre field y := by
  intro y i
  unfold spatialPullback
  have harg :
      centre + scale • (y + scale⁻¹ • EuclideanSpace.single i 1) =
        (centre + scale • y) + EuclideanSpace.single i 1 := by
    calc
      centre + scale • (y + scale⁻¹ • EuclideanSpace.single i 1) =
          centre + (scale • y + (scale * scale⁻¹) • EuclideanSpace.single i 1) := by
            rw [smul_add, smul_smul]
      _ = (centre + scale • y) + EuclideanSpace.single i 1 := by
        rw [mul_inv_cancel₀ hscale, one_smul]
        abel
  change amplitude • field (centre + scale • (y + scale⁻¹ • EuclideanSpace.single i 1)) =
    amplitude • field (centre + scale • y)
  rw [harg]
  congr 1
  exact hperiodic _ i

theorem velocitySpatialPullback_isPeriodic
    {a ell : ℝ} (hell : ell ≠ 0) (centre : Space) (velocity : Space → Space)
    (hperiodic : IsOnePeriodic velocity) :
    ∀ y i, velocitySpatialPullback a ell centre velocity
      (y + ell⁻¹ • EuclideanSpace.single i 1) =
      velocitySpatialPullback a ell centre velocity y := by
  change ∀ y i, spatialPullback a⁻¹ ell centre velocity
      (y + ell⁻¹ • EuclideanSpace.single i 1) =
      spatialPullback a⁻¹ ell centre velocity y
  exact spatialPullback_isPeriodic a⁻¹ ell hell centre hperiodic

theorem pressureSpatialPullback_isPeriodic
    {a ell : ℝ} (hell : ell ≠ 0) (centre : Space) (pressure : Space → ℝ)
    (hperiodic : IsOnePeriodic pressure) :
    ∀ y i, pressureSpatialPullback a ell centre pressure
      (y + ell⁻¹ • EuclideanSpace.single i 1) =
      pressureSpatialPullback a ell centre pressure y := by
  change ∀ y i, spatialPullback (a⁻¹ ^ 2) ell centre pressure
      (y + ell⁻¹ • EuclideanSpace.single i 1) =
      spatialPullback (a⁻¹ ^ 2) ell centre pressure y
  exact spatialPullback_isPeriodic (a⁻¹ ^ 2) ell hell centre hperiodic

section Audit

#print axioms fderiv_spatialPullback
#print axioms divergence_spatialPullback
#print axioms advection_spatialPullback
#print axioms gradient_spatialPullback
#print axioms laplacian_spatialPullback
#print axioms spatialPushforward_spatialPullback
#print axioms spatialPullback_spatialPushforward
#print axioms velocitySpatialPullback_reconstruct
#print axioms spatialPullback_isPeriodic
#print axioms velocitySpatialPullback_isPeriodic
#print axioms pressureSpatialPullback_isPeriodic

end Audit

end Soma.Holonics.Millennium.NavierStokesRescalingSpace
