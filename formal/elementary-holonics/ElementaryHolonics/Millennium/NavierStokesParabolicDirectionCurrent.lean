import ElementaryHolonics.Millennium.NavierStokesParabolicCriticalCurrent
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-!
# The amplitude-normalized vorticity-direction current is subcritical

**[proved-derived]** The preceding scale theorem shows that the BKM magnitude current has exact
parabolic weight two and therefore survives every admitted cover unchanged after chronology is
integrated.  This owner retains the source feature discarded by that receiver: orientation.

The normalized direction of a nonzero vector is invariant under every positive amplitude rebase;
the totalized zero chart has the same covariance.  Consequently the cross seam between two
normalized vorticity directions has weight zero.  A coefficient controlling that seam linearly in
spatial distance has weight one, and its accumulated time current has weight minus one.  This is
the exact scale advantage sought from direction depletion.  The file does not assume or assert
that every Navier--Stokes solution has a terminally integrable direction coefficient.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesParabolicRebase
open Soma.Holonics.Millennium.NavierStokesParabolicVorticityCurrent
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-- The oriented unit receiver, totalized by the zero vector at the zero-amplitude chart. -/
def normalizedDirection (v : Space) : Space :=
  ‖v‖⁻¹ • v

/-- Positive amplitude transport leaves the normalized direction exactly unchanged. -/
@[simp]
theorem normalizedDirection_smul_of_pos
    {amplitude : ℝ} (hamplitude : 0 < amplitude) (v : Space) :
    normalizedDirection (amplitude • v) = normalizedDirection v := by
  by_cases hv : v = 0
  · simp [normalizedDirection, hv]
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    unfold normalizedDirection
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hamplitude, smul_smul]
    congr 1
    field_simp [hamplitude.ne', hvnorm]

/-- The magnitude and the normalized direction reconstruct the complete source occurrence. -/
theorem norm_smul_normalizedDirection (v : Space) :
    ‖v‖ • normalizedDirection v = v := by
  by_cases hv : v = 0
  · simp [normalizedDirection, hv]
  · unfold normalizedDirection
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

/-- The real cross interaction is bilinear in the two independently addressed amplitudes. -/
theorem cross_smul_smul (left right : ℝ) (u v : Space) :
    cross (left • u) (right • v) = (left * right) • cross u v := by
  ext component
  fin_cases component <;> simp [cross, crossProduct] <;> ring

/-- The signed seam between two amplitude-normalized directions.  It is an oriented area face,
not an angle scalar and not a magnitude replacement for either endpoint. -/
def normalizedDirectionSeam (receiver source : Space) : Space :=
  cross (normalizedDirection receiver) (normalizedDirection source)

/-- Magnitude and orientation are exact multiplicative faces of the cross interaction.  No sign
or direction information is recoverable from the two norms alone; it resides in the seam. -/
theorem cross_eq_norm_mul_normalizedDirectionSeam (receiver source : Space) :
    cross receiver source =
      (‖receiver‖ * ‖source‖) • normalizedDirectionSeam receiver source := by
  calc
    cross receiver source =
        cross (‖receiver‖ • normalizedDirection receiver)
          (‖source‖ • normalizedDirection source) := by
      rw [norm_smul_normalizedDirection, norm_smul_normalizedDirection]
    _ = (‖receiver‖ * ‖source‖) •
        normalizedDirectionSeam receiver source := by
      exact cross_smul_smul _ _ _ _

/-- Simultaneously rebasing both endpoints by a positive amplitude preserves the complete seam. -/
@[simp]
theorem normalizedDirectionSeam_smul_of_pos
    {amplitude : ℝ} (hamplitude : 0 < amplitude) (receiver source : Space) :
    normalizedDirectionSeam (amplitude • receiver) (amplitude • source) =
      normalizedDirectionSeam receiver source := by
  simp [normalizedDirectionSeam, normalizedDirection_smul_of_pos hamplitude]

/-- A spatial slice has linear direction coherence with coefficient `K` when every oriented seam
is controlled by `K` times the addressed source--receiver distance. -/
def HasLinearDirectionCoherence (field : Space → Space) (K : ℝ) : Prop :=
  ∀ x y, ‖normalizedDirectionSeam (field x) (field y)‖ ≤ K * ‖x - y‖

/-- A direction-coherence law depletes the full cross interaction by factoring it into the two
magnitude faces and the signed spatial seam. -/
theorem norm_cross_le_of_hasLinearDirectionCoherence
    {field : Space → Space} {K : ℝ}
    (hcoherence : HasLinearDirectionCoherence field K) (x y : Space) :
    ‖cross (field x) (field y)‖ ≤
      (‖field x‖ * ‖field y‖) * (K * ‖x - y‖) := by
  rw [cross_eq_norm_mul_normalizedDirectionSeam, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (hcoherence x y)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The real oriented seam is exactly the existing complex cross-difference receiver after the
coordinatewise chart transition. -/
theorem receiverCrossDifference_complexOfRealSpace
    (receiver source : Space) :
    receiverCrossDifference (complexOfRealSpace receiver) (complexOfRealSpace source) =
      complexOfRealSpace (cross receiver source) := by
  ext component
  fin_cases component <;>
    simp [receiverCrossDifference, complexCross, complexOfRealSpace, cross, crossProduct]

/-- The normalized direction law therefore controls the exact complex cross population already
consumed by the dyadic Hodge reconstruction.  The two magnitude faces remain explicit. -/
theorem complexVectorL1_receiverCrossDifference_le_of_hasLinearDirectionCoherence
    {field : Space → Space} {K : ℝ}
    (hcoherence : HasLinearDirectionCoherence field K) (x y : Space) :
    complexVectorL1
        (receiverCrossDifference (complexOfRealSpace (field x))
          (complexOfRealSpace (field y))) ≤
      3 * ((‖field x‖ * ‖field y‖) * (K * ‖x - y‖)) := by
  rw [receiverCrossDifference_complexOfRealSpace]
  calc
    complexVectorL1 (complexOfRealSpace (cross (field x) (field y))) ≤
        3 * ‖cross (field x) (field y)‖ :=
      complexVectorL1_complexOfRealSpace_le_three_norm _
    _ ≤ 3 * ((‖field x‖ * ‖field y‖) * (K * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left
        (norm_cross_le_of_hasLinearDirectionCoherence hcoherence x y) (by norm_num)

/-- The abstract parabolic direction slice.  Its amplitude factor is the exact vorticity weight;
keeping it here makes the amplitude cancellation visible before the spatial chart is folded. -/
def parabolicDirectionSlice (scale : ℝ) (field : Space → Space) : Space → Space :=
  fun x ↦ scale ^ 2 • field (scale • x)

/-- A linear direction-coherence coefficient has exact parabolic weight one.  The reverse
direction reconstructs every source pair through the inverse spatial chart, so this is an iff and
not an estimate-only transport. -/
theorem hasLinearDirectionCoherence_parabolicDirectionSlice_iff
    {scale K : ℝ} (hscale : 0 < scale) (field : Space → Space) :
    HasLinearDirectionCoherence (parabolicDirectionSlice scale field) (scale * K) ↔
      HasLinearDirectionCoherence field K := by
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · intro hreturned x y
    have hpair := hreturned (scale⁻¹ • x) (scale⁻¹ • y)
    have hleftX : scale • (scale⁻¹ • x) = x := by
      rw [← mul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
    have hleftY : scale • (scale⁻¹ • y) = y := by
      rw [← mul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
    change
      ‖normalizedDirectionSeam
          (scale ^ 2 • field (scale • (scale⁻¹ • x)))
          (scale ^ 2 • field (scale • (scale⁻¹ • y)))‖ ≤
        (scale * K) * ‖scale⁻¹ • x - scale⁻¹ • y‖ at hpair
    rw [hleftX, hleftY, normalizedDirectionSeam_smul_of_pos hscaleSq] at hpair
    calc
      ‖normalizedDirectionSeam (field x) (field y)‖ ≤
          (scale * K) * ‖scale⁻¹ • x - scale⁻¹ • y‖ := hpair
      _ = K * ‖x - y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
        field_simp [hscale.ne']
  · intro hsource x y
    change
      ‖normalizedDirectionSeam
          (scale ^ 2 • field (scale • x))
          (scale ^ 2 • field (scale • y))‖ ≤
        (scale * K) * ‖x - y‖
    rw [normalizedDirectionSeam_smul_of_pos hscaleSq]
    calc
      ‖normalizedDirectionSeam (field (scale • x)) (field (scale • y))‖ ≤
          K * ‖scale • x - scale • y‖ := hsource _ _
      _ = (scale * K) * ‖x - y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
        ring

/-- On the actual Navier--Stokes carrier, the normalized orientation seam has weight zero: only
its spatial addresses and chronology are rebased. -/
theorem normalizedDirectionSeam_vorticityField_parabolicVelocity
    {scale : ℝ} (hscale : 0 < scale) (velocity : VelocityField)
    (x y : Space) (t : ℝ) :
    normalizedDirectionSeam
        (vorticityField (parabolicVelocity scale velocity) x t)
        (vorticityField (parabolicVelocity scale velocity) y t) =
      normalizedDirectionSeam
        (vorticityField velocity (scale • x) (scale ^ 2 * t))
        (vorticityField velocity (scale • y) (scale ^ 2 * t)) := by
  rw [vorticityField_parabolicVelocity, vorticityField_parabolicVelocity]
  exact normalizedDirectionSeam_smul_of_pos (sq_pos_of_pos hscale) _ _

/-- Therefore the actual vorticity slice obeys the same exact weight-one direction law. -/
theorem hasLinearDirectionCoherence_vorticityField_parabolicVelocity_iff
    {scale K : ℝ} (hscale : 0 < scale) (velocity : VelocityField) (t : ℝ) :
    HasLinearDirectionCoherence
        (fun x ↦ vorticityField (parabolicVelocity scale velocity) x t) (scale * K) ↔
      HasLinearDirectionCoherence
        (fun x ↦ vorticityField velocity x (scale ^ 2 * t)) K := by
  have hfield :
      (fun x ↦ vorticityField (parabolicVelocity scale velocity) x t) =
        parabolicDirectionSlice scale
          (fun x ↦ vorticityField velocity x (scale ^ 2 * t)) := by
    funext x
    exact vorticityField_parabolicVelocity scale velocity x t
  rw [hfield]
  exact hasLinearDirectionCoherence_parabolicDirectionSlice_iff hscale _

/-- The time coefficient induced by the weight-one direction carrier. -/
def parabolicDirectionRate (scale : ℝ) (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  scale * rate (scale ^ 2 * t)

/-- The accumulated direction current is strictly subcritical: after the quadratic chronology
fold it returns with the exact inverse spatial weight. -/
theorem integral_parabolicDirectionRate
    {scale T : ℝ} (hscale : 0 < scale) (rate : ℝ → ℝ) :
    (∫ t in 0..T, parabolicDirectionRate scale rate t) =
      scale⁻¹ * ∫ s in 0..(scale ^ 2 * T), rate s := by
  calc
    (∫ t in 0..T, parabolicDirectionRate scale rate t) =
        scale * (∫ t in 0..T, rate (scale ^ 2 * t)) := by
      simp only [parabolicDirectionRate]
      rw [intervalIntegral.integral_const_mul]
    _ = scale⁻¹ *
        ((scale ^ 2) * ∫ t in 0..T, rate (scale ^ 2 * t)) := by
      field_simp [hscale.ne']
    _ = scale⁻¹ * ∫ s in scale ^ 2 * 0..scale ^ 2 * T, rate s := by
      have hchange := intervalIntegral.smul_integral_comp_mul_left
        (f := rate) (a := 0) (b := T) (scale ^ 2)
      rw [smul_eq_mul] at hchange
      rw [hchange]
    _ = scale⁻¹ * ∫ s in 0..(scale ^ 2 * T), rate s := by simp

section Audit

#print axioms normalizedDirection_smul_of_pos
#print axioms norm_smul_normalizedDirection
#print axioms cross_eq_norm_mul_normalizedDirectionSeam
#print axioms normalizedDirectionSeam_smul_of_pos
#print axioms norm_cross_le_of_hasLinearDirectionCoherence
#print axioms receiverCrossDifference_complexOfRealSpace
#print axioms complexVectorL1_receiverCrossDifference_le_of_hasLinearDirectionCoherence
#print axioms hasLinearDirectionCoherence_parabolicDirectionSlice_iff
#print axioms normalizedDirectionSeam_vorticityField_parabolicVelocity
#print axioms hasLinearDirectionCoherence_vorticityField_parabolicVelocity_iff
#print axioms integral_parabolicDirectionRate

end Audit

end Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent
