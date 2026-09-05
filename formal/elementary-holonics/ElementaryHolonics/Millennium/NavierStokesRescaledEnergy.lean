import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux
import ElementaryHolonics.Millennium.NavierStokesRescalingSpace
import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling
import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime
import ElementaryHolonics.Millennium.NavierStokesH2StorageDissipationPayment

/-!
# The transported kinetic `L²` receiver

The moving spatial chart changes the integration population with the chart.  This owner keeps the
actual preimage cell `c + ell • y ∈ unitCube`; it does not silently integrate a rescaled field over
the old unit cube.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesRescaledEnergy

open ContDiff
open Real Set Filter Topology MeasureTheory
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesRescalingSpace
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling
open scoped Pointwise

/-- The spatial population whose physical image lies in the unit cube. -/
def transportedCell (centre : Space) (ell : ℝ) : Set Space :=
  {y | centre + ell • y ∈ unitCube}

/-- The unit cube in coordinates translated by the moving centre. -/
def centredUnitCube (centre : Space) : Set Space :=
  {x | centre + x ∈ unitCube}

/-- The normalized velocity slice with direct amplitude `q`. -/
def rescaledVelocitySlice (q ell : ℝ) (centre : Space)
    (velocity : Space → Space) : Space → Space :=
  spatialPullback q ell centre velocity

theorem transportedCell_smul_image (centre : Space) {ell : ℝ} (hell : 0 < ell) :
    ell • transportedCell centre ell = centredUnitCube centre := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hell.ne']
  change centre + ell • (ell⁻¹ • x) ∈ unitCube ↔ centre + x ∈ unitCube
  rw [smul_smul, mul_inv_cancel₀ hell.ne', one_smul]

theorem centredUnitCube_translation_preimage (centre : Space) :
    (fun x : Space => centre + x) ⁻¹' unitCube = centredUnitCube centre := rfl

theorem integrableOn_energy_comp_translation (centre : Space)
    {velocity : Space → Space}
    (hvelocity : IntegrableOn (fun x : Space => ‖velocity x‖ ^ 2) unitCube) :
    IntegrableOn (fun x : Space => ‖velocity (centre + x)‖ ^ 2)
      (centredUnitCube centre) := by
  rw [← centredUnitCube_translation_preimage centre]
  exact ((measurePreserving_add_left volume centre).integrableOn_comp_preimage
    (Homeomorph.addLeft centre).measurableEmbedding (f := fun x : Space => ‖velocity x‖ ^ 2)
      (s := unitCube)).mpr hvelocity

theorem rescaledEnergy_integrableOn
    (q : ℝ) (centre : Space) {ell : ℝ} (hell : 0 < ell)
    {velocity : Space → Space}
    (hvelocity : IntegrableOn (fun x : Space => ‖velocity x‖ ^ 2) unitCube) :
    IntegrableOn
      (fun y : Space => ‖rescaledVelocitySlice q ell centre velocity y‖ ^ 2)
      (transportedCell centre ell) := by
  have hcube : MeasurableSet unitCube := by
    exact measurableSet_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  have hglobal : Integrable
      (fun y : Space => (unitCube.indicator (fun x : Space => ‖velocity x‖ ^ 2))
        (centre + ell • y)) := by
    have hind : Integrable (unitCube.indicator (fun x : Space => ‖velocity x‖ ^ 2)) :=
      hvelocity.integrable_indicator hcube
    have hshift := hind.comp_add_left centre
    exact hshift.comp_smul hell.ne'
  have hcell : MeasurableSet (transportedCell centre ell) :=
    hcube.preimage (by fun_prop)
  have hqglobal : Integrable
      (fun y : Space => q ^ 2 *
        (unitCube.indicator (fun x : Space => ‖velocity x‖ ^ 2))
          (centre + ell • y)) :=
    hglobal.const_mul (q ^ 2)
  change Integrable
    (fun y : Space => ‖rescaledVelocitySlice q ell centre velocity y‖ ^ 2)
    (volume.restrict (transportedCell centre ell))
  have hqOn' : Integrable
      (fun y : Space => q ^ 2 *
        (unitCube.indicator (fun x : Space => ‖velocity x‖ ^ 2))
          (centre + ell • y))
      (volume.restrict (transportedCell centre ell)) :=
    hqglobal.integrableOn (s := transportedCell centre ell)
  refine hqOn'.congr ?_
  filter_upwards [ae_restrict_mem hcell] with y hy
  change centre + ell • y ∈ unitCube at hy
  unfold rescaledVelocitySlice spatialPullback
  rw [Set.indicator_of_mem hy]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem rescaledEnergy_integral_eq
    (q : ℝ) (centre : Space) {ell : ℝ} (hell : 0 < ell)
    {velocity : Space → Space}
    (_hvelocity : IntegrableOn (fun x : Space => ‖velocity x‖ ^ 2) unitCube) :
    (∫ y in transportedCell centre ell,
      ‖rescaledVelocitySlice q ell centre velocity y‖ ^ 2) =
      (q ^ 2 / ell ^ 3) * (∫ x in unitCube, ‖velocity x‖ ^ 2) := by
  let energy : Space → ℝ := fun x => ‖velocity x‖ ^ 2
  let shiftedEnergy : Space → ℝ := fun x => energy (centre + x)
  have hscale := Measure.setIntegral_comp_smul_of_pos volume shiftedEnergy
    (transportedCell centre ell) hell
  have htrans := (measurePreserving_add_left volume centre).setIntegral_preimage_emb
    (Homeomorph.addLeft centre).measurableEmbedding energy unitCube
  have hset := transportedCell_smul_image centre hell
  have hscaled :
      (∫ y in transportedCell centre ell, shiftedEnergy (ell • y)) =
        (ell ^ 3)⁻¹ * (∫ x in centredUnitCube centre, shiftedEnergy x) := by
    rw [hscale, hset]
    simp
  have htranslated :
      (∫ x in centredUnitCube centre, shiftedEnergy x) =
        ∫ x in unitCube, energy x := by
    rw [← htrans]
    rfl
  calc
    (∫ y in transportedCell centre ell,
        ‖rescaledVelocitySlice q ell centre velocity y‖ ^ 2) =
        q ^ 2 * (∫ y in transportedCell centre ell, shiftedEnergy (ell • y)) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun
          · have hcube : IsCompact unitCube := by
              unfold unitCube
              exact ((EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage).mpr
                isCompact_Icc
            exact hcube.measurableSet.preimage (by fun_prop)
          · intro y hy
            dsimp [rescaledVelocitySlice, spatialPullback, energy, shiftedEnergy]
            rw [norm_smul]
            simp only [Real.norm_eq_abs]
            rw [mul_pow, sq_abs]
    _ = q ^ 2 * ((ell ^ 3)⁻¹ * (∫ x in centredUnitCube centre, shiftedEnergy x)) := by
      rw [hscaled]
    _ = (q ^ 2 / ell ^ 3) * (∫ x in unitCube, ‖velocity x‖ ^ 2) := by
      rw [htranslated]
      simp only [energy]
      field_simp

theorem rescaledEnergy_le_of_source_le
    (q : ℝ) (centre : Space) {ell δ E : ℝ} (hell : 0 < ell)
    {velocity : Space → Space}
    (hvelocity : IntegrableOn (fun x : Space => ‖velocity x‖ ^ 2) unitCube)
    (_hδ : 0 ≤ δ)
    (hcell : δ ≤ ∫ y in transportedCell centre ell,
      ‖rescaledVelocitySlice q ell centre velocity y‖ ^ 2)
    (hsource : (∫ x in unitCube, ‖velocity x‖ ^ 2) ≤ E) :
    δ * ell ^ 3 ≤ q ^ 2 * E := by
  rw [rescaledEnergy_integral_eq q centre hell hvelocity] at hcell
  have hell3 : 0 < ell ^ 3 := by positivity
  have hscaled : 0 ≤ q ^ 2 / ell ^ 3 := by positivity
  have hbound : δ ≤ q ^ 2 / ell ^ 3 * E :=
    hcell.trans (mul_le_mul_of_nonneg_left hsource hscaled)
  calc
    δ * ell ^ 3 ≤ (q ^ 2 / ell ^ 3 * E) * ell ^ 3 :=
      mul_le_mul_of_nonneg_right hbound hell3.le
    _ = q ^ 2 * E := by
      field_simp

theorem exponent_condition_of_rescaled_energy
    {alpha beta ell0 q0 δ E : ℝ}
    (hell0 : 0 < ell0) (_hq0 : 0 < q0) (hδ : 0 < δ) (_hE : 0 ≤ E)
    (henergy : ∀ᶠ s : ℝ in atTop,
      δ * (ell0 * Real.exp (-beta * s)) ^ 3 ≤
        (q0 * Real.exp (-alpha * s)) ^ 2 * E) :
    2 * alpha ≤ 3 * beta := by
  by_contra hcontra
  have hgap : 0 < 2 * alpha - 3 * beta := by linarith
  have hnorm : ∀ᶠ s : ℝ in atTop,
      δ * ell0 ^ 3 ≤ q0 ^ 2 * E * Real.exp ((3 * beta - 2 * alpha) * s) := by
    filter_upwards [henergy] with s hs
    have hmul := mul_le_mul_of_nonneg_right hs (Real.exp_pos (3 * beta * s)).le
    have hleft :
        δ * (ell0 * Real.exp (-beta * s)) ^ 3 * Real.exp (3 * beta * s) =
          δ * ell0 ^ 3 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      calc
        δ * (ell0 ^ 3 * Real.exp (-(3 * (beta * s)))) * Real.exp (3 * beta * s) =
            δ * ell0 ^ 3 *
              (Real.exp (-(3 * (beta * s))) * Real.exp (3 * beta * s)) := by ring
        _ = δ * ell0 ^ 3 := by
          rw [← Real.exp_add]
          rw [show -(3 * (beta * s)) + 3 * beta * s = 0 by ring, Real.exp_zero, mul_one]
    have hright :
        (q0 * Real.exp (-alpha * s)) ^ 2 * E * Real.exp (3 * beta * s) =
          q0 ^ 2 * E * Real.exp ((3 * beta - 2 * alpha) * s) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      calc
        q0 ^ 2 * Real.exp (-(2 * (alpha * s))) * E * Real.exp (3 * beta * s) =
            q0 ^ 2 * E *
              (Real.exp (-(2 * (alpha * s))) * Real.exp (3 * beta * s)) := by ring
        _ = q0 ^ 2 * E * Real.exp ((3 * beta - 2 * alpha) * s) := by
          rw [← Real.exp_add]
          congr 2
          ring
    exact hleft ▸ hright ▸ hmul
  have hlim : Tendsto (fun s : ℝ => q0 ^ 2 * E *
      Real.exp ((3 * beta - 2 * alpha) * s)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => (2 * alpha - 3 * beta) * s) atTop atTop := by
      simpa [mul_comm] using tendsto_id.atTop_mul_const hgap
    have hexp := tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have hconst : Tendsto (fun _ : ℝ => q0 ^ 2 * E) atTop (𝓝 (q0 ^ 2 * E)) :=
      tendsto_const_nhds
    have hlim' := hconst.mul hexp
    simp only [Function.comp_apply] at hlim'
    have hEq : (fun s : ℝ => q0 ^ 2 * E *
        Real.exp (-((2 * alpha - 3 * beta) * s))) =
        (fun s : ℝ => q0 ^ 2 * E * Real.exp ((3 * beta - 2 * alpha) * s)) := by
      funext s
      congr 2
      ring
    rw [hEq] at hlim'
    simpa using hlim'
  have hpos : 0 < δ * ell0 ^ 3 := by positivity
  have hlt : ∀ᶠ s : ℝ in atTop,
      q0 ^ 2 * E * Real.exp ((3 * beta - 2 * alpha) * s) < δ * ell0 ^ 3 :=
    (tendsto_order.1 hlim).2 _ hpos
  obtain ⟨s, hs, hsl⟩ := (hnorm.and hlt).exists
  linarith

theorem exponent_condition_of_actual_rescaled_energy
    {alpha beta ell0 q0 δ E : ℝ} (centre : Space)
    (hell0 : 0 < ell0) (hq0 : 0 < q0) (hδ : 0 < δ) (hE : 0 ≤ E)
    (velocity : VelocityField) (clock : ℝ → ℝ)
    (hslices : ∀ᶠ s : ℝ in atTop,
      IntegrableOn (fun x : Space => ‖velocity x (clock s)‖ ^ 2) unitCube)
    (hsource : ∀ᶠ s : ℝ in atTop,
      (∫ x in unitCube, ‖velocity x (clock s)‖ ^ 2) ≤ E)
    (hnormalized : ∀ᶠ s : ℝ in atTop,
      δ ≤ ∫ y in transportedCell centre (ell0 * Real.exp (-beta * s)),
        ‖rescaledVelocitySlice (q0 * Real.exp (-alpha * s))
          (ell0 * Real.exp (-beta * s)) centre (fun x => velocity x (clock s)) y‖ ^ 2) :
    2 * alpha ≤ 3 * beta := by
  have henergy : ∀ᶠ s : ℝ in atTop,
      δ * (ell0 * Real.exp (-beta * s)) ^ 3 ≤
        (q0 * Real.exp (-alpha * s)) ^ 2 * E := by
    filter_upwards [hslices, hsource, hnormalized] with s hslice hsource hnorm
    exact rescaledEnergy_le_of_source_le
      (q0 * Real.exp (-alpha * s)) centre
      (ell := ell0 * Real.exp (-beta * s))
      (mul_pos hell0 (Real.exp_pos _)) hslice hδ.le hnorm hsource
  exact exponent_condition_of_rescaled_energy hell0 hq0 hδ hE henergy

theorem openPeriodicSolutionOn_unitCube_energy_integrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IntegrableOn (fun x : Space => ‖velocity x t‖ ^ 2) unitCube := by
  have hcube : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hslice : ContDiff ℝ ∞ (fun x : Space => velocity x t) :=
    OpenSmoothSolutionOn.velocitySlice_contDiff solution.toOpenSmoothSolutionOn
      ⟨ht.1.le, ht.2⟩
  exact (hslice.continuous.continuousOn.norm.pow 2).integrableOn_compact hcube

theorem openPeriodicSolutionOn_unitCube_energy_le_initial
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (∫ x in unitCube, ‖velocity x t‖ ^ 2) ≤
      2 * periodicKineticEnergy velocity 0 := by
  have hkin := openPeriodicSolutionOn_periodicKineticEnergy_le_initial solution hnu ht
  unfold periodicKineticEnergy kineticEnergyDensity at hkin ⊢
  have hmul := mul_le_mul_of_nonneg_left hkin (by norm_num : (0 : ℝ) ≤ 2)
  have hrel : (∫ x in unitCube, ‖velocity x t‖ ^ 2) =
      2 * (∫ x in unitCube, (1 / 2 : ℝ) * ‖velocity x t‖ ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun
    · exact measurableSet_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
    · intro x _hx
      ring
  rw [hrel]
  exact hmul

theorem exponent_condition_of_openPeriodicSolutionOn
    {T nu alpha beta ell0 q0 δ : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (centre : Space) (clock : ℝ → ℝ)
    (hell0 : 0 < ell0) (hq0 : 0 < q0) (hδ : 0 < δ)
    (hclock : ∀ᶠ s : ℝ in atTop, clock s ∈ Ioo 0 T)
    (hnormalized : ∀ᶠ s : ℝ in atTop,
      δ ≤ ∫ y in transportedCell centre (ell0 * Real.exp (-beta * s)),
        ‖rescaledVelocitySlice (q0 * Real.exp (-alpha * s))
          (ell0 * Real.exp (-beta * s)) centre (fun x => velocity x (clock s)) y‖ ^ 2) :
    2 * alpha ≤ 3 * beta := by
  have hslices : ∀ᶠ s : ℝ in atTop,
      IntegrableOn (fun x : Space => ‖velocity x (clock s)‖ ^ 2) unitCube := by
    filter_upwards [hclock] with s hs
    exact openPeriodicSolutionOn_unitCube_energy_integrable solution hs
  have hsource : ∀ᶠ s : ℝ in atTop,
      (∫ x in unitCube, ‖velocity x (clock s)‖ ^ 2) ≤
        2 * periodicKineticEnergy velocity 0 := by
    filter_upwards [hclock] with s hs
    exact openPeriodicSolutionOn_unitCube_energy_le_initial solution hnu hs
  have hE : 0 ≤ 2 * periodicKineticEnergy velocity 0 := by
    exact (mul_nonneg (by norm_num) (periodicKineticEnergy_nonneg velocity 0))
  exact exponent_condition_of_actual_rescaled_energy centre hell0 hq0 hδ
    hE velocity clock hslices hsource hnormalized

section Audit

#print axioms transportedCell_smul_image
#print axioms integrableOn_energy_comp_translation
#print axioms rescaledEnergy_integrableOn
#print axioms rescaledEnergy_integral_eq
#print axioms rescaledEnergy_le_of_source_le
#print axioms exponent_condition_of_rescaled_energy
#print axioms exponent_condition_of_actual_rescaled_energy
#print axioms openPeriodicSolutionOn_unitCube_energy_integrable
#print axioms openPeriodicSolutionOn_unitCube_energy_le_initial
#print axioms exponent_condition_of_openPeriodicSolutionOn

end Audit

end Soma.Holonics.Millennium.NavierStokesRescaledEnergy
