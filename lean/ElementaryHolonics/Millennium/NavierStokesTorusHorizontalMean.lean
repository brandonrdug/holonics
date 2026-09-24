import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The horizontal mean retains the entire vertical Fourier population

The mean is a genuine compact-torus integral. Splitting off the axial circle gives its exact
Fourier coefficients. If every nonconstant axial coefficient vanishes, the full continuous mean
is constant; its remaining zero coefficient is retained rather than assigned a gauge value.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesTorusHorizontalMean
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def axialFrequency (n : ℤ) : SpatialFrequency := ![0, 0, n]

@[simp] theorem axialFrequency_zero : axialFrequency 0 = 0 := by
  ext i
  fin_cases i <;> rfl

def joinAxialTorus (z : UnitAddCircle) (horizontal : SpatialTorusTail) : SpatialTorus :=
  ![horizontal 0, horizontal 1, z]

theorem continuous_joinAxialTorus :
    Continuous (fun q : UnitAddCircle × SpatialTorusTail ↦ joinAxialTorus q.1 q.2) := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · change Continuous (fun q : UnitAddCircle × SpatialTorusTail ↦ q.2 0)
    exact (continuous_apply 0).comp continuous_snd
  · change Continuous (fun q : UnitAddCircle × SpatialTorusTail ↦ q.2 1)
    exact (continuous_apply 1).comp continuous_snd
  · change Continuous (fun q : UnitAddCircle × SpatialTorusTail ↦ q.1)
    exact continuous_fst

def splitAxialTorus : SpatialTorus ≃ᵐ UnitAddCircle × SpatialTorusTail :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ UnitAddCircle) 2

theorem splitAxialTorus_symm_apply (q : UnitAddCircle × SpatialTorusTail) :
    splitAxialTorus.symm q = joinAxialTorus q.1 q.2 := by
  change Fin.insertNth (Fin.last 2) q.1 q.2 = joinAxialTorus q.1 q.2
  rw [Fin.insertNth_last']
  ext i
  fin_cases i <;> simp [Fin.snoc, joinAxialTorus]

theorem splitAxialTorus_measurePreserving :
    MeasurePreserving splitAxialTorus (volume : Measure SpatialTorus)
      ((volume : Measure UnitAddCircle).prod (volume : Measure SpatialTorusTail)) := by
  simpa only [splitAxialTorus, volume_pi] using
    measurePreserving_piFinSuccAbove (fun _ : Fin 3 ↦ (volume : Measure UnitAddCircle)) 2

theorem mFourier_axial_join (n : ℤ) (z : UnitAddCircle) (horizontal : SpatialTorusTail) :
    UnitAddTorus.mFourier (axialFrequency n) (joinAxialTorus z horizontal) = fourier n z := by
  simp [UnitAddTorus.mFourier, axialFrequency, joinAxialTorus, Fin.prod_univ_three]

def axialSections (field : C(SpatialTorus, ℂ)) : C(SpatialTorusTail, C(UnitAddCircle, ℂ)) :=
  (field.comp ⟨fun q : SpatialTorusTail × UnitAddCircle ↦ joinAxialTorus q.2 q.1,
    continuous_joinAxialTorus.comp continuous_swap⟩).curry

def horizontalMeanTorus (field : C(SpatialTorus, ℂ)) : C(UnitAddCircle, ℂ) :=
  ∫ horizontal : SpatialTorusTail, axialSections field horizontal

theorem horizontalMeanTorus_apply (field : C(SpatialTorus, ℂ)) (z : UnitAddCircle) :
    horizontalMeanTorus field z = ∫ horizontal : SpatialTorusTail, field (joinAxialTorus z horizontal) := by
  exact ContinuousMap.integral_apply (continuousMap_integrable_on_compact (axialSections field)) z

/-- The averaging map preserves exactly the modes with zero horizontal frequency. -/
theorem horizontalMeanTorus_fourierCoeff (field : C(SpatialTorus, ℂ)) (n : ℤ) :
    fourierCoeff (horizontalMeanTorus field) n = torusSpatialFourierCoeff field (axialFrequency n) := by
  let integrand : C(SpatialTorus, ℂ) := UnitAddTorus.mFourier (-axialFrequency n) * field
  let splitIntegrand : C(UnitAddCircle × SpatialTorusTail, ℂ) :=
    integrand.comp ⟨_, continuous_joinAxialTorus⟩
  have hchange : (∫ q : SpatialTorus, integrand q) =
      ∫ q : UnitAddCircle × SpatialTorusTail, splitIntegrand q := by
    rw [Measure.volume_eq_prod]
    have h := splitAxialTorus_measurePreserving.integral_comp'
      (fun q : UnitAddCircle × SpatialTorusTail ↦ integrand (splitAxialTorus.symm q))
    simpa [splitIntegrand, splitAxialTorus_symm_apply] using h
  have hi : Integrable splitIntegrand := continuousMap_integrable_on_compact splitIntegrand
  have hneg : -axialFrequency n = axialFrequency (-n) := by ext i; fin_cases i <;> simp [axialFrequency]
  rw [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  change _ = ∫ q : SpatialTorus, integrand q
  rw [hchange]
  have hprod : (∫ q : UnitAddCircle × SpatialTorusTail, splitIntegrand q) =
      ∫ z : UnitAddCircle, ∫ horizontal : SpatialTorusTail, splitIntegrand (z, horizontal) :=
    integral_prod splitIntegrand hi
  rw [hprod]
  change (∫ z : UnitAddCircle, fourier (-n) z • horizontalMeanTorus field z) = _
  apply integral_congr_ae
  filter_upwards [] with z
  rw [horizontalMeanTorus_apply]
  change fourier (-n) z * (∫ horizontal : SpatialTorusTail, field (joinAxialTorus z horizontal)) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with horizontal
  simp [splitIntegrand, integrand, hneg, mFourier_axial_join, smul_eq_mul]

/-- Complete reconstruction of the remaining gauge fibre, without an assumed summability port. -/
theorem horizontalMeanTorus_eq_constant (field : C(SpatialTorus, ℂ))
    (hzero : ∀ n : ℤ, n ≠ 0 → torusSpatialFourierCoeff field (axialFrequency n) = 0)
    (z : UnitAddCircle) :
    horizontalMeanTorus field z = torusSpatialFourierCoeff field 0 := by
  have hc (n : ℤ) (hn : n ≠ 0) : fourierCoeff (horizontalMeanTorus field) n = 0 := by
    rw [horizontalMeanTorus_fourierCoeff, hzero n hn]
  have hs : Summable (fourierCoeff (horizontalMeanTorus field)) :=
    (hasSum_single (0 : ℤ) hc).summable
  have h := has_pointwise_sum_fourier_series_of_summable hs z
  have hsingle := hasSum_single (f := fun n : ℤ ↦
    fourierCoeff (horizontalMeanTorus field) n • fourier n z) 0
    (by intro n hn; rw [hc n hn]; simp)
  have heq := h.unique hsingle
  simpa [horizontalMeanTorus_fourierCoeff] using heq

#print axioms splitAxialTorus_measurePreserving
#print axioms horizontalMeanTorus_fourierCoeff
#print axioms horizontalMeanTorus_eq_constant
end Soma.Holonics.Millennium.NavierStokesTorusHorizontalMean
