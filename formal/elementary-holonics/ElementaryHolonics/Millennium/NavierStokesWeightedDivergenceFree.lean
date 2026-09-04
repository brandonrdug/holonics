import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3

/-!
# Modewise incompressibility through the native weighted restart circulation

**[proved-derived]** Sobolev weights change the receiver norm but not the incidence of a Fourier
mode with its three velocity components.  This owner keeps that mode occurrence visible through
same-order heat transport, one-derivative heat recovery, the Leray quadratic source, the
endpoint-totalized Duhamel integrand, and its actual Bochner return.

The final integral proof uses a bounded mode-divergence receiver, so incompressibility is carried
through the integral as an exact returned consequence rather than inferred from a scalar norm.
This file does not construct a mild fixed point or reconstruct a spatial PDE solution.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Actual smooth slices enter the incompressible native fibre -/

/-- Weighting an actual smooth periodic divergence-free slice changes its norm chart but retains
the exact modewise incompressibility equation. -/
theorem isModewiseDivergenceFree_smoothSliceVectorWeightedH3
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ (⊤ : ℕ∞) velocity)
    (hperiodic : IsOnePeriodic velocity)
    (hdivergence : ∀ x, divergence velocity x = 0) :
    IsModewiseDivergenceFree
      (smoothSliceVectorWeightedH3 velocity hvelocity hperiodic) := by
  intro k
  have hunweighted :=
    complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
      velocity (hvelocity.of_le (by norm_num)) hperiodic hdivergence k
  change (∑ component : Fin 3,
      complexFrequencyVector k component *
        vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k component) = 0
    at hunweighted
  change ∑ component : Fin 3,
      complexFrequencyVector k component *
        smoothSliceVectorWeightedH3 velocity hvelocity hperiodic component k = 0
  calc
    (∑ component : Fin 3,
        complexFrequencyVector k component *
          smoothSliceVectorWeightedH3 velocity hvelocity hperiodic component k) =
        (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) *
          ∑ component : Fin 3,
            complexFrequencyVector k component *
              vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k component := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro component _
      rw [smoothSliceVectorWeightedH3, smoothSliceWeightedH3Component,
        coefficientWeightedRealization_apply, smoothSliceSobolevCoefficients,
        smoothSliceFourierL2_apply]
      ring
    _ = 0 := by rw [hunweighted, mul_zero]

/-! ## The bounded receiver for one mode divergence -/

/-- Evaluation of one addressed component and Fourier mode is bounded on every native weighted
carrier. -/
def weightedModeEvaluation (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun state ↦ state component k
      map_add' := by
        intro left right
        rfl
      map_smul' := by
        intro scalar state
        rfl }
    1 (fun state ↦ by
      calc
        ‖state component k‖ ≤ ‖state component‖ :=
          lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (state component) k
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

@[simp]
theorem weightedModeEvaluation_apply
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    weightedModeEvaluation order component k state = state component k :=
  rfl

/-- The complete complex divergence at one Fourier pin as a bounded linear receiver. -/
def weightedModeDivergenceEvaluation (order : ℕ) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℂ] ℂ :=
  ∑ component : Fin 3,
    (complexFrequencyVector k component) •
      weightedModeEvaluation order component k

@[simp]
theorem weightedModeDivergenceEvaluation_apply
    (order : ℕ) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    weightedModeDivergenceEvaluation order k state =
      complexDot (complexFrequencyVector k) (vectorCoefficientAt state k) := by
  simp [weightedModeDivergenceEvaluation, complexDot, vectorCoefficientAt,
    dotProduct]

/-! ## Heat and Leray transport -/

/-- Same-order native heat transport preserves every modewise divergence constraint. -/
theorem IsModewiseDivergenceFree.periodicVectorWeightedHeat
    {order : ℕ} {state : PeriodicVectorWeightedSobolev order}
    (hstate : IsModewiseDivergenceFree state) (nu t : ℝ≥0) :
    IsModewiseDivergenceFree (periodicVectorWeightedHeat order nu t state) := by
  change IsModewiseDivergenceFree
    (infiniteVectorHeatCoefficientEvolution nu t state)
  exact infiniteVectorHeatCoefficientEvolution_preserves_divergenceFree hstate nu t

/-- Recovering one derivative multiplies all three entries of a fixed mode by the same scalar, so
it preserves the modewise divergence constraint. -/
theorem IsModewiseDivergenceFree.periodicVectorWeightedHeatTwoToThree
    {state : PeriodicVectorWeightedSobolev 2}
    (hstate : IsModewiseDivergenceFree state)
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    IsModewiseDivergenceFree
      (periodicVectorWeightedHeatTwoToThree nu t hviscous state) := by
  intro k
  change ∑ component : Fin 3,
      complexFrequencyVector k component *
        periodicWeightedHeatTwoToThree nu t hviscous (state component) k = 0
  simp_rw [periodicWeightedHeatTwoToThree_apply]
  have hsource :
      ∑ component : Fin 3,
          complexFrequencyVector k component * state component k = 0 := hstate k
  let C : ℂ :=
    (Real.sqrt (periodicSobolevWeight 3 k) : ℂ) *
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
      ((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ))
  calc
    (∑ component : Fin 3,
        complexFrequencyVector k component *
          ((Real.sqrt (periodicSobolevWeight 3 k) : ℂ) *
            ((heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
              ((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ) *
                state component k)))) =
        C * ∑ component : Fin 3,
          complexFrequencyVector k component * state component k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro component _
      dsimp [C]
      ring
    _ = 0 := by rw [hsource, mul_zero]

/-- The actual native Leray-divergence return is divergence-free at every weighted mode, for
unrestricted complex inputs. -/
theorem weightedLerayDivergenceConvolution_divergenceFree_native
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    IsModewiseDivergenceFree
      (weightedLerayDivergenceConvolution advecting transported) := by
  intro k
  change ∑ output : Fin 3,
      complexFrequencyVector k output *
        weightedLerayDivergenceConvolution advecting transported output k = 0
  simp_rw [weightedLerayDivergenceConvolution_coefficient]
  let mode : Fin 3 → ℂ := fun component ↦
    (Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear.h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree transported) component).1 k
  have hprojected :
      ∑ output : Fin 3,
          complexFrequencyVector k output * lerayProjectMode k mode output = 0 :=
    complexDot_lerayProjectMode_eq_zero k mode
  calc
    (∑ output : Fin 3,
        complexFrequencyVector k output *
          ((Real.sqrt (periodicSobolevWeight 2 k) : ℂ) *
            lerayProjectMode k mode output)) =
        (Real.sqrt (periodicSobolevWeight 2 k) : ℂ) *
          ∑ output : Fin 3,
            complexFrequencyVector k output * lerayProjectMode k mode output := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _
      ring
    _ = 0 := by rw [hprojected, mul_zero]

/-- The quadratic source inherits the unrestricted Leray divergence constraint. -/
theorem weightedLerayQuadratic_divergenceFree
    (state : PeriodicVectorWeightedSobolev 3) :
    IsModewiseDivergenceFree (weightedLerayQuadratic state) := by
  simpa [weightedLerayQuadratic] using
    weightedLerayDivergenceConvolution_divergenceFree_native state state

/-- Every endpoint-totalized Duhamel integrand is modewise divergence-free. -/
theorem weightedDuhamelIntegrand_divergenceFree
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (s : ℝ) :
    IsModewiseDivergenceFree (weightedDuhamelIntegrand nu hnu t path s) := by
  by_cases hs : s < t
  · rw [weightedDuhamelIntegrand_of_lt nu hnu t path hs]
    exact IsModewiseDivergenceFree.periodicVectorWeightedHeatTwoToThree
      (weightedLerayQuadratic_divergenceFree (path s)) nu
        (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
  · rw [weightedDuhamelIntegrand_of_not_lt nu hnu t path hs]
    intro k
    simp [complexDot, vectorCoefficientAt, dotProduct]

/-! ## Exact Bochner return -/

/-- Every honest Bochner return of the endpoint-totalized integrand preserves the complete
modewise divergence constraint. -/
theorem intervalIntegral_weightedDuhamelIntegrand_divergenceFree
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (hintegrable : IntervalIntegrable
      (weightedDuhamelIntegrand nu hnu t path) volume 0 t) :
    IsModewiseDivergenceFree
      (∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t path s) := by
  intro k
  change weightedModeDivergenceEvaluation 3 k
      (∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t path s) = 0
  rw [← (weightedModeDivergenceEvaluation 3 k).intervalIntegral_comp_comm
    hintegrable]
  have hzero :
      (fun s : ℝ ↦ weightedModeDivergenceEvaluation 3 k
        (weightedDuhamelIntegrand nu hnu t path s)) = 0 := by
    funext s
    rw [Pi.zero_apply, weightedModeDivergenceEvaluation_apply]
    exact weightedDuhamelIntegrand_divergenceFree nu hnu t path s k
  rw [hzero]
  exact intervalIntegral.integral_zero

/-- The actual variable-terminal Duhamel return is modewise divergence-free. -/
theorem weightedDuhamelReturn_divergenceFree
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IsModewiseDivergenceFree (weightedDuhamelReturn nu hnu hT path t) := by
  exact intervalIntegral_weightedDuhamelIntegrand_divergenceFree nu hnu t
    (weightedPathExtension hT path)
    (intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht)

/-- Hence every face of the returned continuous Duhamel path retains incompressibility. -/
theorem weightedDuhamelPath_divergenceFree
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : Icc (0 : ℝ) T) :
    IsModewiseDivergenceFree (weightedDuhamelPath nu hnu hT path t) := by
  rw [weightedDuhamelPath_apply]
  exact weightedDuhamelReturn_divergenceFree nu hnu hT path t.2

section Audit

#print axioms IsModewiseDivergenceFree.periodicVectorWeightedHeat
#print axioms isModewiseDivergenceFree_smoothSliceVectorWeightedH3
#print axioms IsModewiseDivergenceFree.periodicVectorWeightedHeatTwoToThree
#print axioms weightedLerayDivergenceConvolution_divergenceFree_native
#print axioms weightedDuhamelIntegrand_divergenceFree
#print axioms intervalIntegral_weightedDuhamelIntegrand_divergenceFree
#print axioms weightedDuhamelReturn_divergenceFree
#print axioms weightedDuhamelPath_divergenceFree

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
