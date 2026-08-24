import ElementaryHolonics.Millennium.NavierStokesWeightedMildInvariantRestart
import ElementaryHolonics.Millennium.NavierStokesWeightedHeatSemigroup
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear
import ElementaryHolonics.Millennium.NavierStokesScalarHeatVolterra

/-!
# The coefficientwise equation of the actual weighted mild return

**[proved-derived]** A bounded receiver unweights and evaluates one component and one Fourier
mode of the native weighted carrier.  Commuting this receiver through the actual Bochner return
exposes the precise coefficient-level Leray-divergence convolution under the heat multiplier.
Consequently every fixed point of the unforced weighted mild map satisfies the exact scalar
variation-of-constants identity at every addressed time face.

Factoring the scalar kernel through its integrating factor reduces the moving-terminal integral
to the ordinary fundamental theorem of calculus.  The returned interior-time derivative is the
exact viscous diagonal decay minus the same explicit Leray-divergence coefficient.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The bounded physical-coefficient receiver -/

/-- Unweight and evaluate one addressed component and Fourier mode as a bounded complex-linear
receiver on the native weighted vector carrier. -/
def weightedPhysicalCoefficient
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℂ] ℂ :=
  (((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ)) •
    nativeWeightedCoefficient order component k)

@[simp]
theorem weightedPhysicalCoefficient_apply
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    weightedPhysicalCoefficient order component k state =
      (weightedSobolevCoefficients order (state component)).1 k :=
  rfl

/-! ## The scalar mild return -/

/-- The homogeneous scalar heat face minus the shared ordered-time Volterra return. -/
def scalarMildReturn
    (rate : ℝ) (initial : ℂ) (source : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-rate * t) : ℂ) * initial -
    scalarHeatVolterra rate source t

/-- The shared scalar heat-Volterra law gives the exact derivative of the complete mild return. -/
theorem hasDerivAt_scalarMildReturn
    (rate : ℝ) (initial : ℂ) (source : ℝ → ℂ) (hsource : Continuous source)
    (t : ℝ) :
    HasDerivAt (scalarMildReturn rate initial source)
      (((-rate : ℝ) : ℂ) * scalarMildReturn rate initial source t - source t) t := by
  have hheat : HasDerivAt
      (fun tau : ℝ ↦ (Real.exp (-rate * tau) : ℂ))
      (((-rate : ℝ) : ℂ) * (Real.exp (-rate * t) : ℂ)) t := by
    convert (hasDerivAt_negativeRateExp rate t).ofReal_comp using 1
    norm_num
  have hreturn :=
    (hheat.mul_const initial).sub
      (hasDerivAt_scalarHeatVolterra (E := ℂ) rate hsource t)
  convert hreturn using 1
  simp only [scalarMildReturn, Complex.real_smul]
  rw [show (((-rate : ℝ) : ℂ)) = -((rate : ℝ) : ℂ) by norm_num]
  ring

/-! ## The exact coefficient of the singular heat return -/

/-- At a strictly earlier source time, physical-coefficient evaluation of the actual Duhamel
integrand is the heat multiplier times the explicit unweighted Leray-divergence coefficient. -/
theorem weightedPhysicalCoefficient_weightedDuhamelIntegrand_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (k : SpatialFrequency) {s : ℝ} (hs : s < t) :
    weightedPhysicalCoefficient 3 component k
        (weightedDuhamelIntegrand nu hnu t path s) =
      (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (path s))
          (unweightedVectorThree (path s)) component).1 k := by
  rw [weightedDuhamelIntegrand_of_lt nu hnu t path hs,
    weightedPhysicalCoefficient_apply]
  change
    (weightedSobolevCoefficients 3
      (periodicWeightedHeatTwoToThree nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs))
        (weightedLerayQuadratic (path s) component))).1 k = _
  rw [unweighted_periodicWeightedHeatTwoToThree_apply, coe_positiveElapsed,
    weightedLerayQuadratic_apply,
    unweighted_weightedLerayDivergenceConvolution_apply]

/-- The bounded physical-coefficient receiver commutes with the actual Bochner Duhamel return;
the endpoint-totalized representative differs from the displayed scalar kernel only at the
atomless terminal face. -/
theorem weightedPhysicalCoefficient_weightedDuhamelReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (component : Fin 3) (k : SpatialFrequency)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    weightedPhysicalCoefficient 3 component k
        (weightedDuhamelReturn nu hnu hT path t) =
      ∫ s in (0 : ℝ)..t,
        (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (weightedPathExtension hT path s))
            (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k := by
  let coefficient := weightedPhysicalCoefficient 3 component k
  let integrand := weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path)
  let scalarIntegrand : ℝ → ℂ := fun s ↦
    (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT path s))
        (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k
  have hintegrable : IntervalIntegrable integrand volume 0 t :=
    intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht
  have hcommute := coefficient.intervalIntegral_comp_comm hintegrable
  have hAE : (fun s : ℝ ↦ coefficient (integrand s)) =ᵐ[
      volume.restrict (Ι (0 : ℝ) t)] scalarIntegrand := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact weightedPhysicalCoefficient_weightedDuhamelIntegrand_of_lt
      nu hnu t (weightedPathExtension hT path) component k hs.2
  calc
    weightedPhysicalCoefficient 3 component k
        (weightedDuhamelReturn nu hnu hT path t) =
        coefficient (∫ s in (0 : ℝ)..t, integrand s) := by
      rfl
    _ = ∫ s in (0 : ℝ)..t, coefficient (integrand s) := hcommute.symm
    _ = ∫ s in (0 : ℝ)..t, scalarIntegrand s :=
      intervalIntegral.integral_congr_ae_restrict hAE
    _ = ∫ s in (0 : ℝ)..t,
        (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (weightedPathExtension hT path s))
            (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k := by
      rfl

/-! ## The coefficientwise fixed-point equation -/

/-- The linear heat path has exactly the expected physical Fourier coefficient. -/
theorem weightedPhysicalCoefficient_weightedLinearHeatPath
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (k : SpatialFrequency) (t : Icc (0 : ℝ) T) :
    weightedPhysicalCoefficient 3 component k
        (weightedLinearHeatPath nu hT initial t) =
      (heatStokesMultiplier (nu : ℝ) t.1 k : ℂ) *
        (weightedSobolevCoefficients 3 (initial component)).1 k := by
  rw [weightedPhysicalCoefficient_apply]
  change
    (weightedSobolevCoefficients 3
      (periodicWeightedHeat 3 nu (Real.toNNReal t.1) (initial component))).1 k = _
  rw [unweighted_periodicWeightedHeat_apply,
    Real.coe_toNNReal _ t.2.1]

/-- **Exact scalar mild identity.**  Every fixed point of the actual native mild map, evaluated
at any component and mode, is the heat-transported physical initial coefficient minus the actual
heat-transported unweighted Leray-divergence convolution. -/
theorem fixedPoint_weightedMildMap_physicalCoefficient
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    (component : Fin 3) (k : SpatialFrequency) (t : Icc (0 : ℝ) T) :
    (weightedSobolevCoefficients 3 (path t component)).1 k =
      (heatStokesMultiplier (nu : ℝ) t.1 k : ℂ) *
          (weightedSobolevCoefficients 3 (initial component)).1 k -
        ∫ s in (0 : ℝ)..t.1,
          (heatStokesMultiplier (nu : ℝ) (t.1 - s) k : ℂ) *
            (lerayProjectedH3DivergenceConvolution
              (unweightedVectorThree (weightedPathExtension hT path s))
              (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k := by
  have hface := congrArg
    (fun candidate : WeightedH3Path T ↦
      weightedPhysicalCoefficient 3 component k (candidate t)) hfixed
  calc
    (weightedSobolevCoefficients 3 (path t component)).1 k =
        weightedPhysicalCoefficient 3 component k
          (weightedMildMap nu hnu hT initial path t) := by
      simpa only [weightedPhysicalCoefficient_apply] using hface.symm
    _ = weightedPhysicalCoefficient 3 component k
        (weightedLinearHeatPath nu hT initial t -
          weightedDuhamelPath nu hnu hT path t) := by
      rfl
    _ = weightedPhysicalCoefficient 3 component k
          (weightedLinearHeatPath nu hT initial t) -
        weightedPhysicalCoefficient 3 component k
          (weightedDuhamelPath nu hnu hT path t) := by
      rw [map_sub]
    _ = (heatStokesMultiplier (nu : ℝ) t.1 k : ℂ) *
          (weightedSobolevCoefficients 3 (initial component)).1 k -
        ∫ s in (0 : ℝ)..t.1,
          (heatStokesMultiplier (nu : ℝ) (t.1 - s) k : ℂ) *
            (lerayProjectedH3DivergenceConvolution
              (unweightedVectorThree (weightedPathExtension hT path s))
              (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k := by
      rw [weightedPhysicalCoefficient_weightedLinearHeatPath,
        weightedDuhamelPath_apply,
        weightedPhysicalCoefficient_weightedDuhamelReturn
          nu hnu hT path component k t.2]

/-! ## The coefficientwise interior-time ODE -/

/-- The explicit physical Leray-divergence coefficient varies continuously along the endpoint
extension of every native continuous path. -/
theorem continuous_weightedPathLerayPhysicalCoefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (component : Fin 3) (k : SpatialFrequency) :
    Continuous (fun s : ℝ ↦
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT path s))
        (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k) := by
  have hquadratic : Continuous (fun s : ℝ ↦
      weightedLerayQuadratic (weightedPathExtension hT path s)) :=
    continuous_weightedLerayQuadratic.comp (weightedPathExtension hT path).continuous
  have hcoefficient :=
    (weightedPhysicalCoefficient 2 component k).continuous.comp hquadratic
  convert hcoefficient using 1
  funext s
  change
    (lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (weightedPathExtension hT path s))
      (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k =
      weightedPhysicalCoefficient 2 component k
        (weightedLerayQuadratic (weightedPathExtension hT path s))
  rw [weightedPhysicalCoefficient_apply, weightedLerayQuadratic_apply,
    unweighted_weightedLerayDivergenceConvolution_apply]

/-- The exact scalar mild identity is the shared heat-Volterra return with decay rate
`nu * lambda_k`. -/
theorem fixedPoint_weightedMildMap_physicalCoefficient_eq_scalarMildReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    (component : Fin 3) (k : SpatialFrequency) (t : Icc (0 : ℝ) T) :
    (weightedSobolevCoefficients 3 (path t component)).1 k =
      scalarMildReturn
        ((nu : ℝ) * torusStokesEigenvalue k)
        ((weightedSobolevCoefficients 3 (initial component)).1 k)
        (fun s : ℝ ↦
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (weightedPathExtension hT path s))
            (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k)
        t.1 := by
  have hmild := fixedPoint_weightedMildMap_physicalCoefficient
    nu hnu hT initial path hfixed component k t
  have hexponent : ∀ x : ℝ,
      -((nu : ℝ) * x * torusStokesEigenvalue k) =
        (-((nu : ℝ) * torusStokesEigenvalue k)) * x := by
    intro x
    ring
  simpa only [scalarMildReturn, scalarHeatVolterra, heatStokesMultiplier,
    Complex.real_smul, hexponent] using hmild

/-- **Exact coefficientwise ODE.**  At every interior time, the unweighted Fourier coefficient
of a mild fixed point is differentiable.  Its derivative is viscous diagonal decay minus the
actual unweighted Leray-divergence convolution coefficient at that same face. -/
theorem fixedPoint_weightedMildMap_physicalCoefficient_hasDerivAt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        (weightedSobolevCoefficients 3
          (weightedPathExtension hT path tau component)).1 k)
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (weightedPathExtension hT path t component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (weightedPathExtension hT path t))
          (unweightedVectorThree (weightedPathExtension hT path t)) component).1 k) t := by
  let source : ℝ → ℂ := fun s ↦
    (lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (weightedPathExtension hT path s))
      (unweightedVectorThree (weightedPathExtension hT path s)) component).1 k
  let rate : ℝ := (nu : ℝ) * torusStokesEigenvalue k
  let initialCoefficient : ℂ :=
    (weightedSobolevCoefficients 3 (initial component)).1 k
  have hsource : Continuous source := by
    exact continuous_weightedPathLerayPhysicalCoefficient hT path component k
  have hvolterra := hasDerivAt_scalarMildReturn
    rate initialCoefficient source hsource t
  have heqOn : ∀ tau ∈ Icc (0 : ℝ) T,
      weightedPhysicalCoefficient 3 component k
          (weightedPathExtension hT path tau) =
        scalarMildReturn rate initialCoefficient source tau := by
    intro tau htau
    rw [weightedPathExtension_of_mem hT path htau,
      weightedPhysicalCoefficient_apply]
    exact fixedPoint_weightedMildMap_physicalCoefficient_eq_scalarMildReturn
      nu hnu hT initial path hfixed component k ⟨tau, htau⟩
  have heventually :
      (fun tau : ℝ ↦ weightedPhysicalCoefficient 3 component k
        (weightedPathExtension hT path tau)) =ᶠ[𝓝 t]
      scalarMildReturn rate initialCoefficient source := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with tau htau
    exact heqOn tau htau
  have hphysical := hvolterra.congr_of_eventuallyEq heventually
  have heqAt := heqOn t ⟨ht.1.le, ht.2.le⟩
  rw [← heqAt] at hphysical
  simpa only [weightedPhysicalCoefficient_apply, source, rate] using hphysical

section Audit

#print axioms weightedPhysicalCoefficient
#print axioms weightedPhysicalCoefficient_apply
#print axioms scalarMildReturn
#print axioms hasDerivAt_scalarMildReturn
#print axioms weightedPhysicalCoefficient_weightedDuhamelIntegrand_of_lt
#print axioms weightedPhysicalCoefficient_weightedDuhamelReturn
#print axioms weightedPhysicalCoefficient_weightedLinearHeatPath
#print axioms fixedPoint_weightedMildMap_physicalCoefficient
#print axioms continuous_weightedPathLerayPhysicalCoefficient
#print axioms fixedPoint_weightedMildMap_physicalCoefficient_eq_scalarMildReturn
#print axioms fixedPoint_weightedMildMap_physicalCoefficient_hasDerivAt

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
