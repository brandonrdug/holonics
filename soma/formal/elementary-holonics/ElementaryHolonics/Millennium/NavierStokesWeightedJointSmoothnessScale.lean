import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap

/-!
# Scale-wise time bootstrap for a coherent weighted mild tower

**[proved-derived]** This owner lifts the native first-time argument from `H³` to every member
of the coherent Sobolev scale.  Two adjacent bounded derivative passages realize the Stokes
operator at the requested order, while the next-order bounded Leray--divergence passage realizes
the quadratic source.  The exact modal fixed equation is transported to each coherent lift by
bounded coefficient evaluation and the Banach-valued FTC.
-/

noncomputable section

open Function Set Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The bounded scale-indexed projected vector field -/

/-- One diagonal second spatial derivative from native order `m+5` to native order `m+3`. -/
def diagonalSecondDerivativeAtOrder
    (m : ℕ) (coordinate : Fin 3) :
    PeriodicVectorWeightedSobolev (m + 2 + 3) →L[ℂ]
      PeriodicVectorWeightedSobolev (m + 3) :=
  (periodicVectorWeightedSobolevDerivativeSuccThreeCLM m coordinate).comp
    (periodicVectorWeightedSobolevDerivativeSuccThreeCLM (m + 1) coordinate)

/-- The scale-indexed projected momentum state in native order `m+3`. -/
def nativeProjectedTimeDerivativeAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) (t : Icc (0 : ℝ) T) :
    PeriodicVectorWeightedSobolev (m + 3) :=
  (nu : ℂ) •
      (∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate (tower.lift (m + 2) t)) -
    periodicVectorWeightedLerayDivergenceConvolution
      (m + 4) (by omega) (tower.lift (m + 1) t) (tower.lift (m + 1) t)

/-- The order-`m+4` quadratic lift spends one derivative and retains exactly the projected
base-path coefficient. -/
theorem higherLeraySourceAtOrder_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m : ℕ) (t : Icc (0 : ℝ) T)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (periodicVectorWeightedLerayDivergenceConvolution
        (m + 4) (by omega) (tower.lift (m + 1) t)
          (tower.lift (m + 1) t) component)).1 k =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k := by
  have hhigh := congrFun
    (vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      (m + 4) (by omega) (tower.lift (m + 1) t)
        (tower.lift (m + 1) t) k) component
  have hbase := congrFun
    (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) k) component
  have hhigh' :
      vectorCoefficientAt
        (nativeVectorUnderlyingAtOrder (m + 3)
          (periodicVectorWeightedLerayDivergenceConvolution
            (m + 4) (by omega) (tower.lift (m + 1) t)
              (tower.lift (m + 1) t))) k component =
        NavierStokesMildFourierNonlinearity.lerayProjectMode k
          (fun output ↦ ∑ coordinate : Fin 3,
            (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
              (∑' p,
                (weightedSobolevCoefficients (m + 4)
                  (tower.lift (m + 1) t coordinate)).1 p *
                (weightedSobolevCoefficients (m + 4)
                  (tower.lift (m + 1) t output)).1 (k - p))) component := by
    simpa only [show m + 4 - 1 = m + 3 by omega] using hhigh
  change
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (m + 3)
        (periodicVectorWeightedLerayDivergenceConvolution
          (m + 4) (by omega) (tower.lift (m + 1) t)
            (tower.lift (m + 1) t))) k component =
      vectorCoefficientAt
        (periodicVectorSobolevTwoUnderlying
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (base t))
            (unweightedVectorThree (base t)))) k component
  rw [hhigh', hbase]
  congr 1
  funext output
  rw [h3DivergenceConvolution_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  congr 1
  apply tsum_congr
  intro p
  rw [tower.weightedSobolevCoefficients_lift_eq_base,
    tower.weightedSobolevCoefficients_lift_eq_base]
  rfl

/-- Exact coefficient multiplier of one scale-indexed diagonal second derivative. -/
theorem weightedSobolevCoefficients_diagonalSecondDerivativeAtOrder
    (m : ℕ) (coordinate : Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 2 + 3))
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (diagonalSecondDerivativeAtOrder m coordinate state component)).1 k =
      coordinateFourierMultiplier coordinate k ^ 2 *
        (weightedSobolevCoefficients (m + 2 + 3)
          (state component)).1 k := by
  rw [diagonalSecondDerivativeAtOrder, ContinuousLinearMap.comp_apply,
    weightedSobolevCoefficients_periodicVectorWeightedSobolevDerivativeSuccThreeCLM_apply,
    weightedSobolevCoefficients_periodicVectorWeightedSobolevDerivativeSuccThreeCLM_apply]
  ring

/-- The sum of the scale-indexed diagonal second derivative symbols is the negative Stokes
eigenvalue. -/
theorem sum_coordinateFourierMultiplier_sq
    (k : SpatialFrequency) :
    (∑ coordinate : Fin 3, coordinateFourierMultiplier coordinate k ^ 2) =
      -(torusStokesEigenvalue k : ℂ) := by
  have h :=
    Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum.sum_orderedDerivativeMultiplier_diagonalSecondWord k
  simpa [
    Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum.diagonalSecondWord,
    orderedDerivativeMultiplier, pow_two] using h

/-- Every unweighted coefficient of the scale-indexed native jet is the same projected modal
momentum coefficient carried by the base fixed path. -/
theorem weightedSobolevCoefficients_nativeProjectedTimeDerivativeAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) (t : Icc (0 : ℝ) T)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (nativeProjectedTimeDerivativeAtOrder tower nu m t component)).1 k =
      ((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3 (base t component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base t))
          (unweightedVectorThree (base t)) component).1 k := by
  unfold nativeProjectedTimeDerivativeAtOrder
  have hsource := higherLeraySourceAtOrder_coefficient_eq_base
    tower m t component k
  have hdiagonal : ∀ coordinate : Fin 3,
      (weightedSobolevCoefficients (m + 3)
        (diagonalSecondDerivativeAtOrder m coordinate
          (tower.lift (m + 2) t) component)).1 k =
        coordinateFourierMultiplier coordinate k ^ 2 *
          (weightedSobolevCoefficients 3 (base t component)).1 k := by
    intro coordinate
    rw [weightedSobolevCoefficients_diagonalSecondDerivativeAtOrder,
      tower.weightedSobolevCoefficients_lift_eq_base]
  change
    ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
      ((nu : ℂ) *
          (∑ coordinate : Fin 3,
            diagonalSecondDerivativeAtOrder m coordinate
              (tower.lift (m + 2) t) component k) -
        periodicVectorWeightedLerayDivergenceConvolution
          (m + 4) (by omega) (tower.lift (m + 1) t)
            (tower.lift (m + 1) t) component k)) = _
  have hviscous :
      ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
        (∑ coordinate : Fin 3,
          diagonalSecondDerivativeAtOrder m coordinate
            (tower.lift (m + 2) t) component k)) =
        -(torusStokesEigenvalue k : ℂ) *
          (weightedSobolevCoefficients 3 (base t component)).1 k := by
    have hdiagonalRaw : ∀ coordinate : Fin 3,
        ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
          diagonalSecondDerivativeAtOrder m coordinate
            (tower.lift (m + 2) t) component k) =
          coordinateFourierMultiplier coordinate k ^ 2 *
            (weightedSobolevCoefficients 3 (base t component)).1 k := by
      intro coordinate
      exact hdiagonal coordinate
    rw [Finset.mul_sum]
    simp_rw [hdiagonalRaw]
    rw [← Finset.sum_mul, sum_coordinateFourierMultiplier_sq]
  calc
    ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
        ((nu : ℂ) *
            (∑ coordinate : Fin 3,
              diagonalSecondDerivativeAtOrder m coordinate
                (tower.lift (m + 2) t) component k) -
          periodicVectorWeightedLerayDivergenceConvolution
            (m + 4) (by omega) (tower.lift (m + 1) t)
              (tower.lift (m + 1) t) component k)) =
      (nu : ℂ) *
          (-(torusStokesEigenvalue k : ℂ) *
            (weightedSobolevCoefficients 3 (base t component)).1 k) -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base t))
          (unweightedVectorThree (base t)) component).1 k := by
      calc
        ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
            ((nu : ℂ) *
                (∑ coordinate : Fin 3,
                  diagonalSecondDerivativeAtOrder m coordinate
                    (tower.lift (m + 2) t) component k) -
              periodicVectorWeightedLerayDivergenceConvolution
                (m + 4) (by omega) (tower.lift (m + 1) t)
                  (tower.lift (m + 1) t) component k)) =
          (nu : ℂ) *
              ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
                (∑ coordinate : Fin 3,
                  diagonalSecondDerivativeAtOrder m coordinate
                    (tower.lift (m + 2) t) component k)) -
            ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
              periodicVectorWeightedLerayDivergenceConvolution
                (m + 4) (by omega) (tower.lift (m + 1) t)
                  (tower.lift (m + 1) t) component k) := by ring
        _ = _ := by
          change (nu : ℂ) *
                ((((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
                  (∑ coordinate : Fin 3,
                    diagonalSecondDerivativeAtOrder m coordinate
                      (tower.lift (m + 2) t) component k)) -
              (weightedSobolevCoefficients (m + 3)
                (periodicVectorWeightedLerayDivergenceConvolution
                  (m + 4) (by omega) (tower.lift (m + 1) t)
                    (tower.lift (m + 1) t) component)).1 k = _
          rw [hviscous, hsource]
    _ = _ := by
      have hnuCast : (nu : ℂ) = ((nu : ℝ) : ℂ) := rfl
      rw [hnuCast]
      push_cast
      ring

/-! ## Continuous scale paths and strong derivatives -/

/-- The scale-indexed projected momentum state is a continuous addressed path. -/
def nativeProjectedTimeDerivativePathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) : WeightedSobolevPath T (m + 3) where
  toFun t := nativeProjectedTimeDerivativeAtOrder tower nu m t
  continuous_toFun := by
    have hviscous : Continuous (fun t : Icc (0 : ℝ) T ↦
        ∑ coordinate : Fin 3,
          diagonalSecondDerivativeAtOrder m coordinate
            (tower.lift (m + 2) t)) := by
      apply continuous_finset_sum
      intro coordinate _
      exact (diagonalSecondDerivativeAtOrder m coordinate).continuous.comp
        (tower.lift (m + 2)).continuous
    have hsource : Continuous (fun t : Icc (0 : ℝ) T ↦
        periodicVectorWeightedLerayDivergenceConvolution
          (m + 4) (by omega) (tower.lift (m + 1) t)
            (tower.lift (m + 1) t)) := by
      simpa only [periodicVectorWeightedLerayDivergenceConvolutionContinuous_apply,
        show m + 4 - 1 = m + 3 by omega] using
        ((periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (m + 4) (by omega)).continuous.comp
            (tower.lift (m + 1)).continuous).clm_apply
              (tower.lift (m + 1)).continuous
    exact (continuous_const.smul hviscous).sub hsource

@[simp]
theorem nativeProjectedTimeDerivativePathAtOrder_apply
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) (t : Icc (0 : ℝ) T) :
    nativeProjectedTimeDerivativePathAtOrder tower nu m t =
      nativeProjectedTimeDerivativeAtOrder tower nu m t :=
  rfl

/-- Endpoint projection of the coherent order-`m+3` lift. -/
def smoothTowerLiftExtension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) :
    C(ℝ, PeriodicVectorWeightedSobolev (m + 3)) :=
  ContinuousMap.IccExtend hT (tower.lift m)

/-- Endpoint projection preserves the exact coefficient coherence with the base path at every
real time. -/
theorem weightedSobolevCoefficients_smoothTowerLiftExtension_eq_base
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : ℝ) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (smoothTowerLiftExtension hT tower m t component)).1 k =
      (weightedSobolevCoefficients 3
        (weightedPathExtension hT base t component)).1 k := by
  change
    (weightedSobolevCoefficients (m + 3)
      (tower.lift m (Set.projIcc 0 T hT t) component)).1 k =
      (weightedSobolevCoefficients 3
        (base (Set.projIcc 0 T hT t) component)).1 k
  exact tower.weightedSobolevCoefficients_lift_eq_base
    m (Set.projIcc 0 T hT t) component k

/-- **Scale-wise strong first-time bootstrap.** Every coherent native lift is genuinely
differentiable in interior time, and its derivative is the exact bounded projected momentum
state at the same Sobolev order. -/
theorem hasDerivAt_smoothTowerLiftExtension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau ↦ smoothTowerLiftExtension hT tower m tau)
      (ContinuousMap.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m) t) t := by
  let f : ℝ → PeriodicVectorWeightedSobolev (m + 3) :=
    fun tau ↦ smoothTowerLiftExtension hT tower m tau
  let g : ℝ → PeriodicVectorWeightedSobolev (m + 3) :=
    fun tau ↦ ContinuousMap.IccExtend hT
      (nativeProjectedTimeDerivativePathAtOrder tower nu m) tau
  have hf : Continuous f := (smoothTowerLiftExtension hT tower m).continuous
  have hg : Continuous g :=
    (ContinuousMap.IccExtend hT
      (nativeProjectedTimeDerivativePathAtOrder tower nu m)).continuous
  have hcoefficientDerivative : ∀ (component : Fin 3) (k : SpatialFrequency)
      {s : ℝ}, s ∈ Ioo (0 : ℝ) T →
      HasDerivAt
        (fun tau ↦ weightedVectorSobolevCoefficientCLM
          (m + 3) component k (f tau))
        (weightedVectorSobolevCoefficientCLM (m + 3) component k (g s)) s := by
    intro component k s hs
    have hmodal :=
      fixedPoint_weightedMildMap_reconstructedCoefficient_hasDerivAt_projected
        nu hnu hT initial hfixed hreal component k hs
    have hfunction :
        (fun tau ↦ weightedVectorSobolevCoefficientCLM
          (m + 3) component k (f tau)) =
        (fun tau ↦ weightedReconstructedVelocityCoefficient
          hT base component k tau) := by
      funext tau
      rw [weightedVectorSobolevCoefficientCLM_apply,
        weightedSobolevCoefficients_smoothTowerLiftExtension_eq_base]
      exact (weightedReconstructedVelocityCoefficient_eq_native
        hT hreal component k tau).symm
    rw [hfunction]
    convert hmodal using 1
    dsimp only [g]
    rw [weightedVectorSobolevCoefficientCLM_apply,
      show ContinuousMap.IccExtend hT
          (nativeProjectedTimeDerivativePathAtOrder tower nu m) s =
        nativeProjectedTimeDerivativePathAtOrder tower nu m
          ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ by
        change Set.IccExtend hT
          (nativeProjectedTimeDerivativePathAtOrder tower nu m) s = _
        exact Set.IccExtend_of_mem hT _ ⟨hs.1.le, hs.2.le⟩,
      nativeProjectedTimeDerivativePathAtOrder_apply,
      weightedSobolevCoefficients_nativeProjectedTimeDerivativeAtOrder]
  letI : SecondCountableTopologyEither ℝ
      (PeriodicVectorWeightedSobolev (m + 3)) :=
    ⟨Or.inl inferInstance⟩
  have hmodel : HasDerivAt
      (fun y ↦ f t + ∫ s in t..y, g s)
      (g t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable t t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt).const_add (f t)
  have heventually :
      f =ᶠ[nhds t] (fun y ↦ f t + ∫ s in t..y, g s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    apply periodicVectorWeightedSobolev_eq_of_coefficients_eq
    intro component k
    let L := weightedVectorSobolevCoefficientCLM (m + 3) component k
    have hinside : uIcc t y ⊆ Ioo (0 : ℝ) T := by
      intro s hs
      exact ⟨(lt_min ht.1 hy.1).trans_le hs.1,
        hs.2.trans_lt (max_lt ht.2 hy.2)⟩
    have hderiv : ∀ s ∈ uIcc t y,
        HasDerivAt (fun tau ↦ L (f tau)) (L (g s)) s := by
      intro s hs
      exact hcoefficientDerivative component k (hinside hs)
    have hgintegrable : IntervalIntegrable g MeasureTheory.volume t y :=
      hg.intervalIntegrable t y
    have hcoefficientFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((L.continuous.comp hg).intervalIntegrable t y)
    change L (f y) = L (f t + ∫ s in t..y, g s)
    rw [L.map_add, ← L.intervalIntegral_comp_comm hgintegrable,
      hcoefficientFTC]
    abel
  change HasDerivAt f (g t) t
  exact hmodel.congr_of_eventuallyEq heventually

/-- The same strong native derivative reaches the initial face as a genuine right derivative on
the half-open restart aperture.  No differentiability of the endpoint projection to negative
times is asserted: the proof first recovers the Banach-valued integral identity from the interior
modal equation, then applies the one-sided FTC at zero. -/
theorem hasDerivWithinAt_smoothTowerLiftExtension_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt
      (fun tau ↦ smoothTowerLiftExtension hT tower m tau)
      (ContinuousMap.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m) t)
      (Ico (0 : ℝ) T) t := by
  rcases ht.1.eq_or_lt with rfl | htpos
  · let f : ℝ → PeriodicVectorWeightedSobolev (m + 3) :=
      fun tau ↦ smoothTowerLiftExtension hT tower m tau
    let g : ℝ → PeriodicVectorWeightedSobolev (m + 3) := fun tau ↦
      ContinuousMap.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m) tau
    have hf : Continuous f := (smoothTowerLiftExtension hT tower m).continuous
    have hg : Continuous g :=
      (ContinuousMap.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m)).continuous
    have hidentity : ∀ y ∈ Ico (0 : ℝ) T,
        f y = f 0 + ∫ s in (0 : ℝ)..y, g s := by
      intro y hy
      rcases hy.1.eq_or_lt with rfl | hypos
      · simp
      · apply periodicVectorWeightedSobolev_eq_of_coefficients_eq
        intro component k
        let L := weightedVectorSobolevCoefficientCLM (m + 3) component k
        have hderiv : ∀ s ∈ Ioo (0 : ℝ) y,
            HasDerivAt (fun tau ↦ L (f tau)) (L (g s)) s := by
          intro s hs
          have hsT : s ∈ Ioo (0 : ℝ) T :=
            ⟨hs.1, hs.2.trans hy.2⟩
          have hinner : HasDerivAt f (g s) s := by
            simpa only [f, g] using
              hasDerivAt_smoothTowerLiftExtension
                hT tower nu hnu initial hfixed hreal m hsT
          exact ((L.restrictScalars ℝ).hasFDerivAt :
            HasFDerivAt L (L.restrictScalars ℝ) (f s)).comp_hasDerivAt s hinner
        have hcoefficientFTC :
            ∫ s in (0 : ℝ)..y, L (g s) = L (f y) - L (f 0) := by
          simpa only [Function.comp_apply] using
            intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.1
            ((L.continuous.comp hf).continuousOn) hderiv
            ((L.continuous.comp hg).intervalIntegrable 0 y)
        change L (f y) = L (f 0 + ∫ s in (0 : ℝ)..y, g s)
        rw [L.map_add, ← L.intervalIntegral_comp_comm
          (hg.intervalIntegrable 0 y), hcoefficientFTC]
        abel
    letI : SecondCountableTopologyEither ℝ
        (PeriodicVectorWeightedSobolev (m + 3)) :=
      ⟨Or.inl inferInstance⟩
    have hmodel : HasDerivAt
        (fun y ↦ f 0 + ∫ s in (0 : ℝ)..y, g s) (g 0) 0 := by
      exact (intervalIntegral.integral_hasDerivAt_right
        (hg.intervalIntegrable 0 0)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter
        hg.continuousAt).const_add (f 0)
    have heventually : f =ᶠ[nhdsWithin 0 (Ico (0 : ℝ) T)]
        (fun y ↦ f 0 + ∫ s in (0 : ℝ)..y, g s) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hidentity y hy
    change HasDerivWithinAt f (g 0) (Ico (0 : ℝ) T) 0
    exact hmodel.hasDerivWithinAt.congr_of_eventuallyEq heventually (by simp)
  · have hinterior : t ∈ Ioo (0 : ℝ) T := ⟨htpos, ht.2⟩
    have hderiv := hasDerivAt_smoothTowerLiftExtension
      hT tower nu hnu initial hfixed hreal m hinterior
    exact hderiv.hasDerivWithinAt

/-! ## All finite time orders on the complete Sobolev scale -/

/-- The same scale-indexed vector field, expressed through the globally endpoint-projected lift
paths.  On the addressed aperture it is literally the derivative path above. -/
def nativeProjectedVectorFieldExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) (t : ℝ) : PeriodicVectorWeightedSobolev (m + 3) :=
  (nu : ℂ) •
      (∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate
          (smoothTowerLiftExtension hT tower (m + 2) t)) -
    periodicVectorWeightedLerayDivergenceConvolution
      (m + 4) (by omega)
        (smoothTowerLiftExtension hT tower (m + 1) t)
        (smoothTowerLiftExtension hT tower (m + 1) t)

theorem nativeProjectedVectorFieldExtensionAtOrder_of_mem
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t =
      ContinuousMap.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m) t := by
  change
    (nu : ℂ) •
        (∑ coordinate : Fin 3,
          diagonalSecondDerivativeAtOrder m coordinate
            (tower.lift (m + 2) (Set.projIcc 0 T hT t))) -
      periodicVectorWeightedLerayDivergenceConvolution
        (m + 4) (by omega)
          (tower.lift (m + 1) (Set.projIcc 0 T hT t))
          (tower.lift (m + 1) (Set.projIcc 0 T hT t)) =
      Set.IccExtend hT
        (nativeProjectedTimeDerivativePathAtOrder tower nu m) t
  rw [Set.IccExtend_of_mem hT _ ht]
  have hproj : Set.projIcc 0 T hT t = ⟨t, ht⟩ := by
    apply Subtype.ext
    simp [Set.projIcc, ht.1, ht.2]
  rw [hproj]
  rfl

/-- The initial-face derivative receipt, expressed by the globally defined scale-indexed vector
field used in the smoothness induction. -/
theorem hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt
      (fun tau ↦ smoothTowerLiftExtension hT tower m tau)
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)
      (Ico (0 : ℝ) T) t := by
  rw [nativeProjectedVectorFieldExtensionAtOrder_of_mem
    hT tower nu m ⟨ht.1, ht.2.le⟩]
  exact hasDerivWithinAt_smoothTowerLiftExtension_Ico
    hT tower nu hnu initial hfixed hreal m ht

/-- The scale-indexed projected vector field preserves every finite time differentiability
order carried by the two higher lift paths. -/
theorem contDiffOn_nativeProjectedVectorFieldExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (n m : ℕ)
    (hlifts : ∀ q : ℕ, ContDiffOn ℝ n
      (fun t ↦ smoothTowerLiftExtension hT tower q t)
      (Ioo (0 : ℝ) T)) :
    ContDiffOn ℝ n
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m)
      (Ioo (0 : ℝ) T) := by
  have hviscous : ContDiffOn ℝ n (fun t ↦
      ∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate
          (smoothTowerLiftExtension hT tower (m + 2) t))
      (Ioo (0 : ℝ) T) := by
    apply ContDiffOn.sum
    intro coordinate _
    exact (diagonalSecondDerivativeAtOrder m coordinate).restrictScalars ℝ
      |>.contDiff.comp_contDiffOn (hlifts (m + 2))
  let B : PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
      PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 3) :=
    (periodicVectorWeightedLerayDivergenceConvolutionContinuous
      (m + 4) (by omega)).bilinearRestrictScalars ℝ
  have hsource : ContDiffOn ℝ n (fun t ↦
      periodicVectorWeightedLerayDivergenceConvolution
        (m + 4) (by omega)
          (smoothTowerLiftExtension hT tower (m + 1) t)
          (smoothTowerLiftExtension hT tower (m + 1) t))
      (Ioo (0 : ℝ) T) := by
    have hoperator : ContDiffOn ℝ n (fun t ↦
        B (smoothTowerLiftExtension hT tower (m + 1) t))
        (Ioo (0 : ℝ) T) :=
      B.contDiff.comp_contDiffOn (hlifts (m + 1))
    simpa only [B,
      ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      periodicVectorWeightedLerayDivergenceConvolutionContinuous_apply] using
        hoperator.clm_apply (hlifts (m + 1))
  exact (hviscous.const_smul (nu : ℂ)).sub hsource

/-- The same bounded scale vector field preserves finite differentiability on the one-sided
restart aperture. -/
theorem contDiffOn_nativeProjectedVectorFieldExtensionAtOrder_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (n m : ℕ)
    (hlifts : ∀ q : ℕ, ContDiffOn ℝ n
      (fun t ↦ smoothTowerLiftExtension hT tower q t)
      (Ico (0 : ℝ) T)) :
    ContDiffOn ℝ n
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m)
      (Ico (0 : ℝ) T) := by
  have hviscous : ContDiffOn ℝ n (fun t ↦
      ∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate
          (smoothTowerLiftExtension hT tower (m + 2) t))
      (Ico (0 : ℝ) T) := by
    apply ContDiffOn.sum
    intro coordinate _
    exact (diagonalSecondDerivativeAtOrder m coordinate).restrictScalars ℝ
      |>.contDiff.comp_contDiffOn (hlifts (m + 2))
  let B : PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
      PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 3) :=
    (periodicVectorWeightedLerayDivergenceConvolutionContinuous
      (m + 4) (by omega)).bilinearRestrictScalars ℝ
  have hsource : ContDiffOn ℝ n (fun t ↦
      periodicVectorWeightedLerayDivergenceConvolution
        (m + 4) (by omega)
          (smoothTowerLiftExtension hT tower (m + 1) t)
          (smoothTowerLiftExtension hT tower (m + 1) t))
      (Ico (0 : ℝ) T) := by
    have hoperator : ContDiffOn ℝ n (fun t ↦
        B (smoothTowerLiftExtension hT tower (m + 1) t))
        (Ico (0 : ℝ) T) :=
      B.contDiff.comp_contDiffOn (hlifts (m + 1))
    simpa only [B,
      ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      periodicVectorWeightedLerayDivergenceConvolutionContinuous_apply] using
        hoperator.clm_apply (hlifts (m + 1))
  exact (hviscous.const_smul (nu : ℂ)).sub hsource

/-- **All finite native time orders.**  Every member of the coherent Sobolev tower is `C^n` in
interior time for every finite `n`.  The induction differentiates the one scale-indexed vector
field; it does not introduce an assumed hierarchy of time jets. -/
theorem contDiffOn_smoothTowerLiftExtension_allFiniteOrders
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ∀ (n m : ℕ), ContDiffOn ℝ n
      (fun t ↦ smoothTowerLiftExtension hT tower m t)
      (Ioo (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro m
      simpa only using (contDiffOn_zero.mpr
        (smoothTowerLiftExtension hT tower m).continuous.continuousOn)
  | succ n ih =>
      intro m
      rw [show ((↑(n + 1) : WithTop ℕ∞)) =
          ((↑n : WithTop ℕ∞) + 1) by norm_num,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact (hasDerivAt_smoothTowerLiftExtension
          hT tower nu hnu initial hfixed hreal m ht).differentiableAt.differentiableWithinAt
      · intro htop
        norm_num at htop
      · have hfield := contDiffOn_nativeProjectedVectorFieldExtensionAtOrder
          hT tower nu n m ih
        apply hfield.congr
        intro t ht
        rw [(hasDerivAt_smoothTowerLiftExtension
          hT tower nu hnu initial hfixed hreal m ht).deriv]
        exact (nativeProjectedVectorFieldExtensionAtOrder_of_mem
          hT tower nu m ⟨ht.1.le, ht.2.le⟩).symm

/-- Each coherent lift is therefore genuinely `C∞` in interior time. -/
theorem contDiffOn_infty_smoothTowerLiftExtension
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun t ↦ smoothTowerLiftExtension hT tower m t)
      (Ioo (0 : ℝ) T) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_smoothTowerLiftExtension_allFiniteOrders
    hT tower nu hnu initial hfixed hreal n m

/-- **One-sided all-order native bootstrap.**  Every scale face is `C^n` in time on `[0,T)` for
every finite `n`; all endpoint derivatives are Mathlib within-derivatives on the actual restart
aperture. -/
theorem contDiffOn_smoothTowerLiftExtension_Ico_allFiniteOrders
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ∀ (n m : ℕ), ContDiffOn ℝ n
      (fun t ↦ smoothTowerLiftExtension hT tower m t)
      (Ico (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro m
      simpa only using (contDiffOn_zero.mpr
        (smoothTowerLiftExtension hT tower m).continuous.continuousOn)
  | succ n ih =>
      intro m
      rw [show ((↑(n + 1) : WithTop ℕ∞)) =
          ((↑n : WithTop ℕ∞) + 1) by norm_num,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ico 0 T)]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact (hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
          hT tower nu hnu initial hfixed hreal m ht).differentiableWithinAt
      · intro htop
        norm_num at htop
      · have hfield := contDiffOn_nativeProjectedVectorFieldExtensionAtOrder_Ico
          hT tower nu n m ih
        apply hfield.congr
        intro t ht
        exact (hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
          hT tower nu hnu initial hfixed hreal m ht).derivWithin
            ((uniqueDiffOn_Ico 0 T).uniqueDiffWithinAt ht)

/-- Every coherent native lift is genuinely time-`C∞` on the half-open aperture, including its
one-sided initial face. -/
theorem contDiffOn_infty_smoothTowerLiftExtension_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun t ↦ smoothTowerLiftExtension hT tower m t)
      (Ico (0 : ℝ) T) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_smoothTowerLiftExtension_Ico_allFiniteOrders
    hT tower nu hnu initial hfixed hreal n m

section Audit

#print axioms hasDerivAt_smoothTowerLiftExtension
#print axioms hasDerivWithinAt_smoothTowerLiftExtension_Ico
#print axioms contDiffOn_smoothTowerLiftExtension_Ico_allFiniteOrders
#print axioms contDiffOn_infty_smoothTowerLiftExtension_Ico

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
