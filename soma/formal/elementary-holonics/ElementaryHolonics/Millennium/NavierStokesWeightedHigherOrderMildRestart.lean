import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
import ElementaryHolonics.Millennium.NavierStokesWeightedMildRestart

/-!
# An actual arbitrary-order weighted mild restart

**[proved-derived]** For every predecessor order `base ≥ 2`, this owner closes the
`H^(base+1)` path-space recurrence from an actual high-order initial state.  The complete native
Leray--divergence population spends one derivative, the adjacent heat word returns it, and the
variable-terminal Bochner integral is proved continuous by its exact heat-semigroup/Volterra
split.  Explicit one- and two-path estimates then select a genuine positive contraction aperture
and return a fixed point.

The last section compares this high recurrence with the established `H³` recurrence only through
exact coefficient-preserving restriction.  No higher-order state is inferred from an `H³` state.
-/

noncomputable section

open Function MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesQuadraticContraction
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedHeatScaleWord
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Exact semigroup split of the high-order return -/

/-- The adjacent-order vector heat word factors through any earlier positive elapsed time and a
same-order heat orbit on its target carrier. -/
theorem higherOrderHeatLift_factor
    (base : ℕ) (nu tau delta : ℝ≥0)
    (hnu : 0 < (nu : ℝ)) (hdelta : 0 < (delta : ℝ))
    (hdeltaTau : delta ≤ tau)
    (state : PeriodicVectorWeightedSobolev base) :
    higherOrderHeatLift base nu tau
        (mul_pos hnu (show 0 < (tau : ℝ) from
          lt_of_lt_of_le hdelta (by exact_mod_cast hdeltaTau))) state =
      periodicVectorWeightedHeat (base + 1) nu (tau - delta)
        (higherOrderHeatLift base nu delta (mul_pos hnu hdelta) state) := by
  funext component
  exact periodicWeightedHeatSucc_factor
    base nu tau delta hnu hdelta hdeltaTau (state component)

/-- Before an earlier terminal face, changing the high-order terminal face adds exactly the
same-order heat transport through the intervening elapsed time. -/
theorem higherOrderDuhamelIntegrand_later_eq_heat_earlier
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {a t s : ℝ}
    (hat : a ≤ t) (hsa : s < a)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1)) :
    higherOrderDuhamelIntegrand base hbase nu hnu t path s =
      periodicVectorWeightedHeat (base + 1) nu (elapsedBetween t a hat)
        (higherOrderDuhamelIntegrand base hbase nu hnu a path s) := by
  have hst : s < t := lt_of_lt_of_le hsa hat
  rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t path hst,
    higherOrderDuhamelIntegrand_of_lt base hbase nu hnu a path hsa]
  have hdeltaTau : positiveElapsed a s hsa ≤ positiveElapsed t s hst := by
    apply NNReal.coe_le_coe.mp
    simp only [coe_positiveElapsed]
    linarith
  have hfactor := higherOrderHeatLift_factor
    base nu (positiveElapsed t s hst) (positiveElapsed a s hsa) hnu
      (sub_pos.mpr hsa) hdeltaTau
      (higherOrderLerayQuadratic base hbase (path s))
  have helapsed : positiveElapsed t s hst - positiveElapsed a s hsa =
      elapsedBetween t a hat := by
    apply NNReal.eq
    rw [NNReal.coe_sub hdeltaTau]
    simp only [coe_positiveElapsed, coe_elapsedBetween]
    ring
  simpa only [helapsed] using hfactor

/-- Every terminal slice of a continuous high path is an honest Bochner-integrable word. -/
theorem intervalIntegrable_higherOrderDuhamelIntegrand_path
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
      (higherOrderDuhamelIntegrand base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path)) volume 0 t := by
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact IntervalIntegrable.refl
  · exact (higherOrderDuhamelReturn_exists_with_tame_bound_of_path_continuous
      base hbase nu hnu htpos ‖path‖ ‖path‖
      (weightedHigherOrderPathExtension hT path)
      (weightedHigherOrderPathExtension hT path).continuous.continuousOn
      (fun s _ ↦ (norm_periodicVectorWeightedRestrictToThree_le
          (base + 1) (by omega)
          (weightedHigherOrderPathExtension hT path s)).trans
        (norm_weightedHigherOrderPathExtension_le hT path s))
      (fun s _ ↦ norm_weightedHigherOrderPathExtension_le hT path s)).1

/-- Earlier high-order history commutes exactly through the target same-order heat map. -/
theorem intervalIntegral_earlier_eq_heat_higherOrderDuhamelReturn
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hat : a ≤ t) :
    (∫ s in (0 : ℝ)..a,
        higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path) s) =
      periodicVectorWeightedHeat (base + 1) nu (elapsedBetween t a hat)
        (higherOrderDuhamelReturn base hbase nu hnu a
          (weightedHigherOrderPathExtension hT path)) := by
  let heat := periodicVectorWeightedHeat (base + 1) nu (elapsedBetween t a hat)
  have hAE :
      (fun s : ℝ ↦ higherOrderDuhamelIntegrand base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) s) =ᵐ[
          volume.restrict (Ι (0 : ℝ) a)]
        (fun s : ℝ ↦ heat
          (higherOrderDuhamelIntegrand base hbase nu hnu a
            (weightedHigherOrderPathExtension hT path) s)) := by
    rw [uIoc_of_le ha.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact higherOrderDuhamelIntegrand_later_eq_heat_earlier
      base hbase nu hnu hat hs.2 (weightedHigherOrderPathExtension hT path)
  calc
    (∫ s in (0 : ℝ)..a,
        higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path) s) =
        ∫ s in (0 : ℝ)..a, heat
          (higherOrderDuhamelIntegrand base hbase nu hnu a
            (weightedHigherOrderPathExtension hT path) s) :=
      intervalIntegral.integral_congr_ae_restrict hAE
    _ = heat (∫ s in (0 : ℝ)..a,
          higherOrderDuhamelIntegrand base hbase nu hnu a
            (weightedHigherOrderPathExtension hT path) s) :=
      heat.intervalIntegral_comp_comm
        (intervalIntegrable_higherOrderDuhamelIntegrand_path
          base hbase nu hnu hT path ha)
    _ = periodicVectorWeightedHeat (base + 1) nu (elapsedBetween t a hat)
        (higherOrderDuhamelReturn base hbase nu hnu a
          (weightedHigherOrderPathExtension hT path)) := by rfl

/-- Exact Volterra/heat split of the arbitrary-order variable-terminal return. -/
theorem higherOrderDuhamelReturn_eq_heat_add_tail
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) (hat : a ≤ t) :
    higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) =
      periodicVectorWeightedHeat (base + 1) nu (elapsedBetween t a hat)
          (higherOrderDuhamelReturn base hbase nu hnu a
            (weightedHigherOrderPathExtension hT path)) +
        ∫ s in a..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t
            (weightedHigherOrderPathExtension hT path) s := by
  let integrand := fun s : ℝ ↦
    higherOrderDuhamelIntegrand base hbase nu hnu t
      (weightedHigherOrderPathExtension hT path) s
  have hfull : IntervalIntegrable integrand volume 0 t :=
    intervalIntegrable_higherOrderDuhamelIntegrand_path
      base hbase nu hnu hT path ht
  have hearlier : IntervalIntegrable integrand volume 0 a := by
    apply hfull.mono_set
    rw [uIcc_of_le ha.1, uIcc_of_le ht.1]
    exact Icc_subset_Icc_right hat
  have htail : IntervalIntegrable integrand volume a t := by
    apply hfull.mono_set
    rw [uIcc_of_le hat, uIcc_of_le ht.1]
    exact Icc_subset_Icc ha.1 le_rfl
  rw [higherOrderDuhamelReturn, ← intervalIntegral.integral_add_adjacent_intervals
    hearlier htail]
  rw [intervalIntegral_earlier_eq_heat_higherOrderDuhamelReturn
    base hbase nu hnu hT path ha hat]

/-! ## One-path tail bounds and continuity -/

/-- The recent high-order history is controlled by the same one-derivative aperture budget. -/
theorem norm_higherOrderDuhamelTail_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {a t : ℝ} (hat : a ≤ t) :
    ‖∫ s in a..t,
        higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path) s‖ ≤
      higherOrderTameConstant base * ‖path‖ ^ 2 *
        duhamelApertureBudget nu (t - a) := by
  rcases hat.eq_or_lt with rfl | hatlt
  · simp
  · let K : ℝ := higherOrderTameConstant base * ‖path‖ ^ 2
    have hK : 0 ≤ K := mul_nonneg (higherOrderTameConstant_nonneg base) (sq_nonneg ‖path‖)
    have hdelta : 0 < t - a := sub_pos.mpr hatlt
    have hreflected : IntervalIntegrable
        (fun s : ℝ ↦ duhamelHeatKernelMajorant (nu : ℝ) (t - s))
        volume a t := by
      have hbaseInt := intervalIntegrable_duhamelHeatKernelMajorant hnu hdelta
      have hreflect := (hbaseInt.comp_sub_left t).symm
      convert hreflect using 1 <;> ring
    have hmajorant : IntervalIntegrable
        (fun s : ℝ ↦ K * duhamelHeatKernelMajorant (nu : ℝ) (t - s))
        volume a t := hreflected.const_mul K
    have hnorm :
        ‖∫ s in a..t,
            higherOrderDuhamelIntegrand base hbase nu hnu t
              (weightedHigherOrderPathExtension hT path) s‖ ≤
          ∫ s in a..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hat
      · filter_upwards with s
        intro _hs
        simpa only [K, pow_two, mul_assoc] using
          (norm_higherOrderDuhamelIntegrand_le_of_bounds
          base hbase nu hnu t ‖path‖ ‖path‖
          (weightedHigherOrderPathExtension hT path) s (norm_nonneg path)
          (norm_nonneg path)
          ((norm_periodicVectorWeightedRestrictToThree_le
            (base + 1) (by omega)
            (weightedHigherOrderPathExtension hT path s)).trans
              (norm_weightedHigherOrderPathExtension_le hT path s))
          (norm_weightedHigherOrderPathExtension_le hT path s))
      · exact hmajorant
    calc
      ‖∫ s in a..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t
            (weightedHigherOrderPathExtension hT path) s‖ ≤
          ∫ s in a..t, K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
      _ = K * ∫ s in a..t,
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * ∫ tau in (0 : ℝ)..(t - a),
          duhamelHeatKernelMajorant (nu : ℝ) tau := by
        rw [intervalIntegral.integral_comp_sub_left]
        simp only [sub_self]
      _ ≤ K * duhamelApertureBudget nu (t - a) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral_duhamelHeatKernelMajorant_le hnu hdelta) hK
      _ = higherOrderTameConstant base * ‖path‖ ^ 2 *
          duhamelApertureBudget nu (t - a) := by rfl

/-- Pointwise one-path control of the actual high-order return. -/
theorem norm_higherOrderDuhamelReturn_path_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path)‖ ≤
      higherOrderTameConstant base * ‖path‖ ^ 2 * duhamelApertureBudget nu t := by
  simpa only [higherOrderDuhamelReturn, sub_zero] using
    norm_higherOrderDuhamelTail_le base hbase nu hnu hT path ht.1

@[simp]
theorem higherOrderDuhamelReturn_path_zero
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    higherOrderDuhamelReturn base hbase nu hnu 0
      (weightedHigherOrderPathExtension hT path) = 0 := by
  simp [higherOrderDuhamelReturn]

theorem continuousWithinAt_higherOrderDuhamelReturn_zero
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    ContinuousWithinAt
      (fun t ↦ higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path)) (Icc (0 : ℝ) T) 0 := by
  let K : ℝ := higherOrderTameConstant base * ‖path‖ ^ 2
  have hK : 0 ≤ K := mul_nonneg (higherOrderTameConstant_nonneg base) (sq_nonneg ‖path‖)
  have hscalar : Continuous (fun t : ℝ ↦ K * duhamelApertureBudget nu t) :=
    continuous_const.mul (continuous_duhamelApertureBudget nu)
  rw [Metric.continuousWithinAt_iff]
  intro epsilon hepsilon
  have hscalarAt : ContinuousAt
      (fun t : ℝ ↦ K * duhamelApertureBudget nu t) 0 := hscalar.continuousAt
  rw [Metric.continuousAt_iff] at hscalarAt
  obtain ⟨delta, hdelta, hnear⟩ := hscalarAt epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hdist
  have hscalarNear := hnear hdist
  have hbudgetNonneg : 0 ≤ K * duhamelApertureBudget nu t :=
    mul_nonneg hK (duhamelApertureBudget_nonneg nu ht.1)
  have hbudgetLt : K * duhamelApertureBudget nu t < epsilon := by
    simpa only [duhamelApertureBudget_zero, mul_zero, Real.dist_eq,
      sub_zero, abs_of_nonneg hbudgetNonneg] using hscalarNear
  have hreturn := norm_higherOrderDuhamelReturn_path_le
    base hbase nu hnu hT path ht
  change ‖higherOrderDuhamelReturn base hbase nu hnu t
      (weightedHigherOrderPathExtension hT path)‖ ≤
        K * duhamelApertureBudget nu t at hreturn
  simpa only [higherOrderDuhamelReturn_path_zero, dist_zero_right] using
    hreturn.trans_lt hbudgetLt

/-- At every positive terminal face, an earlier high-order return supplies a continuous
same-order heat-orbit model and the two recent tails vanish with their aperture. -/
theorem continuousWithinAt_higherOrderDuhamelReturn_of_pos
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht₀pos : 0 < t₀) :
    ContinuousWithinAt
      (fun t ↦ higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path))
      (Icc (0 : ℝ) T) t₀ := by
  let K : ℝ := higherOrderTameConstant base * ‖path‖ ^ 2
  have hK : 0 ≤ K := mul_nonneg (higherOrderTameConstant_nonneg base) (sq_nonneg ‖path‖)
  have hbudgetContinuous : Continuous
      (fun delta : ℝ ↦ K * duhamelApertureBudget nu delta) :=
    continuous_const.mul (continuous_duhamelApertureBudget nu)
  rw [Metric.continuousWithinAt_iff]
  intro epsilon hepsilon
  have hbudgetAtZero : ContinuousAt
      (fun delta : ℝ ↦ K * duhamelApertureBudget nu delta) 0 :=
    hbudgetContinuous.continuousAt
  rw [Metric.continuousAt_iff] at hbudgetAtZero
  obtain ⟨rho, hrho, hbudgetNearZero⟩ :=
    hbudgetAtZero (epsilon / 6) (by linarith)
  let d : ℝ := min (t₀ / 2) (rho / 2)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by linarith)
  have hdltT₀ : d < t₀ := by
    have hdle : d ≤ t₀ / 2 := min_le_left _ _
    linarith
  have hdltRho : d < rho := by
    have hdle : d ≤ rho / 2 := min_le_right _ _
    linarith
  let a : ℝ := t₀ - d
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hat₀ : a ≤ t₀ := by dsimp [a]; linarith
  have hat₀lt : a < t₀ := by dsimp [a]; linarith
  have ha : a ∈ Icc (0 : ℝ) T := ⟨ha0, hat₀.trans ht₀.2⟩
  have ht₀sub : t₀ - a = d := by dsimp [a]; ring
  have hdistDZero : dist d (0 : ℝ) < rho := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdpos]
    exact hdltRho
  have hbudgetDdist := hbudgetNearZero hdistDZero
  have hbudgetDNonneg : 0 ≤ K * duhamelApertureBudget nu d :=
    mul_nonneg hK (duhamelApertureBudget_nonneg nu hdpos.le)
  have hbudgetD : K * duhamelApertureBudget nu d < epsilon / 6 := by
    simpa only [duhamelApertureBudget_zero, mul_zero, Real.dist_eq,
      sub_zero, abs_of_nonneg hbudgetDNonneg] using hbudgetDdist
  let earlier := higherOrderDuhamelReturn base hbase nu hnu a
    (weightedHigherOrderPathExtension hT path)
  let model : ℝ → PeriodicVectorWeightedSobolev (base + 1) := fun t ↦
    periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal (t - a)) earlier
  let recent : ℝ → PeriodicVectorWeightedSobolev (base + 1) := fun t ↦
    ∫ s in a..t,
      higherOrderDuhamelIntegrand base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) s
  let localBudget : ℝ → ℝ := fun t ↦ K * duhamelApertureBudget nu (t - a)
  have hmodelContinuous : Continuous model := by
    exact (continuous_periodicVectorWeightedHeat_orbit (base + 1) nu earlier).comp
      (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hlocalBudgetContinuous : Continuous localBudget := by
    exact continuous_const.mul ((continuous_duhamelApertureBudget nu).comp
      (continuous_id.sub continuous_const))
  have hmodelAt : ContinuousAt model t₀ := hmodelContinuous.continuousAt
  rw [Metric.continuousAt_iff] at hmodelAt
  obtain ⟨deltaModel, hdeltaModel, hmodelNear⟩ :=
    hmodelAt (epsilon / 3) (by linarith)
  have hlocalBudgetAt : ContinuousAt localBudget t₀ :=
    hlocalBudgetContinuous.continuousAt
  rw [Metric.continuousAt_iff] at hlocalBudgetAt
  obtain ⟨deltaBudget, hdeltaBudget, hlocalBudgetNear⟩ :=
    hlocalBudgetAt (epsilon / 6) (by linarith)
  let delta : ℝ := min d (min deltaModel deltaBudget)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdpos (lt_min hdeltaModel hdeltaBudget)
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hdist
  have hdistD : dist t t₀ < d := hdist.trans_le (min_le_left _ _)
  have habsD : |t - t₀| < d := by simpa only [Real.dist_eq] using hdistD
  have hat : a ≤ t := by
    rw [abs_lt] at habsD
    dsimp [a]
    linarith
  have hdistModel : dist t t₀ < deltaModel :=
    hdist.trans_le ((min_le_right d (min deltaModel deltaBudget)).trans
      (min_le_left deltaModel deltaBudget))
  have hmodelClose : ‖model t - model t₀‖ < epsilon / 3 := by
    simpa only [dist_eq_norm] using hmodelNear hdistModel
  have hdistBudget : dist t t₀ < deltaBudget :=
    hdist.trans_le ((min_le_right d (min deltaModel deltaBudget)).trans
      (min_le_right deltaModel deltaBudget))
  have hlocalBudgetClose := hlocalBudgetNear hdistBudget
  have hlocalBudgetBase : localBudget t₀ = K * duhamelApertureBudget nu d := by
    simp only [localBudget, ht₀sub]
  have hlocalBudgetDiff : localBudget t - localBudget t₀ < epsilon / 6 := by
    have habs : |localBudget t - localBudget t₀| < epsilon / 6 := by
      simpa only [Real.dist_eq] using hlocalBudgetClose
    exact (le_abs_self _).trans_lt habs
  have hlocalBudgetLt : localBudget t < epsilon / 3 := by
    rw [hlocalBudgetBase] at hlocalBudgetDiff
    linarith
  have helapsed : elapsedBetween t a hat = Real.toNNReal (t - a) := by
    apply NNReal.eq
    rw [coe_elapsedBetween, Real.coe_toNNReal _ (sub_nonneg.mpr hat)]
  have helapsed₀ : elapsedBetween t₀ a hat₀ = Real.toNNReal (t₀ - a) := by
    apply NNReal.eq
    rw [coe_elapsedBetween, Real.coe_toNNReal _ (sub_nonneg.mpr hat₀)]
  have hsplit : higherOrderDuhamelReturn base hbase nu hnu t
      (weightedHigherOrderPathExtension hT path) = model t + recent t := by
    simpa only [model, earlier, recent, helapsed] using
      higherOrderDuhamelReturn_eq_heat_add_tail
        base hbase nu hnu hT path ha ht hat
  have hsplit₀ : higherOrderDuhamelReturn base hbase nu hnu t₀
      (weightedHigherOrderPathExtension hT path) = model t₀ + recent t₀ := by
    simpa only [model, earlier, recent, helapsed₀] using
      higherOrderDuhamelReturn_eq_heat_add_tail
        base hbase nu hnu hT path ha ht₀ hat₀
  have hrecent : ‖recent t‖ < epsilon / 3 := by
    have htail := norm_higherOrderDuhamelTail_le base hbase nu hnu hT path hat
    change ‖recent t‖ ≤ localBudget t at htail
    exact htail.trans_lt hlocalBudgetLt
  have hrecent₀ : ‖recent t₀‖ < epsilon / 6 := by
    have htail := norm_higherOrderDuhamelTail_le base hbase nu hnu hT path hat₀
    change ‖recent t₀‖ ≤ K * duhamelApertureBudget nu (t₀ - a) at htail
    rw [ht₀sub] at htail
    exact htail.trans_lt hbudgetD
  rw [hsplit, hsplit₀, dist_eq_norm]
  calc
    ‖model t + recent t - (model t₀ + recent t₀)‖ =
        ‖(model t - model t₀) + (recent t - recent t₀)‖ := by
      congr 1
      abel
    _ ≤ ‖model t - model t₀‖ + ‖recent t - recent t₀‖ := norm_add_le _ _
    _ ≤ ‖model t - model t₀‖ + (‖recent t‖ + ‖recent t₀‖) :=
      add_le_add_right (norm_sub_le _ _) _
    _ < epsilon := by linarith

/-- The actual high-order Bochner return is continuous on the full closed aperture. -/
theorem continuousOn_higherOrderDuhamelReturn_path
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    ContinuousOn
      (fun t ↦ higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path)) (Icc (0 : ℝ) T) := by
  intro t ht
  rcases ht.1.eq_or_lt with hzero | hpos
  · subst t
    exact continuousWithinAt_higherOrderDuhamelReturn_zero
      base hbase nu hnu hT path
  · exact continuousWithinAt_higherOrderDuhamelReturn_of_pos
      base hbase nu hnu hT path ht hpos

/-- The nonlinear high-order Volterra passage as an element of the complete path carrier. -/
def higherOrderDuhamelPath
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) : WeightedHigherOrderPath base T where
  toFun := fun t ↦ higherOrderDuhamelReturn base hbase nu hnu t.1
    (weightedHigherOrderPathExtension hT path)
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (continuousOn_higherOrderDuhamelReturn_path base hbase nu hnu hT path)

@[simp]
theorem higherOrderDuhamelPath_apply
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) (t : Icc (0 : ℝ) T) :
    higherOrderDuhamelPath base hbase nu hnu hT path t =
      higherOrderDuhamelReturn base hbase nu hnu t.1
        (weightedHigherOrderPathExtension hT path) := rfl

@[simp]
theorem higherOrderDuhamelPath_zero
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    higherOrderDuhamelPath base hbase nu hnu hT path
      ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := by
  simp

/-- Supremum-norm one-path control of the actual high-order nonlinear return. -/
theorem norm_higherOrderDuhamelPath_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    ‖higherOrderDuhamelPath base hbase nu hnu hT path‖ ≤
      higherOrderTameConstant base * duhamelApertureBudget nu T * ‖path‖ ^ 2 := by
  let K : ℝ := higherOrderTameConstant base * ‖path‖ ^ 2
  have hK : 0 ≤ K := mul_nonneg (higherOrderTameConstant_nonneg base) (sq_nonneg ‖path‖)
  rw [show higherOrderTameConstant base * duhamelApertureBudget nu T * ‖path‖ ^ 2 =
      K * duhamelApertureBudget nu T by dsimp [K]; ring]
  apply (ContinuousMap.norm_le (higherOrderDuhamelPath base hbase nu hnu hT path)
    (mul_nonneg hK (duhamelApertureBudget_nonneg nu hT))).2
  intro t
  rw [higherOrderDuhamelPath_apply]
  have hpoint := norm_higherOrderDuhamelReturn_path_le
    base hbase nu hnu hT path t.2
  change ‖higherOrderDuhamelReturn base hbase nu hnu t.1
      (weightedHigherOrderPathExtension hT path)‖ ≤
    K * duhamelApertureBudget nu T
  calc
    ‖higherOrderDuhamelReturn base hbase nu hnu t.1
        (weightedHigherOrderPathExtension hT path)‖ ≤
        K * duhamelApertureBudget nu t.1 := by
      simpa only [K, pow_two, mul_assoc] using hpoint
    _ ≤ K * duhamelApertureBudget nu T :=
      mul_le_mul_of_nonneg_left
        (duhamelApertureBudget_mono nu hnu t.2.2) hK
    _ = K * duhamelApertureBudget nu T := rfl

/-! ## The high linear orbit and mild map -/

/-- The exact same-order heat orbit of an actual high-order initial state. -/
def higherOrderLinearHeatPath
    (base : ℕ) (nu : ℝ≥0) {T : ℝ} (_hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    WeightedHigherOrderPath base T where
  toFun := fun t ↦ periodicVectorWeightedHeat (base + 1) nu
    (Real.toNNReal t.1) initial
  continuous_toFun :=
    (continuous_periodicVectorWeightedHeat_orbit (base + 1) nu initial).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)

@[simp]
theorem higherOrderLinearHeatPath_zero
    (base : ℕ) (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    higherOrderLinearHeatPath base nu hT initial ⟨0, ⟨le_rfl, hT⟩⟩ = initial := by
  funext component
  unfold higherOrderLinearHeatPath
  simp only [ContinuousMap.coe_mk, Real.toNNReal_zero]
  change periodicWeightedHeat (base + 1) nu 0 (initial component) = initial component
  have hzero := congrArg (fun operator ↦ operator (initial component))
    (periodicWeightedHeat_zero_time (base + 1) nu)
  simpa only [ContinuousLinearMap.id_apply] using hzero

theorem norm_higherOrderLinearHeatPath_le
    (base : ℕ) (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    ‖higherOrderLinearHeatPath base nu hT initial‖ ≤ ‖initial‖ := by
  apply (ContinuousMap.norm_le (higherOrderLinearHeatPath base nu hT initial)
    (norm_nonneg initial)).2
  intro t
  exact norm_periodicVectorWeightedHeat_le (base + 1) nu
    (Real.toNNReal t.1) initial

/-- The unforced native mild map on `C([0,T], H^(base+1))`. -/
def higherOrderMildMap
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    WeightedHigherOrderPath base T → WeightedHigherOrderPath base T := fun path ↦
  higherOrderLinearHeatPath base nu hT initial -
    higherOrderDuhamelPath base hbase nu hnu hT path

@[simp]
theorem higherOrderMildMap_zero
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T) :
    higherOrderMildMap base hbase nu hnu hT initial path
      ⟨0, ⟨le_rfl, hT⟩⟩ = initial := by
  simp [higherOrderMildMap]

/-! ## Exact two-path estimates -/

/-- Polarization of the full arbitrary-order quadratic source retains both ordered populations. -/
theorem higherOrderLerayQuadratic_sub_eq
    (base : ℕ) (hbase : 2 ≤ base)
    (u v : PeriodicVectorWeightedSobolev (base + 1)) :
    higherOrderLerayQuadratic base hbase u -
        higherOrderLerayQuadratic base hbase v =
      periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) (u - v) u +
        periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) v (u - v) := by
  let B := periodicVectorWeightedLerayDivergenceConvolution
    (base + 1) (by omega)
  have hleft : B u u = B (u - v) u + B v u := by
    rw [← periodicVectorWeightedLerayDivergenceConvolution_add_left
      (base + 1) (by omega)]
    congr 1
    abel
  have hright : B v u = B v (u - v) + B v v := by
    rw [← periodicVectorWeightedLerayDivergenceConvolution_add_right
      (base + 1) (by omega)]
    congr 1
    abel
  change B u u - B v v = B (u - v) u + B v (u - v)
  rw [hleft, hright]
  abel

/-- The arbitrary-order quadratic source is locally Lipschitz with the exact sum-of-norms
population carried by its bundled bilinear owner. -/
theorem norm_higherOrderLerayQuadratic_sub_le
    (base : ℕ) (hbase : 2 ≤ base)
    (u v : PeriodicVectorWeightedSobolev (base + 1)) :
    ‖higherOrderLerayQuadratic base hbase u -
        higherOrderLerayQuadratic base hbase v‖ ≤
      higherOrderTameConstant base * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [higherOrderLerayQuadratic_sub_eq base hbase]
  calc
    ‖periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) (u - v) u +
        periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) v (u - v)‖ ≤
      ‖periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) (u - v) u‖ +
        ‖periodicVectorWeightedLerayDivergenceConvolution
          (base + 1) (by omega) v (u - v)‖ := norm_add_le _ _
    _ ≤ higherOrderTameConstant base * ‖u - v‖ * ‖u‖ +
        higherOrderTameConstant base * ‖v‖ * ‖u - v‖ :=
      add_le_add
        (norm_periodicVectorWeightedLerayDivergenceConvolution_le
          (base + 1) (by omega) (u - v) u)
        (norm_periodicVectorWeightedLerayDivergenceConvolution_le
          (base + 1) (by omega) v (u - v))
    _ = higherOrderTameConstant base * (‖u‖ + ‖v‖) * ‖u - v‖ := by
      unfold higherOrderTameConstant
      ring

/-- The exact positive-time high-order integrand difference. -/
theorem norm_higherOrderDuhamelIntegrand_sub_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u v : ℝ → PeriodicVectorWeightedSobolev (base + 1)) (s : ℝ) :
    ‖higherOrderDuhamelIntegrand base hbase nu hnu t u s -
        higherOrderDuhamelIntegrand base hbase nu hnu t v s‖ ≤
      higherOrderTameConstant base * (‖u s‖ + ‖v s‖) * ‖u s - v s‖ *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
  by_cases hs : s < t
  · rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t u hs,
      higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t v hs,
      ← (higherOrderHeatLift base nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs))).map_sub]
    calc
      ‖higherOrderHeatLift base nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs))
          (higherOrderLerayQuadratic base hbase (u s) -
            higherOrderLerayQuadratic base hbase (v s))‖ ≤
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          ‖higherOrderLerayQuadratic base hbase (u s) -
            higherOrderLerayQuadratic base hbase (v s)‖ := by
        simpa only [coe_positiveElapsed] using norm_higherOrderHeatLift_le
          base nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
          (higherOrderLerayQuadratic base hbase (u s) -
            higherOrderLerayQuadratic base hbase (v s))
      _ ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          (higherOrderTameConstant base * (‖u s‖ + ‖v s‖) * ‖u s - v s‖) :=
        mul_le_mul_of_nonneg_left
          (norm_higherOrderLerayQuadratic_sub_le base hbase (u s) (v s))
          (Real.sqrt_nonneg _)
      _ = higherOrderTameConstant base * (‖u s‖ + ‖v s‖) * ‖u s - v s‖ *
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by ring
  · rw [higherOrderDuhamelIntegrand_of_not_lt base hbase nu hnu t u hs,
      higherOrderDuhamelIntegrand_of_not_lt base hbase nu hnu t v hs,
      sub_zero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (higherOrderTameConstant_nonneg base)
          (add_nonneg (norm_nonneg (u s)) (norm_nonneg (v s))))
        (norm_nonneg (u s - v s)))
      (Real.sqrt_nonneg _)

/-- Extension to the real line preserves the pointwise separation bound of two high paths. -/
theorem norm_weightedHigherOrderPathExtension_sub_le
    {base : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedHigherOrderPath base T) (t : ℝ) :
    ‖weightedHigherOrderPathExtension hT u t -
        weightedHigherOrderPathExtension hT v t‖ ≤ ‖u - v‖ := by
  change ‖(u - v) (Set.projIcc 0 T hT t)‖ ≤ ‖u - v‖
  exact (u - v).norm_coe_le_norm _

/-- Pointwise two-path control of the actual high-order Bochner return. -/
theorem norm_higherOrderDuhamelReturn_sub_le_sum
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedHigherOrderPath base T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖higherOrderDuhamelReturn base hbase nu hnu t
          (weightedHigherOrderPathExtension hT u) -
        higherOrderDuhamelReturn base hbase nu hnu t
          (weightedHigherOrderPathExtension hT v)‖ ≤
      higherOrderTameConstant base * duhamelApertureBudget nu t *
        (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rcases ht.1.eq_or_lt with hzero | htpos
  · subst t
    simp
  · have huIntegrable := intervalIntegrable_higherOrderDuhamelIntegrand_path
      base hbase nu hnu hT u ht
    have hvIntegrable := intervalIntegrable_higherOrderDuhamelIntegrand_path
      base hbase nu hnu hT v ht
    rw [higherOrderDuhamelReturn, higherOrderDuhamelReturn,
      ← intervalIntegral.integral_sub huIntegrable hvIntegrable]
    let K : ℝ := higherOrderTameConstant base * (‖u‖ + ‖v‖) * ‖u - v‖
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg
        (mul_nonneg (higherOrderTameConstant_nonneg base)
          (add_nonneg (norm_nonneg u) (norm_nonneg v)))
        (norm_nonneg (u - v))
    have hmajorant : IntervalIntegrable
        (fun s : ℝ ↦ K * duhamelHeatKernelMajorant (nu : ℝ) (t - s)) volume 0 t :=
      (intervalIntegrable_reflectedDuhamelHeatKernelMajorant nu hnu htpos).const_mul K
    have hnorm :
        ‖∫ s in (0 : ℝ)..t,
          (higherOrderDuhamelIntegrand base hbase nu hnu t
              (weightedHigherOrderPathExtension hT u) s -
            higherOrderDuhamelIntegrand base hbase nu hnu t
              (weightedHigherOrderPathExtension hT v) s)‖ ≤
          ∫ s in (0 : ℝ)..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      apply intervalIntegral.norm_integral_le_of_norm_le htpos.le
      · filter_upwards with s
        intro _hs
        have hpoint := norm_higherOrderDuhamelIntegrand_sub_le
          base hbase nu hnu t (weightedHigherOrderPathExtension hT u)
            (weightedHigherOrderPathExtension hT v) s
        have hsum : ‖weightedHigherOrderPathExtension hT u s‖ +
            ‖weightedHigherOrderPathExtension hT v s‖ ≤ ‖u‖ + ‖v‖ :=
          add_le_add (norm_weightedHigherOrderPathExtension_le hT u s)
            (norm_weightedHigherOrderPathExtension_le hT v s)
        have hdiff : ‖weightedHigherOrderPathExtension hT u s -
            weightedHigherOrderPathExtension hT v s‖ ≤ ‖u - v‖ :=
          norm_weightedHigherOrderPathExtension_sub_le hT u v s
        have hinside : higherOrderTameConstant base *
              (‖weightedHigherOrderPathExtension hT u s‖ +
                ‖weightedHigherOrderPathExtension hT v s‖) *
              ‖weightedHigherOrderPathExtension hT u s -
                weightedHigherOrderPathExtension hT v s‖ ≤ K := by
          dsimp [K]
          calc
            higherOrderTameConstant base *
                (‖weightedHigherOrderPathExtension hT u s‖ +
                  ‖weightedHigherOrderPathExtension hT v s‖) *
                ‖weightedHigherOrderPathExtension hT u s -
                  weightedHigherOrderPathExtension hT v s‖ ≤
              higherOrderTameConstant base *
                (‖weightedHigherOrderPathExtension hT u s‖ +
                  ‖weightedHigherOrderPathExtension hT v s‖) * ‖u - v‖ :=
                mul_le_mul_of_nonneg_left hdiff
                  (mul_nonneg (higherOrderTameConstant_nonneg base)
                    (add_nonneg (norm_nonneg _) (norm_nonneg _)))
            _ ≤ higherOrderTameConstant base * (‖u‖ + ‖v‖) * ‖u - v‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsum
                  (higherOrderTameConstant_nonneg base)) (norm_nonneg _)
        exact hpoint.trans (mul_le_mul_of_nonneg_right hinside (Real.sqrt_nonneg _))
      · exact hmajorant
    calc
      ‖∫ s in (0 : ℝ)..t,
          (higherOrderDuhamelIntegrand base hbase nu hnu t
              (weightedHigherOrderPathExtension hT u) s -
            higherOrderDuhamelIntegrand base hbase nu hnu t
              (weightedHigherOrderPathExtension hT v) s)‖ ≤
          ∫ s in (0 : ℝ)..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
      _ = K * ∫ s in (0 : ℝ)..t,
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * ∫ tau in (0 : ℝ)..t,
          duhamelHeatKernelMajorant (nu : ℝ) tau := by
        rw [intervalIntegral_reflectedDuhamelHeatKernelMajorant]
      _ ≤ K * duhamelApertureBudget nu t :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral_duhamelHeatKernelMajorant_le hnu htpos) hK
      _ = higherOrderTameConstant base * duhamelApertureBudget nu t *
          (‖u‖ + ‖v‖) * ‖u - v‖ := by
        dsimp [K, duhamelApertureBudget]
        ring

/-- Supremum-norm separation of the high nonlinear path return. -/
theorem norm_higherOrderDuhamelPath_sub_le_sum
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedHigherOrderPath base T) :
    ‖higherOrderDuhamelPath base hbase nu hnu hT u -
        higherOrderDuhamelPath base hbase nu hnu hT v‖ ≤
      higherOrderTameConstant base * duhamelApertureBudget nu T *
        (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let L : ℝ := higherOrderTameConstant base * (‖u‖ + ‖v‖) * ‖u - v‖
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (higherOrderTameConstant_nonneg base)
        (add_nonneg (norm_nonneg u) (norm_nonneg v)))
      (norm_nonneg (u - v))
  rw [show higherOrderTameConstant base * duhamelApertureBudget nu T *
      (‖u‖ + ‖v‖) * ‖u - v‖ = L * duhamelApertureBudget nu T by
    dsimp [L]; ring]
  apply (ContinuousMap.norm_le
    (higherOrderDuhamelPath base hbase nu hnu hT u -
      higherOrderDuhamelPath base hbase nu hnu hT v)
    (mul_nonneg hL (duhamelApertureBudget_nonneg nu hT))).2
  intro t
  change ‖higherOrderDuhamelReturn base hbase nu hnu t.1
      (weightedHigherOrderPathExtension hT u) -
    higherOrderDuhamelReturn base hbase nu hnu t.1
      (weightedHigherOrderPathExtension hT v)‖ ≤
    L * duhamelApertureBudget nu T
  have hpoint := norm_higherOrderDuhamelReturn_sub_le_sum
    base hbase nu hnu hT u v t.2
  calc
    ‖higherOrderDuhamelReturn base hbase nu hnu t.1
        (weightedHigherOrderPathExtension hT u) -
      higherOrderDuhamelReturn base hbase nu hnu t.1
        (weightedHigherOrderPathExtension hT v)‖ ≤
        L * duhamelApertureBudget nu t.1 := by
      convert hpoint using 1
      all_goals dsimp [L]; ring
    _ ≤ L * duhamelApertureBudget nu T :=
      mul_le_mul_of_nonneg_left (duhamelApertureBudget_mono nu hnu t.2.2) hL

/-- The one-path mild remainder has the exact arbitrary-order quadratic coefficient. -/
theorem norm_higherOrderMildMap_sub_linear_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (u : WeightedHigherOrderPath base T) :
    ‖higherOrderMildMap base hbase nu hnu hT initial u -
        higherOrderLinearHeatPath base nu hT initial‖ ≤
      (higherOrderTameConstant base * duhamelApertureBudget nu T) * ‖u‖ ^ 2 := by
  simp only [higherOrderMildMap]
  rw [show
    (higherOrderLinearHeatPath base nu hT initial -
        higherOrderDuhamelPath base hbase nu hnu hT u) -
      higherOrderLinearHeatPath base nu hT initial =
        -higherOrderDuhamelPath base hbase nu hnu hT u by abel, norm_neg]
  exact norm_higherOrderDuhamelPath_le base hbase nu hnu hT u

/-- The difference of two high mild remainders carries the exact sum-of-path-norms factor. -/
theorem norm_higherOrderMildMap_remainder_sub_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (u v : WeightedHigherOrderPath base T) :
    ‖(higherOrderMildMap base hbase nu hnu hT initial u -
          higherOrderLinearHeatPath base nu hT initial) -
        (higherOrderMildMap base hbase nu hnu hT initial v -
          higherOrderLinearHeatPath base nu hT initial)‖ ≤
      (higherOrderTameConstant base * duhamelApertureBudget nu T) *
        (‖u‖ + ‖v‖) * ‖u - v‖ := by
  simp only [higherOrderMildMap]
  rw [show
    ((higherOrderLinearHeatPath base nu hT initial -
        higherOrderDuhamelPath base hbase nu hnu hT u) -
      higherOrderLinearHeatPath base nu hT initial) -
      ((higherOrderLinearHeatPath base nu hT initial -
          higherOrderDuhamelPath base hbase nu hnu hT v) -
        higherOrderLinearHeatPath base nu hT initial) =
      -(higherOrderDuhamelPath base hbase nu hnu hT u -
        higherOrderDuhamelPath base hbase nu hnu hT v) by abel, norm_neg]
  exact norm_higherOrderDuhamelPath_sub_le_sum base hbase nu hnu hT u v

/-! ## A genuine high-data-dependent contraction aperture -/

/-- The strictly positive high path radius, including the zero initial state. -/
def higherOrderRestartRadius
    {base : ℕ} (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  2 * (1 + ‖initial‖)

theorem higherOrderRestartRadius_pos
    {base : ℕ} (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 < higherOrderRestartRadius initial := by
  unfold higherOrderRestartRadius
  positivity

/-- The arbitrary-order coefficient weighted by its actual high path radius. -/
def higherOrderRestartLoad
    (base : ℕ) (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  higherOrderTameConstant base * higherOrderRestartRadius initial

theorem higherOrderRestartLoad_nonneg
    (base : ℕ) (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 ≤ higherOrderRestartLoad base initial :=
  mul_nonneg (higherOrderTameConstant_nonneg base)
    (higherOrderRestartRadius_pos initial).le

/-- The positive viscous time selected from the actual high initial norm. -/
def higherOrderRestartTime
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  duhamelRestartTime nu (higherOrderRestartLoad base initial)

theorem higherOrderRestartTime_pos
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 < higherOrderRestartTime base nu initial :=
  duhamelRestartTime_pos hnu (higherOrderRestartLoad_nonneg base initial)

/-- The actual arbitrary-order integrated coefficient on a real viscous aperture. -/
def higherOrderDuhamelCoefficient (base : ℕ) (nu T : ℝ) : ℝ :=
  higherOrderTameConstant base *
    (T + 2 * Real.sqrt (T / (2 * nu)))

theorem higherOrderDuhamelCoefficient_nonneg
    (base : ℕ) {nu T : ℝ} (hT : 0 ≤ T) :
    0 ≤ higherOrderDuhamelCoefficient base nu T := by
  unfold higherOrderDuhamelCoefficient
  exact mul_nonneg (higherOrderTameConstant_nonneg base)
    (add_nonneg hT (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- At the selected high aperture, the two-path factor is strictly below one. -/
theorem two_higherOrderDuhamelCoefficient_mul_radius_lt_one
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    2 * higherOrderDuhamelCoefficient base nu
        (higherOrderRestartTime base nu initial) *
      higherOrderRestartRadius initial < 1 := by
  have h := two_load_mul_restartKernelBound_lt_one hnu
    (higherOrderRestartLoad_nonneg base initial)
  unfold higherOrderDuhamelCoefficient higherOrderRestartTime
  unfold higherOrderRestartLoad at h ⊢
  nlinarith

/-- The same strict inequality supplies the quadratic half-ball estimate. -/
theorem higherOrderDuhamelCoefficient_mul_radius_sq_le_half
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    higherOrderDuhamelCoefficient base nu
        (higherOrderRestartTime base nu initial) *
        higherOrderRestartRadius initial ^ 2 ≤
      higherOrderRestartRadius initial / 2 := by
  let A := higherOrderDuhamelCoefficient base nu
    (higherOrderRestartTime base nu initial)
  let R := higherOrderRestartRadius initial
  have hR : 0 < R := higherOrderRestartRadius_pos initial
  have hcontract : 2 * A * R < 1 :=
    two_higherOrderDuhamelCoefficient_mul_radius_lt_one base hnu initial
  have hhalf : 0 < R / 2 := by positivity
  have hscaled := mul_lt_mul_of_pos_right hcontract hhalf
  have hstrict : A * R ^ 2 < R / 2 := by nlinarith
  exact hstrict.le

/-- The actual high mild map at its selected data-dependent aperture. -/
def higherOrderMildRestartMap
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ) (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    WeightedHigherOrderPath base (higherOrderRestartTime base nu initial) →
      WeightedHigherOrderPath base (higherOrderRestartTime base nu initial) :=
  higherOrderMildMap base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
    (higherOrderRestartTime_pos base hnu initial).le initial

/-- **Actual arbitrary-order fixed-point return.**  Every genuine `H^(base+1)` initial state
returns a fixed high path at an explicit positive aperture determined by its own norm. -/
theorem exists_higherOrderMildRestart_fixedPoint
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    ∃ u : WeightedHigherOrderPath base (higherOrderRestartTime base nu initial),
      ‖u‖ ≤ higherOrderRestartRadius initial ∧
        IsFixedPt (higherOrderMildRestartMap base hbase nu hnu initial) u ∧
          u ⟨0, ⟨le_rfl, (higherOrderRestartTime_pos base hnu initial).le⟩⟩ = initial := by
  let T := higherOrderRestartTime base nu initial
  let hT : 0 ≤ T := (higherOrderRestartTime_pos base hnu initial).le
  let linear : WeightedHigherOrderPath base T :=
    higherOrderLinearHeatPath base (Real.toNNReal nu) hT initial
  let A : ℝ := higherOrderDuhamelCoefficient base nu T
  let R : ℝ := higherOrderRestartRadius initial
  have hlinearNorm : ‖linear‖ ≤ ‖initial‖ :=
    norm_higherOrderLinearHeatPath_le base (Real.toNNReal nu) hT initial
  have hlinearHalf : ‖linear‖ ≤ R / 2 := by
    dsimp [R, higherOrderRestartRadius]
    linarith [norm_nonneg initial]
  have hremainder : ∀ u : WeightedHigherOrderPath base T,
      ‖higherOrderMildRestartMap base hbase nu hnu initial u - linear‖ ≤
        A * ‖u‖ ^ 2 := by
    intro u
    simpa only [higherOrderMildRestartMap, linear, A, T,
      higherOrderDuhamelCoefficient, Real.coe_toNNReal _ hnu.le,
      duhamelApertureBudget] using
      norm_higherOrderMildMap_sub_linear_le base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial u
  have hdifference : ∀ u v : WeightedHigherOrderPath base T,
      ‖(higherOrderMildRestartMap base hbase nu hnu initial u - linear) -
          (higherOrderMildRestartMap base hbase nu hnu initial v - linear)‖ ≤
        A * (‖u‖ + ‖v‖) * ‖u - v‖ := by
    intro u v
    simpa only [higherOrderMildRestartMap, linear, A, T,
      higherOrderDuhamelCoefficient, Real.coe_toNNReal _ hnu.le,
      duhamelApertureBudget] using
      norm_higherOrderMildMap_remainder_sub_le base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial u v
  have hdata : QuadraticContractionData
      (higherOrderMildRestartMap base hbase nu hnu initial) linear A R := by
    refine
      { coefficient_nonneg := higherOrderDuhamelCoefficient_nonneg base hT
        radius_nonneg := (higherOrderRestartRadius_pos initial).le
        linear_le_half := hlinearHalf
        quadratic_le_half := ?_
        contraction_lt_one := ?_
        remainder_bound := hremainder
        remainder_difference_bound := hdifference }
    · simpa only [A, R, T] using
        higherOrderDuhamelCoefficient_mul_radius_sq_le_half base hnu initial
    · simpa only [A, R, T] using
        two_higherOrderDuhamelCoefficient_mul_radius_lt_one base hnu initial
  obtain ⟨u, hu, hfixed⟩ := hdata.exists_fixedPoint_mem_restartBall
  refine ⟨u, hu, hfixed, ?_⟩
  have hface := congrArg
    (fun path : WeightedHigherOrderPath base T ↦
      path ⟨0, ⟨le_rfl, hT⟩⟩) hfixed
  simpa only [higherOrderMildRestartMap, higherOrderMildMap_zero, T, hT] using hface.symm

/-! ## Exact restriction to the established `H³` recurrence -/

/-- Equality of every unweighted component/mode determines a native weighted vector state. -/
theorem periodicVectorWeightedSobolev_ext_physical
    {order : ℕ} {left right : PeriodicVectorWeightedSobolev order}
    (hcoeff : ∀ component k,
      (weightedSobolevCoefficients order (left component)).1 k =
        (weightedSobolevCoefficients order (right component)).1 k) :
    left = right := by
  funext component
  calc
    left component = coefficientWeightedRealization order
        (weightedSobolevCoefficients order (left component)) :=
      (coefficientWeightedRealization_weightedSobolevCoefficients
        order (left component)).symm
    _ = coefficientWeightedRealization order
        (weightedSobolevCoefficients order (right component)) := by
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact hcoeff component k
    _ = right component :=
      coefficientWeightedRealization_weightedSobolevCoefficients
        order (right component)

/-- High-to-low restriction commutes exactly with same-order heat transport. -/
theorem restrict_periodicVectorWeightedHeat
    (low high : ℕ) (hlowhigh : low ≤ high)
    (nu tau : ℝ≥0) (state : PeriodicVectorWeightedSobolev high) :
    periodicVectorWeightedSobolevRestrictCLM low high hlowhigh
        (periodicVectorWeightedHeat high nu tau state) =
      periodicVectorWeightedHeat low nu tau
        (periodicVectorWeightedSobolevRestrictCLM low high hlowhigh state) := by
  apply periodicVectorWeightedSobolev_ext_physical
  intro component k
  change
    (weightedSobolevCoefficients low
      (periodicWeightedSobolevRestrict low high hlowhigh
        (periodicWeightedHeat high nu tau (state component)))).1 k =
    (weightedSobolevCoefficients low
      (periodicWeightedHeat low nu tau
        (periodicWeightedSobolevRestrict low high hlowhigh (state component)))).1 k
  rw [weightedSobolevCoefficients_restrict_apply,
    unweighted_periodicWeightedHeat_apply,
    unweighted_periodicWeightedHeat_apply,
    weightedSobolevCoefficients_restrict_apply]

/-- The generic arbitrary-order Leray source restricts to exactly the established native
`H³ × H³ → H²` Leray source, with every ordered convolution mode retained. -/
theorem restrict_higherOrderLerayQuadratic_to_weightedLerayQuadratic
    (base : ℕ) (hbase : 2 ≤ base)
    (state : PeriodicVectorWeightedSobolev (base + 1)) :
    periodicVectorWeightedSobolevRestrictCLM 2 base hbase
        (higherOrderLerayQuadratic base hbase state) =
      weightedLerayQuadratic
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) state) := by
  apply periodicVectorWeightedSobolev_ext_physical
  intro output k
  change
    (weightedSobolevCoefficients 2
      (periodicWeightedSobolevRestrict 2 base hbase
        (higherOrderLerayQuadratic base hbase state output))).1 k =
    (weightedSobolevCoefficients 2
      (weightedLerayQuadratic
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) state)
        output)).1 k
  rw [weightedSobolevCoefficients_restrict_apply,
    weightedLerayQuadratic_apply,
    unweighted_weightedLerayDivergenceConvolution_apply]
  let low := periodicVectorWeightedRestrictToThree (base + 1) (by omega) state
  have hgeneric := congrFun
    (vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      (base + 1) (by omega) state state k) output
  have hold := congrFun
    (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree low) (unweightedVectorThree low) k) output
  change vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder base
        (higherOrderLerayQuadratic base hbase state)) k output =
    (lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree low) (unweightedVectorThree low) output).1 k
  calc
    vectorCoefficientAt
        (nativeVectorUnderlyingAtOrder base
          (higherOrderLerayQuadratic base hbase state)) k output =
      lerayProjectMode k
        (fun out ↦ ∑ coordinate : Fin 3,
          (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
            (∑' p,
              (weightedSobolevCoefficients (base + 1) (state coordinate)).1 p *
                (weightedSobolevCoefficients (base + 1)
                  (state out)).1 (k - p))) output := by
      have horder : base + 1 - 1 = base := by omega
      rw [horder] at hgeneric
      convert hgeneric using 1
      rfl
    _ = lerayProjectMode k
        (fun out ↦
          (h3DivergenceConvolution
            (unweightedVectorThree low) (unweightedVectorThree low) out).1 k) output := by
      congr 1
      funext component
      rw [h3DivergenceConvolution_apply]
      apply Finset.sum_congr rfl
      intro coordinate _
      congr 1
      apply tsum_congr
      intro p
      change
        (weightedSobolevCoefficients (base + 1) (state coordinate)).1 p *
            (weightedSobolevCoefficients (base + 1) (state component)).1 (k - p) =
          (weightedSobolevCoefficients 3 (low coordinate)).1 p *
            (weightedSobolevCoefficients 3 (low component)).1 (k - p)
      simp only [low, periodicVectorWeightedRestrictToThree_apply,
        weightedSobolevCoefficients_restrict_apply]
    _ = (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree low) (unweightedVectorThree low) output).1 k := by
      simpa only [vectorCoefficientAt, periodicVectorSobolevTwoUnderlying] using hold.symm

/-- Restricting an arbitrary adjacent-order heat lift gives exactly the established `H² → H³`
heat passage on the restricted predecessor population. -/
theorem restrict_higherOrderHeatLift_to_twoToThree
    (base : ℕ) (hbase : 2 ≤ base)
    (nu tau : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (tau : ℝ))
    (state : PeriodicVectorWeightedSobolev base) :
    periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
        (higherOrderHeatLift base nu tau hviscous state) =
      periodicVectorWeightedHeatTwoToThree nu tau hviscous
        (periodicVectorWeightedSobolevRestrictCLM 2 base hbase state) := by
  apply periodicVectorWeightedSobolev_ext_physical
  intro component k
  change
    (weightedSobolevCoefficients 3
      (periodicWeightedSobolevRestrict 3 (base + 1) (by omega)
        (periodicVectorWeightedHeatScaleWord base 1 nu tau hviscous
          state component))).1 k =
    (weightedSobolevCoefficients 3
      (periodicWeightedHeatTwoToThree nu tau hviscous
        (periodicWeightedSobolevRestrict 2 base hbase (state component)))).1 k
  rw [weightedSobolevCoefficients_restrict_apply,
    weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply,
    pow_one, unweighted_periodicWeightedHeatTwoToThree_apply,
    weightedSobolevCoefficients_restrict_apply]

/-- Restriction commutes with the common endpoint-projection extension of a high path. -/
theorem restrict_weightedHigherOrderPathExtension_to_three
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) (t : ℝ) :
    periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
        (weightedHigherOrderPathExtension hT path t) =
      weightedPathExtension hT
        (higherOrderRestrictionPathToThree base hbase path) t := by
  rfl

/-- The high positive-time integrand restricts exactly to the established `H³` integrand. -/
theorem restrict_higherOrderDuhamelIntegrand_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) (path : WeightedHigherOrderPath base T) (s : ℝ) :
    periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
        (higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path) s) =
      weightedDuhamelIntegrand nu hnu t
        (weightedPathExtension hT
          (higherOrderRestrictionPathToThree base hbase path)) s := by
  by_cases hs : s < t
  · rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) hs,
      weightedDuhamelIntegrand_of_lt nu hnu t
        (weightedPathExtension hT
          (higherOrderRestrictionPathToThree base hbase path)) hs,
      restrict_higherOrderHeatLift_to_twoToThree base hbase]
    congr 1
    rw [restrict_higherOrderLerayQuadratic_to_weightedLerayQuadratic]
    congr 1
  · rw [higherOrderDuhamelIntegrand_of_not_lt base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) hs,
      weightedDuhamelIntegrand_of_not_lt nu hnu t
        (weightedPathExtension hT
          (higherOrderRestrictionPathToThree base hbase path)) hs]
    exact (periodicVectorWeightedSobolevRestrictCLM
      3 (base + 1) (by omega)).map_zero

/-- The bounded high-to-`H³` receiver commutes through the honest variable-terminal Bochner
integral. -/
theorem restrict_higherOrderDuhamelReturn_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
        (higherOrderDuhamelReturn base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path)) =
      weightedDuhamelReturn nu hnu hT
        (higherOrderRestrictionPathToThree base hbase path) t := by
  let restrict := periodicVectorWeightedSobolevRestrictCLM
    3 (base + 1) (by omega)
  have hintegrable := intervalIntegrable_higherOrderDuhamelIntegrand_path
    base hbase nu hnu hT path ht
  calc
    restrict (higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path)) =
      ∫ s in (0 : ℝ)..t, restrict
        (higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hT path) s) := by
        rw [higherOrderDuhamelReturn]
        exact restrict.intervalIntegral_comp_comm hintegrable |>.symm
    _ = ∫ s in (0 : ℝ)..t,
        weightedDuhamelIntegrand nu hnu t
          (weightedPathExtension hT
            (higherOrderRestrictionPathToThree base hbase path)) s := by
      refine intervalIntegral.integral_congr fun s _hs ↦ ?_
      exact restrict_higherOrderDuhamelIntegrand_to_weighted
        base hbase nu hnu hT t path s
    _ = weightedDuhamelReturn nu hnu hT
        (higherOrderRestrictionPathToThree base hbase path) t := by rfl

/-- Pathwise restriction is nonexpanding in the compact supremum norm. -/
theorem norm_higherOrderRestrictionPathToThree_le
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ}
    (path : WeightedHigherOrderPath base T) :
    ‖higherOrderRestrictionPathToThree base hbase path‖ ≤ ‖path‖ := by
  apply (ContinuousMap.norm_le
    (higherOrderRestrictionPathToThree base hbase path) (norm_nonneg path)).2
  intro t
  exact (norm_periodicVectorWeightedRestrictToThree_le
    (base + 1) (by omega) (path t)).trans (path.norm_coe_le_norm t)

/-- The complete high nonlinear path return restricts to the established `H³` nonlinear path. -/
theorem restrict_higherOrderDuhamelPath_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T) :
    higherOrderRestrictionPathToThree base hbase
        (higherOrderDuhamelPath base hbase nu hnu hT path) =
      weightedDuhamelPath nu hnu hT
        (higherOrderRestrictionPathToThree base hbase path) := by
  apply ContinuousMap.ext
  intro t
  exact restrict_higherOrderDuhamelReturn_to_weighted
    base hbase nu hnu hT path t.2

/-- The high linear heat orbit restricts to the established `H³` linear heat orbit. -/
theorem restrict_higherOrderLinearHeatPath_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    higherOrderRestrictionPathToThree base hbase
        (higherOrderLinearHeatPath base nu hT initial) =
      weightedLinearHeatPath nu hT
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial) := by
  apply ContinuousMap.ext
  intro t
  exact restrict_periodicVectorWeightedHeat 3 (base + 1) (by omega)
    nu (Real.toNNReal t.1) initial

/-- **Exact mild intertwiner.**  Restriction carries the complete high mild map to the
established `H³` mild map on the same aperture. -/
theorem restrict_higherOrderMildMap_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T) :
    higherOrderRestrictionPathToThree base hbase
        (higherOrderMildMap base hbase nu hnu hT initial path) =
      weightedMildMap nu hnu hT
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
        (higherOrderRestrictionPathToThree base hbase path) := by
  apply ContinuousMap.ext
  intro t
  change periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
      (higherOrderLinearHeatPath base nu hT initial t -
        higherOrderDuhamelPath base hbase nu hnu hT path t) =
    weightedLinearHeatPath nu hT
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial) t -
      weightedDuhamelPath nu hnu hT
        (higherOrderRestrictionPathToThree base hbase path) t
  rw [(periodicVectorWeightedSobolevRestrictCLM
      3 (base + 1) (by omega)).map_sub]
  have hlinear := ContinuousMap.congr_fun
    (restrict_higherOrderLinearHeatPath_to_weighted
      base hbase nu hT initial) t
  have hduhamel := ContinuousMap.congr_fun
    (restrict_higherOrderDuhamelPath_to_weighted
      base hbase nu hnu hT path) t
  change periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
      (higherOrderLinearHeatPath base nu hT initial t) =
    weightedLinearHeatPath nu hT
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial) t at hlinear
  change periodicVectorWeightedSobolevRestrictCLM 3 (base + 1) (by omega)
      (higherOrderDuhamelPath base hbase nu hnu hT path t) =
    weightedDuhamelPath nu hnu hT
      (higherOrderRestrictionPathToThree base hbase path) t at hduhamel
  rw [hlinear, hduhamel]

/-- Every high mild fixed point restricts to a fixed point of the established `H³` mild map on
the very same aperture. -/
theorem isFixedPt_restrict_higherOrderMildMap_to_weighted
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hT initial) path) :
    IsFixedPt
      (weightedMildMap nu hnu hT
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
      (higherOrderRestrictionPathToThree base hbase path) := by
  calc
    weightedMildMap nu hnu hT
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
        (higherOrderRestrictionPathToThree base hbase path) =
      higherOrderRestrictionPathToThree base hbase
        (higherOrderMildMap base hbase nu hnu hT initial path) :=
      (restrict_higherOrderMildMap_to_weighted
        base hbase nu hnu hT initial path).symm
    _ = higherOrderRestrictionPathToThree base hbase path :=
      congrArg (higherOrderRestrictionPathToThree base hbase) hfixed

/-- The arbitrary-order Banach return therefore comes with its exact established `H³` fixed
receiver on the common high aperture, without postulating a second solution. -/
theorem exists_higherOrderMildRestart_fixedPoint_with_weighted_receiver
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    ∃ u : WeightedHigherOrderPath base (higherOrderRestartTime base nu initial),
      ‖u‖ ≤ higherOrderRestartRadius initial ∧
      IsFixedPt (higherOrderMildRestartMap base hbase nu hnu initial) u ∧
      IsFixedPt
        (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
          (higherOrderRestartTime_pos base hnu initial).le
          (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
        (higherOrderRestrictionPathToThree base hbase u) ∧
      ‖higherOrderRestrictionPathToThree base hbase u‖ ≤
        higherOrderRestartRadius initial ∧
      u ⟨0, ⟨le_rfl, (higherOrderRestartTime_pos base hnu initial).le⟩⟩ = initial := by
  obtain ⟨u, hu, hfixed, hzero⟩ :=
    exists_higherOrderMildRestart_fixedPoint base hbase hnu initial
  refine ⟨u, hu, hfixed, ?_,
    (norm_higherOrderRestrictionPathToThree_le base hbase u).trans hu, hzero⟩
  exact isFixedPt_restrict_higherOrderMildMap_to_weighted
    base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (higherOrderRestartTime_pos base hnu initial).le initial u hfixed

section Audit

#print axioms continuousOn_higherOrderDuhamelReturn_path
#print axioms norm_higherOrderDuhamelPath_sub_le_sum
#print axioms exists_higherOrderMildRestart_fixedPoint
#print axioms restrict_higherOrderLerayQuadratic_to_weightedLerayQuadratic
#print axioms restrict_higherOrderDuhamelReturn_to_weighted
#print axioms restrict_higherOrderMildMap_to_weighted
#print axioms exists_higherOrderMildRestart_fixedPoint_with_weighted_receiver

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart
