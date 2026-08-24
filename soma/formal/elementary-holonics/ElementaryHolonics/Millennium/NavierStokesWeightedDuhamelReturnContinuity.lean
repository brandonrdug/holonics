import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelDifference
import ElementaryHolonics.Millennium.NavierStokesWeightedLinearPath

/-!
# Continuity of the native weighted Duhamel return

**[proved-derived]** This owner packages the endpoint-totalized positive-time integrand as its
actual Bochner return on the complete native path carrier.  Its main structural receipt is the
Volterra/heat-semigroup split: earlier source history is transported by the same-order heat orbit,
while only the newly exposed terminal interval remains.  The explicit one-derivative kernel budget
makes that recent tail vanish with its aperture.  Together with strong continuity of every fixed
heat orbit, this proves continuity in terminal time, including the zero-time face.

This is a path-space analytic port.  It asserts neither a fixed point nor a Navier--Stokes
solution.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelDifference
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The actual variable-terminal return -/

/-- The actual Bochner Duhamel return of one native continuous `H³` path. -/
def weightedDuhamelReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : ℝ) :
    PeriodicVectorWeightedSobolev 3 :=
  ∫ s in (0 : ℝ)..t,
    weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s

@[simp]
theorem weightedDuhamelReturn_zero
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    weightedDuhamelReturn nu hnu hT path 0 = 0 := by
  simp [weightedDuhamelReturn]

/-- Every terminal slice on the declared aperture is an honest Bochner-integrable passage. -/
theorem intervalIntegrable_weightedDuhamelIntegrand_path
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
      (weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path)) volume 0 t := by
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact IntervalIntegrable.refl
  · exact intervalIntegrable_weightedDuhamelIntegrand_of_continuousOn
      nu hnu htpos ‖path‖ (weightedPathExtension hT path)
      (weightedPathExtension hT path).continuous.continuousOn
      (fun s _ ↦ norm_weightedPathExtension_le hT path s)

/-! ## Exact semigroup transport of earlier history -/

/-- Componentwise positive-time smoothing factors through any earlier positive smoothing time. -/
theorem periodicVectorWeightedHeatTwoToThree_factor
    (nu tau delta : ℝ≥0) (hnu : 0 < (nu : ℝ)) (hdelta : 0 < (delta : ℝ))
    (hdeltaTau : delta ≤ tau) (state : PeriodicVectorWeightedSobolev 2) :
    periodicVectorWeightedHeatTwoToThree nu tau
        (mul_pos hnu (show 0 < (tau : ℝ) from
          lt_of_lt_of_le hdelta (by exact_mod_cast hdeltaTau))) state =
      periodicVectorWeightedHeat 3 nu (tau - delta)
        (periodicVectorWeightedHeatTwoToThree nu delta (mul_pos hnu hdelta) state) := by
  funext component
  exact periodicWeightedHeatTwoToThree_factor
    nu tau delta hnu hdelta hdeltaTau (state component)

/-- The nonnegative elapsed time between two ordered terminal faces. -/
def elapsedBetween (t a : ℝ) (hat : a ≤ t) : ℝ≥0 :=
  ⟨t - a, sub_nonneg.mpr hat⟩

@[simp]
theorem coe_elapsedBetween (t a : ℝ) (hat : a ≤ t) :
    ((elapsedBetween t a hat : ℝ≥0) : ℝ) = t - a :=
  rfl

/-- Before an earlier terminal time, changing the terminal face only adds a same-order heat
transport by the intervening elapsed time. -/
theorem weightedDuhamelIntegrand_later_eq_heat_earlier
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {a t s : ℝ}
    (hat : a ≤ t) (hsa : s < a)
    (u : ℝ → PeriodicVectorWeightedSobolev 3) :
    weightedDuhamelIntegrand nu hnu t u s =
      periodicVectorWeightedHeat 3 nu (elapsedBetween t a hat)
        (weightedDuhamelIntegrand nu hnu a u s) := by
  have hst : s < t := lt_of_lt_of_le hsa hat
  rw [weightedDuhamelIntegrand_of_lt nu hnu t u hst,
    weightedDuhamelIntegrand_of_lt nu hnu a u hsa]
  have hdeltaTau : positiveElapsed a s hsa ≤ positiveElapsed t s hst := by
    apply NNReal.coe_le_coe.mp
    simp only [coe_positiveElapsed]
    linarith
  have hfactor := periodicVectorWeightedHeatTwoToThree_factor
    nu (positiveElapsed t s hst) (positiveElapsed a s hsa) hnu
      (sub_pos.mpr hsa) hdeltaTau (weightedLerayQuadratic (u s))
  have helapsed : positiveElapsed t s hst - positiveElapsed a s hsa =
      elapsedBetween t a hat := by
    apply NNReal.eq
    rw [NNReal.coe_sub hdeltaTau]
    simp only [coe_positiveElapsed, coe_elapsedBetween]
    ring
  simpa only [helapsed] using hfactor

/-- On the earlier interval, the later-terminal integral is exactly the same-order heat transport
of the earlier-terminal return.  The one endpoint where the totalized representatives differ is
discarded by the atomless interval measure. -/
theorem intervalIntegral_earlier_eq_heat_weightedDuhamelReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hat : a ≤ t) :
    (∫ s in (0 : ℝ)..a,
        weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s) =
      periodicVectorWeightedHeat 3 nu (elapsedBetween t a hat)
        (weightedDuhamelReturn nu hnu hT path a) := by
  let heat := periodicVectorWeightedHeat 3 nu (elapsedBetween t a hat)
  have hAE :
      (fun s : ℝ ↦
        weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s) =ᵐ[
          volume.restrict (Ι (0 : ℝ) a)]
        (fun s : ℝ ↦ heat
          (weightedDuhamelIntegrand nu hnu a (weightedPathExtension hT path) s)) := by
    rw [uIoc_of_le ha.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact weightedDuhamelIntegrand_later_eq_heat_earlier
      nu hnu hat hs.2 (weightedPathExtension hT path)
  calc
    (∫ s in (0 : ℝ)..a,
        weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s) =
        ∫ s in (0 : ℝ)..a, heat
          (weightedDuhamelIntegrand nu hnu a (weightedPathExtension hT path) s) :=
      intervalIntegral.integral_congr_ae_restrict hAE
    _ = heat (∫ s in (0 : ℝ)..a,
          weightedDuhamelIntegrand nu hnu a (weightedPathExtension hT path) s) :=
      heat.intervalIntegral_comp_comm
        (intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ha)
    _ = periodicVectorWeightedHeat 3 nu (elapsedBetween t a hat)
          (weightedDuhamelReturn nu hnu hT path a) := by
      rfl

/-- Exact Volterra split of the variable-terminal Bochner return. -/
theorem weightedDuhamelReturn_eq_heat_add_tail
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) (hat : a ≤ t) :
    weightedDuhamelReturn nu hnu hT path t =
      periodicVectorWeightedHeat 3 nu (elapsedBetween t a hat)
          (weightedDuhamelReturn nu hnu hT path a) +
        ∫ s in a..t,
          weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s := by
  let integrand := fun s : ℝ ↦
    weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s
  have hfull : IntervalIntegrable integrand volume 0 t :=
    intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht
  have hearlier : IntervalIntegrable integrand volume 0 a := by
    apply hfull.mono_set
    rw [uIcc_of_le ha.1, uIcc_of_le ht.1]
    exact Icc_subset_Icc_right hat
  have htail : IntervalIntegrable integrand volume a t := by
    apply hfull.mono_set
    rw [uIcc_of_le hat, uIcc_of_le ht.1]
    exact Icc_subset_Icc ha.1 le_rfl
  rw [weightedDuhamelReturn, ← intervalIntegral.integral_add_adjacent_intervals
    hearlier htail]
  rw [intervalIntegral_earlier_eq_heat_weightedDuhamelReturn
    nu hnu hT path ha hat]

/-! ## Quantitative vanishing of the recent-history tail -/

/-- The scalar aperture budget carried by the one-derivative heat kernel. -/
def duhamelApertureBudget (nu : ℝ≥0) (delta : ℝ) : ℝ :=
  delta + 2 * Real.sqrt (delta / (2 * (nu : ℝ)))

@[simp]
theorem duhamelApertureBudget_zero (nu : ℝ≥0) :
    duhamelApertureBudget nu 0 = 0 := by
  simp [duhamelApertureBudget]

/-- The explicit aperture budget is continuous in its real time argument. -/
theorem continuous_duhamelApertureBudget (nu : ℝ≥0) :
    Continuous (duhamelApertureBudget nu) := by
  unfold duhamelApertureBudget
  fun_prop

/-- On nonnegative apertures the explicit kernel budget is nonnegative. -/
theorem duhamelApertureBudget_nonneg
    (nu : ℝ≥0) {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ duhamelApertureBudget nu delta := by
  exact add_nonneg hdelta (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The recent-history interval is controlled solely by its width and the path radius. -/
theorem norm_weightedDuhamelTail_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {a t : ℝ} (hat : a ≤ t) :
    ‖∫ s in a..t,
        weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2 *
        duhamelApertureBudget nu (t - a) := by
  rcases hat.eq_or_lt with rfl | hatlt
  · simp
  · let K : ℝ := (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg
        (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
        (sq_nonneg ‖path‖)
    have hdelta : 0 < t - a := sub_pos.mpr hatlt
    have hreflected : IntervalIntegrable
        (fun s : ℝ ↦ duhamelHeatKernelMajorant (nu : ℝ) (t - s))
        volume a t := by
      have hbase := intervalIntegrable_duhamelHeatKernelMajorant hnu hdelta
      have hreflect := (hbase.comp_sub_left t).symm
      convert hreflect using 1 <;> ring
    have hmajorant : IntervalIntegrable
        (fun s : ℝ ↦ K * duhamelHeatKernelMajorant (nu : ℝ) (t - s))
        volume a t := hreflected.const_mul K
    have hnorm :
        ‖∫ s in a..t,
            weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s‖ ≤
          ∫ s in a..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hat
      · filter_upwards with s
        intro _hs
        simpa only [K] using norm_weightedDuhamelIntegrand_le_of_norm_le
          nu hnu t ‖path‖ (weightedPathExtension hT path) s
            (norm_nonneg path) (norm_weightedPathExtension_le hT path s)
      · exact hmajorant
    calc
      ‖∫ s in a..t,
          weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s‖ ≤
          ∫ s in a..t,
            K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
      _ = K * ∫ s in a..t,
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * ∫ tau in (0 : ℝ)..(t - a),
          duhamelHeatKernelMajorant (nu : ℝ) tau := by
        rw [intervalIntegral.integral_comp_sub_left]
        simp only [sub_self]
      _ ≤ K * duhamelApertureBudget nu (t - a) := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral_duhamelHeatKernelMajorant_le hnu hdelta) hK
      _ = (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2 *
          duhamelApertureBudget nu (t - a) := by
        rfl

/-- Pointwise one-path control of the actual variable-terminal return. -/
theorem norm_weightedDuhamelReturn_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖weightedDuhamelReturn nu hnu hT path t‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2 *
        duhamelApertureBudget nu t := by
  simpa only [weightedDuhamelReturn, sub_zero] using
    norm_weightedDuhamelTail_le nu hnu hT path ht.1

/-! ## Continuity at the initial face -/

/-- The variable-terminal return is continuous within its aperture at time zero. -/
theorem continuousWithinAt_weightedDuhamelReturn_zero
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    ContinuousWithinAt (weightedDuhamelReturn nu hnu hT path) (Icc (0 : ℝ) T) 0 := by
  let K : ℝ := (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
      (sq_nonneg ‖path‖)
  have hscalar : Continuous (fun t : ℝ ↦ K * duhamelApertureBudget nu t) :=
    continuous_const.mul (continuous_duhamelApertureBudget nu)
  rw [Metric.continuousWithinAt_iff]
  intro epsilon hepsilon
  have hscalarAt : ContinuousAt
      (fun t : ℝ ↦ K * duhamelApertureBudget nu t) 0 := hscalar.continuousAt
  rw [Metric.continuousAt_iff] at hscalarAt
  obtain ⟨delta, hdelta, hnear⟩ :=
    hscalarAt epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro t ht hdist
  have hscalarNear := hnear hdist
  have hbudgetNonneg : 0 ≤ K * duhamelApertureBudget nu t :=
    mul_nonneg hK (duhamelApertureBudget_nonneg nu ht.1)
  have hbudgetLt : K * duhamelApertureBudget nu t < epsilon := by
    simpa only [duhamelApertureBudget_zero, mul_zero, Real.dist_eq,
      sub_zero, abs_of_nonneg hbudgetNonneg] using hscalarNear
  have hreturn := norm_weightedDuhamelReturn_le nu hnu hT path ht
  change ‖weightedDuhamelReturn nu hnu hT path t‖ ≤
      K * duhamelApertureBudget nu t at hreturn
  simpa only [weightedDuhamelReturn_zero, dist_zero_right] using
    hreturn.trans_lt hbudgetLt

/-! ## Continuity at every positive terminal face -/

/-- At a positive terminal time, one fixed earlier face supplies a continuous heat-orbit model;
both discarded recent-history tails are uniformly small by the aperture budget. -/
theorem continuousWithinAt_weightedDuhamelReturn_of_pos
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht₀pos : 0 < t₀) :
    ContinuousWithinAt (weightedDuhamelReturn nu hnu hT path)
      (Icc (0 : ℝ) T) t₀ := by
  let K : ℝ := (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
      (sq_nonneg ‖path‖)
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
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have hat₀ : a ≤ t₀ := by
    dsimp [a]
    linarith
  have hat₀lt : a < t₀ := by
    dsimp [a]
    linarith
  have ha : a ∈ Icc (0 : ℝ) T := ⟨ha0, hat₀.trans ht₀.2⟩
  have ht₀sub : t₀ - a = d := by
    dsimp [a]
    ring
  have hdistDZero : dist d (0 : ℝ) < rho := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdpos]
    exact hdltRho
  have hbudgetDdist := hbudgetNearZero hdistDZero
  have hbudgetDNonneg : 0 ≤ K * duhamelApertureBudget nu d :=
    mul_nonneg hK (duhamelApertureBudget_nonneg nu hdpos.le)
  have hbudgetD : K * duhamelApertureBudget nu d < epsilon / 6 := by
    simpa only [duhamelApertureBudget_zero, mul_zero, Real.dist_eq,
      sub_zero, abs_of_nonneg hbudgetDNonneg] using hbudgetDdist
  let earlier := weightedDuhamelReturn nu hnu hT path a
  let model : ℝ → PeriodicVectorWeightedSobolev 3 := fun t ↦
    periodicVectorWeightedHeat 3 nu (Real.toNNReal (t - a)) earlier
  let recent : ℝ → PeriodicVectorWeightedSobolev 3 := fun t ↦
    ∫ s in a..t,
      weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path) s
  let localBudget : ℝ → ℝ := fun t ↦
    K * duhamelApertureBudget nu (t - a)
  have hmodelContinuous : Continuous model := by
    exact (continuous_periodicVectorWeightedHeat_orbit 3 nu earlier).comp
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
  have hdistD : dist t t₀ < d :=
    hdist.trans_le (min_le_left _ _)
  have habsD : |t - t₀| < d := by
    simpa only [Real.dist_eq] using hdistD
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
  have hlocalBudgetBase : localBudget t₀ =
      K * duhamelApertureBudget nu d := by
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
  have hsplit : weightedDuhamelReturn nu hnu hT path t =
      model t + recent t := by
    simpa only [model, earlier, recent, helapsed] using
      weightedDuhamelReturn_eq_heat_add_tail nu hnu hT path ha ht hat
  have hsplit₀ : weightedDuhamelReturn nu hnu hT path t₀ =
      model t₀ + recent t₀ := by
    simpa only [model, earlier, recent, helapsed₀] using
      weightedDuhamelReturn_eq_heat_add_tail nu hnu hT path ha ht₀ hat₀
  have hrecent : ‖recent t‖ < epsilon / 3 := by
    have htail := norm_weightedDuhamelTail_le nu hnu hT path hat
    change ‖recent t‖ ≤ localBudget t at htail
    exact htail.trans_lt hlocalBudgetLt
  have hrecent₀ : ‖recent t₀‖ < epsilon / 6 := by
    have htail := norm_weightedDuhamelTail_le nu hnu hT path hat₀
    change ‖recent t₀‖ ≤ K * duhamelApertureBudget nu (t₀ - a) at htail
    rw [ht₀sub] at htail
    exact htail.trans_lt hbudgetD
  rw [hsplit, hsplit₀, dist_eq_norm]
  calc
    ‖model t + recent t - (model t₀ + recent t₀)‖ =
        ‖(model t - model t₀) + (recent t - recent t₀)‖ := by
      congr 1
      abel
    _ ≤ ‖model t - model t₀‖ + ‖recent t - recent t₀‖ :=
      norm_add_le _ _
    _ ≤ ‖model t - model t₀‖ + (‖recent t‖ + ‖recent t₀‖) :=
      add_le_add_right (norm_sub_le _ _) _
    _ < epsilon := by
      linarith

/-! ## The returned continuous path -/

/-- The actual Bochner Duhamel return is continuous in terminal time on the full closed aperture. -/
theorem continuousOn_weightedDuhamelReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    ContinuousOn (weightedDuhamelReturn nu hnu hT path) (Icc (0 : ℝ) T) := by
  intro t ht
  rcases ht.1.eq_or_lt with hzero | hpos
  · subst t
    exact continuousWithinAt_weightedDuhamelReturn_zero nu hnu hT path
  · exact continuousWithinAt_weightedDuhamelReturn_of_pos
      nu hnu hT path ht hpos

/-- The nonlinear Volterra passage as an element of the complete native path carrier. -/
def weightedDuhamelPath
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) : WeightedH3Path T where
  toFun := fun t ↦ weightedDuhamelReturn nu hnu hT path t.1
  continuous_toFun :=
    (continuousOn_iff_continuous_restrict.mp
      (continuousOn_weightedDuhamelReturn nu hnu hT path))

@[simp]
theorem weightedDuhamelPath_apply
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : Icc (0 : ℝ) T) :
    weightedDuhamelPath nu hnu hT path t =
      weightedDuhamelReturn nu hnu hT path t.1 :=
  rfl

@[simp]
theorem weightedDuhamelPath_zero
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    weightedDuhamelPath nu hnu hT path ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := by
  simp only [weightedDuhamelPath_apply, weightedDuhamelReturn_zero]

/-- The aperture budget is monotone on nonnegative elapsed times. -/
theorem duhamelApertureBudget_mono
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {a b : ℝ} (hab : a ≤ b) :
    duhamelApertureBudget nu a ≤ duhamelApertureBudget nu b := by
  have hden : 0 < 2 * (nu : ℝ) := mul_pos (by norm_num) hnu
  have hdiv : a / (2 * (nu : ℝ)) ≤ b / (2 * (nu : ℝ)) :=
    (div_le_div_iff_of_pos_right hden).2 hab
  unfold duhamelApertureBudget
  exact add_le_add hab (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt hdiv) (by norm_num))

/-- Supremum-norm control of the actual nonlinear path return. -/
theorem norm_weightedDuhamelPath_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    ‖weightedDuhamelPath nu hnu hT path‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2 *
        duhamelApertureBudget nu T := by
  let K : ℝ := (23328 * periodicH3EmbeddingConstant) * ‖path‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
      (sq_nonneg ‖path‖)
  apply (ContinuousMap.norm_le (weightedDuhamelPath nu hnu hT path)
    (mul_nonneg hK (duhamelApertureBudget_nonneg nu hT))).2
  intro t
  rw [weightedDuhamelPath_apply]
  have hpoint := norm_weightedDuhamelReturn_le nu hnu hT path t.2
  change ‖weightedDuhamelReturn nu hnu hT path t.1‖ ≤
      K * duhamelApertureBudget nu t.1 at hpoint
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (duhamelApertureBudget_mono nu hnu t.2.2) hK)

/-! ## Actual two-path return and path-space separation -/

/-- On a common path ball, the difference of the two actual Bochner returns has the exact
Volterra Lipschitz budget. -/
theorem norm_weightedDuhamelReturn_sub_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedH3Path T) (R : ℝ) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖weightedDuhamelReturn nu hnu hT u t -
        weightedDuhamelReturn nu hnu hT v t‖ ≤
      (23328 * periodicH3EmbeddingConstant) * (2 * R) * ‖u - v‖ *
        duhamelApertureBudget nu t := by
  rcases ht.1.eq_or_lt with hzero | htpos
  · subst t
    simp
  · have huIntegrable :=
      intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT u ht
    have hvIntegrable :=
      intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT v ht
    rw [weightedDuhamelReturn, weightedDuhamelReturn,
      ← intervalIntegral.integral_sub huIntegrable hvIntegrable]
    simpa only [duhamelApertureBudget] using
      (norm_intervalIntegral_weightedDuhamelIntegrand_sub_le
        nu hnu htpos R ‖u - v‖
          (weightedPathExtension hT u) (weightedPathExtension hT v)
          (fun s _ ↦ (norm_weightedPathExtension_le hT u s).trans hu)
          (fun s _ ↦ (norm_weightedPathExtension_le hT v s).trans hv)
          (fun s _ ↦ norm_weightedPathExtension_sub_le hT u v s))

/-- The nonlinear Duhamel passage is locally Lipschitz as an actual map of the complete native
path carrier, with the same explicit aperture budget. -/
theorem norm_weightedDuhamelPath_sub_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (u v : WeightedH3Path T) (R : ℝ) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖weightedDuhamelPath nu hnu hT u - weightedDuhamelPath nu hnu hT v‖ ≤
      (23328 * periodicH3EmbeddingConstant) * (2 * R) * ‖u - v‖ *
        duhamelApertureBudget nu T := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  let L : ℝ := (23328 * periodicH3EmbeddingConstant) * (2 * R) * ‖u - v‖
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
        (mul_nonneg (by norm_num) hR))
      (norm_nonneg (u - v))
  apply (ContinuousMap.norm_le
    (weightedDuhamelPath nu hnu hT u - weightedDuhamelPath nu hnu hT v)
    (mul_nonneg hL (duhamelApertureBudget_nonneg nu hT))).2
  intro t
  change ‖weightedDuhamelReturn nu hnu hT u t.1 -
      weightedDuhamelReturn nu hnu hT v t.1‖ ≤
    L * duhamelApertureBudget nu T
  have hpoint := norm_weightedDuhamelReturn_sub_le
    nu hnu hT u v R hu hv t.2
  change ‖weightedDuhamelReturn nu hnu hT u t.1 -
      weightedDuhamelReturn nu hnu hT v t.1‖ ≤
    L * duhamelApertureBudget nu t.1 at hpoint
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (duhamelApertureBudget_mono nu hnu t.2.2) hL)

section Audit

#print axioms weightedDuhamelReturn_eq_heat_add_tail
#print axioms norm_weightedDuhamelTail_le
#print axioms continuousOn_weightedDuhamelReturn
#print axioms weightedDuhamelPath
#print axioms norm_weightedDuhamelPath_le
#print axioms norm_weightedDuhamelPath_sub_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
