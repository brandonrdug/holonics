import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelBound

/-!
# Joint positive-time continuity of the weighted Duhamel passage

The weighted heat owner supplies strong continuity at elapsed time zero on every fixed native
Sobolev carrier, as well as the exact semigroup law.  This file composes those two receipts to
obtain strong continuity at every nonnegative same-order time, then factors the one-derivative
`H² → H³` passage through a fixed positive smoothing time.  The result is joint continuity in
positive elapsed time and the source state.

Applied to a continuous `H³` path, this closes the only measurability port left open by
`NavierStokesWeightedDuhamelBound`: the endpoint-totalized integrand is continuous away from its
single terminal endpoint, hence strongly measurable almost everywhere and honestly Bochner
interval-integrable.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Strong continuity of the same-order heat orbit -/

private theorem nndist_eq_tsub_of_le {a b : ℝ≥0} (h : b ≤ a) :
    nndist a b = a - b := by
  apply NNReal.eq
  rw [coe_nndist, NNReal.dist_eq, abs_of_nonneg]
  · exact (NNReal.coe_sub h).symm
  · exact sub_nonneg.mpr h

/-- Two points on a contractive heat orbit differ by no more than the zero-time orbit displacement
at their elapsed-time distance. -/
theorem norm_periodicWeightedHeat_sub_le_nndist
    (order : ℕ) (nu tau tau₀ : ℝ≥0) (state : PeriodicWeightedSobolev order) :
    ‖periodicWeightedHeat order nu tau state -
        periodicWeightedHeat order nu tau₀ state‖ ≤
      ‖periodicWeightedHeat order nu (nndist tau tau₀) state - state‖ := by
  rcases le_total tau₀ tau with hforward | hbackward
  · have hadd : tau₀ + (tau - tau₀) = tau := by
      rw [add_comm, tsub_add_cancel_of_le hforward]
    have horbit : periodicWeightedHeat order nu tau state =
        periodicWeightedHeat order nu tau₀
          (periodicWeightedHeat order nu (tau - tau₀) state) := by
      have hsemigroup := congrArg (fun operator ↦ operator state)
        (periodicWeightedHeat_add order nu tau₀ (tau - tau₀))
      simpa only [hadd, ContinuousLinearMap.comp_apply] using hsemigroup
    rw [horbit, ← map_sub]
    calc
      ‖periodicWeightedHeat order nu tau₀
          (periodicWeightedHeat order nu (tau - tau₀) state - state)‖ ≤
          ‖periodicWeightedHeat order nu (tau - tau₀) state - state‖ :=
        norm_periodicWeightedHeat_le order nu tau₀ _
      _ = ‖periodicWeightedHeat order nu (nndist tau tau₀) state - state‖ := by
        rw [nndist_eq_tsub_of_le hforward]
  · have hadd : tau + (tau₀ - tau) = tau₀ := by
      rw [add_comm, tsub_add_cancel_of_le hbackward]
    have horbit : periodicWeightedHeat order nu tau₀ state =
        periodicWeightedHeat order nu tau
          (periodicWeightedHeat order nu (tau₀ - tau) state) := by
      have hsemigroup := congrArg (fun operator ↦ operator state)
        (periodicWeightedHeat_add order nu tau (tau₀ - tau))
      simpa only [hadd, ContinuousLinearMap.comp_apply] using hsemigroup
    rw [horbit, ← map_sub]
    calc
      ‖periodicWeightedHeat order nu tau
          (state - periodicWeightedHeat order nu (tau₀ - tau) state)‖ ≤
          ‖state - periodicWeightedHeat order nu (tau₀ - tau) state‖ :=
        norm_periodicWeightedHeat_le order nu tau _
      _ = ‖periodicWeightedHeat order nu (tau₀ - tau) state - state‖ :=
        norm_sub_rev _ _
      _ = ‖periodicWeightedHeat order nu (nndist tau tau₀) state - state‖ := by
        rw [nndist_comm, nndist_eq_tsub_of_le hbackward]

/-- Every same-order weighted heat orbit is strongly continuous at every elapsed time. -/
theorem continuous_periodicWeightedHeat_orbit
    (order : ℕ) (nu : ℝ≥0) (state : PeriodicWeightedSobolev order) :
    Continuous (fun tau : ℝ≥0 ↦ periodicWeightedHeat order nu tau state) := by
  rw [continuous_iff_continuousAt]
  intro tau₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hnndist : Tendsto (fun tau : ℝ≥0 ↦ nndist tau tau₀)
      (nhds tau₀) (nhds 0) := by
    have hcontinuous : Continuous (fun tau : ℝ≥0 ↦ nndist tau tau₀) := by
      fun_prop
    simpa only [nndist_self] using hcontinuous.tendsto tau₀
  have hzero := (tendsto_periodicWeightedHeat_zero_time order nu state).comp hnndist
  have hupper : Tendsto
      (fun tau : ℝ≥0 ↦
        ‖periodicWeightedHeat order nu (nndist tau tau₀) state - state‖)
      (nhds tau₀) (nhds (0 : ℝ)) := by
    have hsub := hzero.sub_const state
    change Tendsto
      ((fun value : PeriodicWeightedSobolev order ↦ ‖value‖) ∘
        fun tau : ℝ≥0 ↦
          (((fun elapsed : ℝ≥0 ↦ periodicWeightedHeat order nu elapsed state) ∘
            fun point : ℝ≥0 ↦ nndist point tau₀) tau) - state)
      (nhds tau₀) (nhds (0 : ℝ))
    simpa only [sub_self, norm_zero] using tendsto_norm.comp hsub
  simpa only [dist_eq_norm] using squeeze_zero
    (fun tau ↦ norm_nonneg
      (periodicWeightedHeat order nu tau state - periodicWeightedHeat order nu tau₀ state))
    (fun tau ↦ norm_periodicWeightedHeat_sub_le_nndist order nu tau tau₀ state)
    hupper

/-- Same-order heat transport is jointly continuous in elapsed time and the native state. -/
theorem continuous_periodicWeightedHeat_joint
    (order : ℕ) (nu : ℝ≥0) :
    Continuous (fun pair : ℝ≥0 × PeriodicWeightedSobolev order ↦
      periodicWeightedHeat order nu pair.1 pair.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨tau₀, state₀⟩
  apply tendsto_iff_dist_tendsto_zero.2
  let upper : ℝ≥0 × PeriodicWeightedSobolev order → ℝ := fun pair ↦
    dist pair.2 state₀ +
      dist (periodicWeightedHeat order nu pair.1 state₀)
        (periodicWeightedHeat order nu tau₀ state₀)
  have hfirst : Tendsto
      (fun pair : ℝ≥0 × PeriodicWeightedSobolev order ↦ dist pair.2 state₀)
      (nhds (tau₀, state₀)) (nhds (0 : ℝ)) := by
    have hcontinuous : Continuous
        (fun pair : ℝ≥0 × PeriodicWeightedSobolev order ↦ dist pair.2 state₀) := by
      fun_prop
    simpa only [dist_self] using hcontinuous.tendsto (tau₀, state₀)
  have horbit := continuous_periodicWeightedHeat_orbit order nu state₀
  have hsecond : Tendsto
      (fun pair : ℝ≥0 × PeriodicWeightedSobolev order ↦
        dist (periodicWeightedHeat order nu pair.1 state₀)
          (periodicWeightedHeat order nu tau₀ state₀))
      (nhds (tau₀, state₀)) (nhds (0 : ℝ)) := by
    have hcontinuous : Continuous
        (fun pair : ℝ≥0 × PeriodicWeightedSobolev order ↦
          dist (periodicWeightedHeat order nu pair.1 state₀)
            (periodicWeightedHeat order nu tau₀ state₀)) :=
      (horbit.comp continuous_fst).dist continuous_const
    simpa only [dist_self] using hcontinuous.tendsto (tau₀, state₀)
  have hupper : Tendsto upper (nhds (tau₀, state₀)) (nhds (0 : ℝ)) := by
    simpa only [upper, zero_add] using hfirst.add hsecond
  apply squeeze_zero (fun pair ↦ dist_nonneg) _ hupper
  intro pair
  calc
    dist (periodicWeightedHeat order nu pair.1 pair.2)
        (periodicWeightedHeat order nu tau₀ state₀) =
        ‖periodicWeightedHeat order nu pair.1 pair.2 -
          periodicWeightedHeat order nu tau₀ state₀‖ := dist_eq_norm _ _
    _ ≤ ‖periodicWeightedHeat order nu pair.1 pair.2 -
          periodicWeightedHeat order nu pair.1 state₀‖ +
        ‖periodicWeightedHeat order nu pair.1 state₀ -
          periodicWeightedHeat order nu tau₀ state₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖pair.2 - state₀‖ +
        ‖periodicWeightedHeat order nu pair.1 state₀ -
          periodicWeightedHeat order nu tau₀ state₀‖ := by
      gcongr
      rw [← map_sub]
      exact norm_periodicWeightedHeat_le order nu pair.1 _
    _ = upper pair := by
      simp only [upper, dist_eq_norm]

/-! ## Positive-time `H² → H³` factorization -/

/-- Once a fixed positive smoothing time `delta` has acted, every later `H² → H³` heat
passage is the same-order `H³` heat orbit of that returned state. -/
theorem periodicWeightedHeatTwoToThree_factor
    (nu tau delta : ℝ≥0) (hnu : 0 < (nu : ℝ)) (hdelta : 0 < (delta : ℝ))
    (hdeltaTau : delta ≤ tau) (state : PeriodicWeightedSobolev 2) :
    periodicWeightedHeatTwoToThree nu tau
        (mul_pos hnu (show 0 < (tau : ℝ) from
          lt_of_lt_of_le hdelta (by exact_mod_cast hdeltaTau))) state =
      periodicWeightedHeat 3 nu (tau - delta)
        (periodicWeightedHeatTwoToThree nu delta (mul_pos hnu hdelta) state) := by
  apply Subtype.ext
  funext k
  simp only [periodicWeightedHeatTwoToThree_apply, periodicWeightedHeat_apply,
    NNReal.coe_sub hdeltaTau]
  have htime : (tau : ℝ) = ((tau : ℝ) - (delta : ℝ)) + (delta : ℝ) := by
    have hreal : (delta : ℝ) ≤ (tau : ℝ) := by exact_mod_cast hdeltaTau
    linarith
  rw [htime, heatStokesMultiplier_add, Complex.ofReal_mul]
  ring_nf

/-- Positive elapsed times, carrying the proof that the one-derivative heat passage is defined. -/
abbrev PositiveElapsedTime := {tau : ℝ≥0 // 0 < (tau : ℝ)}

/-- The one-derivative weighted heat passage as a joint map of positive elapsed time and source. -/
def periodicWeightedHeatTwoToThreeJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (pair : PositiveElapsedTime × PeriodicWeightedSobolev 2) :
    PeriodicWeightedSobolev 3 :=
  periodicWeightedHeatTwoToThree nu pair.1.1
    (mul_pos hnu pair.1.2) pair.2

/-- The scalar native `H² → H³` heat passage is jointly continuous on strictly positive
elapsed time and the source state. -/
theorem continuous_periodicWeightedHeatTwoToThreeJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) :
    Continuous (periodicWeightedHeatTwoToThreeJoint nu hnu) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨tau₀, htau₀⟩, state₀⟩
  let delta : ℝ≥0 := tau₀ / 2
  have hdelta : 0 < (delta : ℝ) := by
    dsimp [delta]
    positivity
  have hdeltaLt : delta < tau₀ := by
    apply NNReal.coe_lt_coe.mp
    dsimp [delta]
    linarith
  let fixedSmooth : PeriodicWeightedSobolev 2 →L[ℂ] PeriodicWeightedSobolev 3 :=
    periodicWeightedHeatTwoToThreeCLM nu delta (mul_pos hnu hdelta)
  let factored : PositiveElapsedTime × PeriodicWeightedSobolev 2 →
      PeriodicWeightedSobolev 3 := fun pair ↦
    periodicWeightedHeat 3 nu (pair.1.1 - delta) (fixedSmooth pair.2)
  have htime : Continuous
      (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 ↦ pair.1.1 - delta) := by
    fun_prop
  have hsource : Continuous
      (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 ↦ fixedSmooth pair.2) := by
    fun_prop
  have hfactored : Continuous factored := by
    have hpair : Continuous
        (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 ↦
          (pair.1.1 - delta, fixedSmooth pair.2)) :=
      htime.prodMk hsource
    have hjoint := continuous_periodicWeightedHeat_joint 3 nu
    change Continuous
      ((fun pair : ℝ≥0 × PeriodicWeightedSobolev 3 ↦
          periodicWeightedHeat 3 nu pair.1 pair.2) ∘
        fun pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 ↦
          (pair.1.1 - delta, fixedSmooth pair.2))
    exact hjoint.comp hpair
  have heventually : ∀ᶠ pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 in
      nhds (⟨⟨tau₀, htau₀⟩, state₀⟩ : PositiveElapsedTime × PeriodicWeightedSobolev 2),
      delta ≤ pair.1.1 := by
    have hfirst : ∀ᶠ time : PositiveElapsedTime in nhds ⟨tau₀, htau₀⟩,
        delta < time.1 :=
      (continuous_subtype_val.tendsto ⟨tau₀, htau₀⟩).eventually
        (Ioi_mem_nhds hdeltaLt)
    have hfst : Tendsto
        (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev 2 ↦ pair.1)
        (nhds (⟨tau₀, htau₀⟩, state₀)) (nhds ⟨tau₀, htau₀⟩) :=
      continuous_fst.tendsto _
    exact (hfst.eventually hfirst).mono fun pair hp ↦ hp.le
  apply hfactored.continuousAt.congr_of_eventuallyEq
  filter_upwards [heventually] with pair hp
  dsimp only [periodicWeightedHeatTwoToThreeJoint, factored, fixedSmooth]
  exact periodicWeightedHeatTwoToThree_factor nu pair.1.1 delta hnu hdelta hp pair.2

/-! ## Three-component joint passage -/

/-- Componentwise joint positive-time smoothing for the native velocity carrier. -/
def periodicVectorWeightedHeatTwoToThreeJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2) :
    PeriodicVectorWeightedSobolev 3 := fun component ↦
  periodicWeightedHeatTwoToThreeJoint nu hnu ⟨pair.1, pair.2 component⟩

/-- The componentwise one-derivative heat passage is jointly continuous. -/
theorem continuous_periodicVectorWeightedHeatTwoToThreeJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) :
    Continuous (periodicVectorWeightedHeatTwoToThreeJoint nu hnu) := by
  apply continuous_pi
  intro component
  exact (continuous_periodicWeightedHeatTwoToThreeJoint nu hnu).comp
    (continuous_fst.prodMk (continuous_apply component |>.comp continuous_snd))

/-! ## The endpoint-totalized Duhamel integrand -/

/-- Elapsed time before a terminal time, now packaged as a strictly positive heat time. -/
def positiveElapsedBefore (t : ℝ) (s : Iio t) : PositiveElapsedTime :=
  ⟨Real.toNNReal (t - s.1), by
    exact_mod_cast Real.toNNReal_pos.mpr (sub_pos.mpr s.2)⟩

/-- Positive elapsed time varies continuously on the open past of the terminal time. -/
theorem continuous_positiveElapsedBefore (t : ℝ) :
    Continuous (positiveElapsedBefore t) := by
  exact (continuous_real_toNNReal.comp
    (continuous_const.sub continuous_subtype_val)).subtype_mk _

private theorem positiveElapsedBefore_eq
    (t : ℝ) (s : Iio t) :
    (positiveElapsedBefore t s).1 = positiveElapsed t s.1 s.2 := by
  apply NNReal.eq
  rw [show ((positiveElapsedBefore t s).1 : ℝ) = t - s.1 by
    exact Real.coe_toNNReal (t - s.1) (sub_nonneg.mpr s.2.le)]
  rfl

/-- A path continuous on `[0,t]` produces an actual Duhamel integrand continuous at every
interior time.  The singular terminal value itself is deliberately excluded. -/
theorem continuousOn_weightedDuhamelIntegrand_Ioo
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ContinuousOn u (Icc (0 : ℝ) t)) :
    ContinuousOn (weightedDuhamelIntegrand nu hnu t u) (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have huInterior : Continuous (fun s : Ioo (0 : ℝ) t ↦ u s.1) :=
    continuousOn_iff_continuous_domRestrict.mp (hu.mono Ioo_subset_Icc_self)
  have hsource : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ weightedLerayQuadratic (u s.1)) :=
    continuous_weightedLerayQuadratic.comp huInterior
  have helapsed : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t)) := by
    exact (continuous_positiveElapsedBefore t).comp
      (continuous_subtype_val.subtype_mk _)
  have hmodel : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        periodicVectorWeightedHeatTwoToThreeJoint nu hnu
          ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
            weightedLerayQuadratic (u s.1)⟩) :=
    (continuous_periodicVectorWeightedHeatTwoToThreeJoint nu hnu).comp
      (helapsed.prodMk hsource)
  apply hmodel.congr
  intro s
  change periodicVectorWeightedHeatTwoToThreeJoint nu hnu
      ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
        weightedLerayQuadratic (u s.1)⟩ = weightedDuhamelIntegrand nu hnu t u s.1
  rw [weightedDuhamelIntegrand_of_lt nu hnu t u s.2.2]
  have helapsedEq : positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t) =
      (⟨positiveElapsed t s.1 s.2.2, sub_pos.mpr s.2.2⟩ : PositiveElapsedTime) := by
    apply Subtype.ext
    exact positiveElapsedBefore_eq t ⟨s.1, s.2.2⟩
  rw [helapsedEq]
  rfl

/-- The terminal endpoint is a null set, so interior continuity closes the exact
almost-everywhere strong-measurability port required by the Bochner integral. -/
theorem aestronglyMeasurable_weightedDuhamelIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ContinuousOn u (Icc (0 : ℝ) t)) :
    AEStronglyMeasurable (weightedDuhamelIntegrand nu hnu t u)
      (volume.restrict (Ioc (0 : ℝ) t)) := by
  let : SecondCountableTopologyEither ℝ (PeriodicVectorWeightedSobolev 3) :=
    ⟨Or.inl (by infer_instance)⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_weightedDuhamelIntegrand_Ioo nu hnu u hu).aestronglyMeasurable
    measurableSet_Ioo

/-- The endpoint-totalized native Duhamel integrand is honestly interval-integrable for every
continuous path lying in a bounded `H³` ball. -/
theorem intervalIntegrable_weightedDuhamelIntegrand_of_continuousOn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (huContinuous : ContinuousOn u (Icc (0 : ℝ) t))
    (huBound : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R) :
    IntervalIntegrable (weightedDuhamelIntegrand nu hnu t u) volume 0 t :=
  intervalIntegrable_weightedDuhamelIntegrand nu hnu ht R u huBound
    (aestronglyMeasurable_weightedDuhamelIntegrand nu hnu u huContinuous)

/-- The meaningful Bochner return: honest interval integrability together with the explicit
quadratic Duhamel budget. -/
theorem weightedDuhamelIntegrable_and_norm_integral_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (huContinuous : ContinuousOn u (Icc (0 : ℝ) t))
    (huBound : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R) :
    IntervalIntegrable (weightedDuhamelIntegrand nu hnu t u) volume 0 t ∧
      ‖∫ s in (0 : ℝ)..t, weightedDuhamelIntegrand nu hnu t u s‖ ≤
        (23328 * periodicH3EmbeddingConstant) * R ^ 2 *
          (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
  ⟨intervalIntegrable_weightedDuhamelIntegrand_of_continuousOn
      nu hnu ht R u huContinuous huBound,
    norm_intervalIntegral_weightedDuhamelIntegrand_le nu hnu ht R u huBound⟩

section Audit

#print axioms continuous_periodicWeightedHeat_orbit
#print axioms continuous_periodicWeightedHeat_joint
#print axioms continuous_periodicWeightedHeatTwoToThreeJoint
#print axioms continuous_periodicVectorWeightedHeatTwoToThreeJoint
#print axioms aestronglyMeasurable_weightedDuhamelIntegrand
#print axioms intervalIntegrable_weightedDuhamelIntegrand_of_continuousOn
#print axioms weightedDuhamelIntegrable_and_norm_integral_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
