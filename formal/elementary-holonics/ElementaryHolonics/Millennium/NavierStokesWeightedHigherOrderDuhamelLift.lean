import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderBilinear
import ElementaryHolonics.Millennium.NavierStokesWeightedHeatScaleWord
import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelMeasurability
import ElementaryHolonics.Millennium.NavierStokesWeightedMildCoefficientEquation

/-!
# A tame nonlinear word recovers one arbitrary Sobolev order

**[proved-derived]** Fix a base order `n ≥ 2`.  The complete native quadratic
Leray--divergence population of an `H^(n+1)` state lands in `H^n`; its mixed tame receipt uses
the exact restriction of that same state to `H³`.  One positive-time adjacent heat word then
returns the population to `H^(n+1)`.  Integrating this word over an ordered time interval gives an
honest higher-order Bochner Duhamel return with an explicit singular-kernel budget.

The construction does not infer an `H^(n+1)` state from an `H³` state.  Its high-order input is
retained, while `H³` is the low receiver controlling the tame norm.  This is the persistence
shape valid at arbitrary order; a literal map `H^m × H³ → H^(m-1)` is not available for
unbounded `m` because the second factor does not carry the requested target regularity.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedHeatScale
open Soma.Holonics.Millennium.NavierStokesWeightedHeatScaleWord
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact adjacent nonlinear scale word -/

/-- The explicit tame constant for the quadratic passage from order `base + 1` to `base`. -/
def higherOrderTameConstant (base : ℕ) : ℝ :=
  36 * (2 : ℝ) ^ (base + 1) * periodicH3EmbeddingConstant

theorem higherOrderTameConstant_nonneg (base : ℕ) :
    0 ≤ higherOrderTameConstant base := by
  unfold higherOrderTameConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) (base + 1)))
    periodicH3EmbeddingConstant_nonneg

/-- The complete native quadratic population at the predecessor scale. -/
def higherOrderLerayQuadratic
    (base : ℕ) (hbase : 2 ≤ base)
    (state : PeriodicVectorWeightedSobolev (base + 1)) :
    PeriodicVectorWeightedSobolev base :=
  periodicVectorWeightedLerayDivergenceConvolution
    (base + 1) (by omega) state state

/-- The generic bundled bilinear owner makes the arbitrary-order quadratic source continuous. -/
theorem continuous_higherOrderLerayQuadratic
    (base : ℕ) (hbase : 2 ≤ base) :
    Continuous (higherOrderLerayQuadratic base hbase) := by
  have hcontinuous : Continuous
      (fun state : PeriodicVectorWeightedSobolev (base + 1) ↦
        periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (base + 1) (by omega) state state) :=
    (periodicVectorWeightedLerayDivergenceConvolutionContinuous
      (base + 1) (by omega)).continuous.clm_apply continuous_id
  have horder : base + 1 - 1 = base := by omega
  rw [horder] at hcontinuous
  apply hcontinuous.congr
  intro state
  funext component
  apply Subtype.ext
  funext k
  rfl

/-- Every continuous high-order path therefore has a continuous predecessor-scale nonlinear
source path; this is the analytic port previously left explicit. -/
theorem ContinuousOn.comp_higherOrderLerayQuadratic
    (base : ℕ) (hbase : 2 ≤ base) {X : Type*} [TopologicalSpace X]
    {path : X → PeriodicVectorWeightedSobolev (base + 1)} {s : Set X}
    (hpath : ContinuousOn path s) :
    ContinuousOn
      (fun x ↦ higherOrderLerayQuadratic base hbase (path x)) s :=
  (continuous_higherOrderLerayQuadratic base hbase).comp_continuousOn hpath

/-- The arbitrary-order quadratic source is controlled by one high norm and the exact `H³`
receiver of the same coefficient population. -/
theorem norm_higherOrderLerayQuadratic_le_tame
    (base : ℕ) (hbase : 2 ≤ base)
    (state : PeriodicVectorWeightedSobolev (base + 1)) :
    ‖higherOrderLerayQuadratic base hbase state‖ ≤
      higherOrderTameConstant base *
        ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) state‖ *
        ‖state‖ := by
  have h := norm_periodicVectorWeightedLerayDivergenceConvolution_le_tame
    (base + 1) (by omega) state state
  change ‖higherOrderLerayQuadratic base hbase state‖ ≤ _
  calc
    ‖higherOrderLerayQuadratic base hbase state‖ ≤
        (18 * (2 : ℝ) ^ (base + 1) * periodicH3EmbeddingConstant) *
          (‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) state‖ *
              ‖state‖ +
            ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) state‖ *
              ‖state‖) := h
    _ = higherOrderTameConstant base *
        ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) state‖ *
        ‖state‖ := by
      unfold higherOrderTameConstant
      ring

/-- One positive-time word recovers the derivative spent by the quadratic source. -/
def higherOrderHeatLift
    (base : ℕ) (nu dt : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (dt : ℝ)) :
    PeriodicVectorWeightedSobolev base →L[ℂ]
      PeriodicVectorWeightedSobolev (base + 1) :=
  periodicVectorWeightedHeatScaleWord base 1 nu dt hviscous

private theorem norm_periodicVectorWeightedHeatScaleWord_le
    (start steps : ℕ) (nu dt : ℝ≥0)
    (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev start) :
    ‖periodicVectorWeightedHeatScaleWord start steps nu dt hviscous state‖ ≤
      (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps * ‖state‖ := by
  have hright : 0 ≤
      (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps * ‖state‖ :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg hright]
  intro component
  calc
    ‖periodicVectorWeightedHeatScaleWord start steps nu dt hviscous state component‖ ≤
        (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps *
          ‖state component‖ :=
      norm_periodicWeightedHeatScaleWord_le
        start steps nu dt hviscous (state component)
    _ ≤ (Real.sqrt (heatOneStepSquaredConstant (nu : ℝ) (dt : ℝ))) ^ steps *
          ‖state‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm state component)
        (pow_nonneg (Real.sqrt_nonneg _) _)

/-- The scale word retains the standard integrable one-derivative heat constant. -/
theorem norm_higherOrderHeatLift_le
    (base : ℕ) (nu dt : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev base) :
    ‖higherOrderHeatLift base nu dt hviscous state‖ ≤
      duhamelHeatKernelMajorant (nu : ℝ) (dt : ℝ) * ‖state‖ := by
  simpa only [higherOrderHeatLift, duhamelHeatKernelMajorant, pow_one] using
    norm_periodicVectorWeightedHeatScaleWord_le
      base 1 nu dt hviscous state

/-! ## Joint continuity of every adjacent heat word -/

/-- After any fixed positive portion of an adjacent heat word has acted, the remainder is a
same-order heat orbit on the target carrier. -/
theorem periodicWeightedHeatSucc_factor
    (base : ℕ) (nu tau delta : ℝ≥0)
    (hnu : 0 < (nu : ℝ)) (hdelta : 0 < (delta : ℝ))
    (hdeltaTau : delta ≤ tau) (state : PeriodicWeightedSobolev base) :
    periodicWeightedHeatSucc base nu tau
        (mul_pos hnu (show 0 < (tau : ℝ) from
          lt_of_lt_of_le hdelta (by exact_mod_cast hdeltaTau))) state =
      periodicWeightedHeat (base + 1) nu (tau - delta)
        (periodicWeightedHeatSucc base nu delta (mul_pos hnu hdelta) state) := by
  apply Subtype.ext
  funext k
  simp only [periodicWeightedHeatSucc_apply, periodicWeightedHeat_apply,
    NNReal.coe_sub hdeltaTau]
  have htime : (tau : ℝ) = ((tau : ℝ) - (delta : ℝ)) + (delta : ℝ) := by
    have hreal : (delta : ℝ) ≤ (tau : ℝ) := by exact_mod_cast hdeltaTau
    linarith
  rw [htime, heatStokesMultiplier_add, Complex.ofReal_mul]
  ring_nf

/-- The scalar adjacent heat word as a joint map of positive elapsed time and source. -/
def periodicWeightedHeatSuccJoint
    (base : ℕ) (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (pair : PositiveElapsedTime × PeriodicWeightedSobolev base) :
    PeriodicWeightedSobolev (base + 1) :=
  periodicWeightedHeatSucc base nu pair.1.1
    (mul_pos hnu pair.1.2) pair.2

/-- Joint positive-time continuity is scale-uniform for every adjacent scalar heat word. -/
theorem continuous_periodicWeightedHeatSuccJoint
    (base : ℕ) (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) :
    Continuous (periodicWeightedHeatSuccJoint base nu hnu) := by
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
  let fixedSmooth : PeriodicWeightedSobolev base →L[ℂ]
      PeriodicWeightedSobolev (base + 1) :=
    periodicWeightedHeatSuccCLM base nu delta (mul_pos hnu hdelta)
  let factored : PositiveElapsedTime × PeriodicWeightedSobolev base →
      PeriodicWeightedSobolev (base + 1) := fun pair ↦
    periodicWeightedHeat (base + 1) nu (pair.1.1 - delta) (fixedSmooth pair.2)
  have htime : Continuous
      (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev base ↦
        pair.1.1 - delta) := by
    fun_prop
  have hsource : Continuous
      (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev base ↦
        fixedSmooth pair.2) := by
    fun_prop
  have hfactored : Continuous factored := by
    have hpair : Continuous
        (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev base ↦
          (pair.1.1 - delta, fixedSmooth pair.2)) :=
      htime.prodMk hsource
    have hjoint := continuous_periodicWeightedHeat_joint (base + 1) nu
    change Continuous
      ((fun pair : ℝ≥0 × PeriodicWeightedSobolev (base + 1) ↦
          periodicWeightedHeat (base + 1) nu pair.1 pair.2) ∘
        fun pair : PositiveElapsedTime × PeriodicWeightedSobolev base ↦
          (pair.1.1 - delta, fixedSmooth pair.2))
    exact hjoint.comp hpair
  have heventually : ∀ᶠ pair : PositiveElapsedTime × PeriodicWeightedSobolev base in
      nhds (⟨⟨tau₀, htau₀⟩, state₀⟩ :
        PositiveElapsedTime × PeriodicWeightedSobolev base),
      delta ≤ pair.1.1 := by
    have hfirst : ∀ᶠ time : PositiveElapsedTime in nhds ⟨tau₀, htau₀⟩,
        delta < time.1 :=
      (continuous_subtype_val.tendsto ⟨tau₀, htau₀⟩).eventually
        (Ioi_mem_nhds hdeltaLt)
    have hfst : Tendsto
        (fun pair : PositiveElapsedTime × PeriodicWeightedSobolev base ↦ pair.1)
        (nhds (⟨tau₀, htau₀⟩, state₀)) (nhds ⟨tau₀, htau₀⟩) :=
      continuous_fst.tendsto _
    exact (hfst.eventually hfirst).mono fun pair hp ↦ hp.le
  apply hfactored.continuousAt.congr_of_eventuallyEq
  filter_upwards [heventually] with pair hp
  dsimp only [periodicWeightedHeatSuccJoint, factored, fixedSmooth]
  exact periodicWeightedHeatSucc_factor
    base nu pair.1.1 delta hnu hdelta hp pair.2

/-- The full three-component adjacent heat word, jointly parameterized by positive elapsed time
and its predecessor-scale source. -/
def higherOrderHeatLiftJoint
    (base : ℕ) (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev base) :
    PeriodicVectorWeightedSobolev (base + 1) := fun component ↦
  periodicWeightedHeatSuccJoint base nu hnu ⟨pair.1, pair.2 component⟩

/-- The complete adjacent vector heat word is jointly continuous at every Sobolev address. -/
theorem continuous_higherOrderHeatLiftJoint
    (base : ℕ) (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) :
    Continuous (higherOrderHeatLiftJoint base nu hnu) := by
  apply continuous_pi
  intro component
  exact (continuous_periodicWeightedHeatSuccJoint base nu hnu).comp
    (continuous_fst.prodMk (continuous_apply component |>.comp continuous_snd))

private theorem positiveElapsedBefore_eq_positiveElapsed
    (t : ℝ) (s : Iio t) :
    (positiveElapsedBefore t s).1 = positiveElapsed t s.1 s.2 := by
  apply NNReal.eq
  rw [show ((positiveElapsedBefore t s).1 : ℝ) = t - s.1 by
    exact Real.coe_toNNReal (t - s.1) (sub_nonneg.mpr s.2.le)]
  rfl

/-- The endpoint-totalized nonlinear scale word at terminal time `t`. -/
def higherOrderDuhamelIntegrand
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1)) (s : ℝ) :
    PeriodicVectorWeightedSobolev (base + 1) :=
  if hs : s < t then
    higherOrderHeatLift base nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs))
      (higherOrderLerayQuadratic base hbase (path s))
  else
    0

theorem higherOrderDuhamelIntegrand_of_lt
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    {s : ℝ} (hs : s < t) :
    higherOrderDuhamelIntegrand base hbase nu hnu t path s =
      higherOrderHeatLift base nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs))
        (higherOrderLerayQuadratic base hbase (path s)) := by
  rw [higherOrderDuhamelIntegrand, dif_pos hs]

@[simp]
theorem higherOrderDuhamelIntegrand_of_not_lt
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    {s : ℝ} (hs : ¬ s < t) :
    higherOrderDuhamelIntegrand base hbase nu hnu t path s = 0 := by
  simp [higherOrderDuhamelIntegrand, hs]

/-- Pointwise composition of the tame nonlinear receipt with the adjacent heat word. -/
theorem norm_higherOrderDuhamelIntegrand_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1)) (s : ℝ) :
    ‖higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
      higherOrderTameConstant base *
        ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ *
        ‖path s‖ * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
  by_cases hs : s < t
  · rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t path hs]
    calc
      ‖higherOrderHeatLift base nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs))
          (higherOrderLerayQuadratic base hbase (path s))‖ ≤
          duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
            ‖higherOrderLerayQuadratic base hbase (path s)‖ := by
        simpa only [coe_positiveElapsed] using
          norm_higherOrderHeatLift_le base nu (positiveElapsed t s hs)
            (mul_pos hnu (sub_pos.mpr hs))
            (higherOrderLerayQuadratic base hbase (path s))
      _ ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) *
          (higherOrderTameConstant base *
            ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ *
            ‖path s‖) := by
        exact mul_le_mul_of_nonneg_left
          (norm_higherOrderLerayQuadratic_le_tame base hbase (path s))
          (Real.sqrt_nonneg _)
      _ = higherOrderTameConstant base *
          ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ *
          ‖path s‖ * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by ring
  · rw [higherOrderDuhamelIntegrand_of_not_lt base hbase nu hnu t path hs,
      norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (higherOrderTameConstant_nonneg base) (norm_nonneg _))
        (norm_nonneg _))
      (Real.sqrt_nonneg _)

/-- Uniform `H³`-receiver and high-order bounds produce the reflected integrable heat
majorant. -/
theorem norm_higherOrderDuhamelIntegrand_le_of_bounds
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1)) (s : ℝ)
    (hR3 : 0 ≤ R3) (_hRm : 0 ≤ Rm)
    (hlow : ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ‖path s‖ ≤ Rm) :
    ‖higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
      higherOrderTameConstant base * R3 * Rm *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
  calc
    ‖higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        higherOrderTameConstant base *
          ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ *
          ‖path s‖ * duhamelHeatKernelMajorant (nu : ℝ) (t - s) :=
      norm_higherOrderDuhamelIntegrand_le base hbase nu hnu t path s
    _ ≤ higherOrderTameConstant base * R3 * Rm *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      have hkernel : 0 ≤ duhamelHeatKernelMajorant (nu : ℝ) (t - s) :=
        Real.sqrt_nonneg _
      have hconstant : 0 ≤ higherOrderTameConstant base :=
        higherOrderTameConstant_nonneg base
      have hproduct :
          higherOrderTameConstant base *
              ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ *
              ‖path s‖ ≤
            higherOrderTameConstant base * R3 * Rm := by
        have hpair := mul_le_mul hlow hhigh (norm_nonneg (path s)) hR3
        have hscaled := mul_le_mul_of_nonneg_left hpair hconstant
        simpa only [mul_assoc] using hscaled
      exact mul_le_mul_of_nonneg_right
        hproduct hkernel

/-! ## The exact time-dependent analytic port -/

/-- Continuity of the predecessor-scale nonlinear source suffices for continuity of the recovered
word at every interior source time.  No continuity of the singular terminal representative is
claimed. -/
theorem continuousOn_higherOrderDuhamelIntegrand_Ioo
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hsource : ContinuousOn
      (fun s ↦ higherOrderLerayQuadratic base hbase (path s))
      (Icc (0 : ℝ) t)) :
    ContinuousOn
      (higherOrderDuhamelIntegrand base hbase nu hnu t path)
      (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_restrict]
  have hsourceInterior : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        higherOrderLerayQuadratic base hbase (path s.1)) :=
    continuousOn_iff_continuous_restrict.mp
      (hsource.mono Ioo_subset_Icc_self)
  have helapsed : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t)) :=
    (continuous_positiveElapsedBefore t).comp
      (continuous_subtype_val.subtype_mk _)
  have hmodel : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        higherOrderHeatLiftJoint base nu hnu
          ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
            higherOrderLerayQuadratic base hbase (path s.1)⟩) :=
    (continuous_higherOrderHeatLiftJoint base nu hnu).comp
      (helapsed.prodMk hsourceInterior)
  apply hmodel.congr
  intro s
  change higherOrderHeatLiftJoint base nu hnu
      ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
        higherOrderLerayQuadratic base hbase (path s.1)⟩ =
      higherOrderDuhamelIntegrand base hbase nu hnu t path s.1
  rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t path s.2.2]
  have helapsedEq : positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t) =
      (⟨positiveElapsed t s.1 s.2.2, sub_pos.mpr s.2.2⟩ :
        PositiveElapsedTime) := by
    apply Subtype.ext
    exact positiveElapsedBefore_eq_positiveElapsed t ⟨s.1, s.2.2⟩
  rw [helapsedEq]
  rfl

/-- Interior continuity removes the singular endpoint and returns the exact almost-everywhere
strong-measurability receipt needed by the Bochner integral. -/
theorem aestronglyMeasurable_higherOrderDuhamelIntegrand
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hsource : ContinuousOn
      (fun s ↦ higherOrderLerayQuadratic base hbase (path s))
      (Icc (0 : ℝ) t)) :
    AEStronglyMeasurable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path)
      (volume.restrict (Ioc (0 : ℝ) t)) := by
  letI : SecondCountableTopologyEither ℝ
      (PeriodicVectorWeightedSobolev (base + 1)) :=
    ⟨Or.inl (by infer_instance)⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_higherOrderDuhamelIntegrand_Ioo
    base hbase nu hnu path hsource).aestronglyMeasurable measurableSet_Ioo

/-! ## Honest higher-order Bochner return -/

/-- The actual recovered-order Duhamel return, valued in the full native `H^(base+1)` carrier. -/
def higherOrderDuhamelReturn
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1)) :
    PeriodicVectorWeightedSobolev (base + 1) :=
  ∫ s in (0 : ℝ)..t,
    higherOrderDuhamelIntegrand base hbase nu hnu t path s

/-- The scalar budget for the recovered-order Duhamel word is interval-integrable. -/
theorem intervalIntegrable_higherOrderDuhamelMajorant
    (base : ℕ) (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {t : ℝ} (ht : 0 < t) (R3 Rm : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ higherOrderTameConstant base * R3 * Rm *
        duhamelHeatKernelMajorant (nu : ℝ) (t - s)) volume 0 t :=
  (intervalIntegrable_reflectedDuhamelHeatKernelMajorant nu hnu ht).const_mul
    (higherOrderTameConstant base * R3 * Rm)

/-- Strong measurability of the actual scale word, together with tame path bounds, closes honest
interval integrability.  The premise is the exact time-dependent analytic port; it does not assume
the returned integral or its norm estimate. -/
theorem intervalIntegrable_higherOrderDuhamelIntegrand
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t)
    (R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hlow : ∀ s ∈ Icc (0 : ℝ) t,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ∀ s ∈ Icc (0 : ℝ) t, ‖path s‖ ≤ Rm)
    (hmeas : AEStronglyMeasurable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path)
      (volume.restrict (Ioc (0 : ℝ) t))) :
    IntervalIntegrable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t := by
  have hR3 : 0 ≤ R3 :=
    (norm_nonneg
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path 0))).trans
      (hlow 0 ⟨le_rfl, ht.le⟩)
  have hRm : 0 ≤ Rm :=
    (norm_nonneg (path 0)).trans (hhigh 0 ⟨le_rfl, ht.le⟩)
  have hmeas' : AEStronglyMeasurable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path)
      (volume.restrict (Ι (0 : ℝ) t)) := by
    simpa only [uIoc_of_le ht.le] using hmeas
  apply (intervalIntegrable_higherOrderDuhamelMajorant
    base nu hnu ht R3 Rm).mono_fun' hmeas'
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le ht.le] at hs
  exact norm_higherOrderDuhamelIntegrand_le_of_bounds
    base hbase nu hnu t R3 Rm path s hR3 hRm
      (hlow s ⟨hs.1.le, hs.2⟩) (hhigh s ⟨hs.1.le, hs.2⟩)

/-! ## Exact mode lineage and the shared scalar Volterra word -/

/-- Before the terminal face, every recovered physical coefficient is exactly one heat
multiplier times the corresponding physical coefficient of the complete nonlinear source. -/
theorem weightedPhysicalCoefficient_higherOrderDuhamelIntegrand_of_lt
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (component : Fin 3) (k : SpatialFrequency) {s : ℝ} (hs : s < t) :
    weightedPhysicalCoefficient (base + 1) component k
        (higherOrderDuhamelIntegrand base hbase nu hnu t path s) =
      (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
        weightedPhysicalCoefficient base component k
          (higherOrderLerayQuadratic base hbase (path s)) := by
  rw [higherOrderDuhamelIntegrand_of_lt base hbase nu hnu t path hs,
    weightedPhysicalCoefficient_apply, weightedPhysicalCoefficient_apply]
  change
    (weightedSobolevCoefficients (base + 1)
      (periodicVectorWeightedHeatScaleWord base 1 nu
        (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
        (higherOrderLerayQuadratic base hbase (path s)) component)).1 k = _
  rw [weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply,
    coe_positiveElapsed, pow_one]

/-- Bounded physical-coefficient evaluation commutes through the honest higher-order Bochner
return.  The endpoint-totalized representative differs from the displayed kernel only at the
atomless terminal face. -/
theorem weightedPhysicalCoefficient_higherOrderDuhamelReturn
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (component : Fin 3) (k : SpatialFrequency)
    (hintegrable : IntervalIntegrable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t) :
    weightedPhysicalCoefficient (base + 1) component k
        (higherOrderDuhamelReturn base hbase nu hnu t path) =
      ∫ s in (0 : ℝ)..t,
        (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
          weightedPhysicalCoefficient base component k
            (higherOrderLerayQuadratic base hbase (path s)) := by
  let coefficient := weightedPhysicalCoefficient (base + 1) component k
  let integrand := higherOrderDuhamelIntegrand base hbase nu hnu t path
  let scalarIntegrand : ℝ → ℂ := fun s ↦
    (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
      weightedPhysicalCoefficient base component k
        (higherOrderLerayQuadratic base hbase (path s))
  have hcommute := coefficient.intervalIntegral_comp_comm hintegrable
  have hAE : (fun s : ℝ ↦ coefficient (integrand s)) =ᵐ[
      volume.restrict (Ι (0 : ℝ) t)] scalarIntegrand := by
    rw [uIoc_of_le ht, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact weightedPhysicalCoefficient_higherOrderDuhamelIntegrand_of_lt
      base hbase nu hnu t path component k hs.2
  calc
    weightedPhysicalCoefficient (base + 1) component k
        (higherOrderDuhamelReturn base hbase nu hnu t path) =
        coefficient (∫ s in (0 : ℝ)..t, integrand s) := by rfl
    _ = ∫ s in (0 : ℝ)..t, coefficient (integrand s) := hcommute.symm
    _ = ∫ s in (0 : ℝ)..t, scalarIntegrand s :=
      intervalIntegral.integral_congr_ae_restrict hAE
    _ = ∫ s in (0 : ℝ)..t,
        (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
          weightedPhysicalCoefficient base component k
            (higherOrderLerayQuadratic base hbase (path s)) := by rfl

/-- The same recovered coefficient is exactly the repository's scalar heat-Volterra return with
decay rate `ν λₖ`; thus the arbitrary-order word shares the established mild coefficient law. -/
theorem weightedPhysicalCoefficient_higherOrderDuhamelReturn_eq_scalarHeatVolterra
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (component : Fin 3) (k : SpatialFrequency)
    (hintegrable : IntervalIntegrable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t) :
    weightedPhysicalCoefficient (base + 1) component k
        (higherOrderDuhamelReturn base hbase nu hnu t path) =
      scalarHeatVolterra ((nu : ℝ) * torusStokesEigenvalue k)
        (fun s : ℝ ↦ weightedPhysicalCoefficient base component k
          (higherOrderLerayQuadratic base hbase (path s))) t := by
  rw [weightedPhysicalCoefficient_higherOrderDuhamelReturn
    base hbase nu hnu ht path component k hintegrable]
  have hexponent : ∀ s : ℝ,
      -((nu : ℝ) * (t - s) * torusStokesEigenvalue k) =
        -((nu : ℝ) * torusStokesEigenvalue k) * (t - s) := by
    intro s
    ring
  simp only [scalarHeatVolterra, heatStokesMultiplier, Complex.real_smul,
    hexponent]

/-! ## Continuous high paths over an `H³` receiver -/

/-- The adjacent high-order path carrier on the same compact time aperture as `WeightedH3Path`. -/
abbrev WeightedHigherOrderPath (base : ℕ) (T : ℝ) :=
  C(Icc (0 : ℝ) T, PeriodicVectorWeightedSobolev (base + 1))

/-- Extend a high-order path by endpoint projection, exactly as for the established `H³` path
carrier. -/
def weightedHigherOrderPathExtension
    {base : ℕ} {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T) :
    C(ℝ, PeriodicVectorWeightedSobolev (base + 1)) :=
  ContinuousMap.IccExtend hT path

@[simp]
theorem weightedHigherOrderPathExtension_of_mem
    {base : ℕ} {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    weightedHigherOrderPathExtension hT path t = path ⟨t, ht⟩ := by
  simp [weightedHigherOrderPathExtension, ContinuousMap.IccExtend,
    Set.IccExtend, Set.projIcc, ht.1, ht.2]

theorem norm_weightedHigherOrderPathExtension_le
    {base : ℕ} {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T)
    (t : ℝ) :
    ‖weightedHigherOrderPathExtension hT path t‖ ≤ ‖path‖ := by
  change ‖path (Set.projIcc 0 T hT t)‖ ≤ ‖path‖
  exact path.norm_coe_le_norm _

/-- Apply the exact high-to-`H³` receiver at every time without changing the time population. -/
def higherOrderRestrictionPathToThree
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ}
    (path : WeightedHigherOrderPath base T) : WeightedH3Path T :=
  ⟨fun t ↦ periodicVectorWeightedRestrictToThree
      (base + 1) (by omega) (path t),
    (periodicVectorWeightedSobolevRestrictCLM
      3 (base + 1) (by omega)).continuous.comp path.continuous⟩

@[simp]
theorem higherOrderRestrictionPathToThree_apply
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ}
    (path : WeightedHigherOrderPath base T) (t : Icc (0 : ℝ) T) :
    higherOrderRestrictionPathToThree base hbase path t =
      periodicVectorWeightedRestrictToThree
        (base + 1) (by omega) (path t) :=
  rfl

/-- A high-order path is controlled by an established native `H³` path when restriction commutes
at every time face. -/
def IsH3ControlledHigherOrderLift
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ}
    (high : WeightedHigherOrderPath base T) (low : WeightedH3Path T) : Prop :=
  higherOrderRestrictionPathToThree base hbase high = low

/-- The actual higher-order Bochner return has the explicit tame persistence budget. -/
theorem norm_intervalIntegral_higherOrderDuhamelIntegrand_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t)
    (R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hlow : ∀ s ∈ Icc (0 : ℝ) t,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ∀ s ∈ Icc (0 : ℝ) t, ‖path s‖ ≤ Rm) :
    ‖∫ s in (0 : ℝ)..t,
        higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
      higherOrderTameConstant base * R3 * Rm *
        (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by
  have hR3 : 0 ≤ R3 :=
    (norm_nonneg
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path 0))).trans
      (hlow 0 ⟨le_rfl, ht.le⟩)
  have hRm : 0 ≤ Rm :=
    (norm_nonneg (path 0)).trans (hhigh 0 ⟨le_rfl, ht.le⟩)
  let K : ℝ := higherOrderTameConstant base * R3 * Rm
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (higherOrderTameConstant_nonneg base) hR3) hRm
  have hmajorant := intervalIntegrable_higherOrderDuhamelMajorant
    base nu hnu ht R3 Rm
  have hnorm :
      ‖∫ s in (0 : ℝ)..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        ∫ s in (0 : ℝ)..t,
          K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht.le
    · filter_upwards with s
      intro hs
      exact norm_higherOrderDuhamelIntegrand_le_of_bounds
        base hbase nu hnu t R3 Rm path s hR3 hRm
          (hlow s ⟨hs.1.le, hs.2⟩) (hhigh s ⟨hs.1.le, hs.2⟩)
    · simpa only [K] using hmajorant
  calc
    ‖∫ s in (0 : ℝ)..t,
        higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        ∫ s in (0 : ℝ)..t,
          K * duhamelHeatKernelMajorant (nu : ℝ) (t - s) := hnorm
    _ = K * ∫ s in (0 : ℝ)..t,
        duhamelHeatKernelMajorant (nu : ℝ) (t - s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = K * ∫ tau in (0 : ℝ)..t,
        duhamelHeatKernelMajorant (nu : ℝ) tau := by
      rw [intervalIntegral_reflectedDuhamelHeatKernelMajorant]
    _ ≤ K * (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_duhamelHeatKernelMajorant_le hnu ht) hK
    _ = higherOrderTameConstant base * R3 * Rm *
        (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) := by rfl

/-- The strongest immediate persistence return: an honest `H^(base+1)` Duhamel integral and its
explicit tame budget, derived from the actual high path, its `H³` receiver bound, and the exact
strong-measurability port. -/
theorem higherOrderDuhamelReturn_exists_with_tame_bound
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t)
    (R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hlow : ∀ s ∈ Icc (0 : ℝ) t,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ∀ s ∈ Icc (0 : ℝ) t, ‖path s‖ ≤ Rm)
    (hmeas : AEStronglyMeasurable
      (higherOrderDuhamelIntegrand base hbase nu hnu t path)
      (volume.restrict (Ioc (0 : ℝ) t))) :
    IntervalIntegrable
        (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t ∧
      ‖∫ s in (0 : ℝ)..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        higherOrderTameConstant base * R3 * Rm *
          (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
  ⟨intervalIntegrable_higherOrderDuhamelIntegrand
      base hbase nu hnu ht R3 Rm path hlow hhigh hmeas,
    norm_intervalIntegral_higherOrderDuhamelIntegrand_le
      base hbase nu hnu ht R3 Rm path hlow hhigh⟩

/-- Source continuity closes the analytic port internally and yields the complete arbitrary-order
persistence return without a measurability premise at the call site. -/
theorem higherOrderDuhamelReturn_exists_with_tame_bound_of_source_continuous
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t)
    (R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hsource : ContinuousOn
      (fun s ↦ higherOrderLerayQuadratic base hbase (path s))
      (Icc (0 : ℝ) t))
    (hlow : ∀ s ∈ Icc (0 : ℝ) t,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ∀ s ∈ Icc (0 : ℝ) t, ‖path s‖ ≤ Rm) :
    IntervalIntegrable
        (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t ∧
      ‖∫ s in (0 : ℝ)..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        higherOrderTameConstant base * R3 * Rm *
          (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
  higherOrderDuhamelReturn_exists_with_tame_bound
    base hbase nu hnu ht R3 Rm path hlow hhigh
      (aestronglyMeasurable_higherOrderDuhamelIntegrand
        base hbase nu hnu path hsource)

/-- A continuous high-order path now closes the nonlinear-source port automatically through the
bundled arbitrary-order bilinear map. -/
theorem higherOrderDuhamelReturn_exists_with_tame_bound_of_path_continuous
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ} (ht : 0 < t)
    (R3 Rm : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev (base + 1))
    (hpath : ContinuousOn path (Icc (0 : ℝ) t))
    (hlow : ∀ s ∈ Icc (0 : ℝ) t,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega) (path s)‖ ≤ R3)
    (hhigh : ∀ s ∈ Icc (0 : ℝ) t, ‖path s‖ ≤ Rm) :
    IntervalIntegrable
        (higherOrderDuhamelIntegrand base hbase nu hnu t path) volume 0 t ∧
      ‖∫ s in (0 : ℝ)..t,
          higherOrderDuhamelIntegrand base hbase nu hnu t path s‖ ≤
        higherOrderTameConstant base * R3 * Rm *
          (t + 2 * Real.sqrt (t / (2 * (nu : ℝ)))) :=
  higherOrderDuhamelReturn_exists_with_tame_bound_of_source_continuous
    base hbase nu hnu ht R3 Rm path
      (ContinuousOn.comp_higherOrderLerayQuadratic base hbase hpath) hlow hhigh

/-- An actual continuous high path over an `H³` receiver returns an honest adjacent-order
Duhamel word.  The bounds are now the native compact-path norms themselves; no unrelated radii
are supplied. -/
theorem higherOrderDuhamelReturn_of_H3ControlledLift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 < T)
    (high : WeightedHigherOrderPath base T) (low : WeightedH3Path T)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low) :
    IntervalIntegrable
        (higherOrderDuhamelIntegrand base hbase nu hnu T
          (weightedHigherOrderPathExtension hT.le high)) volume 0 T ∧
      ‖higherOrderDuhamelReturn base hbase nu hnu T
          (weightedHigherOrderPathExtension hT.le high)‖ ≤
        higherOrderTameConstant base * ‖low‖ * ‖high‖ *
          (T + 2 * Real.sqrt (T / (2 * (nu : ℝ)))) := by
  have hlow : ∀ s ∈ Icc (0 : ℝ) T,
      ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega)
        (weightedHigherOrderPathExtension hT.le high s)‖ ≤ ‖low‖ := by
    intro s hs
    rw [weightedHigherOrderPathExtension_of_mem hT.le high hs]
    have hface := ContinuousMap.congr_fun hlift ⟨s, hs⟩
    change periodicVectorWeightedRestrictToThree
        (base + 1) (by omega) (high ⟨s, hs⟩) = low ⟨s, hs⟩ at hface
    rw [hface]
    exact norm_weightedPath_apply_le low ⟨s, hs⟩
  have hhigh : ∀ s ∈ Icc (0 : ℝ) T,
      ‖weightedHigherOrderPathExtension hT.le high s‖ ≤ ‖high‖ := by
    intro s _hs
    exact norm_weightedHigherOrderPathExtension_le hT.le high s
  have hpath : ContinuousOn
      (weightedHigherOrderPathExtension hT.le high :
        ℝ → PeriodicVectorWeightedSobolev (base + 1))
      (Icc (0 : ℝ) T) :=
    (weightedHigherOrderPathExtension hT.le high).continuous.continuousOn
  simpa only [higherOrderDuhamelReturn] using
    higherOrderDuhamelReturn_exists_with_tame_bound_of_path_continuous
      base hbase nu hnu hT ‖low‖ ‖high‖
        (weightedHigherOrderPathExtension hT.le high)
        hpath hlow hhigh

section Audit

#print axioms norm_higherOrderLerayQuadratic_le_tame
#print axioms continuous_higherOrderLerayQuadratic
#print axioms norm_higherOrderHeatLift_le
#print axioms norm_higherOrderDuhamelIntegrand_le
#print axioms continuous_periodicWeightedHeatSuccJoint
#print axioms aestronglyMeasurable_higherOrderDuhamelIntegrand
#print axioms intervalIntegrable_higherOrderDuhamelIntegrand
#print axioms weightedPhysicalCoefficient_higherOrderDuhamelReturn_eq_scalarHeatVolterra
#print axioms norm_intervalIntegral_higherOrderDuhamelIntegrand_le
#print axioms higherOrderDuhamelReturn_exists_with_tame_bound
#print axioms higherOrderDuhamelReturn_exists_with_tame_bound_of_source_continuous
#print axioms higherOrderDuhamelReturn_exists_with_tame_bound_of_path_continuous
#print axioms higherOrderDuhamelReturn_of_H3ControlledLift

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
