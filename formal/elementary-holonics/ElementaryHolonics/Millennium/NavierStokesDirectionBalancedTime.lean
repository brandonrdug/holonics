import ElementaryHolonics.Millennium.NavierStokesDirectionBalancedScale
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalTime

/-!
# Time transport of the balanced direction current

**[proved-derived]** The large-scale balanced high/low direction population is glued into one
`tsum` and bounded by a receiver-independent time section times one fixed, summable fourth-root
dyadic population.  Both time factors are actual receivers of the admitted periodic solution: the
torus vorticity supremum and the canonical compact-chart spatial derivative norm.

The resulting scale-summed current is continuous, hence interval-integrable, on every compact
time interval strictly inside the admitted lifespan.  The theorem does not cross the maximal-time
face; doing so still requires a quantitative Navier--Stokes terminal estimate.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesDirectionBalancedTime

open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance
open Soma.Holonics.Millennium.NavierStokesDirectionBalancedScale
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime

local instance : MeasureSpace UnitAddCircle :=
  Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance.instMeasureSpaceUnitAddCircle_elementaryHolonics
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The complete scale population and its separated envelope -/

/-- The inverse-fourth-root weight retained by the large-scale Hodge receiver. -/
def inverseFourthRootDyadicTailWeight (scale : ℕ) : ℝ :=
  1 / Real.sqrt (Real.sqrt (dyadicRadius (scale + 3) : ℝ))

theorem inverseFourthRootDyadicTailWeight_nonneg (scale : ℕ) :
    0 ≤ inverseFourthRootDyadicTailWeight scale := by
  unfold inverseFourthRootDyadicTailWeight
  positivity

theorem summable_inverseFourthRootDyadicTailWeight :
    Summable inverseFourthRootDyadicTailWeight := by
  have hfull := summable_const_div_sqrt_sqrt_dyadicRadius 1
  unfold inverseFourthRootDyadicTailWeight
  simpa [one_div] using
    (summable_nat_add_iff 3).2 hfull

/-- The complete returned population of inverse-fourth-root large-scale weights. -/
def inverseFourthRootDyadicTailMass : ℝ :=
  ∑' scale : ℕ, inverseFourthRootDyadicTailWeight scale

theorem inverseFourthRootDyadicTailMass_nonneg :
    0 ≤ inverseFourthRootDyadicTailMass := by
  unfold inverseFourthRootDyadicTailMass
  exact tsum_nonneg inverseFourthRootDyadicTailWeight_nonneg

/-- The solution-owned high/high envelope, with the exact returned Hodge constant retained. -/
def balancedHighTemporalEnvelope
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  sliceVorticitySup solution t ^ 2 *
    (405 * dyadicHodgeUniformSubsetMassConstant / 2)

/-- The solution-owned low-endpoint envelope. -/
def balancedLowTemporalEnvelope
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  (2 * sliceVorticitySup solution t) *
    (216 * dyadicHodgeUniformSubsetMassConstant)

/-- The time-only factor after the Hodge scale population has separated. -/
def balancedTemporalFactor
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  Real.sqrt
      (2 * (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
        balancedHighTemporalEnvelope solution t) *
    Real.sqrt (balancedLowTemporalEnvelope solution t)

theorem balancedTemporalFactor_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ balancedTemporalFactor solution t := by
  unfold balancedTemporalFactor
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The complete time envelope after the fixed spatial scale population is summed. -/
def balancedTemporalEnvelope
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  balancedTemporalFactor solution t * inverseFourthRootDyadicTailMass

/-- The actual large-scale direction current at one time and receiver. -/
def largeScaleBalancedDirectionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℝ :=
  ∑' scale : ℕ, canonicalBalancedScaleCurrent solution t q (scale + 3)

theorem largeScaleBalancedDirectionCurrent_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    0 ≤ largeScaleBalancedDirectionCurrent solution t q := by
  unfold largeScaleBalancedDirectionCurrent
  exact tsum_nonneg fun scale ↦
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem canonicalBalancedScaleCurrent_le_temporalFactor_mul_weight
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    canonicalBalancedScaleCurrent solution t q (scale + 3) ≤
      balancedTemporalFactor solution t * inverseFourthRootDyadicTailWeight scale := by
  let omega : ℝ := sliceVorticitySup solution t
  let L : ℝ := openPeriodicCanonicalVorticityLipschitzConstant solution t
  let kernelConstant : ℝ := dyadicHodgeUniformSubsetMassConstant
  have homega : 0 ≤ omega := norm_nonneg _
  have hL : 0 ≤ L :=
    (openPeriodicCanonicalVorticityLipschitzConstant solution t).coe_nonneg
  have hkernel : 0 ≤ kernelConstant := by
    dsimp [kernelConstant, dyadicHodgeUniformSubsetMassConstant]
    norm_num
  have hscale : 3 ≤ scale + 3 := by omega
  have hdistance := dyadicHodgeJacobianKernelDistanceMoment_le
    (scale + 3) hscale
  have hzero := dyadicHodgeJacobianKernelZeroMoment_le (scale + 3) hscale
  have hhigh := highDirectionKernelMoment_le solution t q (scale + 3)
  have hlow := lowAmplitudeKernelMoment_le solution t q (scale + 3)
  have hhighBound :
      highDirectionKernelMoment solution t q (scale + 3) ≤
        balancedHighTemporalEnvelope solution t /
          Real.sqrt (dyadicRadius (scale + 3) : ℝ) := by
    calc
      highDirectionKernelMoment solution t q (scale + 3) ≤
          omega ^ 2 * dyadicHodgeJacobianKernelModulusMoment
            (torusDistancePowerModulus 1) (scale + 3) := hhigh
      _ ≤ omega ^ 2 *
          ((405 * kernelConstant) /
            (2 * Real.sqrt (dyadicRadius (scale + 3) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hdistance (sq_nonneg omega)
      _ = balancedHighTemporalEnvelope solution t /
          Real.sqrt (dyadicRadius (scale + 3) : ℝ) := by
        dsimp [balancedHighTemporalEnvelope, omega, kernelConstant]
        ring
  have hlowBound :
      lowAmplitudeKernelMoment solution t q (scale + 3) ≤
        balancedLowTemporalEnvelope solution t := by
    calc
      lowAmplitudeKernelMoment solution t q (scale + 3) ≤
          (2 * omega) * dyadicHodgeJacobianKernelZeroMoment (scale + 3) := hlow
      _ ≤ (2 * omega) * (216 * kernelConstant) :=
        mul_le_mul_of_nonneg_left hzero (mul_nonneg (by norm_num) homega)
      _ = balancedLowTemporalEnvelope solution t := by
        rfl
  have hhighEnvelope : 0 ≤ balancedHighTemporalEnvelope solution t := by
    unfold balancedHighTemporalEnvelope
    positivity
  have hnumerator :
      0 ≤ 2 * L * balancedHighTemporalEnvelope solution t :=
    mul_nonneg (mul_nonneg (by norm_num) hL) hhighEnvelope
  change
    Real.sqrt (2 * L * highDirectionKernelMoment solution t q (scale + 3)) *
        Real.sqrt (lowAmplitudeKernelMoment solution t q (scale + 3)) ≤ _
  calc
    Real.sqrt (2 * L * highDirectionKernelMoment solution t q (scale + 3)) *
          Real.sqrt (lowAmplitudeKernelMoment solution t q (scale + 3)) ≤
        Real.sqrt (2 * L *
          (balancedHighTemporalEnvelope solution t /
            Real.sqrt (dyadicRadius (scale + 3) : ℝ))) *
          Real.sqrt (balancedLowTemporalEnvelope solution t) :=
      mul_le_mul
        (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left hhighBound
            (mul_nonneg (by norm_num) hL)))
        (Real.sqrt_le_sqrt hlowBound)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = balancedTemporalFactor solution t * inverseFourthRootDyadicTailWeight scale := by
      unfold balancedTemporalFactor inverseFourthRootDyadicTailWeight
      rw [show 2 * L *
          (balancedHighTemporalEnvelope solution t /
            Real.sqrt (dyadicRadius (scale + 3) : ℝ)) =
        (2 * L * balancedHighTemporalEnvelope solution t) /
          Real.sqrt (dyadicRadius (scale + 3) : ℝ) by ring]
      rw [Real.sqrt_div hnumerator]
      ring

/-- **Exact reconstruction/gluing theorem.**  The complete large-scale current is dominated by
one receiver-independent temporal factor times the returned fourth-root Hodge population. -/
theorem largeScaleBalancedDirectionCurrent_le_temporalEnvelope
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    largeScaleBalancedDirectionCurrent solution t q ≤
      balancedTemporalEnvelope solution t := by
  have hcurrent : Summable (fun scale : ℕ ↦
      canonicalBalancedScaleCurrent solution t q (scale + 3)) :=
    (summable_nat_add_iff 3).2
      (summable_canonicalBalancedScaleCurrent solution t q)
  have hmajorant :=
    summable_inverseFourthRootDyadicTailWeight.mul_left
      (balancedTemporalFactor solution t)
  have hsum := hcurrent.tsum_le_tsum
    (canonicalBalancedScaleCurrent_le_temporalFactor_mul_weight solution t q) hmajorant
  unfold largeScaleBalancedDirectionCurrent balancedTemporalEnvelope
    inverseFourthRootDyadicTailMass
  simpa only [tsum_mul_left] using hsum

/-! ## Strict-interior time continuity -/

theorem highDirectionKernelMoment_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (scale : ℕ) :
    Continuous (fun t : Set.Ioo 0 T ↦
      highDirectionKernelMoment solution t q scale) := by
  letI : LocallyCompactSpace (Set.Ioo (0 : ℝ) T) :=
    isOpen_Ioo.locallyCompactSpace
  unfold highDirectionKernelMoment
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure SpatialTorus)) (s := Set.univ) (by
        unfold dyadicHodgeJacobianKernelPointMass
        fun_prop) isCompact_univ

theorem lowAmplitudeKernelMoment_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (scale : ℕ) :
    Continuous (fun t : Set.Ioo 0 T ↦
      lowAmplitudeKernelMoment solution t q scale) := by
  letI : LocallyCompactSpace (Set.Ioo (0 : ℝ) T) :=
    isOpen_Ioo.locallyCompactSpace
  unfold lowAmplitudeKernelMoment
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure SpatialTorus)) (s := Set.univ) (by
        unfold dyadicHodgeJacobianKernelPointMass
        fun_prop) isCompact_univ

theorem canonicalBalancedScaleCurrent_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (scale : ℕ) :
    Continuous (fun t : Set.Ioo 0 T ↦
      canonicalBalancedScaleCurrent solution t q scale) := by
  unfold canonicalBalancedScaleCurrent
  have hL : Continuous (fun t : Set.Ioo 0 T ↦
      (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)) :=
    NNReal.continuous_coe.comp
      (openPeriodicCanonicalVorticityLipschitzConstant_continuous solution)
  have hhigh := highDirectionKernelMoment_continuous solution q scale
  have hlow := lowAmplitudeKernelMoment_continuous solution q scale
  exact (Real.continuous_sqrt.comp ((continuous_const.mul hL).mul hhigh)).mul
    (Real.continuous_sqrt.comp hlow)

theorem balancedTemporalFactor_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (balancedTemporalFactor solution) := by
  have homega := continuous_norm_torusVorticityEvolution solution
  have hL : Continuous (fun t : Set.Ioo 0 T ↦
      (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)) :=
    NNReal.continuous_coe.comp
      (openPeriodicCanonicalVorticityLipschitzConstant_continuous solution)
  have hhigh : Continuous (balancedHighTemporalEnvelope solution) := by
    unfold balancedHighTemporalEnvelope sliceVorticitySup
    exact (homega.pow 2).mul continuous_const
  have hlow : Continuous (balancedLowTemporalEnvelope solution) := by
    unfold balancedLowTemporalEnvelope sliceVorticitySup
    exact (continuous_const.mul homega).mul continuous_const
  unfold balancedTemporalFactor
  exact (Real.continuous_sqrt.comp ((continuous_const.mul hL).mul hhigh)).mul
    (Real.continuous_sqrt.comp hlow)

theorem balancedTemporalEnvelope_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (balancedTemporalEnvelope solution) := by
  unfold balancedTemporalEnvelope
  exact (balancedTemporalFactor_continuous solution).mul continuous_const

/-! ## Compact-interior gluing of the complete scale current -/

/-- The complete large-scale current, totalized outside the admitted open lifespan. -/
def largeScaleBalancedDirectionCurrentRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo (0 : ℝ) T then
    largeScaleBalancedDirectionCurrent solution ⟨s, hs⟩ q
  else 0

/-- The receiver-independent envelope, totalized through the same lifespan aperture. -/
def balancedTemporalEnvelopeRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo (0 : ℝ) T then
    balancedTemporalEnvelope solution ⟨s, hs⟩
  else 0

theorem largeScaleBalancedDirectionCurrentRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (s : ℝ) :
    0 ≤ largeScaleBalancedDirectionCurrentRate solution q s := by
  unfold largeScaleBalancedDirectionCurrentRate
  split_ifs with hs
  · exact largeScaleBalancedDirectionCurrent_nonneg solution ⟨s, hs⟩ q
  · exact le_rfl

theorem largeScaleBalancedDirectionCurrentRate_le_envelopeRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) (s : ℝ) :
    largeScaleBalancedDirectionCurrentRate solution q s ≤
      balancedTemporalEnvelopeRate solution s := by
  unfold largeScaleBalancedDirectionCurrentRate balancedTemporalEnvelopeRate
  split_ifs with hs
  · exact largeScaleBalancedDirectionCurrent_le_temporalEnvelope solution ⟨s, hs⟩ q
  · exact le_rfl

/-- On every compact interval strictly inside the lifespan, the actual scale-summed current is a
continuous receiver.  The proof uses a uniform fourth-root Weierstrass population rather than
interchanging an unproved terminal limit. -/
theorem largeScaleBalancedDirectionCurrentRate_continuousOn_Icc
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) {a b : ℝ}
    (ha : 0 < a) (hb : b < T) :
    ContinuousOn (largeScaleBalancedDirectionCurrentRate solution q) (Set.Icc a b) := by
  have hab : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  let lift : Set.Icc a b → Set.Ioo (0 : ℝ) T :=
    fun s ↦ ⟨s.1, hab s.2⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hfactorContinuous : Continuous (fun s : Set.Icc a b ↦
      balancedTemporalFactor solution (lift s)) :=
    (balancedTemporalFactor_continuous solution).comp hlift
  obtain ⟨K, hK⟩ := bddAbove_def.mp
    (isCompact_univ.bddAbove_image hfactorContinuous.continuousOn)
  let K₀ : ℝ := max 0 K
  have hfactorBound : ∀ s : Set.Icc a b,
      balancedTemporalFactor solution (lift s) ≤ K₀ := by
    intro s
    have hsK : balancedTemporalFactor solution (lift s) ≤ K := by
      apply hK
      exact ⟨s, Set.mem_univ s, rfl⟩
    exact hsK.trans (le_max_right _ _)
  have hmodes : ∀ scale : ℕ, Continuous (fun s : Set.Icc a b ↦
      canonicalBalancedScaleCurrent solution (lift s) q (scale + 3)) := by
    intro scale
    exact (canonicalBalancedScaleCurrent_continuous solution q (scale + 3)).comp hlift
  have hmajorant : Summable (fun scale : ℕ ↦
      K₀ * inverseFourthRootDyadicTailWeight scale) :=
    summable_inverseFourthRootDyadicTailWeight.mul_left K₀
  have hseries : Continuous (fun s : Set.Icc a b ↦
      ∑' scale : ℕ,
        canonicalBalancedScaleCurrent solution (lift s) q (scale + 3)) := by
    apply continuous_tsum hmodes hmajorant
    intro scale s
    rw [Real.norm_of_nonneg]
    · exact
        (canonicalBalancedScaleCurrent_le_temporalFactor_mul_weight
          solution (lift s) q scale).trans
          (mul_le_mul_of_nonneg_right (hfactorBound s)
            (inverseFourthRootDyadicTailWeight_nonneg scale))
    · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [continuousOn_iff_continuous_restrict]
  apply hseries.congr
  intro s
  simp [largeScaleBalancedDirectionCurrentRate,
    largeScaleBalancedDirectionCurrent, lift, hab s.2]

/-- **Strict-interior time theorem.**  The complete large-scale balanced current is
interval-integrable on every ordered compact interval strictly inside the maximal lifespan. -/
theorem largeScaleBalancedDirectionCurrentRate_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (q : SpatialTorus) {a b : ℝ}
    (ha : 0 < a) (habOrder : a ≤ b) (hb : b < T) :
    IntervalIntegrable
      (largeScaleBalancedDirectionCurrentRate solution q) volume a b := by
  have hcontinuous :=
    largeScaleBalancedDirectionCurrentRate_continuousOn_Icc
      solution q ha hb
  have huIcc : ContinuousOn
      (largeScaleBalancedDirectionCurrentRate solution q) [[a, b]] := by
    simpa [uIcc_of_le habOrder] using hcontinuous
  exact huIcc.intervalIntegrable

section Audit

#print axioms summable_inverseFourthRootDyadicTailWeight
#print axioms canonicalBalancedScaleCurrent_le_temporalFactor_mul_weight
#print axioms largeScaleBalancedDirectionCurrent_le_temporalEnvelope
#print axioms highDirectionKernelMoment_continuous
#print axioms lowAmplitudeKernelMoment_continuous
#print axioms canonicalBalancedScaleCurrent_continuous
#print axioms balancedTemporalFactor_continuous
#print axioms balancedTemporalEnvelope_continuous
#print axioms largeScaleBalancedDirectionCurrentRate_le_envelopeRate
#print axioms largeScaleBalancedDirectionCurrentRate_continuousOn_Icc
#print axioms largeScaleBalancedDirectionCurrentRate_intervalIntegrable

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionBalancedTime
