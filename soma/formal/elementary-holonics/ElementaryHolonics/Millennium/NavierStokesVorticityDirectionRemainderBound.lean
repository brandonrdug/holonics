import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionProjection

/-!
# A uniform finite-frequency bound through the direction remainder

**[proved-derived]** The exact scalar-triple-product law is degree zero in frequency.  This owner
makes that scale cancellation quantitative with an explicit three-coordinate `L¹` receiver.  Dot
transport, cross transport, and the lattice inequality `|k|₁² ≤ 3 |k|₂²` give one exact
frequency-independent constant.  Finite Hodge stretching is consequently controlled only by the
mass of the canonical direction remainders, with every addressed mode retained.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

/-- Exact three-coordinate `L¹` receiver for one complex vorticity occurrence. -/
def complexVectorL1 (v : ComplexVector) : ℝ :=
  ‖v 0‖ + ‖v 1‖ + ‖v 2‖

/-- Exact three-coordinate `L¹` receiver for one integer lattice frequency. -/
def frequencyL1 (frequency : SpatialFrequency) : ℝ :=
  |(frequency 0 : ℝ)| + |(frequency 1 : ℝ)| + |(frequency 2 : ℝ)|

theorem complexVectorL1_nonneg (v : ComplexVector) :
    0 ≤ complexVectorL1 v := by
  unfold complexVectorL1
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem frequencyL1_nonneg (frequency : SpatialFrequency) :
    0 ≤ frequencyL1 frequency := by
  unfold frequencyL1
  exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-- Bilinear complex dot transport is bounded by the product of the explicit `L¹` receivers. -/
theorem norm_complexDot_le_l1_mul_l1 (a b : ComplexVector) :
    ‖complexDot a b‖ ≤ complexVectorL1 a * complexVectorL1 b := by
  rw [complexDot, dotProduct]
  calc
    ‖∑ coordinate : Fin 3, a coordinate * b coordinate‖ ≤
        ∑ coordinate : Fin 3, ‖a coordinate * b coordinate‖ := norm_sum_le _ _
    _ = ‖a 0‖ * ‖b 0‖ + ‖a 1‖ * ‖b 1‖ + ‖a 2‖ * ‖b 2‖ := by
      simp [Fin.sum_univ_succ]
      ring
    _ ≤ complexVectorL1 a * complexVectorL1 b := by
      unfold complexVectorL1
      nlinarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2),
        norm_nonneg (b 0), norm_nonneg (b 1), norm_nonneg (b 2),
        mul_nonneg (norm_nonneg (a 0)) (norm_nonneg (b 1)),
        mul_nonneg (norm_nonneg (a 0)) (norm_nonneg (b 2)),
        mul_nonneg (norm_nonneg (a 1)) (norm_nonneg (b 0)),
        mul_nonneg (norm_nonneg (a 1)) (norm_nonneg (b 2)),
        mul_nonneg (norm_nonneg (a 2)) (norm_nonneg (b 0)),
        mul_nonneg (norm_nonneg (a 2)) (norm_nonneg (b 1))]

/-- The oriented cross transport obeys the same exact `L¹` product receiver. -/
theorem complexVectorL1_cross_le_mul
    (a b : ComplexVector) :
    complexVectorL1 (complexCross a b) ≤ complexVectorL1 a * complexVectorL1 b := by
  have h0 : ‖a 1 * b 2 - a 2 * b 1‖ ≤
      ‖a 1‖ * ‖b 2‖ + ‖a 2‖ * ‖b 1‖ := by
    simpa only [norm_mul] using norm_sub_le (a 1 * b 2) (a 2 * b 1)
  have h1 : ‖a 2 * b 0 - a 0 * b 2‖ ≤
      ‖a 2‖ * ‖b 0‖ + ‖a 0‖ * ‖b 2‖ := by
    simpa only [norm_mul] using norm_sub_le (a 2 * b 0) (a 0 * b 2)
  have h2 : ‖a 0 * b 1 - a 1 * b 0‖ ≤
      ‖a 0‖ * ‖b 1‖ + ‖a 1‖ * ‖b 0‖ := by
    simpa only [norm_mul] using norm_sub_le (a 0 * b 1) (a 1 * b 0)
  change
    ‖a 1 * b 2 - a 2 * b 1‖ +
        ‖a 2 * b 0 - a 0 * b 2‖ +
          ‖a 0 * b 1 - a 1 * b 0‖ ≤
      (‖a 0‖ + ‖a 1‖ + ‖a 2‖) * (‖b 0‖ + ‖b 1‖ + ‖b 2‖)
  nlinarith [norm_nonneg (a 0), norm_nonneg (a 1), norm_nonneg (a 2),
    norm_nonneg (b 0), norm_nonneg (b 1), norm_nonneg (b 2),
    mul_nonneg (norm_nonneg (a 0)) (norm_nonneg (b 0)),
    mul_nonneg (norm_nonneg (a 1)) (norm_nonneg (b 1)),
    mul_nonneg (norm_nonneg (a 2)) (norm_nonneg (b 2))]

/-- The complex embedding of an integer frequency has exactly its real `L¹` reading. -/
theorem complexVectorL1_complexFrequencyVector
    (frequency : SpatialFrequency) :
    complexVectorL1 (complexFrequencyVector frequency) = frequencyL1 frequency := by
  simp [complexVectorL1, complexFrequencyVector, frequencyL1, Complex.norm_intCast]

/-- Three-coordinate Cauchy inequality for the exact integer lattice faces. -/
theorem frequencyL1_sq_le_three_mul_frequencySquared
    (frequency : SpatialFrequency) :
    frequencyL1 frequency ^ 2 ≤ 3 * frequencySquared frequency := by
  have hsquared : frequencySquared frequency =
      (frequency 0 : ℝ) ^ 2 + (frequency 1 : ℝ) ^ 2 +
        (frequency 2 : ℝ) ^ 2 := by
    simp [frequencySquared, Fin.sum_univ_succ]
    ring
  rw [hsquared]
  unfold frequencyL1
  have h0 : |(frequency 0 : ℝ)| ^ 2 = (frequency 0 : ℝ) ^ 2 := sq_abs _
  have h1 : |(frequency 1 : ℝ)| ^ 2 = (frequency 1 : ℝ) ^ 2 := sq_abs _
  have h2 : |(frequency 2 : ℝ)| ^ 2 = (frequency 2 : ℝ) ^ 2 := sq_abs _
  nlinarith [h0, h1, h2,
    sq_nonneg (|(frequency 0 : ℝ)| - |(frequency 1 : ℝ)|),
    sq_nonneg (|(frequency 0 : ℝ)| - |(frequency 2 : ℝ)|),
    sq_nonneg (|(frequency 1 : ℝ)| - |(frequency 2 : ℝ)|)]

/-- **Uniform degree-zero mode bound.**  The frequency magnitude cancels exactly; only the
receiver magnitude and the direction-remainder magnitude survive. -/
theorem norm_hodgeStrainModeReading_le_directionRemainder
    (frequency : SpatialFrequency) (receiver remainder : ComplexVector) :
    ‖hodgeStrainModeReading frequency receiver remainder‖ ≤
      3 * complexVectorL1 receiver ^ 2 * complexVectorL1 remainder := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [hodgeStrainModeReading, hodgeStrainMode, hodgeJacobianMode_zero]
    simp [symmetricComplexJacobianPart, complexStretchingReading, complexMatrixAction,
      complexDot]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (complexVectorL1_nonneg remainder)
  · rw [hodgeStrainModeReading_eq_scalarTriple hfrequency, norm_div, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (frequencySquared_pos hfrequency)]
    have hdotFrequency := norm_complexDot_le_l1_mul_l1 receiver
      (complexFrequencyVector frequency)
    rw [complexVectorL1_complexFrequencyVector] at hdotFrequency
    have hdotCross := norm_complexDot_le_l1_mul_l1 receiver
      (complexCross (complexFrequencyVector frequency) remainder)
    have hcross := complexVectorL1_cross_le_mul
      (complexFrequencyVector frequency) remainder
    rw [complexVectorL1_complexFrequencyVector] at hcross
    have hdotCross' :
        ‖complexDot receiver
          (complexCross (complexFrequencyVector frequency) remainder)‖ ≤
          complexVectorL1 receiver *
            (frequencyL1 frequency * complexVectorL1 remainder) :=
      hdotCross.trans (mul_le_mul_of_nonneg_left hcross
        (complexVectorL1_nonneg receiver))
    have hspos := frequencySquared_pos hfrequency
    have hfrequencyL1 := frequencyL1_sq_le_three_mul_frequencySquared frequency
    have hproduct :
        ‖complexDot receiver (complexFrequencyVector frequency)‖ *
            ‖complexDot receiver
              (complexCross (complexFrequencyVector frequency) remainder)‖ ≤
          (complexVectorL1 receiver * frequencyL1 frequency) *
            (complexVectorL1 receiver *
              (frequencyL1 frequency * complexVectorL1 remainder)) :=
      mul_le_mul hdotFrequency hdotCross' (norm_nonneg _)
        (mul_nonneg (complexVectorL1_nonneg receiver)
          (frequencyL1_nonneg frequency))
    have hratio : frequencyL1 frequency ^ 2 / frequencySquared frequency ≤ 3 :=
      (div_le_iff₀ hspos).2 hfrequencyL1
    calc
      ‖complexDot receiver (complexFrequencyVector frequency)‖ *
            ‖complexDot receiver
              (complexCross (complexFrequencyVector frequency) remainder)‖ /
          frequencySquared frequency ≤
        ((complexVectorL1 receiver * frequencyL1 frequency) *
            (complexVectorL1 receiver *
              (frequencyL1 frequency * complexVectorL1 remainder))) /
          frequencySquared frequency :=
        div_le_div_of_nonneg_right hproduct hspos.le
      _ = (complexVectorL1 receiver ^ 2 * complexVectorL1 remainder) *
          (frequencyL1 frequency ^ 2 / frequencySquared frequency) := by ring
      _ ≤ (complexVectorL1 receiver ^ 2 * complexVectorL1 remainder) * 3 :=
        mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (sq_nonneg _) (complexVectorL1_nonneg remainder))
      _ = 3 * complexVectorL1 receiver ^ 2 * complexVectorL1 remainder := by ring

/-- Total canonical direction-remainder mass in one finite addressed population. -/
def finiteDirectionRemainderMass
    (modes : Finset SpatialFrequency) (receiver : ComplexVector)
    (source : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ frequency ∈ modes,
    complexVectorL1 (receiverDirectionRemainder receiver (source frequency))

/-- The complete finite Hodge-strain return is bounded by the canonical remainder mass. -/
theorem norm_finiteHodgeStrainReading_le_directionRemainderMass
    (modes : Finset SpatialFrequency) (receiver : ComplexVector)
    (source : SpatialFrequency → ComplexVector) :
    ‖finiteHodgeStrainReading modes receiver source‖ ≤
      3 * complexVectorL1 receiver ^ 2 *
        finiteDirectionRemainderMass modes receiver source := by
  rw [← finiteHodgeStrainReading_sub_aligned modes receiver source
    (fun frequency ↦ receiverAlignedAmplitude receiver (source frequency))]
  unfold finiteHodgeStrainReading finiteDirectionRemainderMass receiverDirectionRemainder
  calc
    ‖∑ frequency ∈ modes,
        hodgeStrainModeReading frequency receiver
          (source frequency - receiverAlignedAmplitude receiver (source frequency) • receiver)‖ ≤
      ∑ frequency ∈ modes,
        ‖hodgeStrainModeReading frequency receiver
          (source frequency - receiverAlignedAmplitude receiver (source frequency) • receiver)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ frequency ∈ modes,
        3 * complexVectorL1 receiver ^ 2 *
          complexVectorL1
            (source frequency - receiverAlignedAmplitude receiver (source frequency) • receiver) := by
      gcongr with frequency hfrequency
      exact norm_hodgeStrainModeReading_le_directionRemainder frequency receiver _
    _ = 3 * complexVectorL1 receiver ^ 2 *
        ∑ frequency ∈ modes,
          complexVectorL1
            (source frequency - receiverAlignedAmplitude receiver (source frequency) • receiver) := by
      rw [Finset.mul_sum]

/-- **[proved-derived; formal-checked]** The actual finite periodic strain occurrence is bounded
by the pointwise receiving-vorticity magnitude squared times the exact transported canonical
direction-remainder population, uniformly in every admitted frequency. -/
theorem norm_openPeriodicFiniteHodgeStrainReading_le_directionRemainderMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    ‖openPeriodicFiniteHodgeStrainReading solution t q modes‖ ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
        finiteDirectionRemainderMass modes
          (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicTransportedVorticityMode solution t q) := by
  exact norm_finiteHodgeStrainReading_le_directionRemainderMass modes
    (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q)

section Audit

#print axioms norm_complexDot_le_l1_mul_l1
#print axioms complexVectorL1_cross_le_mul
#print axioms frequencyL1_sq_le_three_mul_frequencySquared
#print axioms norm_hodgeStrainModeReading_le_directionRemainder
#print axioms norm_finiteHodgeStrainReading_le_directionRemainderMass
#print axioms norm_openPeriodicFiniteHodgeStrainReading_le_directionRemainderMass

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
