import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import ElementaryHolonics.Millennium.NavierStokesSmoothHodgeJacobianBand
import Mathlib.Algebra.BigOperators.Module

/-!
# Discrete cancellation data for the annular Hodge kernel

**[proved-derived]** The adjacent Hodge kernel is already an exact finite Fourier multiplier,
but its radius-independent physical `L1` bound is still open.  This owner records two inputs for
the discrete scale route without assuming that bound:

* every addressed Hodge Jacobian multiplier entry is the degree-zero ratio obtained by cancelling
  the two Fourier derivative constants;
* Abel summation turns a finite character synthesis into an endpoint plus first coefficient
  differences, and exact zero padding permits a second passage with no boundary loss;
* the resulting pointwise receiver is the minimum of raw coefficient mass and zero-padded second
  variation divided by the squared distance to the character identity.

The second return is deliberately coefficient-generic.  It is the one-coordinate passage that can
be iterated through the three torus coordinates once suitable first/second difference bounds for
the annular Hodge multiplier have been supplied.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand

/-! ## Exact degree-zero multiplier entry -/

/-- Cancelling the derivative multiplier against the Biot--Savart constant exposes the exact
degree-zero Hodge ratio.  The zero mode is included: both sides use totalized division and vanish.
-/
theorem hodgeJacobianMultiplierEntry_eq_ratio
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    hodgeJacobianMultiplierEntry frequency component coordinate input =
      -((frequency coordinate : ℂ) *
          complexCross (complexFrequencyVector frequency) (Pi.single input 1) component) /
        (frequencySquared frequency : ℂ) := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    simp [hodgeJacobianMultiplierEntry, hodgeJacobianMode,
      fourierJacobianMode, nonzeroModeHodgeReconstruction]
  · have hs : (frequencySquared frequency : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (frequencySquared_pos hfrequency).ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [hodgeJacobianMultiplierEntry, hodgeJacobianMode,
      fourierJacobianMode, nonzeroModeHodgeReconstruction, Pi.smul_apply,
      smul_eq_mul]
    field_simp [hs, hpi]
    rw [Complex.I_sq]
    ring

/-- The numerator of every addressed Hodge ratio is dominated by the full squared frequency.
This is the elementary magnitude input behind the degree-zero bound. -/
theorem norm_hodgeJacobianMultiplierNumerator_le_frequencySquared
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    ‖(frequency coordinate : ℂ) *
        complexCross (complexFrequencyVector frequency) (Pi.single input 1) component‖ ≤
      frequencySquared frequency := by
  have h01 := two_mul_le_add_sq |(frequency 0 : ℝ)| |(frequency 1 : ℝ)|
  have h02 := two_mul_le_add_sq |(frequency 0 : ℝ)| |(frequency 2 : ℝ)|
  have h12 := two_mul_le_add_sq |(frequency 1 : ℝ)| |(frequency 2 : ℝ)|
  simp only [sq_abs] at h01 h02 h12
  fin_cases component <;> fin_cases coordinate <;> fin_cases input <;>
    simp [complexCross, complexFrequencyVector, crossProduct, frequencySquared,
      Fin.sum_univ_succ, Complex.norm_intCast] <;>
    nlinarith [sq_nonneg (frequency 0 : ℝ), sq_nonneg (frequency 1 : ℝ),
      sq_nonneg (frequency 2 : ℝ), h01, h02, h12]

/-- Every addressed Hodge Jacobian entry has degree-zero magnitude at most one, uniformly over
all lattice frequencies.  This estimate alone does not control the physical kernel `L1` norm;
the missing input is summable variation across the annular lattice population. -/
theorem norm_hodgeJacobianMultiplierEntry_le_one
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    ‖hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤ 1 := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    simp [hodgeJacobianMultiplierEntry, hodgeJacobianMode,
      fourierJacobianMode, nonzeroModeHodgeReconstruction]
  · have hspos : 0 < frequencySquared frequency := frequencySquared_pos hfrequency
    rw [hodgeJacobianMultiplierEntry_eq_ratio, norm_div, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
    exact (div_le_one hspos).mpr
      (norm_hodgeJacobianMultiplierNumerator_le_frequencySquared
        frequency component coordinate input)

/-- The magnitude of the actual adjacent Hodge coefficient is no larger than the magnitude of
its scalar scale chart.  Thus all remaining scale growth lies in lattice variation and population,
not in the degree-zero Hodge factor. -/
theorem norm_adjacentHodgeJacobianMultiplierEntry_le_weight
    (radius : ℕ) (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    ‖(adjacentValleePoussinWeight radius frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      |adjacentValleePoussinWeight radius frequency| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |adjacentValleePoussinWeight radius frequency| *
        ‖hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      |adjacentValleePoussinWeight radius frequency| * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_hodgeJacobianMultiplierEntry_le_one frequency component coordinate input)
          (abs_nonneg _)
    _ = |adjacentValleePoussinWeight radius frequency| := mul_one _

/-- Exact cancellation of every scalar entry on the inner plateau cube. -/
theorem adjacentHodgeJacobianMultiplierEntry_eq_zero_of_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1))
    (component coordinate input : Fin 3) :
    (adjacentValleePoussinWeight radius frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input = 0 := by
  rw [adjacentValleePoussinWeight_eq_zero_of_mem_inner radius hfrequency]
  norm_num

/-- Exact cancellation of every scalar entry outside the adjacent outer cube. -/
theorem adjacentHodgeJacobianMultiplierEntry_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (component coordinate input : Fin 3) :
    (adjacentValleePoussinWeight radius frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input = 0 := by
  rw [adjacentValleePoussinWeight_eq_zero_of_not_mem_outer radius hfrequency]
  norm_num

/-! ## One-coordinate Abel transport -/

/-- The partial character population used by Abel summation. -/
def characterPartialSum (z : ℂ) (count : ℕ) : ℂ :=
  ∑ index ∈ Finset.range count, z ^ index

/-- Exact Abel transformation for a finite character synthesis.  This is a direct specialization
of summation by parts, with all endpoint and first-difference terms retained. -/
theorem finiteCharacterSynthesis_eq_endpoint_sub_differences
    (coefficient : ℕ → ℂ) (z : ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range count, coefficient index * z ^ index) =
      coefficient (count - 1) * characterPartialSum z count -
        ∑ index ∈ Finset.range (count - 1),
          (coefficient (index + 1) - coefficient index) *
            characterPartialSum z (index + 1) := by
  simpa only [characterPartialSum, smul_eq_mul] using
    (Finset.sum_range_by_parts coefficient (fun index : ℕ ↦ z ^ index) count)

/-- A unit-modulus character has partial sums bounded by the inverse distance to the identity.
No estimate is made at the identity point, where the divisor vanishes. -/
theorem norm_characterPartialSum_le
    {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) (count : ℕ) :
    ‖characterPartialSum z count‖ ≤ 2 / ‖1 - z‖ := by
  have hdenominator : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm)
  have hgeom : characterPartialSum z count * (1 - z) = 1 - z ^ count := by
    exact geom_sum_mul_neg z count
  have hpower : ‖z ^ count‖ = 1 := by simp [norm_pow, hzNorm]
  have hrhs : ‖1 - z ^ count‖ ≤ 2 := by
    calc
      ‖1 - z ^ count‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ count‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, hpower]; norm_num
  rw [← hgeom, norm_mul] at hrhs
  exact (le_div_iff₀ hdenominator).mpr hrhs

/-- First-difference control of finite character synthesis away from the character identity.
This is the precise discrete receiver supplied by one Abel passage. -/
theorem norm_finiteCharacterSynthesis_le_firstVariation
    (coefficient : ℕ → ℂ) {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1)
    (count : ℕ) :
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ ≤
      (2 / ‖1 - z‖) *
        (‖coefficient (count - 1)‖ +
          ∑ index ∈ Finset.range (count - 1),
            ‖coefficient (index + 1) - coefficient index‖) := by
  rw [finiteCharacterSynthesis_eq_endpoint_sub_differences]
  calc
    ‖coefficient (count - 1) * characterPartialSum z count -
        ∑ index ∈ Finset.range (count - 1),
          (coefficient (index + 1) - coefficient index) *
            characterPartialSum z (index + 1)‖ ≤
      ‖coefficient (count - 1) * characterPartialSum z count‖ +
        ‖∑ index ∈ Finset.range (count - 1),
          (coefficient (index + 1) - coefficient index) *
            characterPartialSum z (index + 1)‖ := norm_sub_le _ _
    _ ≤
      ‖coefficient (count - 1)‖ * (2 / ‖1 - z‖) +
        ∑ index ∈ Finset.range (count - 1),
          ‖coefficient (index + 1) - coefficient index‖ *
            (2 / ‖1 - z‖) := by
      gcongr
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_characterPartialSum_le hzNorm hz count) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro index _hindex
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_characterPartialSum_le hzNorm hz (index + 1)) (norm_nonneg _)
    _ = (2 / ‖1 - z‖) *
        (‖coefficient (count - 1)‖ +
          ∑ index ∈ Finset.range (count - 1),
            ‖coefficient (index + 1) - coefficient index‖) := by
      rw [← Finset.sum_mul]
      ring

/-! ## Zero-padded finite support -/

/-- Extend a coefficient population by one exact zero.  This is the appropriate chart for a
compactly supported annular multiplier: padding just beyond its outer radius deletes the Abel
endpoint without changing the synthesis. -/
def zeroPaddedCoefficient (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  if index < count then coefficient index else 0

/-- Appending the exact zero coefficient leaves the finite character synthesis unchanged. -/
theorem finiteCharacterSynthesis_zeroPadded
    (coefficient : ℕ → ℂ) (z : ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 1),
        zeroPaddedCoefficient coefficient count index * z ^ index) =
      ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
  rw [Finset.sum_range_succ]
  have hinterior :
      (∑ index ∈ Finset.range count,
          zeroPaddedCoefficient coefficient count index * z ^ index) =
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    simp [zeroPaddedCoefficient, hindex]
  rw [hinterior]
  simp [zeroPaddedCoefficient]

/-- Backward difference of the coefficient population after exact zero extension at both ends.
Its addressed population has length `count + 1`. -/
def zeroPaddedBackwardDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  zeroPaddedCoefficient coefficient count index -
    if index = 0 then 0 else zeroPaddedCoefficient coefficient count (index - 1)

/-- Multiplication by `1 - z` is exactly one backward-difference passage on a zero-padded finite
character synthesis.  Unlike an interval formula with exposed endpoints, this form can be
iterated without losing boundary terms. -/
theorem finiteCharacterSynthesis_zeroPaddedBackwardDifference
    (coefficient : ℕ → ℂ) (z : ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 1),
        zeroPaddedBackwardDifference coefficient count index * z ^ index) =
      (1 - z) *
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
  have hinterior :
      (∑ index ∈ Finset.range count,
          zeroPaddedCoefficient coefficient count index * z ^ index) =
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    simp [zeroPaddedCoefficient, hindex]
  have hupper := finiteCharacterSynthesis_zeroPadded coefficient z count
  rw [Finset.sum_range_succ'] at hupper
  simp only [pow_zero, mul_one] at hupper
  have hupper' :
      zeroPaddedCoefficient coefficient count 0 +
          ∑ index ∈ Finset.range count,
            zeroPaddedCoefficient coefficient count (index + 1) * z ^ (index + 1) =
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
    simpa [add_comm] using hupper
  have hlower :
      (∑ index ∈ Finset.range count,
          zeroPaddedCoefficient coefficient count index * z ^ (index + 1)) =
        z * ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
    calc
      (∑ index ∈ Finset.range count,
          zeroPaddedCoefficient coefficient count index * z ^ (index + 1)) =
          z * ∑ index ∈ Finset.range count,
            zeroPaddedCoefficient coefficient count index * z ^ index := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [pow_succ]
        ring
      _ = z * ∑ index ∈ Finset.range count,
          coefficient index * z ^ index := by rw [hinterior]
  rw [Finset.sum_range_succ']
  simp only [zeroPaddedBackwardDifference, if_pos, pow_zero, mul_one,
    Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hlower]
  simp only [sub_zero]
  calc
    (∑ index ∈ Finset.range count,
          zeroPaddedCoefficient coefficient count (index + 1) * z ^ (index + 1)) -
          z * ∑ index ∈ Finset.range count, coefficient index * z ^ index +
          zeroPaddedCoefficient coefficient count 0 =
        (zeroPaddedCoefficient coefficient count 0 +
            ∑ index ∈ Finset.range count,
              zeroPaddedCoefficient coefficient count (index + 1) * z ^ (index + 1)) -
          z * ∑ index ∈ Finset.range count, coefficient index * z ^ index := by abel
    _ = (∑ index ∈ Finset.range count, coefficient index * z ^ index) -
          z * ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
      rw [hupper']
    _ = 1 * (∑ index ∈ Finset.range count, coefficient index * z ^ index) -
          z * ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
      rw [one_mul]

/-- The second backward difference is the same zero-padded passage applied once more to the first
difference population.  Its addressed population has length `count + 2`. -/
def zeroPaddedSecondDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  zeroPaddedBackwardDifference
    (zeroPaddedBackwardDifference coefficient count) (count + 1) index

/-- Two exact Abel passages.  Multiplication by `(1 - z)²` is precisely synthesis of the
zero-padded second differences; no endpoint term or cyclicity assumption is hidden. -/
theorem finiteCharacterSynthesis_zeroPaddedSecondDifference
    (coefficient : ℕ → ℂ) (z : ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 2),
        zeroPaddedSecondDifference coefficient count index * z ^ index) =
      (1 - z) ^ 2 *
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
  have hsecond := finiteCharacterSynthesis_zeroPaddedBackwardDifference
    (zeroPaddedBackwardDifference coefficient count) z (count + 1)
  rw [finiteCharacterSynthesis_zeroPaddedBackwardDifference coefficient z count] at hsecond
  simpa [zeroPaddedSecondDifference, pow_two, mul_assoc, Nat.add_assoc] using hsecond

/-- Pointwise second-variation control away from the character identity.  This is the repeatable
Abel receiver needed by the annular kernel route: an application now owes an actual scale-uniform
bound for the zero-padded second differences of its coefficients. -/
theorem norm_finiteCharacterSynthesis_le_zeroPaddedSecondVariation
    (coefficient : ℕ → ℂ) {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1)
    (count : ℕ) :
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ ≤
      (∑ index ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count index‖) /
        ‖1 - z‖ ^ 2 := by
  have hdenominator : 0 < ‖1 - z‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm))
  apply (le_div_iff₀ hdenominator).mpr
  calc
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ * ‖1 - z‖ ^ 2 =
        ‖(1 - z) ^ 2 *
          ∑ index ∈ Finset.range count, coefficient index * z ^ index‖ := by
      rw [norm_mul, norm_pow]
      ring
    _ = ‖∑ index ∈ Finset.range (count + 2),
          zeroPaddedSecondDifference coefficient count index * z ^ index‖ := by
      rw [finiteCharacterSynthesis_zeroPaddedSecondDifference]
    _ ≤ ∑ index ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count index * z ^ index‖ :=
      norm_sum_le _ _
    _ ≤ (∑ index ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count index‖) := by
      apply Finset.sum_le_sum
      intro index _hindex
      simp [norm_pow, hzNorm]

/-- The complementary near-identity estimate: finite synthesis is bounded by its raw coefficient
mass.  Together with the second-variation estimate this supplies the standard two-regime envelope
used to integrate through the character identity. -/
theorem norm_finiteCharacterSynthesis_le_coefficientMass
    (coefficient : ℕ → ℂ) {z : ℂ} (hzNorm : ‖z‖ = 1) (count : ℕ) :
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ ≤
      ∑ index ∈ Finset.range count, ‖coefficient index‖ := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro index _hindex
  simp [norm_pow, hzNorm]

/-- The exact two-regime pointwise envelope after two Abel passages.  An annular application must
now estimate the coefficient mass and zero-padded second variation with reciprocal scale; the
minimum then crosses over at the physical angular scale. -/
theorem norm_finiteCharacterSynthesis_le_mass_min_secondVariation
    (coefficient : ℕ → ℂ) {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1)
    (count : ℕ) :
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ ≤
      min
        (∑ index ∈ Finset.range count, ‖coefficient index‖)
        ((∑ index ∈ Finset.range (count + 2),
            ‖zeroPaddedSecondDifference coefficient count index‖) /
          ‖1 - z‖ ^ 2) := by
  apply le_min
  · exact norm_finiteCharacterSynthesis_le_coefficientMass coefficient hzNorm count
  · exact norm_finiteCharacterSynthesis_le_zeroPaddedSecondVariation
      coefficient hzNorm hz count

/-- With one zero pad, the Abel estimate is purely the total first variation of the zero-extended
coefficient population.  No artificial endpoint magnitude remains. -/
theorem norm_finiteCharacterSynthesis_le_zeroPaddedFirstVariation
    (coefficient : ℕ → ℂ) {z : ℂ} (hzNorm : ‖z‖ = 1) (hz : z ≠ 1)
    (count : ℕ) :
    ‖∑ index ∈ Finset.range count, coefficient index * z ^ index‖ ≤
      (2 / ‖1 - z‖) *
        ∑ index ∈ Finset.range count,
          ‖zeroPaddedCoefficient coefficient count (index + 1) -
            zeroPaddedCoefficient coefficient count index‖ := by
  have hbound := norm_finiteCharacterSynthesis_le_firstVariation
    (zeroPaddedCoefficient coefficient count) hzNorm hz (count + 1)
  rw [finiteCharacterSynthesis_zeroPadded] at hbound
  simpa [zeroPaddedCoefficient] using hbound

section Audit

#print axioms hodgeJacobianMultiplierEntry_eq_ratio
#print axioms norm_hodgeJacobianMultiplierNumerator_le_frequencySquared
#print axioms norm_hodgeJacobianMultiplierEntry_le_one
#print axioms norm_adjacentHodgeJacobianMultiplierEntry_le_weight
#print axioms adjacentHodgeJacobianMultiplierEntry_eq_zero_of_mem_inner
#print axioms adjacentHodgeJacobianMultiplierEntry_eq_zero_of_not_mem_outer
#print axioms finiteCharacterSynthesis_eq_endpoint_sub_differences
#print axioms norm_characterPartialSum_le
#print axioms norm_finiteCharacterSynthesis_le_firstVariation
#print axioms finiteCharacterSynthesis_zeroPadded
#print axioms finiteCharacterSynthesis_zeroPaddedBackwardDifference
#print axioms finiteCharacterSynthesis_zeroPaddedSecondDifference
#print axioms norm_finiteCharacterSynthesis_le_zeroPaddedSecondVariation
#print axioms norm_finiteCharacterSynthesis_le_coefficientMass
#print axioms norm_finiteCharacterSynthesis_le_mass_min_secondVariation
#print axioms norm_finiteCharacterSynthesis_le_zeroPaddedFirstVariation

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference

/-! ## The annular attachment to the generic oriented-difference carrier

This section deliberately lives on the Navier--Stokes side of the dependency boundary.  The
generic difference calculus owns `OrientedEdge`; this analytic owner supplies the zero-padded
coefficient current attached to it.
-/

namespace Soma.Holonics.Millennium.HolonicDifferenceCalculus.AnnularHodge

open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference

/-- One zero-padded annular-coefficient difference with both endpoint values retained. -/
def backwardDifferenceEdge
    (coefficient : ℕ → ℂ) (count index : ℕ) : OrientedEdge ℂ :=
  ⟨if index = 0 then 0 else zeroPaddedCoefficient coefficient count (index - 1),
    zeroPaddedCoefficient coefficient count index⟩

/-- The analytic first backward difference is exactly the generic oriented-edge difference. -/
theorem backwardDifference_isEdgeDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedBackwardDifference coefficient count index =
      (backwardDifferenceEdge coefficient count index).difference := by
  rfl

/-- One second-difference edge is an edge in the already differentiated population. -/
def secondDifferenceEdge
    (coefficient : ℕ → ℂ) (count index : ℕ) : OrientedEdge ℂ :=
  backwardDifferenceEdge
    (zeroPaddedBackwardDifference coefficient count) (count + 1) index

/-- The annular owner's second difference is carried by the generic second edge. -/
theorem secondDifference_isEdgeDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference coefficient count index =
      (secondDifferenceEdge coefficient count index).difference := by
  rfl

/-- Two Abel passages integrate the actual second-difference edge population through the
character receiver. -/
theorem characterWeightedSecondEdges_integrate
    (coefficient : ℕ → ℂ) (z : ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 2),
        (secondDifferenceEdge coefficient count index).difference * z ^ index) =
      (1 - z) ^ 2 *
        ∑ index ∈ Finset.range count, coefficient index * z ^ index := by
  simpa only [← secondDifference_isEdgeDifference] using
    finiteCharacterSynthesis_zeroPaddedSecondDifference coefficient z count

#print axioms characterWeightedSecondEdges_integrate

end Soma.Holonics.Millennium.HolonicDifferenceCalculus.AnnularHodge
