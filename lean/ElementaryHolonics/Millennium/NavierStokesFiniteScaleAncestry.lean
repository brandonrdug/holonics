import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation

/-!
# Finite scale ancestry for quadratic Fourier interactions

**[proved-derived; formal-checked]**  A finite Fourier population supported in one coordinate
cube cannot create an arbitrarily remote output in one quadratic interaction.  Two independently
addressed parent cubes of radii `r` and `s` reach only the cube of radius `r + s`.  Consequently a
finite quadratic Picard word seeded below dyadic level `J` reaches at most level `J + n` after
`n` interaction depths.

This is the exact spatial ancestry half of the Clocked Pantographic Swing.  It neither inserts a
time integral nor discards a high-frequency seed fibre; chronology and the marked high ancestor
remain separate constructions.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry

open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- One complete complex-vector Fourier population. -/
abbrev ComplexFourierModePopulation := SpatialFrequency → ComplexVector

/-- Exact support in an addressed coordinate-frequency cube. -/
def SupportedInFrequencyCube
    (radius : ℕ) (field : ComplexFourierModePopulation) : Prop :=
  ∀ frequency, frequency ∉ frequencyCube radius → field frequency = 0

theorem supportedInFrequencyCube_mono
    {inner outer : ℕ} (hradius : inner ≤ outer)
    {field : ComplexFourierModePopulation}
    (hsupport : SupportedInFrequencyCube inner field) :
    SupportedInFrequencyCube outer field := by
  intro frequency hfrequency
  apply hsupport frequency
  intro hinner
  exact hfrequency (frequencyCube_mono hradius hinner)

/-- Parents from differently sized cubes add inside the exact sum-radius cube. -/
theorem add_mem_frequencyCube_add
    (leftRadius rightRadius : ℕ) {left right : SpatialFrequency}
    (hleft : left ∈ frequencyCube leftRadius)
    (hright : right ∈ frequencyCube rightRadius) :
    left + right ∈ frequencyCube (leftRadius + rightRadius) := by
  rw [mem_frequencyCube_iff] at hleft hright ⊢
  intro coordinate
  have hl := hleft coordinate
  have hr := hright coordinate
  change -(((leftRadius + rightRadius : ℕ) : ℤ)) ≤
      left coordinate + right coordinate ∧
    left coordinate + right coordinate ≤
      ((leftRadius + rightRadius : ℕ) : ℤ)
  norm_num only [Nat.cast_add]
  omega

/-- A diagonal scalar transport changes amplitudes but creates no new Fourier address. -/
theorem supportedInFrequencyCube_smul
    (radius : ℕ) (multiplier : SpatialFrequency → ℂ)
    {field : ComplexFourierModePopulation}
    (hsupport : SupportedInFrequencyCube radius field) :
    SupportedInFrequencyCube radius
      (fun frequency ↦ multiplier frequency • field frequency) := by
  intro frequency hfrequency
  change multiplier frequency • field frequency = 0
  rw [hsupport frequency hfrequency, smul_zero]

/-- Pointwise addition preserves a common addressed support. -/
theorem supportedInFrequencyCube_add
    (radius : ℕ) {left right : ComplexFourierModePopulation}
    (hleft : SupportedInFrequencyCube radius left)
    (hright : SupportedInFrequencyCube radius right) :
    SupportedInFrequencyCube radius (fun frequency ↦ left frequency + right frequency) := by
  intro frequency hfrequency
  change left frequency + right frequency = 0
  rw [hleft frequency hfrequency, hright frequency hfrequency, zero_add]

/-- **Exact one-swing ancestry.**  The finite advective convolution of parents supported in
radius `r` and radius `s` is supported in radius `r + s`, independently of the finite aperture. -/
theorem finiteAdvectiveCoefficient_supportedInFrequencyCube_add
    (aperture : Finset SpatialFrequency)
    {advecting transported : ComplexFourierModePopulation}
    {leftRadius rightRadius : ℕ}
    (hadvecting : SupportedInFrequencyCube leftRadius advecting)
    (htransported : SupportedInFrequencyCube rightRadius transported) :
    SupportedInFrequencyCube (leftRadius + rightRadius)
      (finiteAdvectiveCoefficient aperture advecting transported) := by
  intro output houtput
  unfold finiteAdvectiveCoefficient
  apply Finset.sum_eq_zero
  intro parent hparent
  by_cases hleft : parent ∈ frequencyCube leftRadius
  · have hright :
        transportedFrequencyAt output parent ∉ frequencyCube rightRadius := by
      intro hright
      have hsum := add_mem_frequencyCube_add leftRadius rightRadius hleft hright
      rw [advecting_add_transportedFrequencyAt output parent] at hsum
      exact houtput hsum
    rw [htransported _ hright]
    simp [complexAdvectiveInteraction, complexDot]
  · rw [hadvecting _ hleft]
    simp [complexAdvectiveInteraction, complexDot]

/-- The sum of two equal dyadic radii is the next dyadic radius. -/
theorem dyadicRadius_add_self (level : ℕ) :
    dyadicRadius level + dyadicRadius level = dyadicRadius (level + 1) := by
  simp [dyadicRadius, pow_succ, two_mul, Nat.mul_comm]

/-- One quadratic interaction depth advances finite support by at most one dyadic level. -/
theorem finiteAdvectiveCoefficient_supportedInNextDyadicCube
    (aperture : Finset SpatialFrequency) (level : ℕ)
    {advecting transported : ComplexFourierModePopulation}
    (hadvecting : SupportedInFrequencyCube (dyadicRadius level) advecting)
    (htransported : SupportedInFrequencyCube (dyadicRadius level) transported) :
    SupportedInFrequencyCube (dyadicRadius (level + 1))
      (finiteAdvectiveCoefficient aperture advecting transported) := by
  rw [← dyadicRadius_add_self level]
  exact finiteAdvectiveCoefficient_supportedInFrequencyCube_add
    aperture hadvecting htransported

/-- A finite algebraic Picard word.  The retained seed is re-presented at each depth and the
previous word interacts quadratically through the declared finite aperture. -/
def finiteQuadraticPicardWord
    (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) : ℕ → ComplexFourierModePopulation
  | 0 => seed
  | depth + 1 => fun frequency ↦
      seed frequency +
        finiteAdvectiveCoefficient aperture
          (finiteQuadraticPicardWord aperture seed depth)
          (finiteQuadraticPicardWord aperture seed depth) frequency

/-- **Finite chain ancestry.**  A seed supported below level `baseLevel` cannot reach past
level `baseLevel + depth` in a depth-`depth` quadratic Picard word. -/
theorem finiteQuadraticPicardWord_supported
    (aperture : Finset SpatialFrequency)
    {seed : ComplexFourierModePopulation} {baseLevel : ℕ}
    (hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed) :
    ∀ depth : ℕ,
      SupportedInFrequencyCube (dyadicRadius (baseLevel + depth))
        (finiteQuadraticPicardWord aperture seed depth) := by
  intro depth
  induction depth with
  | zero =>
      change SupportedInFrequencyCube (dyadicRadius baseLevel) seed
      exact hseed
  | succ depth ih =>
      have hinteraction :
          SupportedInFrequencyCube (dyadicRadius (baseLevel + depth + 1))
            (finiteAdvectiveCoefficient aperture
              (finiteQuadraticPicardWord aperture seed depth)
              (finiteQuadraticPicardWord aperture seed depth)) := by
        exact finiteAdvectiveCoefficient_supportedInNextDyadicCube
          aperture (baseLevel + depth) ih ih
      have hbaseRadius :
          dyadicRadius baseLevel ≤ dyadicRadius (baseLevel + depth + 1) := by
        unfold dyadicRadius
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hseedOuter := supportedInFrequencyCube_mono hbaseRadius hseed
      simpa [finiteQuadraticPicardWord, Nat.add_assoc] using
        supportedInFrequencyCube_add
          (dyadicRadius (baseLevel + depth + 1)) hseedOuter hinteraction

/-! ## The retained high-frequency reconstruction fibre -/

/-- The exact low-frequency section selected by one cube receiver. -/
def frequencyCubeRestriction
    (radius : ℕ) (field : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  fun frequency ↦ if frequency ∈ frequencyCube radius then field frequency else 0

/-- The complementary high-frequency section, retained as a difference from the original
population rather than discarded. -/
def frequencyCubeRemainder
    (radius : ℕ) (field : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  fun frequency ↦ field frequency - frequencyCubeRestriction radius field frequency

theorem frequencyCubeRestriction_supported
    (radius : ℕ) (field : ComplexFourierModePopulation) :
    SupportedInFrequencyCube radius (frequencyCubeRestriction radius field) := by
  intro frequency hfrequency
  simp [frequencyCubeRestriction, hfrequency]

/-- Exact low/high reconstruction at every addressed Fourier occurrence. -/
theorem field_eq_frequencyCubeRestriction_add_remainder
    (radius : ℕ) (field : ComplexFourierModePopulation)
    (frequency : SpatialFrequency) :
    field frequency =
      frequencyCubeRestriction radius field frequency +
        frequencyCubeRemainder radius field frequency := by
  unfold frequencyCubeRemainder
  abel

/-- Difference between the full quadratic word and the word generated by the exact low section.
This is the lossless marked-fibre carrier; a later bilinear expansion may classify its individual
terms by their high seed ancestry without changing this definition. -/
def finiteQuadraticPicardMarkedHighFiber
    (aperture : Finset SpatialFrequency) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ) :
    ComplexFourierModePopulation :=
  fun frequency ↦
    finiteQuadraticPicardWord aperture seed depth frequency -
      finiteQuadraticPicardWord aperture
        (frequencyCubeRestriction baseRadius seed) depth frequency

/-- The marked fibre begins as the literal high-frequency remainder of the seed. -/
theorem finiteQuadraticPicardMarkedHighFiber_zero
    (aperture : Finset SpatialFrequency) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (frequency : SpatialFrequency) :
    finiteQuadraticPicardMarkedHighFiber aperture baseRadius seed 0 frequency =
      frequencyCubeRemainder baseRadius seed frequency := by
  simp [finiteQuadraticPicardMarkedHighFiber, finiteQuadraticPicardWord,
    frequencyCubeRemainder]

/-- Exact full/low/marked-fibre reconstruction at every interaction depth. -/
theorem finiteQuadraticPicardWord_eq_low_add_markedHighFiber
    (aperture : Finset SpatialFrequency) (baseRadius : ℕ)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (frequency : SpatialFrequency) :
    finiteQuadraticPicardWord aperture seed depth frequency =
      finiteQuadraticPicardWord aperture
          (frequencyCubeRestriction baseRadius seed) depth frequency +
        finiteQuadraticPicardMarkedHighFiber
          aperture baseRadius seed depth frequency := by
  unfold finiteQuadraticPicardMarkedHighFiber
  abel

/-- Outside the finite causal cone of the low seed, the complete quadratic word is exactly its
marked high-ancestor fibre. -/
theorem finiteQuadraticPicardWord_eq_markedHighFiber_of_outside
    (aperture : Finset SpatialFrequency) (seed : ComplexFourierModePopulation)
    (baseLevel depth : ℕ) (frequency : SpatialFrequency)
    (hfrequency :
      frequency ∉ frequencyCube (dyadicRadius (baseLevel + depth))) :
    finiteQuadraticPicardWord aperture seed depth frequency =
      finiteQuadraticPicardMarkedHighFiber aperture
        (dyadicRadius baseLevel) seed depth frequency := by
  have hlowSupport := finiteQuadraticPicardWord_supported aperture
    (frequencyCubeRestriction_supported (dyadicRadius baseLevel) seed) depth
  have hlowZero := hlowSupport frequency hfrequency
  rw [finiteQuadraticPicardWord_eq_low_add_markedHighFiber
    aperture (dyadicRadius baseLevel) seed depth frequency, hlowZero, zero_add]

section Audit

#print axioms add_mem_frequencyCube_add
#print axioms finiteAdvectiveCoefficient_supportedInFrequencyCube_add
#print axioms finiteQuadraticPicardWord_supported
#print axioms field_eq_frequencyCubeRestriction_add_remainder
#print axioms finiteQuadraticPicardWord_eq_markedHighFiber_of_outside

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
