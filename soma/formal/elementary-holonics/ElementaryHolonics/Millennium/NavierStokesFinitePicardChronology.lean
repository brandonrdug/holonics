import ElementaryHolonics.Millennium.NavierStokesFiniteScaleAncestry

/-!
# Finite heat-seeded Picard chronology

**[proved-derived; formal-checked]**  This owner inserts genuine source time between the finite
scale-ancestry passages.  A diagonal heat passage changes amplitudes without creating a Fourier
address.  One heat-seeded finite Galerkin Picard generation therefore advances support by at most
one dyadic level, and generation `n` of a seed below level `J` remains below level `J + n`.

The complementary initial section is never discarded.  The full chronology is reconstructed
exactly as its low-seed chronology plus a marked high-seed fibre.  The marked fibre has an exact
recurrence, and its pointwise quadratic source difference is the sum of three interactions, each
carrying the marked fibre in at least one parent slot.

All populations and time integrals in this file are finite-aperture coefficient constructions.
No convergence of the Picard chronology, fixed point, terminal estimate, or Navier--Stokes
regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesFinitePicardChronology

open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Diagonal heat and finite projected quadratic passages -/

/-- The exact diagonal heat passage on a complete coefficient population. -/
def diagonalHeatModeTransport
    (nu elapsed : ℝ) (field : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  fun frequency ↦
    (heatStokesMultiplier nu elapsed frequency : ℂ) • field frequency

/-- Diagonal heat transport creates no new Fourier address. -/
theorem diagonalHeatModeTransport_supported
    (nu elapsed : ℝ) {radius : ℕ}
    {field : ComplexFourierModePopulation}
    (hsupport : SupportedInFrequencyCube radius field) :
    SupportedInFrequencyCube radius
      (diagonalHeatModeTransport nu elapsed field) := by
  exact supportedInFrequencyCube_smul radius
    (fun frequency ↦ (heatStokesMultiplier nu elapsed frequency : ℂ)) hsupport

/-- Pointwise subtraction preserves a common addressed support. -/
theorem supportedInFrequencyCube_sub
    (radius : ℕ) {left right : ComplexFourierModePopulation}
    (hleft : SupportedInFrequencyCube radius left)
    (hright : SupportedInFrequencyCube radius right) :
    SupportedInFrequencyCube radius
      (fun frequency ↦ left frequency - right frequency) := by
  intro frequency hfrequency
  change left frequency - right frequency = 0
  rw [hleft frequency hfrequency, hright frequency hfrequency, sub_self]

/-- Integrating a time-indexed family with a common support creates no new address. -/
theorem supportedInFrequencyCube_intervalIntegral
    (radius : ℕ) (source : ℝ → ComplexFourierModePopulation)
    (lower upper : ℝ)
    (hsupport : ∀ time, SupportedInFrequencyCube radius (source time)) :
    SupportedInFrequencyCube radius
      (fun frequency ↦ ∫ time in lower..upper, source time frequency) := by
  intro frequency hfrequency
  simp_rw [hsupport _ frequency hfrequency]
  simp

/-- The finite advective coefficient followed by its exact pressure-eliminating receiver. -/
def finiteProjectedAdvectiveCoefficient
    (aperture : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  fun output ↦
    lerayProjectMode output
      (finiteAdvectiveCoefficient aperture advecting transported output)

/-- The modewise Leray receiver creates no address beyond the finite quadratic source. -/
theorem finiteProjectedAdvectiveCoefficient_supportedInFrequencyCube_add
    (aperture : Finset SpatialFrequency)
    {advecting transported : ComplexFourierModePopulation}
    {leftRadius rightRadius : ℕ}
    (hadvecting : SupportedInFrequencyCube leftRadius advecting)
    (htransported : SupportedInFrequencyCube rightRadius transported) :
    SupportedInFrequencyCube (leftRadius + rightRadius)
      (finiteProjectedAdvectiveCoefficient aperture advecting transported) := by
  intro output houtput
  have hraw := finiteAdvectiveCoefficient_supportedInFrequencyCube_add
    aperture hadvecting htransported output houtput
  change lerayProjectMode output
    (finiteAdvectiveCoefficient aperture advecting transported output) = 0
  rw [hraw]
  by_cases hzero : output = 0
  · subst output
    simp
  · rw [lerayProjectMode, if_neg hzero]
    simp [complexDot]

/-- One finite projected interaction transported from its source time to its target time. -/
def finiteHeatTransportedProjectedInteraction
    (nu targetTime sourceTime : ℝ)
    (aperture : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  diagonalHeatModeTransport nu (targetTime - sourceTime)
    (finiteProjectedAdvectiveCoefficient aperture advecting transported)

/-- Heat transport preserves the exact sum-radius support of the projected interaction. -/
theorem finiteHeatTransportedProjectedInteraction_supportedInFrequencyCube_add
    (nu targetTime sourceTime : ℝ)
    (aperture : Finset SpatialFrequency)
    {advecting transported : ComplexFourierModePopulation}
    {leftRadius rightRadius : ℕ}
    (hadvecting : SupportedInFrequencyCube leftRadius advecting)
    (htransported : SupportedInFrequencyCube rightRadius transported) :
    SupportedInFrequencyCube (leftRadius + rightRadius)
      (finiteHeatTransportedProjectedInteraction
        nu targetTime sourceTime aperture advecting transported) := by
  apply diagonalHeatModeTransport_supported
  exact finiteProjectedAdvectiveCoefficient_supportedInFrequencyCube_add
    aperture hadvecting htransported

/-! ## The finite heat-seeded chronology -/

/-- A genuine-time finite Galerkin Picard chronology.  Generation zero is the heat-transported
restart.  Each successor re-presents that restart and subtracts the Duhamel history of the
previous generation's finite projected self-interaction. -/
def finiteHeatSeededPicardGeneration
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) :
    ℕ → ℝ → ComplexFourierModePopulation
  | 0, targetTime => diagonalHeatModeTransport nu (targetTime - restartTime) seed
  | depth + 1, targetTime => fun frequency ↦
      diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
        ∫ sourceTime in restartTime..targetTime,
          finiteHeatTransportedProjectedInteraction
            nu targetTime sourceTime aperture
              (finiteHeatSeededPicardGeneration
                nu restartTime aperture seed depth sourceTime)
              (finiteHeatSeededPicardGeneration
                nu restartTime aperture seed depth sourceTime) frequency

/-- **Clocked finite scale ancestry.**  A heat-seeded finite chronology starting below dyadic
level `baseLevel` remains below level `baseLevel + depth` after `depth` quadratic generations. -/
theorem finiteHeatSeededPicardGeneration_supported
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    {seed : ComplexFourierModePopulation} {baseLevel : ℕ}
    (hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed) :
    ∀ (depth : ℕ) (targetTime : ℝ),
      SupportedInFrequencyCube (dyadicRadius (baseLevel + depth))
        (finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth targetTime) := by
  intro depth
  induction depth with
  | zero =>
      intro targetTime
      change SupportedInFrequencyCube (dyadicRadius baseLevel)
        (diagonalHeatModeTransport nu (targetTime - restartTime) seed)
      exact diagonalHeatModeTransport_supported _ _ hseed
  | succ depth inductionHypothesis =>
      intro targetTime
      let previous : ℝ → ComplexFourierModePopulation :=
        finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth
      have hprevious : ∀ sourceTime,
          SupportedInFrequencyCube (dyadicRadius (baseLevel + depth))
            (previous sourceTime) := by
        intro sourceTime
        exact inductionHypothesis sourceTime
      have hinteraction : ∀ sourceTime,
          SupportedInFrequencyCube (dyadicRadius (baseLevel + depth + 1))
            (finiteHeatTransportedProjectedInteraction
              nu targetTime sourceTime aperture
                (previous sourceTime) (previous sourceTime)) := by
        intro sourceTime
        rw [← dyadicRadius_add_self (baseLevel + depth)]
        exact finiteHeatTransportedProjectedInteraction_supportedInFrequencyCube_add
          nu targetTime sourceTime aperture
            (hprevious sourceTime) (hprevious sourceTime)
      have hintegral :
          SupportedInFrequencyCube (dyadicRadius (baseLevel + depth + 1))
            (fun frequency ↦
              ∫ sourceTime in restartTime..targetTime,
                finiteHeatTransportedProjectedInteraction
                  nu targetTime sourceTime aperture
                    (previous sourceTime) (previous sourceTime) frequency) := by
        exact supportedInFrequencyCube_intervalIntegral
          (dyadicRadius (baseLevel + depth + 1))
          (fun sourceTime ↦
            finiteHeatTransportedProjectedInteraction
              nu targetTime sourceTime aperture
                (previous sourceTime) (previous sourceTime))
          restartTime targetTime hinteraction
      have hbaseRadius :
          dyadicRadius baseLevel ≤ dyadicRadius (baseLevel + depth + 1) := by
        unfold dyadicRadius
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hrestart :
          SupportedInFrequencyCube (dyadicRadius (baseLevel + depth + 1))
            (diagonalHeatModeTransport nu (targetTime - restartTime) seed) :=
        diagonalHeatModeTransport_supported _ _
          (supportedInFrequencyCube_mono hbaseRadius hseed)
      simpa [finiteHeatSeededPicardGeneration, previous, Nat.add_assoc] using
        supportedInFrequencyCube_sub
          (dyadicRadius (baseLevel + depth + 1)) hrestart hintegral

/-! ## Exact low/high reconstruction and the marked recurrence -/

/-- Difference between the full heat-seeded chronology and the chronology generated by the
exact low-frequency section. -/
def finiteHeatSeededPicardMarkedHighFiber
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) : ComplexFourierModePopulation :=
  fun frequency ↦
    finiteHeatSeededPicardGeneration
        nu restartTime aperture seed depth targetTime frequency -
      finiteHeatSeededPicardGeneration nu restartTime aperture
        (frequencyCubeRestriction baseRadius seed) depth targetTime frequency

/-- Exact full/low/marked-high reconstruction at every time and interaction depth. -/
theorem finiteHeatSeededPicardGeneration_eq_low_add_markedHighFiber
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) (frequency : SpatialFrequency) :
    finiteHeatSeededPicardGeneration
        nu restartTime aperture seed depth targetTime frequency =
      finiteHeatSeededPicardGeneration nu restartTime aperture
          (frequencyCubeRestriction baseRadius seed) depth targetTime frequency +
        finiteHeatSeededPicardMarkedHighFiber
          nu restartTime aperture baseRadius seed depth targetTime frequency := by
  unfold finiteHeatSeededPicardMarkedHighFiber
  abel

/-- At generation zero the marked fibre is exactly the diagonal heat transport of the retained
high-frequency restart section. -/
theorem finiteHeatSeededPicardMarkedHighFiber_zero
    (nu restartTime targetTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (frequency : SpatialFrequency) :
    finiteHeatSeededPicardMarkedHighFiber
        nu restartTime aperture baseRadius seed 0 targetTime frequency =
      diagonalHeatModeTransport nu (targetTime - restartTime)
        (frequencyCubeRemainder baseRadius seed) frequency := by
  unfold finiteHeatSeededPicardMarkedHighFiber finiteHeatSeededPicardGeneration
    diagonalHeatModeTransport frequencyCubeRemainder
  rw [smul_sub]

/-- Outside the finite causal cone of the low restart section, the full time-dependent Picard
generation is exactly its retained marked-high fibre. -/
theorem finiteHeatSeededPicardGeneration_eq_markedHighFiber_of_outside
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (baseLevel depth : ℕ)
    (targetTime : ℝ) (frequency : SpatialFrequency)
    (hfrequency :
      frequency ∉ frequencyCube (dyadicRadius (baseLevel + depth))) :
    finiteHeatSeededPicardGeneration
        nu restartTime aperture seed depth targetTime frequency =
      finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
        (dyadicRadius baseLevel) seed depth targetTime frequency := by
  have hlowSupport := finiteHeatSeededPicardGeneration_supported
    nu restartTime aperture
      (frequencyCubeRestriction_supported (dyadicRadius baseLevel) seed)
      depth targetTime
  have hlowZero := hlowSupport frequency hfrequency
  rw [finiteHeatSeededPicardGeneration_eq_low_add_markedHighFiber
    nu restartTime aperture (dyadicRadius baseLevel) seed depth targetTime frequency,
    hlowZero, zero_add]

/-! ### The marked source has a high parent in every term -/

private theorem lerayProjectMode_add
    (frequency : SpatialFrequency) (left right : ComplexVector) :
    lerayProjectMode frequency (left + right) =
      lerayProjectMode frequency left + lerayProjectMode frequency right := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    simp
  · rw [lerayProjectMode, if_neg hfrequency,
      lerayProjectMode, if_neg hfrequency,
      lerayProjectMode, if_neg hfrequency]
    ext component
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      complexDot, dotProduct_add]
    ring

private theorem finiteAdvectiveCoefficient_add_add
    (aperture : Finset SpatialFrequency)
    (leftAdvecting highAdvecting leftTransported highTransported :
      ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    finiteAdvectiveCoefficient aperture
        (fun frequency ↦ leftAdvecting frequency + highAdvecting frequency)
        (fun frequency ↦ leftTransported frequency + highTransported frequency)
        output =
      finiteAdvectiveCoefficient aperture leftAdvecting leftTransported output +
        finiteAdvectiveCoefficient aperture highAdvecting leftTransported output +
        finiteAdvectiveCoefficient aperture leftAdvecting highTransported output +
        finiteAdvectiveCoefficient aperture highAdvecting highTransported output := by
  unfold finiteAdvectiveCoefficient
  simp_rw [show ∀ parent : SpatialFrequency,
      complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          (leftAdvecting parent + highAdvecting parent)
          (leftTransported (transportedFrequencyAt output parent) +
            highTransported (transportedFrequencyAt output parent)) =
        complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (leftAdvecting parent) (leftTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (highAdvecting parent) (leftTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (leftAdvecting parent) (highTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (highAdvecting parent) (highTransported (transportedFrequencyAt output parent)) by
    intro parent
    unfold complexAdvectiveInteraction
    simp only [complexDot, dotProduct_add]
    module]
  simp only [Finset.sum_add_distrib]

/-- Expanding a projected quadratic source around its low population leaves precisely three
terms, and every term carries the marked population in at least one parent slot. -/
theorem finiteProjectedAdvectiveCoefficient_add_self_sub
    (aperture : Finset SpatialFrequency)
    (low marked : ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    finiteProjectedAdvectiveCoefficient aperture
        (fun frequency ↦ low frequency + marked frequency)
        (fun frequency ↦ low frequency + marked frequency) output -
      finiteProjectedAdvectiveCoefficient aperture low low output =
        finiteProjectedAdvectiveCoefficient aperture marked low output +
          finiteProjectedAdvectiveCoefficient aperture low marked output +
          finiteProjectedAdvectiveCoefficient aperture marked marked output := by
  unfold finiteProjectedAdvectiveCoefficient
  rw [finiteAdvectiveCoefficient_add_add, lerayProjectMode_add,
    lerayProjectMode_add, lerayProjectMode_add]
  abel

/-- At every source time, the full-minus-low quadratic source of the finite chronology is
literally the three marked interactions.  Thus no term in this returned source difference loses
its high-seed ancestry. -/
theorem finiteHeatSeededPicardQuadraticSourceDifference_eq_markedInteractions
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (sourceTime : ℝ) (output : SpatialFrequency) :
    finiteProjectedAdvectiveCoefficient aperture
        (finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth sourceTime)
        (finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth sourceTime) output -
      finiteProjectedAdvectiveCoefficient aperture
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          (frequencyCubeRestriction baseRadius seed) depth sourceTime)
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          (frequencyCubeRestriction baseRadius seed) depth sourceTime) output =
      finiteProjectedAdvectiveCoefficient aperture
          (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
            baseRadius seed depth sourceTime)
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            (frequencyCubeRestriction baseRadius seed) depth sourceTime) output +
        finiteProjectedAdvectiveCoefficient aperture
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            (frequencyCubeRestriction baseRadius seed) depth sourceTime)
          (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
            baseRadius seed depth sourceTime) output +
        finiteProjectedAdvectiveCoefficient aperture
          (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
            baseRadius seed depth sourceTime)
          (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
            baseRadius seed depth sourceTime) output := by
  let low : ComplexFourierModePopulation :=
    finiteHeatSeededPicardGeneration nu restartTime aperture
      (frequencyCubeRestriction baseRadius seed) depth sourceTime
  let marked : ComplexFourierModePopulation :=
    finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
      baseRadius seed depth sourceTime
  have hfull :
      finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth sourceTime =
        fun frequency ↦ low frequency + marked frequency := by
    funext frequency
    exact finiteHeatSeededPicardGeneration_eq_low_add_markedHighFiber
      nu restartTime aperture baseRadius seed depth sourceTime frequency
  rw [hfull]
  exact finiteProjectedAdvectiveCoefficient_add_self_sub aperture low marked output

/-- Exact marked-high recurrence.  The integral difference is retained without imposing an
integrability premise that the finite chronology has not needed for its support theorem. -/
theorem finiteHeatSeededPicardMarkedHighFiber_succ
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) (frequency : SpatialFrequency) :
    finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
        baseRadius seed (depth + 1) targetTime frequency =
      diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRemainder baseRadius seed) frequency -
        ((∫ sourceTime in restartTime..targetTime,
            finiteHeatTransportedProjectedInteraction
              nu targetTime sourceTime aperture
                (finiteHeatSeededPicardGeneration
                  nu restartTime aperture seed depth sourceTime)
                (finiteHeatSeededPicardGeneration
                  nu restartTime aperture seed depth sourceTime) frequency) -
          (∫ sourceTime in restartTime..targetTime,
            finiteHeatTransportedProjectedInteraction
              nu targetTime sourceTime aperture
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  (frequencyCubeRestriction baseRadius seed) depth sourceTime)
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  (frequencyCubeRestriction baseRadius seed) depth sourceTime)
                frequency)) := by
  unfold finiteHeatSeededPicardMarkedHighFiber
  rw [finiteHeatSeededPicardGeneration, finiteHeatSeededPicardGeneration]
  have hheat :
      diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
          diagonalHeatModeTransport nu (targetTime - restartTime)
            (frequencyCubeRestriction baseRadius seed) frequency =
        diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRemainder baseRadius seed) frequency := by
    unfold diagonalHeatModeTransport frequencyCubeRemainder
    rw [smul_sub]
  let fullHistory : ComplexVector :=
    ∫ sourceTime in restartTime..targetTime,
      finiteHeatTransportedProjectedInteraction
        nu targetTime sourceTime aperture
          (finiteHeatSeededPicardGeneration
            nu restartTime aperture seed depth sourceTime)
          (finiteHeatSeededPicardGeneration
            nu restartTime aperture seed depth sourceTime) frequency
  let lowHistory : ComplexVector :=
    ∫ sourceTime in restartTime..targetTime,
      finiteHeatTransportedProjectedInteraction
        nu targetTime sourceTime aperture
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            (frequencyCubeRestriction baseRadius seed) depth sourceTime)
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            (frequencyCubeRestriction baseRadius seed) depth sourceTime)
          frequency
  change
    (diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
        fullHistory) -
      (diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRestriction baseRadius seed) frequency - lowHistory) =
    diagonalHeatModeTransport nu (targetTime - restartTime)
        (frequencyCubeRemainder baseRadius seed) frequency -
      (fullHistory - lowHistory)
  rw [show
    (diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
        fullHistory) -
      (diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRestriction baseRadius seed) frequency - lowHistory) =
      (diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
        diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRestriction baseRadius seed) frequency) -
        (fullHistory - lowHistory) by abel,
    hheat]

section Audit

#print axioms diagonalHeatModeTransport_supported
#print axioms supportedInFrequencyCube_intervalIntegral
#print axioms finiteHeatSeededPicardGeneration_supported
#print axioms finiteHeatSeededPicardGeneration_eq_markedHighFiber_of_outside
#print axioms finiteProjectedAdvectiveCoefficient_add_self_sub
#print axioms finiteHeatSeededPicardQuadraticSourceDifference_eq_markedInteractions
#print axioms finiteHeatSeededPicardMarkedHighFiber_succ

end Audit

end Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
