import ElementaryHolonics.Millennium.NavierStokesFinitePicardChronology
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite Picard marked-high Volterra mass

**[proved-derived; formal-checked]** This file attaches a concrete finite receiver mass to the
marked-high fibre of the heat-seeded finite Fourier Picard chronology.  The exact cancellation
between the full and low histories is first moved inside the time integral.  The resulting source
is retained as three distinct occurrences: marked--low, low--marked, and marked--marked.

For a forward clock and nonnegative viscosity, diagonal heat is contractive.  Consequently the
successor marked mass is paid by its high-restart mass plus the unoriented-time integral of those
three untransported projected occurrences.  The statement is uniform in the generation index and
uses no unspecified operator or Lipschitz constant.

The returned law is deliberately inhomogeneous and quadratic.  In addition, a finite output
receiver is not in general closed under the parent address `output - parent`.  Thus the homogeneous
linear recurrence required by `NavierStokesOrderedChronologyFactorial` is not yet present: a
factorial conclusion would additionally require an explicit amplitude service bound on the
successive address ancestry (and separation of the repeated restart).  No convergence, terminal
control, Galerkin limit, or Navier--Stokes regularity conclusion is asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesFinitePicardVolterraMass

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The concrete finite receiver mass -/

/-- The extended nonnegative Fourier mass seen by a declared finite receiver.  Keeping the
receiver explicit prevents a finite Galerkin aperture from being mistaken for a global Fourier
summability assertion. -/
def finiteFourierReceiverMass
    (receiver : Finset SpatialFrequency)
    (field : ComplexFourierModePopulation) : ℝ≥0∞ :=
  ∑ frequency ∈ receiver, ‖field frequency‖ₑ

theorem finiteFourierReceiverMass_nonneg
    (receiver : Finset SpatialFrequency)
    (field : ComplexFourierModePopulation) :
    0 ≤ finiteFourierReceiverMass receiver field := by
  exact bot_le

/-- A genuinely finite receiver cannot turn finite mode amplitudes into infinite extended mass. -/
theorem finiteFourierReceiverMass_ne_top
    (receiver : Finset SpatialFrequency)
    (field : ComplexFourierModePopulation) :
    finiteFourierReceiverMass receiver field ≠ ∞ := by
  unfold finiteFourierReceiverMass
  exact ENNReal.sum_ne_top.2 fun _frequency _hfrequency ↦ enorm_ne_top

/-- The concrete generation-indexed marked-high mass. -/
def finiteHeatSeededPicardMarkedHighMass
    (receiver : Finset SpatialFrequency)
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) : ℝ≥0∞ :=
  finiteFourierReceiverMass receiver
    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
      baseRadius seed depth targetTime)

theorem finiteHeatSeededPicardMarkedHighMass_nonneg
    (receiver : Finset SpatialFrequency)
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) :
    0 ≤ finiteHeatSeededPicardMarkedHighMass receiver nu restartTime aperture
      baseRadius seed depth targetTime := by
  exact bot_le

/-- The finite receiver mass of the retained high-frequency restart after diagonal heat. -/
def finiteHeatSeededPicardHighRestartMass
    (receiver : Finset SpatialFrequency)
    (nu restartTime targetTime : ℝ)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation) : ℝ≥0∞ :=
  finiteFourierReceiverMass receiver
    (diagonalHeatModeTransport nu (targetTime - restartTime)
      (frequencyCubeRemainder baseRadius seed))

/-! ## Exact marked source occurrences -/

/-- The low chronology retained separately from its marked-high reconstruction fibre. -/
def finiteHeatSeededPicardLowGeneration
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (sourceTime : ℝ) : ComplexFourierModePopulation :=
  finiteHeatSeededPicardGeneration nu restartTime aperture
    (frequencyCubeRestriction baseRadius seed) depth sourceTime

/-- The three untransported quadratic occurrences in the marked source difference at one output
address.  The low and marked amplitudes remain distinct in the public object. -/
def finiteHeatSeededPicardMarkedQuadraticModeMass
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (sourceTime : ℝ) (output : SpatialFrequency) : ℝ≥0∞ :=
  let low := finiteHeatSeededPicardLowGeneration nu restartTime aperture
    baseRadius seed depth sourceTime
  let marked := finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
    baseRadius seed depth sourceTime
  ‖finiteProjectedAdvectiveCoefficient aperture marked low output‖ₑ +
    ‖finiteProjectedAdvectiveCoefficient aperture low marked output‖ₑ +
    ‖finiteProjectedAdvectiveCoefficient aperture marked marked output‖ₑ

/-- The complete finite receiver payment of the three marked quadratic occurrences over the
forward Volterra clock.  The finite sum is outside the integral, so no exchange of a receiver sum
with a time integral is hidden. -/
def finiteHeatSeededPicardMarkedQuadraticVolterraMass
    (receiver : Finset SpatialFrequency)
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) : ℝ≥0∞ :=
  ∑ output ∈ receiver,
    ∫⁻ sourceTime in Ioc restartTime targetTime,
      finiteHeatSeededPicardMarkedQuadraticModeMass nu restartTime aperture
        baseRadius seed depth sourceTime output

/-! ## Continuity and exact cancellation inside the clock integral -/

private theorem continuous_heatStokesMultiplier_sub
    (nu targetTime : ℝ) (frequency : SpatialFrequency) :
    Continuous fun sourceTime : ℝ ↦
      heatStokesMultiplier nu (targetTime - sourceTime) frequency := by
  unfold heatStokesMultiplier
  fun_prop

private theorem continuous_diagonalHeatModeTransport_fixedTarget
    (nu targetTime : ℝ) (field : ℝ → ComplexFourierModePopulation)
    (frequency : SpatialFrequency)
    (hfield : Continuous fun sourceTime ↦ field sourceTime frequency) :
    Continuous fun sourceTime ↦
      diagonalHeatModeTransport nu (targetTime - sourceTime)
        (field sourceTime) frequency := by
  unfold diagonalHeatModeTransport
  exact (Complex.continuous_ofReal.comp
    (continuous_heatStokesMultiplier_sub nu targetTime frequency)).smul hfield

private theorem continuous_finiteProjectedAdvectiveCoefficient
    (aperture : Finset SpatialFrequency)
    (advecting transported : ℝ → ComplexFourierModePopulation)
    (output : SpatialFrequency)
    (hadvecting : ∀ frequency,
      Continuous fun time ↦ advecting time frequency)
    (htransported : ∀ frequency,
      Continuous fun time ↦ transported time frequency) :
    Continuous fun time ↦
      finiteProjectedAdvectiveCoefficient aperture
        (advecting time) (transported time) output := by
  unfold finiteProjectedAdvectiveCoefficient finiteAdvectiveCoefficient
  by_cases houtput : output = 0
  · subst output
    simp only [lerayProjectMode_zero]
    apply continuous_finsetSum
    intro parent _hparent
    unfold complexAdvectiveInteraction complexDot
    fun_prop
  · simp_rw [lerayProjectMode, if_neg houtput]
    unfold complexAdvectiveInteraction complexDot
    fun_prop

private theorem continuous_finiteHeatSeededPicardGeneration_mode
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) :
    ∀ depth frequency,
      Continuous fun targetTime ↦
        finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth targetTime frequency := by
  intro depth
  induction depth with
  | zero =>
      intro frequency
      unfold finiteHeatSeededPicardGeneration diagonalHeatModeTransport
      unfold heatStokesMultiplier
      fun_prop
  | succ depth inductionHypothesis =>
      intro frequency
      unfold finiteHeatSeededPicardGeneration
      apply Continuous.sub
      · unfold diagonalHeatModeTransport heatStokesMultiplier
        fun_prop
      · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        · unfold Function.uncurry finiteHeatTransportedProjectedInteraction
            diagonalHeatModeTransport
          change Continuous fun times : ℝ × ℝ ↦
            (heatStokesMultiplier nu (times.1 - times.2) frequency : ℂ) •
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth times.2)
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth times.2) frequency
          exact (Complex.continuous_ofReal.comp (by
            unfold heatStokesMultiplier
            fun_prop)).smul
            ((continuous_finiteProjectedAdvectiveCoefficient aperture
              (fun sourceTime ↦
                finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth sourceTime)
              (fun sourceTime ↦
                finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth sourceTime)
              frequency inductionHypothesis inductionHypothesis).comp continuous_snd)
        · exact continuous_id

private theorem intervalIntegrable_finiteHeatTransportedProjectedInteraction_mode
    (nu restartTime targetTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (output : SpatialFrequency) :
    IntervalIntegrable
      (fun sourceTime ↦
        finiteHeatTransportedProjectedInteraction nu targetTime sourceTime aperture
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            seed depth sourceTime)
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            seed depth sourceTime) output)
      volume restartTime targetTime := by
  apply Continuous.intervalIntegrable
  exact continuous_diagonalHeatModeTransport_fixedTarget nu targetTime
    (fun sourceTime ↦
      finiteProjectedAdvectiveCoefficient aperture
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth sourceTime)
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth sourceTime)) output
    (continuous_finiteProjectedAdvectiveCoefficient aperture _ _ output
      (continuous_finiteHeatSeededPicardGeneration_mode
        nu restartTime aperture seed depth)
      (continuous_finiteHeatSeededPicardGeneration_mode
        nu restartTime aperture seed depth))

/-- The exact marked recurrence with the full-minus-low cancellation moved inside the clock
integral and expanded into its three marked occurrences. -/
theorem finiteHeatSeededPicardMarkedHighFiber_succ_eq_markedIntegral
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) (targetTime : ℝ) (output : SpatialFrequency) :
    finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
        baseRadius seed (depth + 1) targetTime output =
      diagonalHeatModeTransport nu (targetTime - restartTime)
          (frequencyCubeRemainder baseRadius seed) output -
        ∫ sourceTime in restartTime..targetTime,
          diagonalHeatModeTransport nu (targetTime - sourceTime)
            (fun frequency ↦
              finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency) output := by
  rw [finiteHeatSeededPicardMarkedHighFiber_succ]
  let fullSeed := seed
  let lowSeed := frequencyCubeRestriction baseRadius seed
  have hfull := intervalIntegrable_finiteHeatTransportedProjectedInteraction_mode
    nu restartTime targetTime aperture fullSeed depth output
  have hlow := intervalIntegrable_finiteHeatTransportedProjectedInteraction_mode
    nu restartTime targetTime aperture lowSeed depth output
  rw [← intervalIntegral.integral_sub hfull hlow]
  congr 2
  funext sourceTime
  unfold finiteHeatTransportedProjectedInteraction diagonalHeatModeTransport
  rw [← smul_sub]
  rw [finiteHeatSeededPicardQuadraticSourceDifference_eq_markedInteractions]
  simp only [smul_add]
  rfl

/-! ## Heat contraction and the unconditional Volterra mass law -/

theorem enorm_diagonalHeatModeTransport_le
    {nu sourceTime targetTime : ℝ} (hnu : 0 ≤ nu)
    (htime : sourceTime ≤ targetTime)
    (field : ComplexFourierModePopulation) (frequency : SpatialFrequency) :
    ‖diagonalHeatModeTransport nu (targetTime - sourceTime) field frequency‖ₑ ≤
      ‖field frequency‖ₑ := by
  unfold diagonalHeatModeTransport
  rw [enorm_smul]
  have hmultiplier := heatStokesMultiplier_mem_unitInterval hnu
    (sub_nonneg.mpr htime) frequency
  have hnorm : ‖(heatStokesMultiplier nu (targetTime - sourceTime) frequency : ℂ)‖ₑ ≤ 1 := by
    rw [enorm_eq_nnnorm, Complex.nnnorm_real]
    have hreal :
        ‖heatStokesMultiplier nu (targetTime - sourceTime) frequency‖ ≤ (1 : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hmultiplier.1] using hmultiplier.2
    exact_mod_cast hreal
  simpa using mul_le_mul hnorm (le_refl ‖field frequency‖ₑ)

private theorem markedIntegralMode_enorm_le_lintegral
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) {targetTime : ℝ} (hnu : 0 ≤ nu)
    (htime : restartTime ≤ targetTime) (output : SpatialFrequency) :
    ‖∫ sourceTime in restartTime..targetTime,
        diagonalHeatModeTransport nu (targetTime - sourceTime)
          (fun frequency ↦
            finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency +
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency +
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency) output‖ₑ ≤
      ∫⁻ sourceTime in Ioc restartTime targetTime,
        finiteHeatSeededPicardMarkedQuadraticModeMass nu restartTime aperture
          baseRadius seed depth sourceTime output := by
  rw [intervalIntegral.integral_of_le htime]
  calc
    ‖∫ sourceTime in Ioc restartTime targetTime,
        diagonalHeatModeTransport nu (targetTime - sourceTime)
          (fun frequency ↦
            finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency +
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency +
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime)
                (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                  baseRadius seed depth sourceTime) frequency) output‖ₑ ≤
        ∫⁻ sourceTime in Ioc restartTime targetTime,
          ‖diagonalHeatModeTransport nu (targetTime - sourceTime)
            (fun frequency ↦
              finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) frequency) output‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with sourceTime hsource
      calc
          ‖diagonalHeatModeTransport nu (targetTime - sourceTime)
              (fun frequency ↦
                finiteProjectedAdvectiveCoefficient aperture
                    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                      baseRadius seed depth sourceTime)
                    (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                      baseRadius seed depth sourceTime) frequency +
                  finiteProjectedAdvectiveCoefficient aperture
                    (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                      baseRadius seed depth sourceTime)
                    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                      baseRadius seed depth sourceTime) frequency +
                  finiteProjectedAdvectiveCoefficient aperture
                    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                      baseRadius seed depth sourceTime)
                    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                      baseRadius seed depth sourceTime) frequency) output‖ₑ ≤
              ‖finiteProjectedAdvectiveCoefficient aperture
                    (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                      baseRadius seed depth sourceTime)
                    (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                      baseRadius seed depth sourceTime) output +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardLowGeneration nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) output +
                finiteProjectedAdvectiveCoefficient aperture
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime)
                  (finiteHeatSeededPicardMarkedHighFiber nu restartTime aperture
                    baseRadius seed depth sourceTime) output‖ₑ :=
            enorm_diagonalHeatModeTransport_le hnu hsource.2 _ output
          _ ≤ _ := by
            unfold finiteHeatSeededPicardMarkedQuadraticModeMass
            exact (enorm_add_le _ _).trans
              (add_le_add_left (enorm_add_le _ _) _)

/-- **Finite-aperture marked Volterra law.**  At every generation, the concrete marked-high mass
is bounded by the retained high-restart mass plus the clock integral of the three actual projected
marked interactions.  This is depth-uniform, contains no free service constant, and keeps the low
and marked amplitudes in separate parent slots. -/
theorem finiteHeatSeededPicardMarkedHighMass_succ_le
    (receiver : Finset SpatialFrequency)
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (baseRadius : ℕ) (seed : ComplexFourierModePopulation)
    (depth : ℕ) {targetTime : ℝ} (hnu : 0 ≤ nu)
    (htime : restartTime ≤ targetTime) :
    finiteHeatSeededPicardMarkedHighMass receiver nu restartTime aperture
        baseRadius seed (depth + 1) targetTime ≤
      finiteHeatSeededPicardHighRestartMass receiver nu restartTime targetTime
          baseRadius seed +
        finiteHeatSeededPicardMarkedQuadraticVolterraMass receiver nu restartTime
          aperture baseRadius seed depth targetTime := by
  unfold finiteHeatSeededPicardMarkedHighMass
    finiteHeatSeededPicardHighRestartMass
    finiteHeatSeededPicardMarkedQuadraticVolterraMass
    finiteFourierReceiverMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output houtput
  rw [finiteHeatSeededPicardMarkedHighFiber_succ_eq_markedIntegral]
  exact enorm_sub_le.trans
    (add_le_add_right
      (markedIntegralMode_enorm_le_lintegral nu restartTime aperture
        baseRadius seed depth hnu htime output) _)

section Audit

#print axioms finiteHeatSeededPicardMarkedHighFiber_succ_eq_markedIntegral
#print axioms enorm_diagonalHeatModeTransport_le
#print axioms finiteHeatSeededPicardMarkedHighMass_succ_le

end Audit

end Soma.Holonics.Millennium.NavierStokesFinitePicardVolterraMass
