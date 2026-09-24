import ElementaryHolonics.Millennium.NavierStokesInitialCriticalVorticityIntegrability
import ElementaryHolonics.Millennium.NavierStokesCriticalMildReceiver

/-!
# Clocked dyadic localization of the actual nonlinear vorticity service

This file exposes a source-side sufficient condition for the terminal dyadic vorticity packing.
At each final time and dyadic shell it retains the exact heat-transported restart coefficients and
the actual clocked nonlinear-source history through that same shell.  The source-time integral is
taken only after the complete finite shell population has been assembled.

The resulting extended-real spacetime service is divergence-safe.  Its finiteness is deliberately
not asserted: the final receipt records that analytic obligation and the theorem below proves only
that such a receipt pays the actual terminal-tail shell packing.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesClockedDyadicLocalizedService

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-- The clocked nonlinear-source mass crossing one actual dyadic shell at source time `tau`,
transported to the addressed final time `t`. -/
def compactClockedDyadicSourceHistoryRate
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (level : ℕ) (tau : ℝ) : ℝ :=
  finiteClockedVorticitySourceHistoryMass solution hs hst ht
    (dyadicFrequencyShell level) tau

theorem continuous_compactClockedDyadicSourceHistoryRate
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    Continuous
      (compactClockedDyadicSourceHistoryRate solution hs hst ht level) := by
  exact continuous_finiteClockedVorticitySourceHistoryMass
    solution hs hst ht (dyadicFrequencyShell level)

theorem compactClockedDyadicSourceHistoryRate_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) (tau : ℝ) :
    0 ≤ compactClockedDyadicSourceHistoryRate solution hs hst ht level tau := by
  unfold compactClockedDyadicSourceHistoryRate
    finiteClockedVorticitySourceHistoryMass
  exact Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _

/-- The exact shell-local mild service: the heat-transported restart population plus the
source-time integral of the actual nonlinear history through the same shell. -/
def compactClockedDyadicLocalizedServiceOn
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) : ℝ :=
  finiteClockedInitialVorticityCoefficientMass solution
      ⟨s, hs, hst.trans_lt ht⟩ t (dyadicFrequencyShell level) +
    ∫ tau in s..t,
      compactClockedDyadicSourceHistoryRate solution hs hst ht level tau

theorem compactClockedDyadicLocalizedServiceOn_nonneg
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    0 ≤ compactClockedDyadicLocalizedServiceOn solution hs hst ht level := by
  apply add_nonneg
  · unfold finiteClockedInitialVorticityCoefficientMass
    exact Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _
  · apply intervalIntegral.integral_nonneg hst
    intro tau _htau
    exact compactClockedDyadicSourceHistoryRate_nonneg
      solution hs hst ht level tau

/-- The actual signed spatial shell is controlled by its source-side clocked service.  This is
the exact finite-aperture mild theorem followed only by delayed-shell synthesis ≤ coefficient
mass; no terminal finiteness premise occurs. -/
theorem openPeriodicVorticityDyadicShellSpatialSup_le_clockedLocalizedService
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (level : ℕ) :
    openPeriodicVorticityDyadicShellSpatialSup solution
        ⟨t, hs.trans_le hst, ht⟩ level ≤
      compactClockedDyadicLocalizedServiceOn solution hs hst ht level := by
  calc
    openPeriodicVorticityDyadicShellSpatialSup solution
        ⟨t, hs.trans_le hst, ht⟩ level ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution
        ⟨t, hs.trans_le hst, ht⟩ level :=
      openPeriodicVorticityDyadicShellSpatialSup_le_coefficientMass
        solution ⟨t, hs.trans_le hst, ht⟩ level
    _ ≤ compactClockedDyadicLocalizedServiceOn solution hs hst ht level := by
      simpa [openPeriodicVorticityDyadicShellCoefficientMass,
        finiteOpenPeriodicVorticityCoefficientMass,
        compactClockedDyadicLocalizedServiceOn,
        compactClockedDyadicSourceHistoryRate] using
        (finiteOpenPeriodicVorticityCoefficientMass_le_clockedMildHistory
          solution hs hst ht (dyadicFrequencyShell level))

/-- Real-time totalization of one clocked dyadic localized service. -/
def compactClockedDyadicLocalizedService
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (level : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo s T then
    compactClockedDyadicLocalizedServiceOn solution hs ht.1.le ht.2 level
  else 0

@[simp]
theorem compactClockedDyadicLocalizedService_eq
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (level : ℕ) (ht : t ∈ Ioo s T) :
    compactClockedDyadicLocalizedService solution hs level t =
      compactClockedDyadicLocalizedServiceOn solution hs ht.1.le ht.2 level := by
  simp [compactClockedDyadicLocalizedService, ht]

theorem compactClockedDyadicLocalizedService_nonneg
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (level : ℕ) (t : ℝ) :
    0 ≤ compactClockedDyadicLocalizedService solution hs level t := by
  by_cases ht : t ∈ Ioo s T
  · rw [compactClockedDyadicLocalizedService_eq solution hs level ht]
    exact compactClockedDyadicLocalizedServiceOn_nonneg
      solution hs ht.1.le ht.2 level
  · simp [compactClockedDyadicLocalizedService, ht]

/-- Divergence-safe sum of every clocked dyadic service at one final time. -/
def compactClockedDyadicLocalizedServiceDensity
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (t : ℝ) : ℝ≥0∞ :=
  ∑' level : ℕ,
    ENNReal.ofReal (compactClockedDyadicLocalizedService solution hs level t)

/-- Divergence-safe scale--time packing of the actual clocked localized service. -/
def compactClockedDyadicLocalizedServicePacking
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) : ℝ≥0∞ :=
  ∫⁻ t in Ioo s T,
    compactClockedDyadicLocalizedServiceDensity solution hs t ∂volume

/-- The honest source-side analytic obligation.  This structure records measurability and finite
scale--time service; this file does not construct either field from energy or smoothness. -/
structure OpenPeriodicClockedDyadicLocalizedServiceReceipt
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) : Prop where
  serviceAEMeasurable :
    AEMeasurable (compactClockedDyadicLocalizedServiceDensity solution hs)
      (volume.restrict (Ioo s T))
  packing_lt_top :
    compactClockedDyadicLocalizedServicePacking solution hs < ∞

/-- Pointwise on the terminal tail, the actual dyadic shell density is dominated by the complete
clocked localized source service. -/
theorem openPeriodicVorticityTerminalDyadicShellDensity_le_clockedLocalizedServiceDensity
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (ht : t ∈ Ioo s T) :
    openPeriodicVorticityTerminalDyadicShellDensity solution t ≤
      compactClockedDyadicLocalizedServiceDensity solution hs t := by
  unfold openPeriodicVorticityTerminalDyadicShellDensity
    compactClockedDyadicLocalizedServiceDensity
  apply ENNReal.tsum_le_tsum
  intro level
  apply ENNReal.ofReal_le_ofReal
  rw [openPeriodicVorticityDyadicShellSpatialSupRate_eq solution level
    ⟨hs.trans ht.1, ht.2⟩]
  rw [compactClockedDyadicLocalizedService_eq solution hs level ht]
  exact openPeriodicVorticityDyadicShellSpatialSup_le_clockedLocalizedService
    solution hs ht.1.le ht.2 level

/-- A finite clocked source service pays the actual vorticity shell packing on the same terminal
tail.  This is a conditional bridge, not a finiteness theorem for the service. -/
theorem openPeriodicVorticityTailDyadicShellPacking_lt_top_of_clockedLocalizedService
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s)
    (receipt : OpenPeriodicClockedDyadicLocalizedServiceReceipt solution hs) :
    openPeriodicVorticityTailDyadicShellPacking (s := s) solution < ∞ := by
  apply lt_of_le_of_lt _ receipt.packing_lt_top
  unfold openPeriodicVorticityTailDyadicShellPacking
    compactClockedDyadicLocalizedServicePacking
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact openPeriodicVorticityTerminalDyadicShellDensity_le_clockedLocalizedServiceDensity
    solution hs ht

section Audit

#print axioms openPeriodicVorticityDyadicShellSpatialSup_le_clockedLocalizedService
#print axioms openPeriodicVorticityTerminalDyadicShellDensity_le_clockedLocalizedServiceDensity
#print axioms openPeriodicVorticityTailDyadicShellPacking_lt_top_of_clockedLocalizedService

end Audit

end Soma.Holonics.Millennium.NavierStokesClockedDyadicLocalizedService
