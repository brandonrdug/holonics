import ElementaryHolonics.Millennium.NavierStokesHighFrequencyHeatDecay
import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity

/-!
# Exterior-mode service inequality from the actual mild transport

**[proved-derived; formal-checked]** The exact compact-interior vorticity-mode identity is
returned as a norm inequality with its complete transported nonlinear history.  For a mode outside
a finite frequency cube, one addressed escaping coordinate selects a boundary-generator mode.
The spectral-clock order then replaces every exterior heat transport by the transport of that same
boundary generator, at both the initial face and every source-time face.

No circumference constant or closed-form exponential is part of the public result.  The remaining
terminal obligation is now the time-distributed norm population of the actual nonlinear modal
source; this module neither assumes nor manufactures a bound for it.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesOpenFourierExteriorMildBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The exact scalar history majorant associated with one actual nonlinear vorticity mode. -/
def vorticityModeHistoryNorm
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) (τ : ℝ) : ℝ :=
  heatStokesMultiplier nu (t - τ) k *
    ‖compactVorticityNonlinearMode solution hs hst ht k τ‖

theorem continuous_vorticityModeHistoryNorm
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    Continuous (vorticityModeHistoryNorm solution hs hst ht k) := by
  unfold vorticityModeHistoryNorm heatStokesMultiplier
  exact (Real.continuous_exp.comp (by fun_prop)).mul
    (continuous_compactVorticityNonlinearMode solution hs hst ht k).norm

/-- **[proved-derived; formal-checked]** The actual mild identity returns a complete norm service
inequality before any spatial cutoff is chosen. -/
theorem norm_vorticityMode_le_heat_initial_add_history
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    ‖frequencyCurlMultiplier k (velocityMode velocity k t)‖ ≤
      heatStokesMultiplier nu (t - s) k *
          ‖frequencyCurlMultiplier k (velocityMode velocity k s)‖ +
        ∫ τ in s..t, vorticityModeHistoryNorm solution hs hst ht k τ := by
  rw [openPeriodicSolutionOn_vorticityMode_mild_identity solution hs hst ht k]
  calc
    ‖heatStokesMultiplier nu (t - s) k •
          frequencyCurlMultiplier k (velocityMode velocity k s) +
        ∫ τ in s..t,
          compactStokesTransportedVorticityNonlinearMode
            solution hs hst ht k τ‖ ≤
        ‖heatStokesMultiplier nu (t - s) k •
          frequencyCurlMultiplier k (velocityMode velocity k s)‖ +
        ‖∫ τ in s..t,
          compactStokesTransportedVorticityNonlinearMode
            solution hs hst ht k τ‖ := norm_add_le _ _
    _ ≤ heatStokesMultiplier nu (t - s) k *
          ‖frequencyCurlMultiplier k (velocityMode velocity k s)‖ +
        ∫ τ in s..t, vorticityModeHistoryNorm solution hs hst ht k τ := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs]
        unfold heatStokesMultiplier
        rw [abs_of_pos (Real.exp_pos _)]
      · apply intervalIntegral.norm_integral_le_of_norm_le hst
        · filter_upwards with τ
          intro _hτ
          unfold compactStokesTransportedVorticityNonlinearMode
            vorticityModeHistoryNorm
          rw [norm_smul, Real.norm_eq_abs]
          unfold heatStokesMultiplier
          rw [abs_of_pos (Real.exp_pos _)]
        · exact (continuous_vorticityModeHistoryNorm
            solution hs hst ht k).intervalIntegrable _ _

/-- The boundary-generator history norm uses one addressed escaped coordinate for every
source-time transport in the history. -/
def boundaryVorticityModeHistoryNorm
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (radius : ℕ) (axis : Fin 3) (k : SpatialFrequency) (τ : ℝ) : ℝ :=
  heatStokesMultiplier nu (t - τ) (exteriorBoundaryFrequency radius axis) *
    ‖compactVorticityNonlinearMode solution hs hst ht k τ‖

theorem continuous_boundaryVorticityModeHistoryNorm
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (radius : ℕ) (axis : Fin 3) (k : SpatialFrequency) :
    Continuous
      (boundaryVorticityModeHistoryNorm solution hs hst ht radius axis k) := by
  unfold boundaryVorticityModeHistoryNorm heatStokesMultiplier
  exact (Real.continuous_exp.comp (by fun_prop)).mul
    (continuous_compactVorticityNonlinearMode solution hs hst ht k).norm

/-- **[proved-derived; formal-checked]** Every actual exterior vorticity mode is served by one
addressed boundary-generator clock throughout its complete compact-interior nonlinear history. -/
theorem exists_boundaryGenerator_norm_vorticityMode_le
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (radius : ℕ) {k : SpatialFrequency} (hk : k ∉ frequencyCube radius) :
    ∃ axis : Fin 3,
      ‖frequencyCurlMultiplier k (velocityMode velocity k t)‖ ≤
        heatStokesMultiplier nu (t - s)
            (exteriorBoundaryFrequency radius axis) *
          ‖frequencyCurlMultiplier k (velocityMode velocity k s)‖ +
        ∫ τ in s..t,
          boundaryVorticityModeHistoryNorm
            solution hs hst ht radius axis k τ := by
  obtain ⟨axis, hspectrum⟩ :=
    exists_boundaryGenerator_spectrum_le_of_not_mem_frequencyCube radius hk
  refine ⟨axis, (norm_vorticityMode_le_heat_initial_add_history
    solution hs hst ht k).trans ?_⟩
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      ((heatSpectralClockAction nu hnu).antitone_spectrum
        (sub_nonneg.mpr hst) hspectrum)
      (norm_nonneg _)
  · apply intervalIntegral.integral_mono_on hst
    · exact (continuous_vorticityModeHistoryNorm
        solution hs hst ht k).intervalIntegrable _ _
    · exact (continuous_boundaryVorticityModeHistoryNorm
        solution hs hst ht radius axis k).intervalIntegrable _ _
    · intro τ hτ
      unfold vorticityModeHistoryNorm boundaryVorticityModeHistoryNorm
      exact mul_le_mul_of_nonneg_right
        ((heatSpectralClockAction nu hnu).antitone_spectrum
          (sub_nonneg.mpr hτ.2) hspectrum)
        (norm_nonneg _)

section Audit

#print axioms norm_vorticityMode_le_heat_initial_add_history
#print axioms exists_boundaryGenerator_norm_vorticityMode_le

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenFourierExteriorMildBound
