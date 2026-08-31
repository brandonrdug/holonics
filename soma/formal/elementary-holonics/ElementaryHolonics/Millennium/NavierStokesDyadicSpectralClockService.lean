import ElementaryHolonics.Millennium.NavierStokesFrozenSharpSourceBoundary
import ElementaryHolonics.Millennium.NavierStokesHighFrequencyHeatDecay

/-!
# Dyadic spectral-clock service for periodic Navier--Stokes

**[proved-derived; formal-checked]**  A dyadic shell is outside its inner frequency cube, so
every one of its modes has spectral cost at least that of one addressed boundary generator.
The exact heat-clock orbit of each nonzero shell mode has a finite elapsed-time service budget;
spectral order rebases that budget to the common shell address.  The shell clock grows at least
as `4^level`, hence its service budget decays at least as the reciprocal parabolic scale.

The public statements use the existing spectral-cost and heat-clock constraint objects.  The
conventional unit-torus realization remains behind those objects.  These results pay the clock
side of a localized Duhamel estimate; they do not bound the nonlinear flux current presented to
that clock.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## One addressed parabolic clock per shell -/

/-- The distinguished boundary-generator address for a dyadic shell.  Any coordinate would
have the same spectrum; coordinate zero fixes one reusable receiver chart. -/
def dyadicShellBoundaryFrequency (level : ℕ) : SpatialFrequency :=
  exteriorBoundaryFrequency (dyadicRadius level) 0

/-- The spectral cost carried by the addressed boundary generator of one shell. -/
def dyadicShellClockCost (level : ℕ) : ℝ :=
  torusStokesEigenvalue (dyadicShellBoundaryFrequency level)

/-- Exact reciprocal service budget of the shell clock at viscosity `nu`. -/
def dyadicShellClockBudget (nu : ℝ) (level : ℕ) : ℝ :=
  (nu * dyadicShellClockCost level)⁻¹

/-- Coarser parabolic receiver of the shell budget, exposing only the `4^level` scale. -/
def dyadicParabolicClockBudget (nu : ℝ) (level : ℕ) : ℝ :=
  (nu * (4 : ℝ) ^ level)⁻¹

theorem dyadicShellBoundaryFrequency_ne_zero (level : ℕ) :
    dyadicShellBoundaryFrequency level ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun k : SpatialFrequency ↦ k 0) hzero
  simp [dyadicShellBoundaryFrequency, exteriorBoundaryFrequency] at hcoordinate
  omega

theorem dyadicShellClockCost_pos (level : ℕ) :
    0 < dyadicShellClockCost level := by
  exact torusStokesEigenvalue_pos (dyadicShellBoundaryFrequency_ne_zero level)

/-- Every mode in a dyadic shell runs at least as fast spectrally as the shell's addressed
boundary clock. -/
theorem dyadicShellClockCost_le_mode
    {level : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ dyadicFrequencyShell level) :
    dyadicShellClockCost level ≤ torusStokesEigenvalue frequency := by
  have hexterior : frequency ∉ frequencyCube (dyadicRadius level) :=
    (mem_dyadicFrequencyShell_iff level frequency).mp hfrequency |>.2
  obtain ⟨axis, hspectrum⟩ :=
    exists_boundaryGenerator_spectrum_le_of_not_mem_frequencyCube
      (dyadicRadius level) hexterior
  calc
    dyadicShellClockCost level =
        torusStokesEigenvalue
          (exteriorBoundaryFrequency (dyadicRadius level) axis) := by
      unfold dyadicShellClockCost dyadicShellBoundaryFrequency torusStokesEigenvalue
      rw [frequencySquared_exteriorBoundaryFrequency,
        frequencySquared_exteriorBoundaryFrequency]
    _ ≤ torusStokesEigenvalue frequency := hspectrum

/-- The addressed shell cost dominates the square of its dyadic radius.  This is the invariant
constraint used below; no circumference coordinate appears in its statement. -/
theorem dyadicRadius_sq_le_dyadicShellClockCost (level : ℕ) :
    (dyadicRadius level : ℝ) ^ 2 ≤ dyadicShellClockCost level := by
  have hradius : 0 ≤ (dyadicRadius level : ℝ) := by positivity
  have hradiusStepLinear :
      (dyadicRadius level : ℝ) ≤ (dyadicRadius level : ℝ) + 1 := by
    linarith
  have hradiusStep :
      (dyadicRadius level : ℝ) ^ 2 ≤
        (dyadicRadius level + 1 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hradius hradiusStepLinear 2
  have hbase :
      1 ≤ torusStokesEigenvalue (exteriorBoundaryFrequency 0 0) :=
    one_le_torusStokesEigenvalue_of_ne_zero (by
      intro hzero
      have hcoordinate := congrArg (fun k : SpatialFrequency ↦ k 0) hzero
      simp [exteriorBoundaryFrequency] at hcoordinate)
  have hscaleIdentity :
      torusStokesEigenvalue
          (exteriorBoundaryFrequency (dyadicRadius level) 0) =
        (dyadicRadius level + 1 : ℝ) ^ 2 *
          torusStokesEigenvalue (exteriorBoundaryFrequency 0 0) := by
    unfold torusStokesEigenvalue
    rw [frequencySquared_exteriorBoundaryFrequency,
      frequencySquared_exteriorBoundaryFrequency]
    norm_num
    ring
  calc
    (dyadicRadius level : ℝ) ^ 2 ≤
        (dyadicRadius level + 1 : ℝ) ^ 2 := hradiusStep
    _ = (dyadicRadius level + 1 : ℝ) ^ 2 * 1 := by ring
    _ ≤ (dyadicRadius level + 1 : ℝ) ^ 2 *
        torusStokesEigenvalue (exteriorBoundaryFrequency 0 0) :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
    _ = dyadicShellClockCost level := by
      rw [← hscaleIdentity]
      rfl

/-- The dyadic shell clock has the expected parabolic `4^level` lower rate. -/
theorem four_pow_le_dyadicShellClockCost (level : ℕ) :
    (4 : ℝ) ^ level ≤ dyadicShellClockCost level := by
  calc
    (4 : ℝ) ^ level = (dyadicRadius level : ℝ) ^ 2 := by
      calc
        (4 : ℝ) ^ level = ((2 : ℝ) * 2) ^ level := by norm_num
        _ = (2 : ℝ) ^ level * (2 : ℝ) ^ level := by rw [mul_pow]
        _ = (dyadicRadius level : ℝ) ^ 2 := by
          simp [dyadicRadius, pow_two]
    _ ≤ dyadicShellClockCost level :=
      dyadicRadius_sq_le_dyadicShellClockCost level

/-! ## Exact elapsed-time service -/

/-- The exact heat orbit of any nonzero mode spends at most the reciprocal of its viscous
spectral rate over every nonnegative elapsed aperture. -/
theorem intervalIntegral_heatStokesMultiplier_le_modeClockBudget
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    {frequency : SpatialFrequency} (hfrequency : frequency ≠ 0) :
    (∫ elapsed in (0 : ℝ)..horizon,
      heatStokesMultiplier nu elapsed frequency) ≤
        (nu * torusStokesEigenvalue frequency)⁻¹ := by
  rw [intervalIntegral_heatStokesMultiplier_eq_boundary hnu horizon hfrequency]
  have hclock := heatStokesMultiplier_mem_unitInterval hnu.le hhorizon frequency
  have hrate : 0 < nu * torusStokesEigenvalue frequency :=
    mul_pos hnu (torusStokesEigenvalue_pos hfrequency)
  unfold finiteHeatBoundaryResolventScalar
  exact mul_le_of_le_one_left (inv_nonneg.mpr hrate.le) (by linarith [hclock.1])

/-- Every mode in shell `level` is served by the same addressed shell-clock budget. -/
theorem intervalIntegral_heatStokesMultiplier_le_dyadicShellClockBudget
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    {level : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ dyadicFrequencyShell level) :
    (∫ elapsed in (0 : ℝ)..horizon,
      heatStokesMultiplier nu elapsed frequency) ≤
        dyadicShellClockBudget nu level := by
  have hfrequencyNe : frequency ≠ 0 := by
    intro hzero
    subst frequency
    have hinterior : (0 : SpatialFrequency) ∈ frequencyCube (dyadicRadius level) := by
      rw [mem_frequencyCube_iff]
      intro coordinate
      simp
    exact ((mem_dyadicFrequencyShell_iff level 0).mp hfrequency).2 hinterior
  have hmode := intervalIntegral_heatStokesMultiplier_le_modeClockBudget
    hnu hhorizon hfrequencyNe
  have hcost := dyadicShellClockCost_le_mode hfrequency
  have hmodeRate : 0 < nu * torusStokesEigenvalue frequency :=
    mul_pos hnu (torusStokesEigenvalue_pos hfrequencyNe)
  have hshellRate : 0 < nu * dyadicShellClockCost level :=
    mul_pos hnu (dyadicShellClockCost_pos level)
  have hrateOrder :
      nu * dyadicShellClockCost level ≤
        nu * torusStokesEigenvalue frequency :=
    mul_le_mul_of_nonneg_left hcost hnu.le
  exact hmode.trans ((inv_le_inv₀ hmodeRate hshellRate).2 hrateOrder)

/-- Collapsing the exact shell address to its parabolic scale preserves the service bound. -/
theorem dyadicShellClockBudget_le_parabolic
    {nu : ℝ} (hnu : 0 < nu) (level : ℕ) :
    dyadicShellClockBudget nu level ≤
      dyadicParabolicClockBudget nu level := by
  have hparabolicRate : 0 < nu * (4 : ℝ) ^ level := by positivity
  have hshellRate : 0 < nu * dyadicShellClockCost level :=
    mul_pos hnu (dyadicShellClockCost_pos level)
  have hrateOrder :
      nu * (4 : ℝ) ^ level ≤ nu * dyadicShellClockCost level :=
    mul_le_mul_of_nonneg_left (four_pow_le_dyadicShellClockCost level) hnu.le
  exact (inv_le_inv₀ hshellRate hparabolicRate).2 hrateOrder

/-- Complete shell service: the elapsed heat clock of every addressed shell mode is bounded by
the reciprocal `4^level` parabolic budget. -/
theorem intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    {level : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ dyadicFrequencyShell level) :
    (∫ elapsed in (0 : ℝ)..horizon,
      heatStokesMultiplier nu elapsed frequency) ≤
        dyadicParabolicClockBudget nu level :=
  (intervalIntegral_heatStokesMultiplier_le_dyadicShellClockBudget
    hnu hhorizon hfrequency).trans
      (dyadicShellClockBudget_le_parabolic hnu level)

section Audit

#print axioms dyadicShellClockCost_le_mode
#print axioms dyadicRadius_sq_le_dyadicShellClockCost
#print axioms intervalIntegral_heatStokesMultiplier_le_modeClockBudget
#print axioms intervalIntegral_heatStokesMultiplier_le_dyadicParabolicClockBudget

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
