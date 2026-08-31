import ElementaryHolonics.Millennium.NavierStokesDyadicSpectralClockService
import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity

/-!
# Projected dyadic vorticity evolution and dissipative shell service

**[proved-derived; formal-checked]**  The actual strict-interior vorticity-mode ODE is passed
through one direct dyadic Hodge multiplier.  A finite advecting aperture then gives the exact
localized transport identity

`finite projected source = - finite transport of the projected vorticity
                           + (-commutator + stretching)`.

The difference between the actual projected nonlinear source and that finite population is
retained as one explicit cofinal reconstruction residual.  Thus the projected actual mode evolves
by viscosity, finite transported-shell flux, and precisely that residual; no infinite convolution
is identified with a finite aperture.

On each sharp dyadic shell, the spectral clock also yields an unconditional finite-shell
dissipative service inequality.  The remaining analytic problem is to control the signed flux and
cofinal residual uniformly and summably over scale and terminal time.  This file asserts no such
estimate and no terminal control.
-/

noncomputable section

open Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## Exact finite-aperture localization -/

/-- The actual vorticity coefficient observed through one direct dyadic Hodge multiplier. -/
def openFilteredVorticityCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) : ComplexVector :=
  (dyadicHodgeBandWeight scale k : ℂ) •
    openPeriodicVorticityFourierMode solution t k

/-- Real-time chart of the same filtered coefficient, used to state its derivative without
totalizing the open-lifespan proof. -/
def openFilteredVorticityMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (_solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) (k : SpatialFrequency) (time : ℝ) : ComplexVector :=
  (dyadicHodgeBandWeight scale k : ℂ) •
    frequencyCurlMultiplier k (velocityMode velocity k time)

theorem openFilteredVorticityMode_eq_coefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) :
    openFilteredVorticityMode solution scale k t.1 =
      openFilteredVorticityCoefficient solution t scale k := by
  unfold openFilteredVorticityMode openFilteredVorticityCoefficient
  rw [frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution t k]

/-- Finite transport of the already-filtered vorticity population.  The multiplier is attached
to the transported pin before the interaction. -/
def finiteOpenFilteredVorticityTransportCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  finiteAdvectiveCoefficient aperture
    (openPeriodicVelocityFourierMode solution t)
    (multiplierFilter (dyadicHodgeBandMultiplier scale)
      (openPeriodicVorticityFourierMode solution t)) k

/-- The finite-aperture approximation to the actual projected nonlinear vorticity source:
project after assembling `-u dot nabla omega + omega dot nabla u`. -/
def finiteOpenProjectedVorticityNonlinearCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  (dyadicHodgeBandWeight scale k : ℂ) •
    (-finiteAdvectiveCoefficient aperture
        (openPeriodicVelocityFourierMode solution t)
        (openPeriodicVorticityFourierMode solution t) k +
      finiteAdvectiveCoefficient aperture
        (openPeriodicVorticityFourierMode solution t)
        (openPeriodicVelocityFourierMode solution t) k)

/-- **Exact signed finite localization law.**  The projected truncated source is the negative
finite transport of the projected vorticity plus the corrected localized flux
`-commutator + stretching`. -/
theorem finiteOpenProjectedVorticityNonlinearCoefficient_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    finiteOpenProjectedVorticityNonlinearCoefficient
        solution t scale aperture k =
      -finiteOpenFilteredVorticityTransportCoefficient
          solution t scale aperture k +
        finiteOpenVorticityFluxCoefficient solution t scale aperture k := by
  unfold finiteOpenProjectedVorticityNonlinearCoefficient
    finiteOpenFilteredVorticityTransportCoefficient
    finiteOpenVorticityFluxCoefficient
    finiteOpenVorticityTransportCommutatorCoefficient
    finiteOpenVorticityStretchingBandCoefficient
    finiteDyadicFlowCommutatorCoefficient
    finiteMultiplierFlowCommutatorCoefficient
  change
    (dyadicHodgeBandWeight scale k : ℂ) •
        (-finiteAdvectiveCoefficient aperture
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVorticityFourierMode solution t) k +
          finiteAdvectiveCoefficient aperture
            (openPeriodicVorticityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) k) =
      -finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (multiplierFilter (dyadicHodgeBandMultiplier scale)
            (openPeriodicVorticityFourierMode solution t)) k +
        (-((dyadicHodgeBandWeight scale k : ℂ) •
            finiteAdvectiveCoefficient aperture
              (openPeriodicVelocityFourierMode solution t)
              (openPeriodicVorticityFourierMode solution t) k -
          finiteAdvectiveCoefficient aperture
            (openPeriodicVelocityFourierMode solution t)
            (multiplierFilter (dyadicHodgeBandMultiplier scale)
              (openPeriodicVorticityFourierMode solution t)) k) +
        (dyadicHodgeBandWeight scale k : ℂ) •
          finiteAdvectiveCoefficient aperture
            (openPeriodicVorticityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) k)
  simp only [smul_add, smul_neg]
  abel

/-- The complete retained fibre between the actual projected PDE source and one finite
advecting aperture.  It includes both the omitted convolution tail and the aperture-boundary
reindexing defect: a general finite `p`-aperture is not closed under `p ↦ k - p`.  Finiteness of
the aperture is therefore never confused with completeness or termwise curl symmetrization. -/
def finiteOpenProjectedVorticitySourceResidual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  (dyadicHodgeBandWeight scale k : ℂ) •
      vorticityNonlinearMode solution t k -
    finiteOpenProjectedVorticityNonlinearCoefficient
      solution t scale aperture k

theorem projectedVorticityNonlinearMode_eq_finite_add_residual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    (dyadicHodgeBandWeight scale k : ℂ) •
        vorticityNonlinearMode solution t k =
      finiteOpenProjectedVorticityNonlinearCoefficient
          solution t scale aperture k +
        finiteOpenProjectedVorticitySourceResidual
          solution t scale aperture k := by
  unfold finiteOpenProjectedVorticitySourceResidual
  abel

/-! ## Projected actual mode evolution -/

/-- Viscous return of the actual filtered vorticity coefficient. -/
def openFilteredVorticityViscousCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) : ComplexVector :=
  (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ)) •
    openFilteredVorticityCoefficient solution t scale k

/-- **Exact projected finite-aperture evolution.**  The derivative of the actual filtered
vorticity mode is viscosity minus finite transport, plus the corrected finite flux, plus the one
explicit cofinal reconstruction residual. -/
theorem openPeriodicSolutionOn_hasDerivAt_filteredVorticityMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    HasDerivAt (openFilteredVorticityMode solution scale k)
      (openFilteredVorticityViscousCoefficient solution t scale k -
        finiteOpenFilteredVorticityTransportCoefficient
          solution t scale aperture k +
        finiteOpenVorticityFluxCoefficient solution t scale aperture k +
        finiteOpenProjectedVorticitySourceResidual
          solution t scale aperture k) t.1 := by
  have hmode := openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes
    solution t k
  have hfiltered := hmode.const_smul (dyadicHodgeBandWeight scale k : ℂ)
  have hviscous :
      (dyadicHodgeBandWeight scale k : ℂ) •
          (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
            frequencyCurlMultiplier k (velocityMode velocity k t.1)) =
        openFilteredVorticityViscousCoefficient solution t scale k := by
    rw [frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
      solution t k]
    unfold openFilteredVorticityViscousCoefficient
      openFilteredVorticityCoefficient
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hvalue :
      (dyadicHodgeBandWeight scale k : ℂ) •
          ((((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
              frequencyCurlMultiplier k (velocityMode velocity k t.1)) +
            vorticityNonlinearMode solution t k) =
        openFilteredVorticityViscousCoefficient solution t scale k -
          finiteOpenFilteredVorticityTransportCoefficient
            solution t scale aperture k +
          finiteOpenVorticityFluxCoefficient solution t scale aperture k +
          finiteOpenProjectedVorticitySourceResidual
            solution t scale aperture k := by
    calc
      (dyadicHodgeBandWeight scale k : ℂ) •
          ((((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
              frequencyCurlMultiplier k (velocityMode velocity k t.1)) +
            vorticityNonlinearMode solution t k) =
        openFilteredVorticityViscousCoefficient solution t scale k +
          (dyadicHodgeBandWeight scale k : ℂ) •
            vorticityNonlinearMode solution t k := by
          rw [smul_add, hviscous]
      _ = openFilteredVorticityViscousCoefficient solution t scale k +
          (finiteOpenProjectedVorticityNonlinearCoefficient
              solution t scale aperture k +
            finiteOpenProjectedVorticitySourceResidual
              solution t scale aperture k) := by
          rw [projectedVorticityNonlinearMode_eq_finite_add_residual
            solution t scale aperture k]
      _ = openFilteredVorticityViscousCoefficient solution t scale k +
          (-finiteOpenFilteredVorticityTransportCoefficient
              solution t scale aperture k +
            finiteOpenVorticityFluxCoefficient solution t scale aperture k) +
          finiteOpenProjectedVorticitySourceResidual
            solution t scale aperture k := by
          rw [finiteOpenProjectedVorticityNonlinearCoefficient_eq
            solution t scale aperture k]
          abel
      _ = _ := by abel
  rw [← hvalue]
  change HasDerivAt
    ((dyadicHodgeBandWeight scale k : ℂ) •
      fun τ : ℝ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
    ((dyadicHodgeBandWeight scale k : ℂ) •
      ((((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
          frequencyCurlMultiplier k (velocityMode velocity k t.1)) +
        vorticityNonlinearMode solution t k)) t.1
  exact hfiltered

/-! ## Sharp-shell dissipative service -/

/-- Finite `l1` coefficient population on one sharp dyadic vorticity shell. -/
def openPeriodicVorticityDyadicShellModeMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (level : ℕ) : ℝ :=
  ∑ k ∈ dyadicFrequencyShell level,
    ‖openPeriodicVorticityFourierMode solution t k‖

/-- Actual viscous coefficient mass presented by one sharp dyadic shell. -/
def openPeriodicVorticityDyadicShellViscousServiceMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (level : ℕ) : ℝ :=
  ∑ k ∈ dyadicFrequencyShell level,
    ‖((nu * torusStokesEigenvalue k : ℝ) : ℂ) •
      openPeriodicVorticityFourierMode solution t k‖

/-- The addressed shell clock is paid by the literal finite viscous population on that shell.
This is an unconditional scale-local coercivity inequality, not a terminal estimate. -/
theorem dyadicShellClock_mul_vorticityMass_le_viscousService
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t : Ioo 0 T) (level : ℕ) :
    nu * dyadicShellClockCost level *
        openPeriodicVorticityDyadicShellModeMass solution t level ≤
      openPeriodicVorticityDyadicShellViscousServiceMass solution t level := by
  unfold openPeriodicVorticityDyadicShellModeMass
    openPeriodicVorticityDyadicShellViscousServiceMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hcost := dyadicShellClockCost_le_mode hk
  have hrate :
      nu * dyadicShellClockCost level ≤ nu * torusStokesEigenvalue k :=
    mul_le_mul_of_nonneg_left hcost hnu.le
  calc
    nu * dyadicShellClockCost level *
        ‖openPeriodicVorticityFourierMode solution t k‖ ≤
      (nu * torusStokesEigenvalue k) *
        ‖openPeriodicVorticityFourierMode solution t k‖ :=
      mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
    _ = ‖((nu * torusStokesEigenvalue k : ℝ) : ℂ) •
        openPeriodicVorticityFourierMode solution t k‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hnu.le (torusStokesEigenvalue_nonneg k))]

/-- Exact heat-clock payment for every addressed sharp-shell mode: viscous spectral rate times
its elapsed heat service is precisely the returned fraction `1 - heat`. -/
theorem viscousRate_mul_intervalIntegral_heatStokesMultiplier_eq_return
    {nu horizon : ℝ} (hnu : 0 < nu)
    {level : ℕ} {k : SpatialFrequency} (hk : k ∈ dyadicFrequencyShell level) :
    (nu * torusStokesEigenvalue k) *
        (∫ elapsed in (0 : ℝ)..horizon,
          heatStokesMultiplier nu elapsed k) =
      1 - heatStokesMultiplier nu horizon k := by
  have hk0 : k ≠ 0 := by
    intro hzero
    subst k
    have hinterior : (0 : SpatialFrequency) ∈ frequencyCube (dyadicRadius level) := by
      rw [mem_frequencyCube_iff]
      intro coordinate
      simp
    exact ((mem_dyadicFrequencyShell_iff level 0).mp hk).2 hinterior
  rw [intervalIntegral_heatStokesMultiplier_eq_boundary hnu horizon hk0]
  unfold finiteHeatBoundaryResolventScalar
  have hrate : nu * torusStokesEigenvalue k ≠ 0 :=
    (mul_pos hnu (torusStokesEigenvalue_pos hk0)).ne'
  calc
    (nu * torusStokesEigenvalue k) *
        ((1 - heatStokesMultiplier nu horizon k) *
          (nu * torusStokesEigenvalue k)⁻¹) =
      (1 - heatStokesMultiplier nu horizon k) *
        ((nu * torusStokesEigenvalue k) *
          (nu * torusStokesEigenvalue k)⁻¹) := by ring
    _ = 1 - heatStokesMultiplier nu horizon k := by
      rw [mul_inv_cancel₀ hrate, mul_one]

section Audit

#print axioms finiteOpenProjectedVorticityNonlinearCoefficient_eq
#print axioms projectedVorticityNonlinearMode_eq_finite_add_residual
#print axioms openPeriodicSolutionOn_hasDerivAt_filteredVorticityMode
#print axioms dyadicShellClock_mul_vorticityMass_le_viscousService
#print axioms viscousRate_mul_intervalIntegral_heatStokesMultiplier_eq_return

end Audit

end Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
