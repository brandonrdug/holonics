import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand

/-!
# Positive finite boundary receiver for the linear phase bands

**[proved-derived; formal-checked]**  The phase-band owner already enlarges every varying native
aperture to one common depth aperture and returns the finite scale population through two
low-pass boundary faces.  This file composes that exact passage with multiplier positivity.
The complete finite population of ordinary two-copy smooth-band energies is therefore paid by
one positive boundary storage, while signed nonlinear work remains the real face of the exact
boundary work.

No depth limit, estimate for the surviving boundary work, or terminal conclusion is asserted.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Finite positive receiver -/

/-- The actual one-copy storage is the complex chart of its nonnegative real energy. -/
theorem openSmoothDyadicLinearBandCoefficientStorage_eq_realEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicLinearBandCoefficientStorage solution t scale =
      (openSmoothDyadicLinearBandRealEnergy solution t scale : ℂ) := by
  unfold openSmoothDyadicLinearBandCoefficientStorage
    smoothDyadicLinearCoefficientStorage linearMultiplierCoefficientStorage
    openSmoothDyadicLinearBandRealEnergy
    openSmoothDyadicLinearBandCoefficientMass
  rw [Complex.ofReal_mul, Complex.ofReal_sum
    (smoothDyadicBandNativeAperture scale), Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [complexVectorHermitianPairing_self_eq]
  ring

/-- The finite sum of actual one-copy energies is exactly the real boundary storage. -/
theorem sum_openSmoothDyadicLinearBandRealEnergy_eq_lowPass_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandRealEnergy solution t scale) =
      (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)).re := by
  have hcomplex :=
    sum_openSmoothDyadicLinearBandCoefficientStorage_eq_lowPass_boundary
      solution t depth
  simp_rw [openSmoothDyadicLinearBandCoefficientStorage_eq_realEnergy] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa using hreal

/-- The complete finite population of the usual two-copy smooth-band energies is paid by the
single positive one-copy low-pass boundary storage.  No depth limit is taken. -/
theorem sum_openSmoothDyadicBandRealEnergy_le_lowPass_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution t scale) ≤
      (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)).re := by
  calc
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution t scale) ≤
      ∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandRealEnergy solution t scale := by
        apply Finset.sum_le_sum
        intro scale _hscale
        exact openSmoothDyadicBandRealEnergy_le_linearRealEnergy
          solution t scale
    _ = _ :=
      sum_openSmoothDyadicLinearBandRealEnergy_eq_lowPass_boundary
        solution t depth

/-- The real finite signed-work population is the real face of the same common-aperture
low-pass boundary work. -/
theorem sum_openSmoothDyadicLinearBandActualSignedWorkRate_eq_lowPass_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandActualSignedWorkRate solution t scale) =
      (linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t)).re := by
  have hcomplex :=
    sum_openSmoothDyadicLinearBandActualSignedWork_eq_lowPass_boundary
      solution t depth
  have hreal := congrArg Complex.re hcomplex
  simpa [openSmoothDyadicLinearBandActualSignedWorkRate] using hreal

/-! ## Exact finite-depth evolution -/

/-- Compact clamping of the finite-depth low-pass boundary work. -/
def compactOpenSmoothDyadicLinearBoundarySignedWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) : ℝ :=
  let t := compactInteriorTime ha hab hbT time
  (linearMultiplierCoefficientWork
    (smoothDyadicCumulativeBoundaryMultiplier depth)
    (smoothDyadicBandNativeAperture depth)
    (openPeriodicVorticityFourierMode solution t)
    (vorticityNonlinearMode solution t)).re

/-- At every compactly clamped time, the complete finite population of actual signed-work rates
is literally the low-pass boundary work rate. -/
theorem sum_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    (∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicLinearBandActualSignedWorkRate
          solution ha hab hbT scale time) =
      compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time := by
  unfold compactOpenSmoothDyadicLinearBandActualSignedWorkRate
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
  exact sum_openSmoothDyadicLinearBandActualSignedWorkRate_eq_lowPass_boundary
    solution (compactInteriorTime ha hab hbT time) depth

/-- The finite sum of compact signed-work integrals is the integral of the single boundary work.
Thus cancellation is retained before integration and before any absolute value. -/
theorem sum_integral_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
            solution ha hab hbT scale time) =
      ∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time := by
  calc
    (∑ scale ∈ Finset.range depth,
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
            solution ha hab hbT scale time) =
      ∫ time in a..b,
        ∑ scale ∈ Finset.range depth,
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
            solution ha hab hbT scale time := by
        rw [intervalIntegral.integral_finsetSum]
        intro scale _hscale
        exact compactOpenSmoothDyadicLinearBandActualSignedWorkRate_intervalIntegrable
          solution ha hab hbT scale
    _ = _ := intervalIntegral.integral_congr fun time _htime ↦
      sum_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
        solution ha hab hbT depth time

/-- **Exact finite-depth phase balance.**  Summing the one-copy PDE law through `depth` returns
the positive low-pass boundary storage, the complete finite spectral service, and one signed
low-pass boundary work integral.  No scale limit or terminal estimate is used. -/
theorem openPeriodicSolutionOn_openSmoothDyadicLinearFiniteScale_integrated_balance
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution
          ⟨b, ha.trans_le hab, hbT⟩)).re +
        nu * ∑ scale ∈ Finset.range depth,
          ∫ time in a..b,
            compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time =
      (linearMultiplierCoefficientStorage
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution
            ⟨a, ha, hab.trans_lt hbT⟩)).re +
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time := by
  have hsum :
      (∑ scale ∈ Finset.range depth,
        (openSmoothDyadicLinearBandRealEnergy solution
            ⟨b, ha.trans_le hab, hbT⟩ scale +
          nu * ∫ time in a..b,
            compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time)) =
        ∑ scale ∈ Finset.range depth,
          (openSmoothDyadicLinearBandRealEnergy solution
              ⟨a, ha, hab.trans_lt hbT⟩ scale +
            ∫ time in a..b,
              compactOpenSmoothDyadicLinearBandActualSignedWorkRate
                solution ha hab hbT scale time) := by
    apply Finset.sum_congr rfl
    intro scale _hscale
    exact openPeriodicSolutionOn_openSmoothDyadicLinearBand_integrated_balance
      solution ha hab hbT scale
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum,
    sum_openSmoothDyadicLinearBandRealEnergy_eq_lowPass_boundary,
    sum_openSmoothDyadicLinearBandRealEnergy_eq_lowPass_boundary,
    sum_integral_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary]
    at hsum
  exact hsum

/-- The ordinary two-copy smooth-band energy population inherits the finite-depth phase balance
as a one-sided estimate.  The nonlinear contribution is still the single signed boundary work;
no per-scale absolute values have been introduced. -/
theorem sum_openSmoothDyadicBandRealEnergy_add_linearDissipation_le_boundary
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution
          ⟨b, ha.trans_le hab, hbT⟩ scale) +
        nu * ∑ scale ∈ Finset.range depth,
          ∫ time in a..b,
            compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time ≤
      (linearMultiplierCoefficientStorage
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution
            ⟨a, ha, hab.trans_lt hbT⟩)).re +
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time := by
  calc
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution
          ⟨b, ha.trans_le hab, hbT⟩ scale) +
        nu * ∑ scale ∈ Finset.range depth,
          ∫ time in a..b,
            compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time ≤
      (linearMultiplierCoefficientStorage
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution
            ⟨b, ha.trans_le hab, hbT⟩)).re +
        nu * ∑ scale ∈ Finset.range depth,
          ∫ time in a..b,
            compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time := by
        exact add_le_add_left
          (sum_openSmoothDyadicBandRealEnergy_le_lowPass_boundary
            solution ⟨b, ha.trans_le hab, hbT⟩ depth) _
    _ = _ :=
      openPeriodicSolutionOn_openSmoothDyadicLinearFiniteScale_integrated_balance
        solution ha hab hbT depth

section Audit

#print axioms sum_openSmoothDyadicLinearBandRealEnergy_eq_lowPass_boundary
#print axioms sum_openSmoothDyadicBandRealEnergy_le_lowPass_boundary
#print axioms sum_openSmoothDyadicLinearBandActualSignedWorkRate_eq_lowPass_boundary
#print axioms sum_integral_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
#print axioms openPeriodicSolutionOn_openSmoothDyadicLinearFiniteScale_integrated_balance
#print axioms sum_openSmoothDyadicBandRealEnergy_add_linearDissipation_le_boundary

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
