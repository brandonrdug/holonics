import ElementaryHolonics.Millennium.NavierStokesH2StorageDissipationPayment
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation

/-!
# Compact-time cofinal modulus payment for weighted H3 occupation

**[proved-derived; formal-checked]** The complete exchanged-face modulus population is
totalized from the strict-interior solution chart to the real clock by `compactInteriorTime`.
Under the explicit hypothesis that this real-time totalization is interval-integrable, its exact
pointwise half-population bound pays the signed coordinate `H2` nonlinear-production integral.

Feeding precisely that production budget into the standing storage--dissipation theorem returns
the weighted-`H3` square occupation estimate with no independent storage debt.  The new
interval-integrability hypothesis is retained visibly; no source payment, running service,
packing, terminal estimate, or Navier--Stokes closure claim is made.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalModulusH3Occupation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation
open Soma.Holonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

/-! ## Compact real-time totalization -/

/-- The literal cofinal exchanged-face modulus population, totalized to every real clock value by
the standing compact-interior projection. -/
def compactPhysicalH2CofinalExchangedModulusPopulation
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) : ℝ :=
  physicalH2CofinalExchangedModulusPopulation solution
    (compactInteriorTime ha hab hbT time)

/-- With the compact modulus population explicitly interval-integrable, its pointwise half bound
pays the signed coordinate nonlinear-production integral. -/
theorem integral_coordinateH2NonlinearProductionCurrent_le_half_compactCofinalModulus
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hmodulus : IntervalIntegrable
      (compactPhysicalH2CofinalExchangedModulusPopulation solution ha hab hbT)
      volume a b) :
    (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) ≤
      (1 / 2 : ℝ) *
        ∫ time in a..b,
          compactPhysicalH2CofinalExchangedModulusPopulation
            solution ha hab hbT time := by
  have hproduction : IntervalIntegrable
      (coordinateH2NonlinearProductionCurrent velocity) volume a b :=
    openPeriodicSolutionOn_coordinateH2NonlinearProductionCurrent_intervalIntegrable
      solution ha hab hbT
  have hscaled : IntervalIntegrable
      (fun time ↦ (1 / 2 : ℝ) *
        compactPhysicalH2CofinalExchangedModulusPopulation
          solution ha hab hbT time) volume a b :=
    hmodulus.const_mul (1 / 2 : ℝ)
  have hmono := intervalIntegral.integral_mono_on hab hproduction hscaled
    (fun time htime ↦ by
      have hpoint :=
        abs_coordinateH2NonlinearProductionCurrent_le_half_cofinalExchangedModulusPopulation
          solution (compactInteriorTime ha hab hbT time)
      rw [compactInteriorTime_eq ha hab hbT htime] at hpoint
      exact (le_abs_self
        (coordinateH2NonlinearProductionCurrent velocity time)).trans hpoint)
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-! ## Exact weighted-H3 occupation consequence -/

/-- The compact cofinal modulus integral is the sole new production payment supplied to the
standing no-storage-debt weighted-`H3` occupation theorem. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_compactCofinalModulus
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hmodulus : IntervalIntegrable
      (compactPhysicalH2CofinalExchangedModulusPopulation solution ha hab hbT)
      volume a b) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((b - a) * periodicKineticEnergy velocity 0 +
        (3 / 2 : ℝ) * nu⁻¹ *
          (coordinateH2Energy velocity a +
            (1 / 2 : ℝ) *
              ∫ time in a..b,
                compactPhysicalH2CofinalExchangedModulusPopulation
                  solution ha hab hbT time)) := by
  exact
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_productionBudget_without_storageDebt
      solution hnu ha hab hbT
      (integral_coordinateH2NonlinearProductionCurrent_le_half_compactCofinalModulus
        solution ha hab hbT hmodulus)

section Audit

#print axioms integral_coordinateH2NonlinearProductionCurrent_le_half_compactCofinalModulus
#print axioms integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_compactCofinalModulus

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalModulusH3Occupation
