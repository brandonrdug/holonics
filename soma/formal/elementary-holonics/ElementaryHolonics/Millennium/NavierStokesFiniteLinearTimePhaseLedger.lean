import ElementaryHolonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger

/-!
# Finite linear work after the complete space--scale--time phase join

**[proved-derived; formal-checked]**  The finite-radius physical direction face, its literal
output-frequency fibre, and all three multiplier-crossing faces remain one signed complex
population.  Only after that population has reached one receiver do we take its real chart.

The actual finite-depth boundary work is exactly this physical phase population plus the explicit
interaction-radius tail.  The equality is then transported through the complete time integral
without inserting pointwise absolute values.  This is strictly more phase-sensitive than the
nonnegative tail majorant and is the appropriate source for a future integrated radius passage.
No scale, radius, terminal, or official-receiver limit is asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesFiniteLinearTimePhaseLedger

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## One finite-radius physical phase population -/

/-- The exact signed physical population after direction reconstruction but before any real
projection or magnitude.  The output tail is subtracted because the coefficient-side Parseval
receiver is the full direction reading minus the omitted output population. -/
def finitePairCompatiblePhysicalBoundaryPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  (∫ q : SpatialTorus,
      finiteDepthDyadicHodgeStrainReading solution t q depth) -
    (∫ q : SpatialTorus,
      finitePairCompatibleStrainOutputTail solution t depth radius q) +
    finitePairCompatibleStretchingMultiplierBoundaryWork
      solution t depth radius -
    finitePairCompatibleTransportCrossBoundaryWork
      solution t depth radius -
    finitePairCompatibleTransportMultiplierBoundaryWork
      solution t depth radius

/-- The finite pair-compatible nonlinear work is exactly the complete signed physical phase
population.  In particular, direction, output, and multiplier faces have not been replaced by
their separate magnitudes. -/
theorem finitePairCompatibleBoundaryNonlinearWork_eq_physicalBoundaryPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleBoundaryNonlinearWork solution t depth radius =
      finitePairCompatiblePhysicalBoundaryPhase solution t depth radius := by
  rw [finitePairCompatibleBoundaryNonlinearWork_eq_direction_plus_boundaries,
    finitePairCompatibleStrainFilteredStretchingWork_eq_directionIntegral_add_defect,
    finitePairCompatibleStrainDirectionIdentificationDefect_eq_neg_integral_outputTail]
  unfold finitePairCompatiblePhysicalBoundaryPhase
  abel

/-! ## Compact time chart and exact time word -/

/-- Real compact-time chart of the complete signed physical phase population. -/
def compactFinitePairCompatiblePhysicalBoundaryPhaseRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) : ℝ :=
  (finitePairCompatiblePhysicalBoundaryPhase solution
    (compactInteriorTime ha hab hbT time) depth radius).re

/-- **Exact phase-first radius decomposition.**  At every compactly charted time, the actual
finite-depth boundary work is the complete finite physical phase plus the literal radius tail. -/
theorem compactLinearBoundaryWork_eq_physicalBoundaryPhase_add_radiusTail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) :
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time =
      compactFinitePairCompatiblePhysicalBoundaryPhaseRate
          solution ha hab hbT depth radius time +
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time := by
  rw [compactLinearBoundaryWork_eq_finiteRadius_add_tail
    solution ha hab hbT depth radius time]
  unfold compactFinitePairCompatibleBoundaryNonlinearWorkRate
    compactFinitePairCompatiblePhysicalBoundaryPhaseRate
  rw [finitePairCompatibleBoundaryNonlinearWork_eq_physicalBoundaryPhase
    solution (compactInteriorTime ha hab hbT time) depth radius]

/-- The complete interval word preserves the same identity.  No magnitude is inserted before
space, scale, physical-face, radius, and time composition have all occurred. -/
theorem integral_compactLinearBoundaryWork_eq_integral_physicalPhase_add_radiusTail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    (∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time) =
      ∫ time in a..b,
        (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
            solution ha hab hbT depth radius time +
          compactFiniteLinearInteractionRadiusTailRate
            solution ha hab hbT depth radius time) := by
  apply intervalIntegral.integral_congr
  intro time _htime
  exact compactLinearBoundaryWork_eq_physicalBoundaryPhase_add_radiusTail
    solution ha hab hbT depth radius time

/-- Extended norm may consequently be applied after the complete phase-sensitive time word. -/
theorem enorm_integral_compactLinearBoundaryWork_eq_physicalPhase_add_radiusTail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    ‖∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ₑ =
      ‖∫ time in a..b,
        (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
            solution ha hab hbT depth radius time +
          compactFiniteLinearInteractionRadiusTailRate
            solution ha hab hbT depth radius time)‖ₑ := by
  rw [integral_compactLinearBoundaryWork_eq_integral_physicalPhase_add_radiusTail]

/-- **Phase-sensitive clock closure.**  The positive parabolic-clock excess above the fixed
earlier-slice storage is bounded by one extended norm taken only after direction, output,
multiplier, radius, and time faces have all interacted.  Unlike the nonnegative tail ledger, this
statement does not replace any of those signed faces by a pointwise magnitude. -/
theorem ofReal_clockedPrefixExcess_le_enorm_integral_physicalPhase_add_radiusTail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth radius : ℕ) :
    ENNReal.ofReal
        (nu * (∫ time in a..b,
            compactOpenSmoothDyadicPrefixClockedCoefficientMass
              solution ha hab hbT depth time) -
          (1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2) ≤
      ‖∫ time in a..b,
        (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
            solution ha hab hbT depth radius time +
          compactFiniteLinearInteractionRadiusTailRate
            solution ha hab hbT depth radius time)‖ₑ := by
  let work : ℝ := ∫ time in a..b,
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
      solution ha hab hbT depth time
  have hclock :=
    openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  have hexcess :
      nu * (∫ time in a..b,
          compactOpenSmoothDyadicPrefixClockedCoefficientMass
            solution ha hab hbT depth time) -
        (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 ≤ |work| := by
    exact sub_le_iff_le_add.mpr (by
      simpa only [work, add_comm] using hclock)
  calc
    ENNReal.ofReal
        (nu * (∫ time in a..b,
            compactOpenSmoothDyadicPrefixClockedCoefficientMass
              solution ha hab hbT depth time) -
          (1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2) ≤
      ENNReal.ofReal |work| := ENNReal.ofReal_le_ofReal hexcess
    _ = ‖work‖ₑ := (Real.enorm_eq_ofReal_abs work).symm
    _ = ‖∫ time in a..b,
        (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
            solution ha hab hbT depth radius time +
          compactFiniteLinearInteractionRadiusTailRate
            solution ha hab hbT depth radius time)‖ₑ := by
      dsimp [work]
      exact enorm_integral_compactLinearBoundaryWork_eq_physicalPhase_add_radiusTail
        solution ha hab hbT depth radius

section Audit

#print axioms finitePairCompatibleBoundaryNonlinearWork_eq_physicalBoundaryPhase
#print axioms compactLinearBoundaryWork_eq_physicalBoundaryPhase_add_radiusTail
#print axioms integral_compactLinearBoundaryWork_eq_integral_physicalPhase_add_radiusTail
#print axioms enorm_integral_compactLinearBoundaryWork_eq_physicalPhase_add_radiusTail
#print axioms ofReal_clockedPrefixExcess_le_enorm_integral_physicalPhase_add_radiusTail

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteLinearTimePhaseLedger
