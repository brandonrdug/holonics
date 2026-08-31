import ElementaryHolonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearTimePhaseLedger
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage

/-!
# Clock-weighted spatial packing through the complete physical phase

**[proved-derived; formal-checked]** The parabolic scale clock controls the square of the
`2⁻ʲ`-weighted spatial packing.  This owner transports that estimate through the exact
finite-radius physical decomposition before taking an absolute-value receiver: direction,
output tail, multiplier crossings, interaction-radius tail, and the complete time interval have
already composed when the magnitude is formed.

The resulting theorem is uniform in the finite scale depth and valid at every finite interaction
radius.  It does not control the unweighted terminal packing.  That missing half derivative is
retained by `openSmoothDyadicClockWeightedTerminalReconstructionFiber`; the radius tail below is
the separate finite-interaction reconstruction fibre.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesClockWeightedPhysicalPhaseLedger

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesFiniteLinearTimePhaseLedger
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-- **Phase-first clock-weighted packing.** The clock-weighted spatial prefix is paid by the
earlier vorticity storage and one absolute value applied only after the complete signed physical
phase and its literal interaction-radius tail have traversed the time interval. -/
theorem openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_physicalPhase
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth radius : ℕ) :
    nu * (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix
        solution ha hab hbT depth time ^ 2) ≤
      1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
              solution ha hab hbT depth radius time +
            compactFiniteLinearInteractionRadiusTailRate
              solution ha hab hbT depth radius time)|) := by
  have hpacking :=
    openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  rw [integral_compactLinearBoundaryWork_eq_integral_physicalPhase_add_radiusTail
    solution ha hab hbT depth radius] at hpacking
  exact hpacking

/-- The same inequality with the finite-radius phase word named as one returned ledger. -/
def compactClockWeightedPhysicalPhaseLedger
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
      openPeriodicFullVorticityCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
    |∫ time in a..b,
      (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
          solution ha hab hbT depth radius time +
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time)|

theorem openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_namedPhysicalLedger
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth radius : ℕ) :
    nu * (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix
        solution ha hab hbT depth time ^ 2) ≤
      1024 * compactClockWeightedPhysicalPhaseLedger
        solution ha hab hbT depth radius := by
  exact openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_physicalPhase
    solution ha hab hbT hnu depth radius

/-! ## The genuine compact interaction-radius passage -/

/-- At fixed depth and radius, the complete physical phase rate is continuous on the compact
time chart.  This is inherited from the finite nonlinear work, not introduced as an integration
premise. -/
theorem continuous_compactFinitePairCompatiblePhysicalBoundaryPhaseRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    Continuous (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
      solution ha hab hbT depth radius) := by
  have hfinite : Continuous
      (compactFinitePairCompatibleBoundaryNonlinearWorkRate
        solution ha hab hbT depth radius) := by
    unfold compactFinitePairCompatibleBoundaryNonlinearWorkRate
    exact Complex.continuous_re.comp
      ((continuous_finitePairCompatibleBoundaryNonlinearWork_time
        solution depth radius).comp
          (continuous_compactInteriorTime ha hab hbT))
  apply hfinite.congr
  intro time
  unfold compactFinitePairCompatibleBoundaryNonlinearWorkRate
    compactFinitePairCompatiblePhysicalBoundaryPhaseRate
  rw [finitePairCompatibleBoundaryNonlinearWork_eq_physicalBoundaryPhase]

/-- Exact compact-time reconstruction: the finite-radius physical phase is the actual cumulative
boundary work minus its literal interaction-radius tail. -/
theorem integral_compactPhysicalBoundaryPhase_eq_boundary_sub_radiusTail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    (∫ time in a..b,
      compactFinitePairCompatiblePhysicalBoundaryPhaseRate
        solution ha hab hbT depth radius time) =
      (∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time) -
      ∫ time in a..b,
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time := by
  have hphase : IntervalIntegrable
      (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
        solution ha hab hbT depth radius) volume a b :=
    (continuous_compactFinitePairCompatiblePhysicalBoundaryPhaseRate
      solution ha hab hbT depth radius).intervalIntegrable a b
  have htail : IntervalIntegrable
      (compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius) volume a b :=
    (continuous_compactFiniteLinearInteractionRadiusTailRate
      solution ha hab hbT depth radius).intervalIntegrable a b
  have hsplit :=
    integral_compactLinearBoundaryWork_eq_integral_physicalPhase_add_radiusTail
      solution ha hab hbT depth radius
  rw [intervalIntegral.integral_add hphase htail] at hsplit
  linarith

/-- **Radius-cleared phase word.** For every compact strict-interior interval and fixed depth,
the time integral of the finite physical phase converges to the actual cumulative boundary work.
The interaction radius has therefore been removed in strong `L¹` before this signed limit; no
terminal or scale-depth passage is hidden here. -/
theorem tendsto_integral_compactPhysicalBoundaryPhase_atTop
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Filter.Tendsto
      (fun radius : ℕ ↦ ∫ time in a..b,
        compactFinitePairCompatiblePhysicalBoundaryPhaseRate
          solution ha hab hbT depth radius time)
      Filter.atTop
      (nhds (∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time)) := by
  have htail :=
    tendsto_integral_compactFiniteLinearInteractionRadiusTailRate_zero
      solution ha hab hbT depth
  have hconstant : Filter.Tendsto
      (fun _radius : ℕ ↦ ∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time)
      Filter.atTop
      (nhds (∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time)) := tendsto_const_nhds
  have hsub := hconstant.sub htail
  simpa only [integral_compactPhysicalBoundaryPhase_eq_boundary_sub_radiusTail, sub_zero]
    using hsub

/-- The preceding passage is strong at the phase-word level: the `L¹` distance between the
finite physical phase and the actual cumulative boundary-work rate tends to zero. -/
theorem tendsto_integral_abs_compactPhysicalPhase_sub_boundary_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Filter.Tendsto
      (fun radius : ℕ ↦ ∫ time in a..b,
        |compactFinitePairCompatiblePhysicalBoundaryPhaseRate
            solution ha hab hbT depth radius time -
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|)
      Filter.atTop (nhds 0) := by
  have htail :=
    tendsto_integral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
      solution ha hab hbT depth
  have heq : (fun radius : ℕ ↦ ∫ time in a..b,
      |compactFinitePairCompatiblePhysicalBoundaryPhaseRate
          solution ha hab hbT depth radius time -
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time|) =
      (fun radius : ℕ ↦ ∫ time in a..b,
        |compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time|) := by
    funext radius
    apply intervalIntegral.integral_congr
    intro time _htime
    change
      |compactFinitePairCompatiblePhysicalBoundaryPhaseRate
          solution ha hab hbT depth radius time -
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time| =
      |compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time|
    rw [compactLinearBoundaryWork_eq_physicalBoundaryPhase_add_radiusTail
      solution ha hab hbT depth radius time]
    have halgebra :
        compactFinitePairCompatiblePhysicalBoundaryPhaseRate
              solution ha hab hbT depth radius time -
            (compactFinitePairCompatiblePhysicalBoundaryPhaseRate
                solution ha hab hbT depth radius time +
              compactFiniteLinearInteractionRadiusTailRate
                solution ha hab hbT depth radius time) =
          -compactFiniteLinearInteractionRadiusTailRate
              solution ha hab hbT depth radius time := by ring
    rw [halgebra, abs_neg]
  rw [heq]
  exact htail

section Audit

#print axioms openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_physicalPhase
#print axioms openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_namedPhysicalLedger
#print axioms integral_compactPhysicalBoundaryPhase_eq_boundary_sub_radiusTail
#print axioms tendsto_integral_compactPhysicalBoundaryPhase_atTop
#print axioms tendsto_integral_abs_compactPhysicalPhase_sub_boundary_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesClockWeightedPhysicalPhaseLedger
