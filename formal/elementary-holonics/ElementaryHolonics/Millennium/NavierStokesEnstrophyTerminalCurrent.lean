import ElementaryHolonics.Millennium.HolonicTerminalCurrent
import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import ElementaryHolonics.Millennium.NavierStokesVorticityThreeStrands
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact terminal enstrophy current and its surviving exterior strand

The periodic spatial transport strand cancels, but the time current does not thereby vanish.
Across an addressed time interval the exact remaining law is

`enstrophy current + viscosity * accumulated dissipation
  = accumulated vortex stretching + accumulated curl-forcing work`.

The right side is retained as the signed exterior current.  It is not replaced by an absolute
value, quartic magnitude, or scale truncation.  A terminal enstrophy trace follows exactly when
the three accumulated strand currents return terminal traces.  Thus this file identifies the
remaining source-specific local-to-global edge without claiming that periodic cancellation alone
closes it.
-/

noncomputable section

open Filter MeasureTheory Real Set
open scoped Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesEnstrophyTerminalCurrent

open Soma.Holonics.Millennium.HolonicTerminalCurrent
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

/-- [definition] The three signed scalar strands are integrable on one addressed interval.  This
is the exact assumption audit required by the fundamental theorem of calculus; no magnitude
substitution is made. -/
structure EnstrophyStrandIntervalReceipt
    (force velocity : VelocityField) (source target : ℝ) : Prop where
  dissipation : IntervalIntegrable (periodicVorticityDissipation velocity) volume source target
  stretching : IntervalIntegrable (periodicVortexStretching velocity) volume source target
  forcing : IntervalIntegrable (periodicCurlForcingWork force velocity) volume source target

/-- [definition] The signed exterior current which survives periodic transport cancellation. -/
def stretchingForcingExteriorCurrent
    (force velocity : VelocityField) (source target : ℝ) : ℝ :=
  (∫ time in source..target, periodicVortexStretching velocity time) +
    ∫ time in source..target, periodicCurlForcingWork force velocity time

/-- [proved-derived; formal-checked] The complete interval enstrophy law.  Every internal time
face is already glued into `intervalCurrent`; viscosity, stretching, and forcing remain separately
addressed on the exterior equation. -/
theorem intervalEnstrophyCurrent_add_dissipation_eq_exterior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target : ℝ} (hsource : 0 < source) (hst : source ≤ target)
    (htT : target < T)
    (receipt : EnstrophyStrandIntervalReceipt force velocity source target) :
    intervalCurrent (periodicEnstrophy velocity) source target +
        nu * (∫ time in source..target, periodicVorticityDissipation velocity time) =
      stretchingForcingExteriorCurrent force velocity source target := by
  have hrateIntegrable : IntervalIntegrable
      (periodicEnstrophyRate nu force velocity) volume source target := by
    unfold periodicEnstrophyRate
    exact ((receipt.dissipation.const_mul (-nu)).add receipt.stretching).add receipt.forcing
  let cutoff : ℝ := (target + T) / 2
  have htargetCutoff : target < cutoff := by
    dsimp [cutoff]
    linarith
  have hcutoffT : cutoff < T := by
    dsimp [cutoff]
    linarith
  have hcutoffPositive : 0 < cutoff :=
    (lt_of_lt_of_le hsource hst).trans htargetCutoff
  let closed : PeriodicSolutionOn cutoff nu initial force velocity pressure :=
    solution.toClosedInterior hcutoffPositive hcutoffT
  have hderivative : ∀ time ∈ uIcc source target,
      HasDerivAt (periodicEnstrophy velocity)
        (periodicEnstrophyRate nu force velocity time) time := by
    intro time htime
    rw [uIcc_of_le hst] at htime
    exact periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum closed
      (lt_of_lt_of_le hsource htime.1) (lt_of_le_of_lt htime.2 htargetCutoff)
  have hfundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderivative hrateIntegrable
  have hdecomposition :
      (∫ time in source..target, periodicEnstrophyRate nu force velocity time) =
        -nu * (∫ time in source..target, periodicVorticityDissipation velocity time) +
          (∫ time in source..target, periodicVortexStretching velocity time) +
            (∫ time in source..target, periodicCurlForcingWork force velocity time) := by
    simp only [periodicEnstrophyRate]
    rw [intervalIntegral.integral_add
        ((receipt.dissipation.const_mul (-nu)).add receipt.stretching) receipt.forcing,
      intervalIntegral.integral_add (receipt.dissipation.const_mul (-nu)) receipt.stretching,
      intervalIntegral.integral_const_mul]
  rw [hdecomposition] at hfundamental
  unfold intervalCurrent stretchingForcingExteriorCurrent
  linear_combination -hfundamental

/-- [definition] The periodic enstrophy receiver attached to the elementary interval boundary
holon.  Its occurrence is an addressed time pair; the underlying carrier remains the same generic
operation complex used by every receiver-valued interval current. -/
def enstrophyIntervalHolon (velocity : VelocityField) :
    Soma.Holonics.BoundaryHolon ℝ ℝ :=
  intervalBoundaryHolon (periodicEnstrophy velocity) Prod.fst Prod.snd

/-- [proved-derived; formal-checked] The Navier--Stokes constitutive law is an attachment to the
elementary boundary holon's returned current.  Viscous storage and signed exterior forcing remain
separate returned faces; the carrier itself contributes only the exact oriented endpoint
difference. -/
theorem enstrophyIntervalHolon_constitutive
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target : ℝ} (hsource : 0 < source) (hst : source ≤ target)
    (htT : target < T)
    (receipt : EnstrophyStrandIntervalReceipt force velocity source target) :
    (enstrophyIntervalHolon velocity).receive (source, target) +
        nu * (∫ time in source..target, periodicVorticityDissipation velocity time) =
      stretchingForcingExteriorCurrent force velocity source target := by
  simpa only [enstrophyIntervalHolon, intervalBoundaryHolon_receive] using
    intervalEnstrophyCurrent_add_dissipation_eq_exterior
      solution hsource hst htT receipt

/-- [definition] Accumulated viscous population from one addressed base time. -/
def accumulatedVorticityDissipation
    (velocity : VelocityField) (base time : ℝ) : ℝ :=
  ∫ s in base..time, periodicVorticityDissipation velocity s

/-- [definition] Accumulated signed vortex-stretching current from one addressed base time. -/
def accumulatedVortexStretching
    (velocity : VelocityField) (base time : ℝ) : ℝ :=
  ∫ s in base..time, periodicVortexStretching velocity s

/-- [definition] Accumulated signed curl-forcing current from one addressed base time. -/
def accumulatedCurlForcingWork
    (force velocity : VelocityField) (base time : ℝ) : ℝ :=
  ∫ s in base..time, periodicCurlForcingWork force velocity s

/-- [definition] The exact data needed to pass the three scalar enstrophy-strand receivers through
the terminal face.  The signed stretching trace is an explicit escape port; its unresolved source
fibre still contains the amplitude, orientation, and scale populations.  This receipt does not
assert that either the scalar trace or that fibre vanishes. -/
structure TerminalEnstrophyStrandReturn
    {T base nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  intervalReceipt : ∀ time ∈ Ioo base T,
    EnstrophyStrandIntervalReceipt force velocity base time
  dissipationTrace : ℝ
  stretchingTrace : ℝ
  forcingTrace : ℝ
  dissipationReturns : Tendsto (accumulatedVorticityDissipation velocity base)
    (incomingTerminalFilter T) (nhds dissipationTrace)
  stretchingReturns : Tendsto (accumulatedVortexStretching velocity base)
    (incomingTerminalFilter T) (nhds stretchingTrace)
  forcingReturns : Tendsto (accumulatedCurlForcingWork force velocity base)
    (incomingTerminalFilter T) (nhds forcingTrace)

/-- [proved-derived; formal-checked] Returned strand currents reconstruct the exact terminal
enstrophy receiver. -/
theorem terminalEnstrophyTrace_of_strandReturns
    {T base nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbase : 0 < base) (hbaseT : base < T)
    (returned : TerminalEnstrophyStrandReturn (base := base) solution) :
    Tendsto (periodicEnstrophy velocity) (incomingTerminalFilter T)
      (nhds (periodicEnstrophy velocity base - nu * returned.dissipationTrace +
        returned.stretchingTrace + returned.forcingTrace)) := by
  have hcombined : Tendsto
      (fun time ↦ periodicEnstrophy velocity base -
        nu * accumulatedVorticityDissipation velocity base time +
          accumulatedVortexStretching velocity base time +
            accumulatedCurlForcingWork force velocity base time)
      (incomingTerminalFilter T)
      (nhds (periodicEnstrophy velocity base - nu * returned.dissipationTrace +
        returned.stretchingTrace + returned.forcingTrace)) :=
    ((tendsto_const_nhds.sub
        (tendsto_const_nhds.mul returned.dissipationReturns)).add
          returned.stretchingReturns).add returned.forcingReturns
  apply hcombined.congr'
  filter_upwards [Ioo_mem_nhdsLT hbaseT] with time htime
  have hlaw := intervalEnstrophyCurrent_add_dissipation_eq_exterior
    solution hbase htime.1.le htime.2 (returned.intervalReceipt time htime)
  unfold intervalCurrent stretchingForcingExteriorCurrent at hlaw
  unfold accumulatedVorticityDissipation accumulatedVortexStretching
    accumulatedCurlForcingWork
  linarith

/-- [proved-derived; formal-checked] Consequently the enstrophy receiver lies in the terminal null
cone whenever its three actual signed strands return. -/
theorem hasNullTerminalEnstrophyCurrentAt_of_strandReturns
    {T base nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbase : 0 < base) (hbaseT : base < T)
    (returned : TerminalEnstrophyStrandReturn (base := base) solution) :
    HasNullTerminalCurrentAt T (periodicEnstrophy velocity) :=
  hasNullTerminalCurrentAt_of_tendsto
    (terminalEnstrophyTrace_of_strandReturns hbase hbaseT returned)

section Audit

#print axioms intervalEnstrophyCurrent_add_dissipation_eq_exterior
#print axioms enstrophyIntervalHolon_constitutive
#print axioms terminalEnstrophyTrace_of_strandReturns
#print axioms hasNullTerminalEnstrophyCurrentAt_of_strandReturns

end Audit

end Soma.Holonics.Millennium.NavierStokesEnstrophyTerminalCurrent
