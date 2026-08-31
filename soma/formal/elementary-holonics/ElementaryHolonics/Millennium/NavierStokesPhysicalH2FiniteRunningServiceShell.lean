import ElementaryHolonics.Millennium.NavierStokesPhysicalH2TriadModulusPayment
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization

/-!
# Finite deterministic running service for physical H2 triads

**[proved-derived; formal-checked]**  This module sums the exact one-address modulus payment over
the finite common-cube population `physicalH2VelocityTriadAperture radius`.  Its two finite
receivers are:

* exchanged-modulus demand, the sum of each positive triad clock times the compact-time modulus
  integral of its completed exchanged face; and
* running service, the sum of each initial face modulus and compact-time modulus integral of its
  actual three-leg projected nonlinear source.

The unique zero-clock address remains in the aperture.  Its face and source insertion vanish by
the existing exact zero-address radical theorems, while every nonzero address is paid by the
one-address Kato theorem.  No address is deleted or divided by its clock.

The successor shell is the literal finite-set difference between consecutive apertures.  The
running-service recurrence is consequently an exact disjoint finite-population decomposition,
not a probabilistic or asymptotic service model.  This module makes no cofinal-summability,
packing, effective-diffusivity, terminal-control, continuation, or solution claim.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2FiniteRunningServiceShell

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesPhysicalH2TriadModulusPayment
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Addresswise demand and service -/

/-- The compact-time exchanged-modulus demand carried by one complete transport address. -/
def physicalH2ExchangedModulusDemandAt
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (_solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (_hsource : 0 < sourceTime) (_htimes : sourceTime ≤ targetTime)
    (_htarget : targetTime < T) (address : CompleteTransportAddress) : ℝ :=
  physicalH2TriadStokesClock nu address *
    ∫ time in sourceTime..targetTime,
      ‖physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency time) address‖

/-- The initial-boundary plus actual-source running service carried by one address. -/
def physicalH2RunningServiceAt
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) : ℝ :=
  ‖physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency sourceTime) address‖ +
    ∫ time in sourceTime..targetTime,
      ‖compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address time‖

/-- Every address is paid.  At `(0, 0)` this follows from the exact multiplier radical; away from
that fibre it is the positive-clock one-address modulus payment. -/
theorem physicalH2ExchangedModulusDemandAt_le_runningServiceAt
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (address : CompleteTransportAddress) :
    physicalH2ExchangedModulusDemandAt
        solution hsource htimes htarget address ≤
      physicalH2RunningServiceAt
        solution hsource htimes htarget address := by
  by_cases haddress : address = (0, 0)
  · subst address
    simp [physicalH2ExchangedModulusDemandAt, physicalH2RunningServiceAt,
      physicalH2TriadStokesClock, completeTransportReceiver]
  · exact
      openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_clock_mul_integral_modulus_le
        solution hnu hsource htimes htarget address haddress

/-! ## The finite aperture payment -/

/-- Total exchanged-modulus demand on the finite physical velocity-triad aperture. -/
def finitePhysicalH2ExchangedModulusDemand
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℝ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2ExchangedModulusDemandAt
      solution hsource htimes htarget address

/-- Total deterministic running service on the same finite addressed population. -/
def finitePhysicalH2RunningService
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℝ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2RunningServiceAt solution hsource htimes htarget address

/-- **Finite running-service law.**  The complete finite demand is bounded by the complete finite
service on the same addressed aperture. -/
theorem finitePhysicalH2ExchangedModulusDemand_le_runningService
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (radius : ℕ) :
    finitePhysicalH2ExchangedModulusDemand
        solution hsource htimes htarget radius ≤
      finitePhysicalH2RunningService
        solution hsource htimes htarget radius := by
  unfold finitePhysicalH2ExchangedModulusDemand finitePhysicalH2RunningService
  exact Finset.sum_le_sum fun address _haddress ↦
    physicalH2ExchangedModulusDemandAt_le_runningServiceAt
      solution hnu hsource htimes htarget address

/-! ## Exact successor-shell recurrence -/

/-- The three-pin common-cube aperture grows monotonically with its radius. -/
theorem physicalH2VelocityTriadAperture_mono :
    Monotone physicalH2VelocityTriadAperture := by
  intro inner outer hinner address haddress
  rw [mem_physicalH2VelocityTriadAperture_iff] at haddress ⊢
  exact ⟨frequencyCube_mono hinner haddress.1,
    frequencyCube_mono hinner haddress.2.1,
    frequencyCube_mono hinner haddress.2.2⟩

/-- The newly admitted address population at the next integer cube radius. -/
def physicalH2VelocityTriadSuccessorShell (radius : ℕ) :
    Finset CompleteTransportAddress :=
  physicalH2VelocityTriadAperture (radius + 1) \
    physicalH2VelocityTriadAperture radius

/-- Running service carried exactly by the successor shell. -/
def finitePhysicalH2RunningServiceSuccessorShell
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℝ :=
  ∑ address ∈ physicalH2VelocityTriadSuccessorShell radius,
    physicalH2RunningServiceAt solution hsource htimes htarget address

/-- **Exact running-service recurrence.**  Increasing the cube radius by one adjoins precisely the
successor shell and no other address occurrence. -/
theorem finitePhysicalH2RunningService_succ_eq_add_successorShell
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) :
    finitePhysicalH2RunningService
        solution hsource htimes htarget (radius + 1) =
      finitePhysicalH2RunningService
          solution hsource htimes htarget radius +
        finitePhysicalH2RunningServiceSuccessorShell
          solution hsource htimes htarget radius := by
  let service : CompleteTransportAddress → ℝ :=
    physicalH2RunningServiceAt solution hsource htimes htarget
  have hsubset :
      physicalH2VelocityTriadAperture radius ⊆
        physicalH2VelocityTriadAperture (radius + 1) :=
    physicalH2VelocityTriadAperture_mono (Nat.le_succ radius)
  have hsplit := Finset.sum_sdiff (f := service) hsubset
  unfold finitePhysicalH2RunningService
    finitePhysicalH2RunningServiceSuccessorShell
    physicalH2VelocityTriadSuccessorShell
  simpa only [service, add_comm] using hsplit.symm

section Audit

#print axioms physicalH2ExchangedModulusDemandAt_le_runningServiceAt
#print axioms finitePhysicalH2ExchangedModulusDemand_le_runningService
#print axioms physicalH2VelocityTriadAperture_mono
#print axioms finitePhysicalH2RunningService_succ_eq_add_successorShell

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2FiniteRunningServiceShell
