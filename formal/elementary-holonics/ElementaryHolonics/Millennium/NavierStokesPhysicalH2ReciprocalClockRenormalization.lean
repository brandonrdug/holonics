import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
import ElementaryHolonics.Millennium.NavierStokesWeightedMildCoefficientEquation
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Reciprocal-clock renormalization of the physical-H2 triad current

This owner divides the exact clocked exchanged-triad identity by its addressed three-pin Stokes
clock before summing the finite common-cube population.  The sole clock-zero address `(0, 0)` is
kept as an occurrence and assigned reciprocal clock zero; its exchanged cubic face and all three
nonlinear source insertions are proved to vanish.  Thus no address is deleted and no zero divisor
is hidden.

The returned compact-interval identity is signed and precedes every norm or absolute-coefficient
receiver.  It expresses the time integral of the finite exchanged cubic current as the difference
of a reciprocal-clock cubic boundary current plus the integral of a reciprocal-clock quartic
source current.  It makes no terminal-control, coercivity, absorption, or continuation claim.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation

/-! ## The total reciprocal three-pin clock -/

/-- The reciprocal physical-`H2` triad clock as a total addressed receiver.  The unique
clock-zero address remains present and is sent to zero. -/
def physicalH2TriadReciprocalClock
    (nu : ℝ) (address : CompleteTransportAddress) : ℂ :=
  if address = (0, 0) then 0
  else (((physicalH2TriadStokesClock nu address : ℝ) : ℂ)⁻¹)

@[simp]
theorem physicalH2TriadReciprocalClock_zero (nu : ℝ) :
    physicalH2TriadReciprocalClock nu (0, 0) = 0 := by
  simp [physicalH2TriadReciprocalClock]

theorem physicalH2TriadReciprocalClock_eq_inv
    (nu : ℝ) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) :
    physicalH2TriadReciprocalClock nu address =
      (((physicalH2TriadStokesClock nu address : ℝ) : ℂ)⁻¹) := by
  simp [physicalH2TriadReciprocalClock, haddress]

/-- Away from the zero address, positive viscosity makes the reciprocal clock an exact inverse. -/
theorem physicalH2TriadReciprocalClock_mul_clock
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) :
    physicalH2TriadReciprocalClock nu address *
        ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) = 1 := by
  rw [physicalH2TriadReciprocalClock_eq_inv nu address haddress]
  apply inv_mul_cancel₀
  exact Complex.ofReal_ne_zero.mpr
    (physicalH2TriadStokesClock_pos_of_address_ne_zero hnu address haddress).ne'

/-! ## Exact zero-clock fibre -/

/-- The completed exchanged cubic face at the zero address lies in the exact multiplier radical. -/
@[simp]
theorem physicalH2VelocityExchangedTriadFace_zero_address
    (velocityMode : SpatialFrequency → ComplexVector) :
    physicalH2VelocityExchangedTriadFace velocityMode (0, 0) = 0 := by
  unfold physicalH2VelocityExchangedTriadFace
  apply physicalH2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
  · simp [completeTransportTriad, completeTransportReceiver,
      complexFrequencyVector, complexDot, dotProduct]
  · simp [completeTransportTriad, completeTransportReceiver]

/-- Every one of the three nonlinear source insertions at the zero address is killed by the exact
completed exchanged multiplier. -/
@[simp]
theorem physicalH2VelocityExchangedSourceInsertion_zero_address
    (velocityMode sourceMode : SpatialFrequency → ComplexVector) :
    physicalH2VelocityExchangedSourceInsertion velocityMode sourceMode (0, 0) = 0 := by
  simp [physicalH2VelocityExchangedSourceInsertion,
    physicalH2ExchangedTriadMultiplier, completeTransportReceiver]

@[simp]
theorem compactPhysicalH2VelocityExchangedSourceInsertion_zero_address
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (τ : ℝ) :
    compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget (0, 0) τ = 0 := by
  unfold compactPhysicalH2VelocityExchangedSourceInsertion
  exact physicalH2VelocityExchangedSourceInsertion_zero_address _ _

/-! ## Addresswise reciprocal-clock normal form -/

/-- The addresswise integrated identity, totalized over the exact zero-clock fibre. -/
theorem intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_reciprocalClock_normalForm
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (address : CompleteTransportAddress) :
    ∫ τ in sourceTime..targetTime,
        physicalH2VelocityExchangedTriadFace
          (fun frequency ↦ velocityMode velocity frequency τ) address =
      physicalH2TriadReciprocalClock nu address *
          physicalH2VelocityExchangedTriadFace
            (fun frequency ↦ velocityMode velocity frequency sourceTime) address -
        physicalH2TriadReciprocalClock nu address *
          physicalH2VelocityExchangedTriadFace
            (fun frequency ↦ velocityMode velocity frequency targetTime) address +
        ∫ τ in sourceTime..targetTime,
          physicalH2TriadReciprocalClock nu address *
            compactPhysicalH2VelocityExchangedSourceInsertion
              solution hsource htimes htarget address τ := by
  by_cases haddress : address = (0, 0)
  · subst address
    simp
  · rw [physicalH2TriadReciprocalClock_eq_inv nu address haddress]
    have hnormal :=
      intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_invClock_mul_source_sub_endpoint
        solution hnu hsource htimes htarget address haddress
    rw [hnormal]
    rw [intervalIntegral.integral_const_mul]
    ring

/-! ## Finite common-cube boundary and quartic source currents -/

/-- The reciprocal-clock cubic boundary current over the complete finite three-pin cube. -/
def finitePhysicalH2ReciprocalClockBoundaryCurrent
    (nu : ℝ) (radius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2TriadReciprocalClock nu address *
      physicalH2VelocityExchangedTriadFace velocityMode address

/-- The reciprocal-clock quartic source current over the same complete finite occurrence
population. -/
def compactFinitePhysicalH2ReciprocalClockSourceCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) (τ : ℝ) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2TriadReciprocalClock nu address *
      compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address τ

/-- The finite reciprocal-clock quartic source current is interval-integrable. -/
theorem intervalIntegrable_compactFinitePhysicalH2ReciprocalClockSourceCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) :
    IntervalIntegrable
      (compactFinitePhysicalH2ReciprocalClockSourceCurrent
        solution hsource htimes htarget radius)
      volume sourceTime targetTime := by
  unfold compactFinitePhysicalH2ReciprocalClockSourceCurrent
  have hsum := IntervalIntegrable.sum (physicalH2VelocityTriadAperture radius)
    (fun address _haddress ↦
      (intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address).const_mul
        (physicalH2TriadReciprocalClock nu address))
  have hfunctions :
      (fun τ ↦ ∑ address ∈ physicalH2VelocityTriadAperture radius,
        physicalH2TriadReciprocalClock nu address *
          compactPhysicalH2VelocityExchangedSourceInsertion
            solution hsource htimes htarget address τ) =
        ∑ address ∈ physicalH2VelocityTriadAperture radius, fun τ ↦
          physicalH2TriadReciprocalClock nu address *
            compactPhysicalH2VelocityExchangedSourceInsertion
              solution hsource htimes htarget address τ := by
    funext τ
    simp
  rw [hfunctions]
  exact hsum

/-- **Finite common-cube reciprocal-clock normal form.**  Every ordered occurrence is retained,
including the exact zero-clock fibre.  The identity is signed and is formed before norms:

`integrated cubic current = source boundary Q - target boundary Q + integrated quartic source R`.
-/
theorem intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_reciprocalClockNormalForm
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (radius : ℕ) :
    ∫ τ in sourceTime..targetTime,
        finitePhysicalH2VelocityExchangedTriadCurrent radius
          (fun frequency ↦ velocityMode velocity frequency τ) =
      finitePhysicalH2ReciprocalClockBoundaryCurrent nu radius
          (fun frequency ↦ velocityMode velocity frequency sourceTime) -
        finitePhysicalH2ReciprocalClockBoundaryCurrent nu radius
          (fun frequency ↦ velocityMode velocity frequency targetTime) +
        ∫ τ in sourceTime..targetTime,
          compactFinitePhysicalH2ReciprocalClockSourceCurrent
            solution hsource htimes htarget radius τ := by
  unfold finitePhysicalH2VelocityExchangedTriadCurrent
    finitePhysicalH2ReciprocalClockBoundaryCurrent
    compactFinitePhysicalH2ReciprocalClockSourceCurrent
  rw [intervalIntegral.integral_finsetSum]
  · rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_reciprocalClock_normalForm
        solution hnu hsource htimes htarget]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    · intro address _haddress
      exact
        (intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
            solution hsource htimes htarget address).const_mul
          (physicalH2TriadReciprocalClock nu address)
  · intro address _haddress
    exact intervalIntegrable_physicalH2VelocityExchangedTriadFace
      solution hsource htimes htarget address

/-! ## Anchored heat-Volterra elimination of the target boundary -/

/-- A globally continuous compact extension of one actual velocity mode.  The same compact-time
projection used by the nonlinear source now also carries the three velocity occurrences. -/
def compactPhysicalH2VelocityMode
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (_solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (frequency : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  velocityMode velocity frequency (compactInteriorTime hsource htimes htarget τ).1

theorem continuous_compactPhysicalH2VelocityMode
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (frequency : SpatialFrequency) :
    Continuous (compactPhysicalH2VelocityMode
      solution hsource htimes htarget frequency) := by
  have hmode : Continuous (fun t : Ioo (0 : ℝ) T ↦
      velocityMode velocity frequency t.1) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact
      (openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
        solution t frequency).continuousAt.comp continuousAt_subtype_val
  exact hmode.comp (continuous_compactInteriorTime hsource htimes htarget)

/-- The fully compact three-source insertion.  It agrees with the earlier compact source on the
selected interval and is continuous on the whole real clock, which is the exact input expected by
the shared scalar heat-Volterra owner. -/
def fullyCompactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (τ : ℝ) : ℂ :=
  physicalH2VelocityExchangedSourceInsertion
    (fun frequency ↦ compactPhysicalH2VelocityMode
      solution hsource htimes htarget frequency τ)
    (fun frequency ↦ compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency τ) address

theorem continuous_fullyCompactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    Continuous (fullyCompactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address) := by
  have hv (frequency : SpatialFrequency) : Continuous
      (compactPhysicalH2VelocityMode
        solution hsource htimes htarget frequency) :=
    continuous_compactPhysicalH2VelocityMode
      solution hsource htimes htarget frequency
  have hs (frequency : SpatialFrequency) : Continuous
      (compactOpenProjectedVelocityNonlinearMode
        solution hsource htimes htarget frequency) :=
    continuous_compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency
  have hfirst := continuousOn_triadicEnergyFace (s := Set.univ) address.1 address.2
    (hs address.1).continuousOn (hv address.2).continuousOn
    (hv (completeTransportReceiver address)).continuousOn
  have hsecond := continuousOn_triadicEnergyFace (s := Set.univ) address.1 address.2
    (hv address.1).continuousOn (hs address.2).continuousOn
    (hv (completeTransportReceiver address)).continuousOn
  have hthird := continuousOn_triadicEnergyFace (s := Set.univ) address.1 address.2
    (hv address.1).continuousOn (hv address.2).continuousOn
    (hs (completeTransportReceiver address)).continuousOn
  have hsum : Continuous (fun τ ↦
      triadicEnergyFace address.1 address.2
          (compactOpenProjectedVelocityNonlinearMode
            solution hsource htimes htarget address.1 τ)
          (compactPhysicalH2VelocityMode
            solution hsource htimes htarget address.2 τ)
          (compactPhysicalH2VelocityMode solution hsource htimes htarget
            (completeTransportReceiver address) τ) +
        triadicEnergyFace address.1 address.2
          (compactPhysicalH2VelocityMode
            solution hsource htimes htarget address.1 τ)
          (compactOpenProjectedVelocityNonlinearMode
            solution hsource htimes htarget address.2 τ)
          (compactPhysicalH2VelocityMode solution hsource htimes htarget
            (completeTransportReceiver address) τ) +
        triadicEnergyFace address.1 address.2
          (compactPhysicalH2VelocityMode
            solution hsource htimes htarget address.1 τ)
          (compactPhysicalH2VelocityMode
            solution hsource htimes htarget address.2 τ)
          (compactOpenProjectedVelocityNonlinearMode solution hsource htimes htarget
            (completeTransportReceiver address) τ)) := by
    exact continuousOn_univ.mp ((hfirst.add hsecond).add hthird)
  unfold fullyCompactPhysicalH2VelocityExchangedSourceInsertion
    physicalH2VelocityExchangedSourceInsertion
  exact continuous_const.mul hsum

theorem fullyCompactPhysicalH2VelocityExchangedSourceInsertion_eq_compact
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress)
    {τ : ℝ} (hτ : τ ∈ Icc sourceTime targetTime) :
    fullyCompactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address τ =
      compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address τ := by
  unfold fullyCompactPhysicalH2VelocityExchangedSourceInsertion
    compactPhysicalH2VelocityExchangedSourceInsertion
    compactPhysicalH2VelocityMode
  rw [compactInteriorTime_eq hsource htimes htarget hτ]

/-- The signed source translated to elapsed time from the chosen anchor. -/
def shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (elapsed : ℝ) : ℂ :=
  fullyCompactPhysicalH2VelocityExchangedSourceInsertion
    solution hsource htimes htarget address (sourceTime + elapsed)

theorem continuous_shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    Continuous (shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address) := by
  exact
    (continuous_fullyCompactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address).comp
        (continuous_const.add continuous_id)

/-- The exact anchored heat-Volterra realization of one exchanged cubic face.  Its initial face is
the actual cubic current at `sourceTime`; the shared scalar owner transports the signed three-leg
source with the addressed triad clock. -/
def anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (τ : ℝ) : ℂ :=
  scalarMildReturn (physicalH2TriadStokesClock nu address)
    (physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency sourceTime) address)
    (fun elapsed ↦
      -shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address elapsed)
    (τ - sourceTime)

/-- The anchored heat-Volterra candidate satisfies the same signed clocked ODE as the actual
exchanged face on the selected interval. -/
theorem hasDerivAt_anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (τ : ℝ) :
    HasDerivAt
      (anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address)
      (fullyCompactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address τ -
        ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) *
          anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
            solution hsource htimes htarget address τ) τ := by
  have hsourceContinuous :=
    (continuous_shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address).neg
  have hmild := hasDerivAt_scalarMildReturn
    (physicalH2TriadStokesClock nu address)
    (physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency sourceTime) address)
    (fun elapsed ↦
      -shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address elapsed)
    hsourceContinuous (τ - sourceTime)
  have hclock : HasDerivAt (fun time : ℝ ↦ time - sourceTime) 1 τ :=
    (hasDerivAt_id τ).sub_const sourceTime
  have hcomposed := hmild.scomp τ hclock
  simp only [one_smul] at hcomposed
  change HasDerivAt
    (fun time ↦ scalarMildReturn (physicalH2TriadStokesClock nu address)
      (physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency sourceTime) address)
      (fun elapsed ↦
        -shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address elapsed)
      (time - sourceTime)) _ τ at hcomposed
  have hshift :
      shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address (τ - sourceTime) =
        fullyCompactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address τ := by
    unfold shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
    rw [show sourceTime + (τ - sourceTime) = τ by ring]
  rw [hshift] at hcomposed
  unfold anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
  convert hcomposed using 1
  push_cast
  ring

@[simp]
theorem anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace_sourceTime
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address sourceTime =
      physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency sourceTime) address := by
  simp [anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace,
    scalarMildReturn, scalarHeatVolterra]

/-- **Anchored heat-Volterra representation of one actual exchanged face.**  The actual face and
the explicit anchored heat return solve the same Lipschitz scalar clock equation and have the same
source face.  ODE uniqueness therefore identifies them throughout the selected compact interval.
The target boundary is no longer an independent occurrence: it is transported from the anchor and
the signed three-source history. -/
theorem physicalH2VelocityExchangedTriadFace_eq_anchoredHeatVolterra
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress)
    {τ : ℝ} (hτ : τ ∈ Icc sourceTime targetTime) :
    physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency τ) address =
      anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address τ := by
  let actual : ℝ → ℂ := fun time ↦
    physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency time) address
  let candidate : ℝ → ℂ :=
    anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
      solution hsource htimes htarget address
  let source : ℝ → ℂ :=
    fullyCompactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address
  let rate : ℂ := ((physicalH2TriadStokesClock nu address : ℝ) : ℂ)
  let vectorField : ℝ → ℂ → ℂ := fun time face ↦ source time - rate * face
  let K : NNReal := ‖rate‖₊
  have hLipschitz (time : ℝ) : LipschitzWith K (vectorField time) := by
    have h := (LipschitzWith.const (source time)).sub (lipschitzWith_smul rate)
    simpa only [vectorField, K, zero_add, smul_eq_mul] using h
  have hactualDeriv (time : ℝ) (htime : time ∈ Icc sourceTime targetTime) :
      HasDerivAt actual (vectorField time (actual time)) time := by
    have hpoint :=
      openPeriodicSolutionOn_hasDerivAt_compactClockedPhysicalH2VelocityExchangedTriadRate
        solution hsource htimes htarget htime address
    have hsourceEq :=
      fullyCompactPhysicalH2VelocityExchangedSourceInsertion_eq_compact
        solution hsource htimes htarget address htime
    unfold compactClockedPhysicalH2VelocityExchangedTriadRate at hpoint
    change HasDerivAt actual
      (compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address time -
        rate * actual time) time at hpoint
    rw [← hsourceEq] at hpoint
    simpa only [vectorField, source] using hpoint
  have hcandidateDeriv (time : ℝ) :
      HasDerivAt candidate (vectorField time (candidate time)) time := by
    have hpoint :=
      hasDerivAt_anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address time
    simpa only [candidate, vectorField, source, rate] using hpoint
  have hactualContinuous : ContinuousOn actual (Icc sourceTime targetTime) :=
    HasDerivAt.continuousOn fun time htime ↦ hactualDeriv time htime
  have hcandidateContinuous : ContinuousOn candidate (Icc sourceTime targetTime) :=
    HasDerivAt.continuousOn fun time _htime ↦ hcandidateDeriv time
  have hinitial : actual sourceTime = candidate sourceTime := by
    simp [actual, candidate]
  have hequal := ODE_solution_unique
    (K := K) (v := vectorField) (f := actual) (g := candidate)
    (a := sourceTime) (b := targetTime)
    hLipschitz hactualContinuous
    (fun time htime ↦
      (hactualDeriv time (Ico_subset_Icc_self htime)).hasDerivWithinAt)
    hcandidateContinuous
    (fun time _htime ↦ (hcandidateDeriv time).hasDerivWithinAt)
    hinitial
  exact hequal hτ

/-- The target face itself is the anchored heat-Volterra return. -/
theorem physicalH2VelocityExchangedTriadFace_targetTime_eq_anchoredHeatVolterra
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency targetTime) address =
      anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address targetTime :=
  physicalH2VelocityExchangedTriadFace_eq_anchoredHeatVolterra
    solution hsource htimes htarget address ⟨htimes, le_rfl⟩

/-- The finite common-cube anchored heat-Volterra endpoint current, with every ordered occurrence
retained. -/
def finiteAnchoredHeatVolterraPhysicalH2VelocityExchangedTriadCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) (τ : ℝ) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
      solution hsource htimes htarget address τ

/-- The actual finite target current is exactly its anchored heat-Volterra realization. -/
theorem finitePhysicalH2VelocityExchangedTriadCurrent_targetTime_eq_anchoredHeatVolterra
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) :
    finitePhysicalH2VelocityExchangedTriadCurrent radius
        (fun frequency ↦ velocityMode velocity frequency targetTime) =
      finiteAnchoredHeatVolterraPhysicalH2VelocityExchangedTriadCurrent
        solution hsource htimes htarget radius targetTime := by
  unfold finitePhysicalH2VelocityExchangedTriadCurrent
    finiteAnchoredHeatVolterraPhysicalH2VelocityExchangedTriadCurrent
  apply Finset.sum_congr rfl
  intro address _haddress
  exact physicalH2VelocityExchangedTriadFace_targetTime_eq_anchoredHeatVolterra
    solution hsource htimes htarget address

/-- The reciprocal-clock boundary receiver applied to the explicit anchored heat-Volterra target,
rather than to an independently retained target face. -/
def finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) (τ : ℝ) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2TriadReciprocalClock nu address *
      anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address τ

/-- The reciprocal target boundary is exactly its anchor-and-source heat-Volterra realization. -/
theorem finitePhysicalH2ReciprocalClockBoundaryCurrent_targetTime_eq_anchoredHeatVolterra
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) :
    finitePhysicalH2ReciprocalClockBoundaryCurrent nu radius
        (fun frequency ↦ velocityMode velocity frequency targetTime) =
      finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryCurrent
        solution hsource htimes htarget radius targetTime := by
  unfold finitePhysicalH2ReciprocalClockBoundaryCurrent
    finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryCurrent
  apply Finset.sum_congr rfl
  intro address _haddress
  rw [physicalH2VelocityExchangedTriadFace_targetTime_eq_anchoredHeatVolterra
    solution hsource htimes htarget address]

/-- **Finite anchored heat-Volterra reciprocal-clock normal form.**  This is the same signed
common-cube identity as the guarded reciprocal endpoint law, with its formerly independent target
boundary replaced by the explicit heat transport of the source anchor and the complete signed
three-insertion history. -/
theorem intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchoredHeatVolterraNormalForm
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (radius : ℕ) :
    ∫ τ in sourceTime..targetTime,
        finitePhysicalH2VelocityExchangedTriadCurrent radius
          (fun frequency ↦ velocityMode velocity frequency τ) =
      finitePhysicalH2ReciprocalClockBoundaryCurrent nu radius
          (fun frequency ↦ velocityMode velocity frequency sourceTime) -
        finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryCurrent
          solution hsource htimes htarget radius targetTime +
        ∫ τ in sourceTime..targetTime,
          compactFinitePhysicalH2ReciprocalClockSourceCurrent
            solution hsource htimes htarget radius τ := by
  rw [intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_reciprocalClockNormalForm
    solution hnu hsource htimes htarget radius]
  rw [finitePhysicalH2ReciprocalClockBoundaryCurrent_targetTime_eq_anchoredHeatVolterra
    solution hsource htimes htarget radius]





/-! ## Half-real physical production receiver -/

/-- The half-real receiver of the reciprocal-clock cubic boundary current, in the orientation of
the complete physical-`H2` production bridge. -/
def finitePhysicalH2ReciprocalClockBoundaryProduction
    (nu : ℝ) (radius : ℕ)
    (velocityMode : SpatialFrequency → ComplexVector) : ℝ :=
  (1 / 2 : ℝ) *
    (finitePhysicalH2ReciprocalClockBoundaryCurrent nu radius velocityMode).re

/-- The half-real receiver of the reciprocal-clock quartic source current. -/
def compactFinitePhysicalH2ReciprocalClockSourceProduction
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) (τ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (compactFinitePhysicalH2ReciprocalClockSourceCurrent
      solution hsource htimes htarget radius τ).re

/-- The half-real receiver of the explicit anchored heat-Volterra target boundary. -/
def finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryProduction
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) (τ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryCurrent
      solution hsource htimes htarget radius τ).re

/-- **Half-real physical-production receiver.**  Applying the physical bridge's half-real
orientation to the signed anchored reciprocal-clock identity preserves the exact anchor,
heat-Volterra target, and quartic source incidences. -/
theorem halfReal_intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchoredHeatVolterra
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (radius : ℕ) :
    (1 / 2 : ℝ) *
        (∫ τ in sourceTime..targetTime,
          finitePhysicalH2VelocityExchangedTriadCurrent radius
            (fun frequency ↦ velocityMode velocity frequency τ)).re =
      finitePhysicalH2ReciprocalClockBoundaryProduction nu radius
          (fun frequency ↦ velocityMode velocity frequency sourceTime) -
        finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryProduction
          solution hsource htimes htarget radius targetTime +
        (1 / 2 : ℝ) *
          (∫ τ in sourceTime..targetTime,
            compactFinitePhysicalH2ReciprocalClockSourceCurrent
              solution hsource htimes htarget radius τ).re := by
  have hcomplex :=
    intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchoredHeatVolterraNormalForm
      solution hnu hsource htimes htarget radius
  have hreal := congrArg (fun value : ℂ ↦ (1 / 2 : ℝ) * value.re) hcomplex
  unfold finitePhysicalH2ReciprocalClockBoundaryProduction
    finitePhysicalH2ReciprocalClockAnchoredHeatVolterraBoundaryProduction
  simp only [Complex.add_re, Complex.sub_re] at hreal
  rw [hreal]
  ring

section Audit

#print axioms physicalH2TriadReciprocalClock_mul_clock
#print axioms physicalH2VelocityExchangedTriadFace_zero_address
#print axioms physicalH2VelocityExchangedSourceInsertion_zero_address
#print axioms intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_reciprocalClock_normalForm
#print axioms intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_reciprocalClockNormalForm
#print axioms physicalH2VelocityExchangedTriadFace_eq_anchoredHeatVolterra
#print axioms intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchoredHeatVolterraNormalForm
#print axioms halfReal_intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchoredHeatVolterra

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
