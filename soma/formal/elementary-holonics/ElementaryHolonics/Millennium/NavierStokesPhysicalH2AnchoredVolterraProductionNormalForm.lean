import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization

/-!
# Anchored Volterra normal form for the physical-H2 production current

**[proved-derived; formal-checked]** The reciprocal-clock identity still presents its target
face as an anchored heat return.  This owner separates that return into two caused occurrences:
the homogeneous transport of the source-time cubic face and the ordered nonlinear source
history.  Substitution into the signed reciprocal identity removes the target face entirely.

For every retained address, the time-integrated cubic current is exactly the sum of

* a future-blind anchor transport difference, and
* the reciprocal-clock difference between the raw source integral and its ordered heat return.

The finite common-cube and half-real physical receivers are then obtained before any norm.  No
estimate of the Volterra residue, terminal control, or continuation consequence is asserted.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2AnchoredVolterraProductionNormalForm

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation

/-! ## Addresswise anchor and source returns -/

/-- Homogeneous heat transport of the actual cubic face at the positive source-time anchor. -/
def physicalH2AnchoredHomogeneousExchangedFace
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (_solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) : ℂ :=
  scalarMildReturn (physicalH2TriadStokesClock nu address)
    (physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency sourceTime) address)
    (fun _ ↦ 0) (targetTime - sourceTime)

/-- Ordered heat return of the complete signed three-leg source history, with zero anchor face. -/
def physicalH2AnchoredSourceVolterraExchangedFace
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) : ℂ :=
  scalarMildReturn (physicalH2TriadStokesClock nu address) 0
    (fun elapsed ↦
      -shiftedFullyCompactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address elapsed)
    (targetTime - sourceTime)

/-- The anchored actual face separates exactly into its homogeneous anchor transport and its
ordered nonlinear source return. -/
theorem anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace_eq_anchor_add_source
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
        solution hsource htimes htarget address targetTime =
      physicalH2AnchoredHomogeneousExchangedFace
          (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
          (velocity := velocity) solution address +
        physicalH2AnchoredSourceVolterraExchangedFace
          solution hsource htimes htarget address := by
  unfold anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace
    physicalH2AnchoredHomogeneousExchangedFace
    physicalH2AnchoredSourceVolterraExchangedFace
  simp only [scalarMildReturn, mul_zero, zero_sub]
  have hzero :
      scalarHeatVolterra (physicalH2TriadStokesClock nu address)
          (fun _ : ℝ ↦ (0 : ℂ)) (targetTime - sourceTime) = 0 := by
    simp [scalarHeatVolterra]
  rw [hzero, sub_zero]
  ring

/-- The reciprocal-clock anchor transport difference.  It depends only on the source-time cubic
face, the addressed clock, and the elapsed interval. -/
def physicalH2ReciprocalClockAnchorTransportCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    (physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency sourceTime) address -
      physicalH2AnchoredHomogeneousExchangedFace
        (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
        (velocity := velocity) solution address)

/-- The signed clocked Volterra residue: raw source occupation minus its ordered heat return. -/
def physicalH2ReciprocalClockVolterraResidueCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    ((∫ τ in sourceTime..targetTime,
        compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address τ) -
      physicalH2AnchoredSourceVolterraExchangedFace
        solution hsource htimes htarget address)

/-- **Addresswise target-free anchored normal form.**  The target cubic occurrence has been
replaced exactly by the homogeneous anchor transport and the ordered nonlinear history. -/
theorem intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_anchor_add_volterraResidue
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
      physicalH2ReciprocalClockAnchorTransportCurrent
          (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
          (velocity := velocity) solution address +
        physicalH2ReciprocalClockVolterraResidueCurrent
          solution hsource htimes htarget address := by
  rw [intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_reciprocalClock_normalForm
    solution hnu hsource htimes htarget address]
  rw [physicalH2VelocityExchangedTriadFace_targetTime_eq_anchoredHeatVolterra
    solution hsource htimes htarget address]
  rw [anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace_eq_anchor_add_source
    solution hsource htimes htarget address]
  rw [intervalIntegral.integral_const_mul]
  unfold physicalH2ReciprocalClockAnchorTransportCurrent
    physicalH2ReciprocalClockVolterraResidueCurrent
  ring

/-! ## Complete finite common-cube receiver -/

/-- Finite common-cube population of the future-blind anchor transport current. -/
def finitePhysicalH2ReciprocalClockAnchorTransportCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (radius : ℕ) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2ReciprocalClockAnchorTransportCurrent
      (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
      (velocity := velocity) solution address

/-- Finite common-cube population of the signed chronological Volterra residue. -/
def finitePhysicalH2ReciprocalClockVolterraResidueCurrent
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2ReciprocalClockVolterraResidueCurrent
      solution hsource htimes htarget address

/-- **Finite target-free anchored normal form.**  Every outer occurrence, including the exact
zero-clock radical, remains in the common cube before the two caused populations are summed. -/
theorem intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchor_add_volterraResidue
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
      finitePhysicalH2ReciprocalClockAnchorTransportCurrent
          (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
          (velocity := velocity) solution radius +
        finitePhysicalH2ReciprocalClockVolterraResidueCurrent
          solution hsource htimes htarget radius := by
  unfold finitePhysicalH2VelocityExchangedTriadCurrent
    finitePhysicalH2ReciprocalClockAnchorTransportCurrent
    finitePhysicalH2ReciprocalClockVolterraResidueCurrent
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_anchor_add_volterraResidue
      solution hnu hsource htimes htarget]
    rw [← Finset.sum_add_distrib]
  · intro address _haddress
    exact intervalIntegrable_physicalH2VelocityExchangedTriadFace
      solution hsource htimes htarget address

/-! ## Half-real physical production receiver -/

/-- Half-real physical orientation of the anchor transport population. -/
def finitePhysicalH2ReciprocalClockAnchorTransportProduction
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (radius : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    (finitePhysicalH2ReciprocalClockAnchorTransportCurrent
      (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
      (velocity := velocity) solution radius).re

/-- Half-real physical orientation of the signed chronological Volterra residue. -/
def finitePhysicalH2ReciprocalClockVolterraResidueProduction
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    (finitePhysicalH2ReciprocalClockVolterraResidueCurrent
      solution hsource htimes htarget radius).re

/-- The physical half-real current inherits the exact target-free anchor/residue split. -/
theorem halfReal_intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchor_add_volterraResidue
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
      finitePhysicalH2ReciprocalClockAnchorTransportProduction
          (T := T) (nu := nu) (sourceTime := sourceTime) (targetTime := targetTime)
          (velocity := velocity) solution radius +
        finitePhysicalH2ReciprocalClockVolterraResidueProduction
          solution hsource htimes htarget radius := by
  have hcomplex :=
    intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchor_add_volterraResidue
      solution hnu hsource htimes htarget radius
  have hreal := congrArg (fun value : ℂ ↦ (1 / 2 : ℝ) * value.re) hcomplex
  unfold finitePhysicalH2ReciprocalClockAnchorTransportProduction
    finitePhysicalH2ReciprocalClockVolterraResidueProduction
  simp only [Complex.add_re] at hreal
  rw [hreal]
  ring

section Audit

#print axioms anchoredHeatVolterraPhysicalH2VelocityExchangedTriadFace_eq_anchor_add_source
#print axioms intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_anchor_add_volterraResidue
#print axioms intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchor_add_volterraResidue
#print axioms halfReal_intervalIntegral_finitePhysicalH2VelocityExchangedTriadCurrent_eq_anchor_add_volterraResidue

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2AnchoredVolterraProductionNormalForm
