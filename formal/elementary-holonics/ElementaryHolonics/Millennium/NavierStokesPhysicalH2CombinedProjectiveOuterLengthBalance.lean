import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterClock

/-!
# Real length balance of the combined physical-H2 projective outer clock

**[proved-derived; formal-checked]** The exact complex boundary current is now observed through
the justified real receiver

`E(t) = (1 / 2) * |B(t)|²`.

Pairing the already-proved combined clock law with `B` gives

`E' + Ω_outer * |B|² = P_horizontal + P_nonlinear`,

where both productions are retained as explicit real inner products against `B`.  The dissipation
coefficient is nonnegative for nonnegative viscosity and strictly positive at a nonzero address
for positive viscosity.  At a zero-mode crossing the complex boundary may acquire a nonzero jet,
but the first derivative of this quadratic receiver is exactly zero; the full carrier jet remains
visible in the imported complex law rather than being falsely reconstructed from the collapsed
length receiver.

The production currents have no sign or size control here.  A concrete scalar-complex witness
shows that an arbitrary forcing can exceed any positive damping coefficient.  No coercivity of the
whole balance, absorption, estimate, terminal control, or Navier--Stokes solution is claimed.
-/

noncomputable section

open Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterLengthBalance

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterClock
open Soma.Holonics.Millennium.NavierStokesPhysicalH2OuterTestProjectiveClock
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The real receiver and its generic derivative -/

/-- Euclidean real inner product on the complex scalar boundary line. -/
def complexScalarRealInner (left right : ℂ) : ℝ :=
  left.re * right.re + left.im * right.im

/-- Half of the squared Euclidean length on the complex scalar boundary line. -/
def complexScalarHalfLengthSquare (value : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Complex.normSq value

theorem complexScalarRealInner_self
    (value : ℂ) :
    complexScalarRealInner value value = Complex.normSq value := by
  simp [complexScalarRealInner, Complex.normSq_apply]

theorem complexScalarHalfLengthSquare_nonneg
    (value : ℂ) :
    0 ≤ complexScalarHalfLengthSquare value := by
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg value)

/-- The derivative of the half-length-square receiver is the real pairing with the literal
complex jet. -/
theorem hasDerivAt_complexScalarHalfLengthSquare
    (boundary : ℝ → ℂ) (boundaryJet : ℂ) (time : ℝ)
    (hboundary : HasDerivAt boundary boundaryJet time) :
    HasDerivAt (fun clock ↦ complexScalarHalfLengthSquare (boundary clock))
      (complexScalarRealInner (boundary time) boundaryJet) time := by
  have hreComplex :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hboundary
  have himComplex :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hboundary
  have hre : HasDerivAt (fun clock ↦ (boundary clock).re) boundaryJet.re time := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using hreComplex
  have him : HasDerivAt (fun clock ↦ (boundary clock).im) boundaryJet.im time := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using himComplex
  have hsquare := (hre.mul hre).add (him.mul him)
  have hhalf := hsquare.const_mul (1 / 2 : ℝ)
  change HasDerivAt
    (fun clock ↦ (1 / 2 : ℝ) *
      ((boundary clock).re * (boundary clock).re +
        (boundary clock).im * (boundary clock).im))
    (complexScalarRealInner (boundary time) boundaryJet) time
  apply hhalf.congr_deriv
  simp [complexScalarRealInner]
  ring

/-! ## Physical length, productions, and dissipation -/

/-- Half-length-square of the actual combined projective outer boundary. -/
def physicalH2CombinedProjectiveOuterHalfLengthSquare
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℝ :=
  complexScalarHalfLengthSquare
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time)

/-- Real horizontal production paired against the contemporaneous complex boundary. -/
def physicalH2CombinedProjectiveHorizontalPower
    (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector) (time : ℝ) : ℝ :=
  complexScalarRealInner
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time)
    (physicalH2CombinedProjectiveHorizontalContribution
      velocity address leg frequency transport mode modeJet time)

/-- Real nonlinear outer variation paired against the contemporaneous complex boundary. -/
def physicalH2CombinedProjectiveOuterNonlinearPower
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) : ℝ :=
  complexScalarRealInner
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time.1)
    (physicalH2CombinedProjectiveOuterNonlinearVariation
      solution time address leg frequency transport mode)

/-- The positive-rate Stokes share observed through the squared boundary length. -/
def physicalH2CombinedProjectiveOuterLengthDissipation
    (nu : ℝ) (velocity : VelocityField) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℝ :=
  physicalH2OuterTestStokesClock nu address leg *
    Complex.normSq
      (physicalH2CombinedProjectiveOuterBoundary
        velocity address leg frequency transport mode time)

/-- The real pairing distributes over the combined complex derivative and converts the negative
real Stokes multiplier into `-Ω_outer * |B|²`. -/
theorem complexScalarRealInner_combinedJet
    (boundary horizontal nonlinear : ℂ) (outerClock : ℝ) :
    complexScalarRealInner boundary
        (horizontal + nonlinear - (outerClock : ℂ) * boundary) =
      complexScalarRealInner boundary horizontal +
        complexScalarRealInner boundary nonlinear -
        outerClock * Complex.normSq boundary := by
  simp [complexScalarRealInner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- **Exact real length law.** This is the derivative form of
`E' + Ω_outer |B|² = P_horizontal + P_nonlinear`. -/
theorem openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterHalfLengthSquare
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector)
    (hmode : HasDerivAt mode (modeJet time.1) time.1)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time.1) (modeJet time.1) *
        transport time.1) time.1) :
    HasDerivAt
      (physicalH2CombinedProjectiveOuterHalfLengthSquare
        velocity address leg frequency transport mode)
      (physicalH2CombinedProjectiveHorizontalPower
          velocity address leg frequency transport mode modeJet time.1 +
        physicalH2CombinedProjectiveOuterNonlinearPower
          solution time address leg frequency transport mode -
        physicalH2CombinedProjectiveOuterLengthDissipation
          nu velocity address leg frequency transport mode time.1) time.1 := by
  have hboundary :=
    openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary
      solution time address leg frequency transport mode modeJet hmode htransport
  have hlength := hasDerivAt_complexScalarHalfLengthSquare
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode)
    (physicalH2CombinedProjectiveHorizontalContribution
        velocity address leg frequency transport mode modeJet time.1 +
      physicalH2CombinedProjectiveOuterNonlinearVariation
        solution time address leg frequency transport mode -
      physicalH2CombinedProjectiveOuterStokesCurrent
        nu velocity address leg frequency transport mode time.1)
    time.1 hboundary
  apply hlength.congr_deriv
  rw [show physicalH2CombinedProjectiveOuterStokesCurrent
      nu velocity address leg frequency transport mode time.1 =
        ((physicalH2OuterTestStokesClock nu address leg : ℝ) : ℂ) *
          physicalH2CombinedProjectiveOuterBoundary
            velocity address leg frequency transport mode time.1 by rfl]
  exact complexScalarRealInner_combinedJet
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time.1)
    (physicalH2CombinedProjectiveHorizontalContribution
      velocity address leg frequency transport mode modeJet time.1)
    (physicalH2CombinedProjectiveOuterNonlinearVariation
      solution time address leg frequency transport mode)
    (physicalH2OuterTestStokesClock nu address leg)

/-- The displayed derivative coefficient satisfies the requested balance algebraically. -/
theorem combinedProjectiveOuterLengthRate_add_dissipation_eq_power
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector) :
    (physicalH2CombinedProjectiveHorizontalPower
          velocity address leg frequency transport mode modeJet time.1 +
        physicalH2CombinedProjectiveOuterNonlinearPower
          solution time address leg frequency transport mode -
        physicalH2CombinedProjectiveOuterLengthDissipation
          nu velocity address leg frequency transport mode time.1) +
        physicalH2CombinedProjectiveOuterLengthDissipation
          nu velocity address leg frequency transport mode time.1 =
      physicalH2CombinedProjectiveHorizontalPower
          velocity address leg frequency transport mode modeJet time.1 +
        physicalH2CombinedProjectiveOuterNonlinearPower
          solution time address leg frequency transport mode := by
  ring

/-! ## Zero crossing and positive Stokes share -/

/-- At a zero-mode crossing the quadratic receiver has zero first derivative even though the
imported complex boundary law retains the full horizontal carrier jet. -/
theorem openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterHalfLengthSquare_zeroCrossing
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector)
    (hzero : mode time.1 = 0)
    (hmode : HasDerivAt mode (modeJet time.1) time.1)
    (htransport : HasDerivAt transport 0 time.1) :
    HasDerivAt
      (physicalH2CombinedProjectiveOuterHalfLengthSquare
        velocity address leg frequency transport mode) 0 time.1 := by
  have hboundary :=
    openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterBoundary_zeroCrossing
      solution time address leg frequency transport mode modeJet
      hzero hmode htransport
  have hlength := hasDerivAt_complexScalarHalfLengthSquare
    (physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode) _ time.1 hboundary
  apply hlength.congr_deriv
  have hboundaryZero : physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time.1 = 0 := by
    have hhodge : nonzeroModeHodgeReconstruction frequency
        (0 : ComplexVector) = 0 := by
      change nonzeroModeHodgeReconstructionRealCLM frequency 0 = 0
      exact map_zero _
    change physicalH2OuterInsertionRealCLM
      (fun outerFrequency ↦ velocityMode velocity outerFrequency time.1)
      address leg
      (nonzeroModeHodgeReconstruction frequency
        (transport time.1 • mode time.1)) = 0
    rw [hzero, smul_zero, hhodge]
    exact map_zero _
  simp [complexScalarRealInner, hboundaryZero]

/-- The dissipation coefficient itself is nonnegative for nonnegative viscosity. -/
theorem combinedProjectiveOuterLength_dissipationCoefficient_nonneg
    {nu : ℝ} (hnu : 0 ≤ nu) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) :
    0 ≤ physicalH2OuterTestStokesClock nu address leg :=
  physicalH2OuterTestStokesClock_nonneg hnu address leg

/-- The dissipation coefficient itself is strictly positive for positive viscosity at a nonzero
address. -/
theorem combinedProjectiveOuterLength_dissipationCoefficient_pos
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) (leg : PhysicalH2InsertionLeg) :
    0 < physicalH2OuterTestStokesClock nu address leg :=
  physicalH2OuterTestStokesClock_pos hnu address haddress leg

theorem combinedProjectiveOuterLengthDissipation_nonneg
    {nu : ℝ} (hnu : 0 ≤ nu) (velocity : VelocityField)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode : ℝ → ComplexVector) (time : ℝ) :
    0 ≤ physicalH2CombinedProjectiveOuterLengthDissipation
      nu velocity address leg frequency transport mode time := by
  exact mul_nonneg
    (physicalH2OuterTestStokesClock_nonneg hnu address leg)
    (Complex.normSq_nonneg _)

theorem combinedProjectiveOuterLengthDissipation_pos
    {nu : ℝ} (hnu : 0 < nu) (velocity : VelocityField)
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0))
    (leg : PhysicalH2InsertionLeg) (frequency : SpatialFrequency)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ)
    (hboundary : physicalH2CombinedProjectiveOuterBoundary
      velocity address leg frequency transport mode time ≠ 0) :
    0 < physicalH2CombinedProjectiveOuterLengthDissipation
      nu velocity address leg frequency transport mode time := by
  exact mul_pos
    (physicalH2OuterTestStokesClock_pos hnu address haddress leg)
    (Complex.normSq_pos.mpr hboundary)

/-! ## Integrated real length identity -/

/-- Total real-time chart of the nonlinear power, extended by zero outside the open lifespan.
The integration theorem restricts its whole interval to that lifespan. -/
def physicalH2CombinedProjectiveOuterNonlinearPowerOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode : ℝ → ComplexVector) (time : ℝ) : ℝ :=
  if htime : time ∈ Ioo 0 T then
    physicalH2CombinedProjectiveOuterNonlinearPower solution
      ⟨time, htime⟩ address leg frequency transport mode
  else 0

/-- Endpoint length difference plus integrated Stokes length dissipation equals the two retained
real production integrals. -/
theorem integral_combinedProjectiveOuterLength_boundary_add_dissipation_eq_powers
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (frequency : SpatialFrequency) (transport : ℝ → ℂ)
    (mode modeJet : ℝ → ComplexVector) (a b : ℝ)
    (hinterval : uIcc a b ⊆ Ioo 0 T)
    (hmode : ∀ time ∈ uIcc a b,
      HasDerivAt mode (modeJet time) time)
    (htransport : ∀ time ∈ uIcc a b,
      HasDerivAt transport
        (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time)
    (hhorizontal : IntervalIntegrable
      (physicalH2CombinedProjectiveHorizontalPower
        velocity address leg frequency transport mode modeJet)
      MeasureTheory.volume a b)
    (hnonlinear : IntervalIntegrable
      (physicalH2CombinedProjectiveOuterNonlinearPowerOn solution
        address leg frequency transport mode)
      MeasureTheory.volume a b)
    (hdissipation : IntervalIntegrable
      (physicalH2CombinedProjectiveOuterLengthDissipation
        nu velocity address leg frequency transport mode)
      MeasureTheory.volume a b) :
    physicalH2CombinedProjectiveOuterHalfLengthSquare
          velocity address leg frequency transport mode b -
        physicalH2CombinedProjectiveOuterHalfLengthSquare
          velocity address leg frequency transport mode a +
        ∫ time in a..b,
          physicalH2CombinedProjectiveOuterLengthDissipation
            nu velocity address leg frequency transport mode time =
      (∫ time in a..b,
          physicalH2CombinedProjectiveHorizontalPower
            velocity address leg frequency transport mode modeJet time) +
        ∫ time in a..b,
          physicalH2CombinedProjectiveOuterNonlinearPowerOn solution
            address leg frequency transport mode time := by
  have hderiv : ∀ time ∈ uIcc a b,
      HasDerivAt
        (physicalH2CombinedProjectiveOuterHalfLengthSquare
          velocity address leg frequency transport mode)
        (physicalH2CombinedProjectiveHorizontalPower
            velocity address leg frequency transport mode modeJet time +
          physicalH2CombinedProjectiveOuterNonlinearPowerOn solution
            address leg frequency transport mode time -
          physicalH2CombinedProjectiveOuterLengthDissipation
            nu velocity address leg frequency transport mode time) time := by
    intro time htime
    have hinterior := hinterval htime
    have hactual :=
      openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterHalfLengthSquare
        solution ⟨time, hinterior⟩ address leg frequency transport mode modeJet
        (hmode time htime) (htransport time htime)
    simpa [physicalH2CombinedProjectiveOuterNonlinearPowerOn, hinterior] using hactual
  have hintegrable := (hhorizontal.add hnonlinear).sub hdissipation
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable
  rw [intervalIntegral.integral_sub (hhorizontal.add hnonlinear) hdissipation,
    intervalIntegral.integral_add hhorizontal hnonlinear] at hftc
  linear_combination -hftc

/-! ## A firing obstruction to absorption from coefficient positivity alone -/

/-- For every positive damping coefficient there is an explicit complex forcing whose real power
at the unit boundary exceeds the associated quadratic dissipation. -/
theorem positive_damping_does_not_bound_arbitrary_signed_forcing
    (outerClock : ℝ) (houterClock : 0 < outerClock) :
    ∃ boundary forcing : ℂ,
      outerClock * Complex.normSq boundary <
        complexScalarRealInner boundary forcing := by
  refine ⟨1, ((2 * outerClock : ℝ) : ℂ), ?_⟩
  simp [complexScalarRealInner]
  linarith

section Audit

#print axioms hasDerivAt_complexScalarHalfLengthSquare
#print axioms openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterHalfLengthSquare
#print axioms openPeriodicSolutionOn_hasDerivAt_combinedProjectiveOuterHalfLengthSquare_zeroCrossing
#print axioms combinedProjectiveOuterLength_dissipationCoefficient_nonneg
#print axioms combinedProjectiveOuterLength_dissipationCoefficient_pos
#print axioms combinedProjectiveOuterLengthDissipation_nonneg
#print axioms combinedProjectiveOuterLengthDissipation_pos
#print axioms integral_combinedProjectiveOuterLength_boundary_add_dissipation_eq_powers
#print axioms positive_damping_does_not_bound_arbitrary_signed_forcing

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CombinedProjectiveOuterLengthBalance
