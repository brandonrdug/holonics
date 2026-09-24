import ElementaryHolonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticSignedPayment

/-!
# Exact projective-clock transport and its outer-Hodge payment

**[proved-derived; formal-checked]** A nonzero complex vorticity mode carries the Hermitian
connection

`a(Ω, Ω') = ⟪Ω, Ω'⟫ / ⟪Ω, Ω⟫`.

Its horizontal clock jet is exactly the standing own-mode phase.  A scalar transport `w` whose
literal derivative is `-a * w` cancels the radial jet without an exponential chart: the
derivative of `w • Ω` is `w • modeHermitianPhase Ω Ω'`.  Under a nonvanishing complex gauge `g`,
the connection changes by `g' / g` and the horizontal jet changes covariantly by `g`.

For a time-varying outer covector `L(t)` composed with the standing Hodge reconstruction, the
exact product rule has two currents.  Integration by parts returns the horizontal current as an
endpoint difference minus the covector-variation remainder.  Neither term is discarded.

The retained zero crossing supplies two unconditional counterexamples.  The terminal boundary
cannot be reconstructed from the initial curl alone, and the already-admitted outer-Hodge witness
has nonzero horizontal current at zero mode while every viscosity multiple of the mode square is
zero.  Thus this exact clock does not by itself produce a future-blind or sub-viscous estimate.

No norm estimate, viscosity absorption, terminal control, or Navier--Stokes closure claim is made.
-/

noncomputable section

open scoped Interval BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticCurlPhaseJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticSignedPayment
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
open Soma.Holonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The Hermitian connection and horizontal clock jet -/

/-- The exact own-mode Hermitian connection coefficient.  Its division is totalized so that the
zero mode remains a separate chart whose entire jet is horizontal. -/
def ownModeHermitianConnection
    (mode modeJet : ComplexVector) : ℂ :=
  complexVectorHermitianPairing mode modeJet /
    complexVectorHermitianPairing mode mode

/-- The covariant, receiver-orthogonal jet of one complex Fourier vorticity mode. -/
def ownModeHermitianHorizontalJet
    (mode modeJet : ComplexVector) : ComplexVector :=
  modeJet - ownModeHermitianConnection mode modeJet • mode

theorem ownModeHermitianConnection_eq_alignedAmplitude
    (mode modeJet : ComplexVector) :
    ownModeHermitianConnection mode modeJet =
      modeHermitianAlignedAmplitude mode modeJet := rfl

theorem ownModeHermitianHorizontalJet_eq_modeHermitianPhase
    (mode modeJet : ComplexVector) :
    ownModeHermitianHorizontalJet mode modeJet =
      modeHermitianPhase mode modeJet := rfl

/-- The connection and horizontal jet reconstruct the literal jet, including at zero. -/
theorem ownModeHermitianHorizontalJet_add_connection
    (mode modeJet : ComplexVector) :
    ownModeHermitianHorizontalJet mode modeJet +
        ownModeHermitianConnection mode modeJet • mode = modeJet := by
  exact modeHermitianPhase_add_aligned mode modeJet

@[simp]
theorem ownModeHermitianConnection_zero
    (modeJet : ComplexVector) :
    ownModeHermitianConnection 0 modeJet = 0 := by
  simp [ownModeHermitianConnection, complexVectorHermitianPairing]

@[simp]
theorem ownModeHermitianHorizontalJet_zero
    (modeJet : ComplexVector) :
    ownModeHermitianHorizontalJet 0 modeJet = modeJet := by
  simp [ownModeHermitianHorizontalJet]

/-! ## Gauge covariance -/

private theorem hermitianPairing_add_right
    (left first second : ComplexVector) :
    complexVectorHermitianPairing left (first + second) =
      complexVectorHermitianPairing left first +
        complexVectorHermitianPairing left second := by
  unfold complexVectorHermitianPairing
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hermitianPairing_smul_right
    (left right : ComplexVector) (scale : ℂ) :
    complexVectorHermitianPairing left (scale • right) =
      scale * complexVectorHermitianPairing left right := by
  unfold complexVectorHermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem hermitianPairing_smul_left
    (left right : ComplexVector) (scale : ℂ) :
    complexVectorHermitianPairing (scale • left) right =
      (starRingEnd ℂ) scale * complexVectorHermitianPairing left right := by
  unfold complexVectorHermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem hermitianPairing_self_ne_zero
    {mode : ComplexVector} (hmode : mode ≠ 0) :
    complexVectorHermitianPairing mode mode ≠ 0 := by
  rw [complexVectorHermitianPairing_self_eq]
  apply Complex.ofReal_ne_zero.mpr
  have hfunction : (fun component : Fin 3 ↦ mode component) ≠ 0 := by
    simpa only using hmode
  obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hfunction
  exact (Finset.sum_pos'
    (fun index _hindex ↦ Complex.normSq_nonneg _)
    ⟨component, Finset.mem_univ component,
      Complex.normSq_pos.mpr hcomponent⟩).ne'

/-- The exact affine gauge law for the Hermitian connection. -/
theorem ownModeHermitianConnection_gauge
    (mode modeJet : ComplexVector) (gauge gaugeJet : ℂ)
    (hmode : mode ≠ 0) (hgauge : gauge ≠ 0) :
    ownModeHermitianConnection (gauge • mode)
        (gaugeJet • mode + gauge • modeJet) =
      ownModeHermitianConnection mode modeJet + gaugeJet / gauge := by
  have hself := hermitianPairing_self_ne_zero hmode
  unfold ownModeHermitianConnection
  rw [hermitianPairing_add_right,
    hermitianPairing_smul_left, hermitianPairing_smul_right,
    hermitianPairing_smul_left, hermitianPairing_smul_right,
    hermitianPairing_smul_left, hermitianPairing_smul_right]
  field_simp [hgauge, hself]
  ring

/-- The horizontal jet is genuinely gauge covariant, not merely equal after a scalar receiver. -/
theorem ownModeHermitianHorizontalJet_gauge
    (mode modeJet : ComplexVector) (gauge gaugeJet : ℂ)
    (hmode : mode ≠ 0) (hgauge : gauge ≠ 0) :
    ownModeHermitianHorizontalJet (gauge • mode)
        (gaugeJet • mode + gauge • modeJet) =
      gauge • ownModeHermitianHorizontalJet mode modeJet := by
  unfold ownModeHermitianHorizontalJet
  rw [ownModeHermitianConnection_gauge mode modeJet gauge gaugeJet hmode hgauge]
  ext component
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hgauge]
  ring

/-! ## Division-free parallel transport product rule -/

/-- An integrating scalar is supplied through its literal derivative law; no exponential or
privileged clock chart is introduced.  The radial connection cancels exactly. -/
theorem hasDerivAt_parallelTransport_mode
    (mode : ℝ → ComplexVector) (modeJet : ComplexVector)
    (transport : ℝ → ℂ) (time : ℝ)
    (hmode : HasDerivAt mode modeJet time)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time) modeJet * transport time) time) :
    HasDerivAt (fun clock ↦ transport clock • mode clock)
      (transport time • ownModeHermitianHorizontalJet (mode time) modeJet) time := by
  have hproduct := htransport.smul hmode
  apply hproduct.congr_deriv
  funext component
  simp only [ownModeHermitianHorizontalJet, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- At a zero crossing, the reconstruction fibre is the full literal mode jet and the transport
law uses no division or nonvanishing assumption. -/
theorem hasDerivAt_parallelTransport_zeroCrossing
    (mode : ℝ → ComplexVector) (modeJet : ComplexVector)
    (transport : ℝ → ℂ) (time : ℝ)
    (hzero : mode time = 0)
    (hmode : HasDerivAt mode modeJet time)
    (htransport : HasDerivAt transport 0 time) :
    HasDerivAt (fun clock ↦ transport clock • mode clock)
      (transport time • modeJet) time := by
  have htransport' : HasDerivAt transport
      (-ownModeHermitianConnection (mode time) modeJet * transport time) time := by
    simpa [hzero] using htransport
  have hparallel := hasDerivAt_parallelTransport_mode
    mode modeJet transport time hmode htransport'
  simpa [hzero] using hparallel

/-! ## Time-varying outer covector composed with Hodge reconstruction -/

/-- Hodge reconstruction bundled as a continuous real-linear passage for literal clock
derivatives.  The underlying map is still the exact complex-linear Hodge owner. -/
def nonzeroModeHodgeReconstructionRealCLM
    (frequency : SpatialFrequency) : ComplexVector →L[ℝ] ComplexVector :=
  ⟨(nonzeroModeHodgeReconstructionLinearMap frequency).restrictScalars ℝ,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem nonzeroModeHodgeReconstructionRealCLM_apply
    (frequency : SpatialFrequency) (sourceCurl : ComplexVector) :
    nonzeroModeHodgeReconstructionRealCLM frequency sourceCurl =
      nonzeroModeHodgeReconstruction frequency sourceCurl := rfl

/-- The transported boundary reading of a time-varying outer covector after Hodge. -/
def projectiveOuterHodgeBoundary
    (frequency : SpatialFrequency)
    (outer : ℝ → ComplexVector →L[ℝ] ℂ)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  outer time
    (nonzeroModeHodgeReconstructionRealCLM frequency
      (transport time • mode time))

/-- The horizontal current tested by the contemporaneous outer Hodge covector. -/
def projectiveOuterHodgeHorizontalCurrent
    (frequency : SpatialFrequency)
    (outer : ℝ → ComplexVector →L[ℝ] ℂ)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector)
    (modeJet : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  outer time
    (nonzeroModeHodgeReconstructionRealCLM frequency
      (transport time • ownModeHermitianHorizontalJet (mode time) (modeJet time)))

/-- The remainder caused by motion of the outer covector itself. -/
def projectiveOuterHodgeCovectorVariation
    (frequency : SpatialFrequency)
    (outerJet : ℝ → ComplexVector →L[ℝ] ℂ)
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ℂ :=
  outerJet time
    (nonzeroModeHodgeReconstructionRealCLM frequency
      (transport time • mode time))

/-- Exact covariant product rule after the time-varying outer covector and Hodge passage. -/
theorem hasDerivAt_projectiveOuterHodgeBoundary
    (frequency : SpatialFrequency)
    (outer outerJet : ℝ → ComplexVector →L[ℝ] ℂ)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector) (time : ℝ)
    (houter : HasDerivAt outer (outerJet time) time)
    (hmode : HasDerivAt mode (modeJet time) time)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time) :
    HasDerivAt
      (projectiveOuterHodgeBoundary frequency outer transport mode)
      (projectiveOuterHodgeCovectorVariation frequency outerJet transport mode time +
        projectiveOuterHodgeHorizontalCurrent
          frequency outer transport mode modeJet time) time := by
  have hparallel := hasDerivAt_parallelTransport_mode
    mode (modeJet time) transport time hmode htransport
  have hhodge :=
    (nonzeroModeHodgeReconstructionRealCLM frequency).hasFDerivAt.comp_hasDerivAt
      time hparallel
  exact houter.clm_apply hhodge

/-- Exact integration by parts for the projective clock.  The horizontal current is the terminal
boundary difference minus the full time-varying-covector remainder. -/
theorem integral_projectiveOuterHodgeHorizontalCurrent_eq_boundary_sub_variation
    (frequency : SpatialFrequency)
    (outer outerJet : ℝ → ComplexVector →L[ℝ] ℂ)
    (transport : ℝ → ℂ) (mode modeJet : ℝ → ComplexVector)
    (a b : ℝ)
    (houter : ∀ time ∈ Set.uIcc a b,
      HasDerivAt outer (outerJet time) time)
    (hmode : ∀ time ∈ Set.uIcc a b,
      HasDerivAt mode (modeJet time) time)
    (htransport : ∀ time ∈ Set.uIcc a b,
      HasDerivAt transport
        (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time)
    (hvariation : IntervalIntegrable
      (projectiveOuterHodgeCovectorVariation frequency outerJet transport mode)
      MeasureTheory.volume a b)
    (hcurrent : IntervalIntegrable
      (projectiveOuterHodgeHorizontalCurrent frequency outer transport mode modeJet)
      MeasureTheory.volume a b) :
    ∫ time in a..b,
        projectiveOuterHodgeHorizontalCurrent frequency outer transport mode modeJet time =
      projectiveOuterHodgeBoundary frequency outer transport mode b -
        projectiveOuterHodgeBoundary frequency outer transport mode a -
        ∫ time in a..b,
          projectiveOuterHodgeCovectorVariation frequency outerJet transport mode time := by
  have hderiv : ∀ time ∈ Set.uIcc a b,
      HasDerivAt
        (projectiveOuterHodgeBoundary frequency outer transport mode)
        (projectiveOuterHodgeCovectorVariation frequency outerJet transport mode time +
          projectiveOuterHodgeHorizontalCurrent
            frequency outer transport mode modeJet time) time := by
    intro time htime
    exact hasDerivAt_projectiveOuterHodgeBoundary
      frequency outer outerJet transport mode modeJet time
      (houter time htime) (hmode time htime) (htransport time htime)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hvariation.add hcurrent)
  rw [intervalIntegral.integral_add hvariation hcurrent] at hftc
  linear_combination hftc

/-! ## Firing limits of future-blind and sub-viscous payment -/

/-- **[counterexample; formal-checked]** No scalar depending only on the initial curl can equal
the outer-Hodge endpoint difference for every possible terminal curl. -/
theorem no_initialCurl_only_outerHodge_endpoint_payment :
    ¬ ∃ payment : ComplexVector → ℂ, ∀ terminalCurl : ComplexVector,
      modeReceiverRebaseWitnessOuterCurlCovector terminalCurl -
          modeReceiverRebaseWitnessOuterCurlCovector 0 = payment 0 := by
  rintro ⟨payment, hpayment⟩
  have hzero := hpayment 0
  have hwitness := hpayment modeReceiverRebaseWitnessPhaseCurl
  have houterZero : modeReceiverRebaseWitnessOuterCurlCovector 0 = 0 := by
    have hhodge :
        nonzeroModeHodgeReconstruction modeReceiverRebaseWitnessOutput 0 = 0 := by
      change nonzeroModeHodgeReconstructionLinearMap
        modeReceiverRebaseWitnessOutput 0 = 0
      exact LinearMap.map_zero _
    simp [modeReceiverRebaseWitnessOuterCurlCovector, hhodge,
      NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol.normalizedPrincipalOuterInsertionFace,
      NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol.normalizedAdvectiveInteraction,
      complexDot]
  rw [houterZero, sub_zero, modeReceiverRebaseWitnessOuterCurlCovector_phase_eq_neg_one]
    at hwitness
  rw [houterZero, sub_self] at hzero
  rw [← hzero] at hwitness
  norm_num at hwitness

/-- **[counterexample; formal-checked]** At the retained zero-mode crossing, the outer-Hodge
horizontal current has norm one while every viscosity multiple of the mode square is zero.  Hence
the projective split alone cannot supply an amplitude-free pointwise sub-viscous payment. -/
theorem zeroCrossing_outerHodgeHorizontalCurrent_not_subViscous
    (viscosity : ℝ) :
    ¬ ‖modeReceiverRebaseWitnessOuterCurlCovector
          (ownModeHermitianHorizontalJet 0 modeReceiverRebaseWitnessPhaseCurl)‖ ≤
        viscosity * ‖(0 : ComplexVector)‖ ^ 2 := by
  rw [ownModeHermitianHorizontalJet_zero,
    modeReceiverRebaseWitnessOuterCurlCovector_phase_eq_neg_one]
  norm_num

section Audit

#print axioms ownModeHermitianConnection_gauge
#print axioms ownModeHermitianHorizontalJet_gauge
#print axioms hasDerivAt_parallelTransport_mode
#print axioms hasDerivAt_parallelTransport_zeroCrossing
#print axioms hasDerivAt_projectiveOuterHodgeBoundary
#print axioms integral_projectiveOuterHodgeHorizontalCurrent_eq_boundary_sub_variation
#print axioms no_initialCurl_only_outerHodge_endpoint_payment
#print axioms zeroCrossing_outerHodgeHorizontalCurrent_not_subViscous

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment
