import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment

/-!
# Exact length of the projectively transported vorticity mode

**[proved-derived; formal-checked]** For the division-free projective transport law already
owned by `NavierStokesPhysicalH2ProjectiveClockPayment`, put `z = w • Ω`.  Its derivative is
`w • H`, where `H` is the Hermitian-horizontal mode jet.  Hermitian orthogonality therefore
makes the Euclidean square of `z` exactly constant.  The statement includes the zero-mode chart
and makes no existence claim for the integrating scalar `w`.

The complete preimage fibre retains every factorization `z = w • Ω`.  When `w ≠ 0`
the mode is reconstructed by reciprocal scalar transport.  When `w = 0`, the transported target
is necessarily zero while the original mode is unrestricted; a constructor for every original
mode records this singular fibre explicitly.

No outer-boundary norm law, estimate, coercivity, transport existence, or Navier--Stokes closure
claim is made.
-/

noncomputable section

open scoped Interval BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveTransportLength

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
open Soma.Holonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockPayment
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Transported carrier and its exact quadratic receivers -/

/-- The literal projectively transported Fourier-vorticity mode `z = w • Ω`. -/
def projectivelyTransportedMode
    (transport : ℝ → ℂ) (mode : ℝ → ComplexVector) (time : ℝ) : ComplexVector :=
  transport time • mode time

/-- The Euclidean half-length square of a complex three-vector.  This is deliberately not the
ambient `Pi`-space supremum norm. -/
def projectiveTransportEuclideanHalfLengthSquare
    (transported : ComplexVector) : ℝ :=
  (1 / 2 : ℝ) * complexVectorEuclideanSquare transported

/-- The Hermitian presentation of the same half-length square. -/
def projectiveTransportHermitianHalfLengthSquare
    (transported : ComplexVector) : ℂ :=
  (1 / 2 : ℂ) * complexVectorHermitianPairing transported transported

theorem projectiveTransportHermitianHalfLengthSquare_eq_ofReal
    (transported : ComplexVector) :
    projectiveTransportHermitianHalfLengthSquare transported =
      (projectiveTransportEuclideanHalfLengthSquare transported : ℂ) := by
  rw [projectiveTransportHermitianHalfLengthSquare,
    projectiveTransportEuclideanHalfLengthSquare,
    complexVectorHermitianPairing_self_eq]
  norm_num

/-! ## Exact horizontal conservation -/

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

private theorem hermitianPairing_swap
    (left right : ComplexVector) :
    complexVectorHermitianPairing right left =
      (starRingEnd ℂ) (complexVectorHermitianPairing left right) := by
  unfold complexVectorHermitianPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- The derivative of the Hermitian square along real time. -/
private theorem hasDerivAt_complexVectorHermitianSquare
    {coefficient : ℝ → ComplexVector} {derivative : ComplexVector} {time : ℝ}
    (hcoefficient : HasDerivAt coefficient derivative time) :
    HasDerivAt
      (fun τ ↦ complexVectorHermitianPairing (coefficient τ) (coefficient τ))
      (complexVectorHermitianPairing derivative (coefficient time) +
        complexVectorHermitianPairing (coefficient time) derivative) time := by
  unfold complexVectorHermitianPairing
  have hcomponent : ∀ component : Fin 3,
      HasDerivAt
        (fun τ ↦ (starRingEnd ℂ) (coefficient τ component) *
          coefficient τ component)
        ((starRingEnd ℂ) (derivative component) * coefficient time component +
          (starRingEnd ℂ) (coefficient time component) * derivative component) time := by
    intro component
    have hcoordinate :=
      (((ContinuousLinearMap.proj component : ComplexVector →L[ℝ] ℂ).hasFDerivAt.comp
        time hcoefficient.hasFDerivAt).hasDerivAt)
    simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply_one,
          ContinuousLinearMap.proj_apply] at hcoordinate
    have hconjugate :=
      (Complex.conjCLE.hasFDerivAt.comp time hcoordinate.hasFDerivAt).hasDerivAt
    convert! hconjugate.mul hcoordinate using 1
    all_goals
      simp only [Function.comp_apply, Complex.conjCLE_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one,
        ContinuousLinearMap.proj_apply]
      rfl
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    fun component _hcomponent ↦ hcomponent component
  simpa only [Finset.sum_add_distrib] using hsum

private theorem transported_horizontal_pairing_eq_zero
    (transport : ℂ) (mode modeJet : ComplexVector) :
    complexVectorHermitianPairing
        (transport • mode)
        (transport • ownModeHermitianHorizontalJet mode modeJet) = 0 := by
  rw [hermitianPairing_smul_left, hermitianPairing_smul_right,
    ownModeHermitianHorizontalJet_eq_modeHermitianPhase,
    complexVectorHermitianPairing_modeHermitianPhase_eq_zero]
  ring

private theorem transported_horizontal_pairing_reverse_eq_zero
    (transport : ℂ) (mode modeJet : ComplexVector) :
    complexVectorHermitianPairing
        (transport • ownModeHermitianHorizontalJet mode modeJet)
        (transport • mode) = 0 := by
  rw [hermitianPairing_swap,
    transported_horizontal_pairing_eq_zero, map_zero]

/-- The projective transport law makes the Hermitian half-length derivative exactly zero.  No
nonzero-mode or nonzero-transport assumption is required. -/
theorem hasDerivAt_projectiveTransportHermitianHalfLengthSquare_zero
    (mode : ℝ → ComplexVector) (modeJet : ComplexVector)
    (transport : ℝ → ℂ) (time : ℝ)
    (hmode : HasDerivAt mode modeJet time)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time) modeJet * transport time) time) :
    HasDerivAt
      (fun clock ↦ projectiveTransportHermitianHalfLengthSquare
        (projectivelyTransportedMode transport mode clock)) 0 time := by
  have hparallel := hasDerivAt_parallelTransport_mode
    mode modeJet transport time hmode htransport
  have hsquare := hasDerivAt_complexVectorHermitianSquare hparallel
  have hhalf := hsquare.const_mul (1 / 2 : ℂ)
  apply hhalf.congr_deriv
  rw [transported_horizontal_pairing_reverse_eq_zero,
    transported_horizontal_pairing_eq_zero]
  ring

/-- The real Euclidean half-length derivative is exactly zero. -/
theorem hasDerivAt_projectiveTransportEuclideanHalfLengthSquare_zero
    (mode : ℝ → ComplexVector) (modeJet : ComplexVector)
    (transport : ℝ → ℂ) (time : ℝ)
    (hmode : HasDerivAt mode modeJet time)
    (htransport : HasDerivAt transport
      (-ownModeHermitianConnection (mode time) modeJet * transport time) time) :
    HasDerivAt
      (fun clock ↦ projectiveTransportEuclideanHalfLengthSquare
        (projectivelyTransportedMode transport mode clock)) 0 time := by
  have hhermitian :=
    hasDerivAt_projectiveTransportHermitianHalfLengthSquare_zero
      mode modeJet transport time hmode htransport
  have hreal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hhermitian
  have hreal' : HasDerivAt
      (fun clock ↦
        (projectiveTransportHermitianHalfLengthSquare
          (projectivelyTransportedMode transport mode clock)).re)
      (0 : ℂ).re time := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using hreal
  simpa only [projectiveTransportHermitianHalfLengthSquare_eq_ofReal,
    Complex.ofReal_re, Complex.zero_re] using hreal'

/-! ## Interval constancy and unit-square propagation -/

/-- Exact endpoint constancy on an unoriented interval. -/
theorem projectiveTransportEuclideanHalfLengthSquare_eq_on_uIcc
    (mode modeJet : ℝ → ComplexVector) (transport : ℝ → ℂ) (a b : ℝ)
    (hmode : ∀ time ∈ Set.uIcc a b,
      HasDerivAt mode (modeJet time) time)
    (htransport : ∀ time ∈ Set.uIcc a b,
      HasDerivAt transport
        (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time) :
    projectiveTransportEuclideanHalfLengthSquare
        (projectivelyTransportedMode transport mode b) =
      projectiveTransportEuclideanHalfLengthSquare
        (projectivelyTransportedMode transport mode a) := by
  have hderiv : ∀ time ∈ Set.uIcc a b,
      HasDerivAt
        (fun clock ↦ projectiveTransportEuclideanHalfLengthSquare
          (projectivelyTransportedMode transport mode clock)) 0 time := by
    intro time htime
    exact hasDerivAt_projectiveTransportEuclideanHalfLengthSquare_zero
      mode (modeJet time) transport time (hmode time htime) (htransport time htime)
  have hzero : IntervalIntegrable (fun _time : ℝ ↦ (0 : ℝ))
      MeasureTheory.volume a b := intervalIntegrable_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hzero
  simpa only [intervalIntegral.integral_zero, sub_eq_zero] using hftc.symm

/-- A unit Euclidean square at one endpoint remains a unit Euclidean square at the other.  This
uses the squared length directly and introduces no square-root chart. -/
theorem projectiveTransportEuclideanSquare_eq_one
    (mode modeJet : ℝ → ComplexVector) (transport : ℝ → ℂ) (a b : ℝ)
    (hmode : ∀ time ∈ Set.uIcc a b,
      HasDerivAt mode (modeJet time) time)
    (htransport : ∀ time ∈ Set.uIcc a b,
      HasDerivAt transport
        (-ownModeHermitianConnection (mode time) (modeJet time) * transport time) time)
    (hunit : complexVectorEuclideanSquare
      (projectivelyTransportedMode transport mode a) = 1) :
    complexVectorEuclideanSquare
      (projectivelyTransportedMode transport mode b) = 1 := by
  have hhalf := projectiveTransportEuclideanHalfLengthSquare_eq_on_uIcc
    mode modeJet transport a b hmode htransport
  unfold projectiveTransportEuclideanHalfLengthSquare at hhalf
  linarith

/-! ## Complete preimage fibre -/

/-- Every scalar/mode factorization of one transported carrier. -/
def ProjectiveTransportPreimageFibre
    (transported : ComplexVector) :=
  { occurrence : ℂ × ComplexVector // occurrence.1 • occurrence.2 = transported }

/-- The literal scalar and original mode inhabit the complete fibre over their transported mode. -/
def projectiveTransportPreimageOccurrence
    (transport : ℂ) (mode : ComplexVector) :
    ProjectiveTransportPreimageFibre (transport • mode) :=
  ⟨(transport, mode), rfl⟩

/-- On a regular scalar chart, the fibre reconstructs its original mode by reciprocal transport. -/
theorem ProjectiveTransportPreimageFibre.mode_eq_inv_smul
    {transported : ComplexVector}
    (occurrence : ProjectiveTransportPreimageFibre transported)
    (htransport : occurrence.1.1 ≠ 0) :
    occurrence.1.2 = occurrence.1.1⁻¹ • transported := by
  calc
    occurrence.1.2 = (occurrence.1.1⁻¹ * occurrence.1.1) • occurrence.1.2 := by
      simp [htransport]
    _ = occurrence.1.1⁻¹ • (occurrence.1.1 • occurrence.1.2) := by
      rw [smul_smul]
    _ = occurrence.1.1⁻¹ • transported := by
      rw [occurrence.property]

/-- If a preimage occurrence has zero scalar, its transported target is forced to zero. -/
theorem ProjectiveTransportPreimageFibre.target_eq_zero_of_transport_eq_zero
    {transported : ComplexVector}
    (occurrence : ProjectiveTransportPreimageFibre transported)
    (htransport : occurrence.1.1 = 0) :
    transported = 0 := by
  rw [← occurrence.property, htransport, zero_smul]

/-- Every original mode, without restriction, survives as a distinct occurrence in the singular
zero-scalar preimage fibre. -/
def singularProjectiveTransportPreimageOccurrence
    (mode : ComplexVector) : ProjectiveTransportPreimageFibre 0 :=
  ⟨(0, mode), by simp⟩

@[simp]
theorem singularProjectiveTransportPreimageOccurrence_transport
    (mode : ComplexVector) :
    (singularProjectiveTransportPreimageOccurrence mode).1.1 = 0 := rfl

@[simp]
theorem singularProjectiveTransportPreimageOccurrence_mode
    (mode : ComplexVector) :
    (singularProjectiveTransportPreimageOccurrence mode).1.2 = mode := rfl

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveTransportLength
