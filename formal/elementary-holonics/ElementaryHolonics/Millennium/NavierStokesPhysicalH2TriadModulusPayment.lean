import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The modulus payment for one physical H2 triad

**[proved-derived; formal-checked]**  This module takes the actual completed exchanged triad
face, its three-leg physical source insertion, and its positive Stokes triad clock from
`NavierStokesPhysicalH2ClockedTriadNormalForm`.  It keeps the full complex face before taking its
norm.  A smooth modulus

`sqrt (‖F‖ ^ 2 + epsilon ^ 2)`

retains every zero crossing and proves the Kato inequality without asserting differentiability of
the ordinary norm there.  Compact integration and the limit `epsilon -> 0` then pay the complete
one-address modulus by the initial face and the time-integrated modulus of the actual source.

The terminal modulus is retained in the strongest inequality and is dropped only by
nonnegativity in a separate corollary.  This is an addresswise compact-interior payment.  It makes
no scale-summability, packing, critical terminal-control, or continuation claim.
-/

noncomputable section

open Function MeasureTheory Set
open scoped Interval RealInnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2TriadModulusPayment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## A zero-retaining regularized modulus -/

/-- The smooth modulus used at a possibly vanishing complex face. -/
def regularizedComplexModulus (epsilon : ℝ) (face : ℂ) : ℝ :=
  Real.sqrt (‖face‖ ^ 2 + epsilon ^ 2)

/-- The time jet of the regularized modulus, written through the real inner-product receiver. -/
def regularizedComplexModulusRate
    (epsilon : ℝ) (face faceJet : ℂ) : ℝ :=
  inner ℝ face faceJet / regularizedComplexModulus epsilon face

theorem regularizedComplexModulus_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (face : ℂ) :
    0 < regularizedComplexModulus epsilon face := by
  unfold regularizedComplexModulus
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖face‖]

theorem norm_le_regularizedComplexModulus
    {epsilon : ℝ} (face : ℂ) :
    ‖face‖ ≤ regularizedComplexModulus epsilon face := by
  unfold regularizedComplexModulus
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg epsilon])

theorem epsilon_le_regularizedComplexModulus
    {epsilon : ℝ} (face : ℂ) :
    epsilon ≤ regularizedComplexModulus epsilon face := by
  unfold regularizedComplexModulus
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖face‖])

theorem regularizedComplexModulus_le_norm_add
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (face : ℂ) :
    regularizedComplexModulus epsilon face ≤ ‖face‖ + epsilon := by
  have hright : 0 ≤ ‖face‖ + epsilon := add_nonneg (norm_nonneg face) hepsilon
  unfold regularizedComplexModulus
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [mul_nonneg (norm_nonneg face) hepsilon]

/-- The regularized modulus is differentiable even when the complex face vanishes. -/
theorem hasDerivAt_regularizedComplexModulus
    {path : ℝ → ℂ} {pathJet : ℂ} {time epsilon : ℝ}
    (hpath : HasDerivAt path pathJet time) (hepsilon : 0 < epsilon) :
    HasDerivAt
      (fun tau ↦ regularizedComplexModulus epsilon (path tau))
      (regularizedComplexModulusRate epsilon (path time) pathJet) time := by
  have hinside : HasDerivAt
      (fun tau ↦ ‖path tau‖ ^ 2 + epsilon ^ 2)
      (2 * inner ℝ (path time) pathJet) time :=
    hpath.norm_sq.add_const (epsilon ^ 2)
  have hinsideNe : ‖path time‖ ^ 2 + epsilon ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ‖path time‖, sq_pos_of_pos hepsilon]
  have hsqrt := hinside.sqrt hinsideNe
  unfold regularizedComplexModulus regularizedComplexModulusRate
  convert hsqrt using 1
  rw [regularizedComplexModulus]
  field_simp [Real.sqrt_ne_zero'.mpr (by positivity :
    0 < ‖path time‖ ^ 2 + epsilon ^ 2)]

/-! ## The regularized Kato inequality -/

/-- Pointwise Kato inequality for a complex clocked face.  The formula includes zero faces because
the denominator is the positive regularized modulus. -/
theorem regularizedComplexModulusRate_add_clock_le
    {epsilon clock : ℝ} (hepsilon : 0 < epsilon) (hclock : 0 ≤ clock)
    (face source : ℂ) :
    regularizedComplexModulusRate epsilon face
          (source - ((clock : ℝ) : ℂ) * face) +
        clock * regularizedComplexModulus epsilon face ≤
      ‖source‖ + clock * epsilon := by
  let modulus := regularizedComplexModulus epsilon face
  have hmodulusPos : 0 < modulus :=
    regularizedComplexModulus_pos hepsilon face
  have hmodulusNe : modulus ≠ 0 := hmodulusPos.ne'
  have hfaceLe : ‖face‖ ≤ modulus :=
    norm_le_regularizedComplexModulus face
  have hepsilonLe : epsilon ≤ modulus :=
    epsilon_le_regularizedComplexModulus face
  have hmodulusSq : modulus ^ 2 = ‖face‖ ^ 2 + epsilon ^ 2 := by
    unfold modulus regularizedComplexModulus
    exact Real.sq_sqrt (by positivity)
  have hdamping : (((clock : ℝ) : ℂ) * face) = clock • face := by
    rw [Complex.real_smul]
  have hinnerODE :
      inner ℝ face (source - ((clock : ℝ) : ℂ) * face) =
        inner ℝ face source - clock * ‖face‖ ^ 2 := by
    rw [hdamping, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have hinnerBound : inner ℝ face source ≤ modulus * ‖source‖ := by
    exact (real_inner_le_norm face source).trans
      (mul_le_mul_of_nonneg_right hfaceLe (norm_nonneg source))
  have hepsilonSqLe : epsilon ^ 2 ≤ epsilon * modulus := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hepsilonLe hepsilon.le
  have hclockEpsilonSqLe :
      clock * epsilon ^ 2 ≤ clock * epsilon * modulus := by
    calc
      clock * epsilon ^ 2 ≤ clock * (epsilon * modulus) :=
        mul_le_mul_of_nonneg_left hepsilonSqLe hclock
      _ = clock * epsilon * modulus := by ring
  unfold regularizedComplexModulusRate
  change
    inner ℝ face (source - ((clock : ℝ) : ℂ) * face) / modulus +
        clock * modulus ≤ ‖source‖ + clock * epsilon
  rw [hinnerODE]
  calc
    (inner ℝ face source - clock * ‖face‖ ^ 2) / modulus + clock * modulus =
        (inner ℝ face source + clock * epsilon ^ 2) / modulus := by
      field_simp [hmodulusNe]
      nlinarith [hmodulusSq]
    _ ≤ (modulus * ‖source‖ + clock * epsilon * modulus) / modulus :=
      div_le_div_of_nonneg_right
        (add_le_add hinnerBound hclockEpsilonSqLe) hmodulusPos.le
    _ = ‖source‖ + clock * epsilon := by
      field_simp [hmodulusNe]

/-! ## Compact integration before removing the regularization -/

/-- The exact compact payment for the smooth modulus.  Its only defect is the displayed,
quantified regularization residue. -/
theorem regularizedComplexModulus_compact_payment
    {sourceTime targetTime epsilon clock : ℝ} {face source : ℝ → ℂ}
    (htimes : sourceTime ≤ targetTime) (hepsilon : 0 < epsilon)
    (hclock : 0 ≤ clock)
    (hODE : ∀ time ∈ Icc sourceTime targetTime,
      HasDerivAt face
        (source time - ((clock : ℝ) : ℂ) * face time) time)
    (hsource : ContinuousOn source (Icc sourceTime targetTime))
    (hsourceIntegrable :
      IntervalIntegrable source volume sourceTime targetTime) :
    regularizedComplexModulus epsilon (face targetTime) +
        clock * (∫ time in sourceTime..targetTime,
          regularizedComplexModulus epsilon (face time)) ≤
      regularizedComplexModulus epsilon (face sourceTime) +
        (∫ time in sourceTime..targetTime, ‖source time‖) +
          clock * epsilon * (targetTime - sourceTime) := by
  have hface : ContinuousOn face (Icc sourceTime targetTime) := by
    intro time htime
    exact (hODE time htime).continuousAt.continuousWithinAt
  have hregularized : ContinuousOn
      (fun time ↦ regularizedComplexModulus epsilon (face time))
      (Icc sourceTime targetTime) := by
    intro time htime
    exact (hasDerivAt_regularizedComplexModulus
      (hODE time htime) hepsilon).continuousAt.continuousWithinAt
  have hjet : ContinuousOn
      (fun time ↦ source time - ((clock : ℝ) : ℂ) * face time)
      (Icc sourceTime targetTime) := by
    exact hsource.sub
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ ↦ ((clock : ℝ) : ℂ)) (Icc sourceTime targetTime)).mul hface)
  have hinner : ContinuousOn
      (fun time ↦ inner ℝ (face time)
        (source time - ((clock : ℝ) : ℂ) * face time))
      (Icc sourceTime targetTime) :=
    hface.inner hjet
  have hrate : ContinuousOn
      (fun time ↦ regularizedComplexModulusRate epsilon (face time)
        (source time - ((clock : ℝ) : ℂ) * face time))
      (Icc sourceTime targetTime) := by
    unfold regularizedComplexModulusRate
    exact hinner.div hregularized
      (fun time _htime ↦
        (regularizedComplexModulus_pos hepsilon (face time)).ne')
  have hrateIntegrable : IntervalIntegrable
      (fun time ↦ regularizedComplexModulusRate epsilon (face time)
        (source time - ((clock : ℝ) : ℂ) * face time))
      volume sourceTime targetTime := by
    have hrate' : ContinuousOn
        (fun time ↦ regularizedComplexModulusRate epsilon (face time)
          (source time - ((clock : ℝ) : ℂ) * face time))
        (uIcc sourceTime targetTime) := by
      simpa only [uIcc_of_le htimes] using hrate
    exact hrate'.intervalIntegrable
  have hregularizedIntegrable : IntervalIntegrable
      (fun time ↦ regularizedComplexModulus epsilon (face time))
      volume sourceTime targetTime := by
    have hregularized' : ContinuousOn
        (fun time ↦ regularizedComplexModulus epsilon (face time))
        (uIcc sourceTime targetTime) := by
      simpa only [uIcc_of_le htimes] using hregularized
    exact hregularized'.intervalIntegrable
  have hsourceNormIntegrable : IntervalIntegrable
      (fun time ↦ ‖source time‖) volume sourceTime targetTime :=
    hsourceIntegrable.norm
  have hderivativeIntegral :
      (∫ time in sourceTime..targetTime,
          regularizedComplexModulusRate epsilon (face time)
            (source time - ((clock : ℝ) : ℂ) * face time)) =
        regularizedComplexModulus epsilon (face targetTime) -
          regularizedComplexModulus epsilon (face sourceTime) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro time htime
      have htimeIcc : time ∈ Icc sourceTime targetTime := by
        simpa only [uIcc_of_le htimes] using htime
      exact hasDerivAt_regularizedComplexModulus
        (hODE time htimeIcc) hepsilon
    · exact hrateIntegrable
  have hpointwise (time : ℝ) :
      regularizedComplexModulusRate epsilon (face time)
            (source time - ((clock : ℝ) : ℂ) * face time) +
          clock * regularizedComplexModulus epsilon (face time) ≤
        ‖source time‖ + clock * epsilon :=
    regularizedComplexModulusRate_add_clock_le hepsilon hclock
      (face time) (source time)
  have hintegral := intervalIntegral.integral_mono_on htimes
    (hrateIntegrable.add (hregularizedIntegrable.const_mul clock))
    (hsourceNormIntegrable.add intervalIntegrable_const)
    (fun time _htime ↦ hpointwise time)
  rw [intervalIntegral.integral_add hrateIntegrable
        (hregularizedIntegrable.const_mul clock),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hsourceNormIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const] at hintegral
  rw [hderivativeIntegral] at hintegral
  simp only [smul_eq_mul] at hintegral
  nlinarith

/-! ## Removing the regularization -/

/-- Kato's compact modulus payment for a complex path satisfying a clocked ODE.  The terminal
modulus remains on the left; no zero of the path is deleted. -/
theorem complexModulus_compact_payment_of_clockedODE
    {sourceTime targetTime clock : ℝ} {face source : ℝ → ℂ}
    (htimes : sourceTime ≤ targetTime) (hclock : 0 ≤ clock)
    (hODE : ∀ time ∈ Icc sourceTime targetTime,
      HasDerivAt face
        (source time - ((clock : ℝ) : ℂ) * face time) time)
    (hsource : ContinuousOn source (Icc sourceTime targetTime))
    (hsourceIntegrable :
      IntervalIntegrable source volume sourceTime targetTime) :
    ‖face targetTime‖ +
        clock * (∫ time in sourceTime..targetTime, ‖face time‖) ≤
      ‖face sourceTime‖ +
        ∫ time in sourceTime..targetTime, ‖source time‖ := by
  have hface : ContinuousOn face (Icc sourceTime targetTime) := by
    intro time htime
    exact (hODE time htime).continuousAt.continuousWithinAt
  have hfaceNormIntegrable : IntervalIntegrable
      (fun time ↦ ‖face time‖) volume sourceTime targetTime := by
    have hfaceNorm : ContinuousOn (fun time ↦ ‖face time‖)
        (uIcc sourceTime targetTime) := by
      simpa only [uIcc_of_le htimes] using hface.norm
    exact hfaceNorm.intervalIntegrable
  refine le_of_forall_pos_le_add ?_
  intro residue hresidue
  let coefficient := 1 + clock * (targetTime - sourceTime)
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    nlinarith [mul_nonneg hclock (sub_nonneg.mpr htimes)]
  have hcoefficientNe : coefficient ≠ 0 := hcoefficientPos.ne'
  let epsilon := residue / coefficient
  have hepsilon : 0 < epsilon := div_pos hresidue hcoefficientPos
  have hregularizedPayment :=
    regularizedComplexModulus_compact_payment
      htimes hepsilon hclock hODE hsource hsourceIntegrable
  have hregularized : ContinuousOn
      (fun time ↦ regularizedComplexModulus epsilon (face time))
      (Icc sourceTime targetTime) := by
    intro time htime
    exact (hasDerivAt_regularizedComplexModulus
      (hODE time htime) hepsilon).continuousAt.continuousWithinAt
  have hregularizedIntegrable : IntervalIntegrable
      (fun time ↦ regularizedComplexModulus epsilon (face time))
      volume sourceTime targetTime := by
    have hregularized' : ContinuousOn
        (fun time ↦ regularizedComplexModulus epsilon (face time))
        (uIcc sourceTime targetTime) := by
      simpa only [uIcc_of_le htimes] using hregularized
    exact hregularized'.intervalIntegrable
  have hintegralLe :
      (∫ time in sourceTime..targetTime, ‖face time‖) ≤
        ∫ time in sourceTime..targetTime,
          regularizedComplexModulus epsilon (face time) :=
    intervalIntegral.integral_mono_on htimes hfaceNormIntegrable
      hregularizedIntegrable
      (fun time _htime ↦ norm_le_regularizedComplexModulus (face time))
  have hleftLe :
      ‖face targetTime‖ +
          clock * (∫ time in sourceTime..targetTime, ‖face time‖) ≤
        regularizedComplexModulus epsilon (face targetTime) +
          clock * (∫ time in sourceTime..targetTime,
            regularizedComplexModulus epsilon (face time)) :=
    add_le_add (norm_le_regularizedComplexModulus (face targetTime))
      (mul_le_mul_of_nonneg_left hintegralLe hclock)
  have hinitialLe :
      regularizedComplexModulus epsilon (face sourceTime) ≤
        ‖face sourceTime‖ + epsilon :=
    regularizedComplexModulus_le_norm_add hepsilon.le (face sourceTime)
  have hepsilonCoefficient : epsilon * coefficient = residue := by
    exact div_mul_cancel₀ residue hcoefficientNe
  calc
    ‖face targetTime‖ +
          clock * (∫ time in sourceTime..targetTime, ‖face time‖) ≤
        regularizedComplexModulus epsilon (face targetTime) +
          clock * (∫ time in sourceTime..targetTime,
            regularizedComplexModulus epsilon (face time)) := hleftLe
    _ ≤ regularizedComplexModulus epsilon (face sourceTime) +
          (∫ time in sourceTime..targetTime, ‖source time‖) +
            clock * epsilon * (targetTime - sourceTime) := hregularizedPayment
    _ ≤ (‖face sourceTime‖ + epsilon) +
          (∫ time in sourceTime..targetTime, ‖source time‖) +
            clock * epsilon * (targetTime - sourceTime) := by
      gcongr
    _ = (‖face sourceTime‖ +
          ∫ time in sourceTime..targetTime, ‖source time‖) + residue := by
      dsimp only [coefficient] at hepsilonCoefficient
      nlinarith

/-! ## The actual completed exchanged physical-H2 triad -/

/-- The compactly totalized three-leg source insertion is continuous on its physical compact
interval.  Its interval integrability remains supplied by the existing normal-form owner. -/
theorem continuousOn_compactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    ContinuousOn
      (compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address)
      (Icc sourceTime targetTime) := by
  let interval := Icc sourceTime targetTime
  have hvelocity (frequency : SpatialFrequency) :
      ContinuousOn (velocityMode velocity frequency) interval :=
    continuousOn_velocityMode_compactInterior
      solution hsource htimes htarget frequency
  have hprojectedSource (frequency : SpatialFrequency) :
      ContinuousOn
        (compactOpenProjectedVelocityNonlinearMode
          solution hsource htimes htarget frequency) interval :=
    (continuous_compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency).continuousOn
  have hfirst := continuousOn_triadicEnergyFace address.1 address.2
    (hprojectedSource address.1) (hvelocity address.2)
    (hvelocity (completeTransportReceiver address))
  have hsecond := continuousOn_triadicEnergyFace address.1 address.2
    (hvelocity address.1) (hprojectedSource address.2)
    (hvelocity (completeTransportReceiver address))
  have hthird := continuousOn_triadicEnergyFace address.1 address.2
    (hvelocity address.1) (hvelocity address.2)
    (hprojectedSource (completeTransportReceiver address))
  have hscaled :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ ↦ physicalH2ExchangedTriadMultiplier address) interval).mul
      ((hfirst.add hsecond).add hthird)
  change ContinuousOn (fun time ↦
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.1 time)
            (velocityMode velocity address.2 time)
            (velocityMode velocity (completeTransportReceiver address) time) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 time)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.2 time)
            (velocityMode velocity (completeTransportReceiver address) time) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 time)
            (velocityMode velocity address.2 time)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget
                (completeTransportReceiver address) time))) interval
  exact hscaled

/-- **One-address physical-H2 triad modulus payment.**  For a nontrivial transport address and
positive viscosity, the positive three-mode Stokes clock pays the time-integrated modulus of the
actual completed exchanged face by its initial modulus plus the modulus of the actual three-leg
projected nonlinear source.  The terminal modulus is retained. -/
theorem openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_modulus_payment
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0)) :
    ‖physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency targetTime) address‖ +
      physicalH2TriadStokesClock nu address *
        (∫ time in sourceTime..targetTime,
          ‖physicalH2VelocityExchangedTriadFace
            (fun frequency ↦ velocityMode velocity frequency time) address‖) ≤
    ‖physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency sourceTime) address‖ +
      ∫ time in sourceTime..targetTime,
        ‖compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address time‖ := by
  let face : ℝ → ℂ := fun time ↦
    physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency time) address
  let source : ℝ → ℂ :=
    compactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address
  let clock := physicalH2TriadStokesClock nu address
  have hclockPos : 0 < clock :=
    physicalH2TriadStokesClock_pos_of_address_ne_zero hnu address haddress
  have hODE : ∀ time ∈ Icc sourceTime targetTime,
      HasDerivAt face
        (source time - ((clock : ℝ) : ℂ) * face time) time := by
    intro time htime
    have hnamed :=
      openPeriodicSolutionOn_hasDerivAt_compactClockedPhysicalH2VelocityExchangedTriadRate
        solution hsource htimes htarget htime address
    simpa only [face, source, clock,
      compactClockedPhysicalH2VelocityExchangedTriadRate] using hnamed
  have hsourceContinuous : ContinuousOn source (Icc sourceTime targetTime) := by
    exact continuousOn_compactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address
  have hsourceIntegrable :
      IntervalIntegrable source volume sourceTime targetTime := by
    exact intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address
  simpa only [face, source, clock] using
    complexModulus_compact_payment_of_clockedODE
      htimes hclockPos.le hODE hsourceContinuous hsourceIntegrable

/-- The requested payment after dropping the terminal modulus only by its nonnegativity. -/
theorem openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_clock_mul_integral_modulus_le
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0)) :
    physicalH2TriadStokesClock nu address *
        (∫ time in sourceTime..targetTime,
          ‖physicalH2VelocityExchangedTriadFace
            (fun frequency ↦ velocityMode velocity frequency time) address‖) ≤
      ‖physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency sourceTime) address‖ +
      ∫ time in sourceTime..targetTime,
        ‖compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address time‖ := by
  have hpayment :=
    openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_modulus_payment
      solution hnu hsource htimes htarget address haddress
  nlinarith [norm_nonneg
    (physicalH2VelocityExchangedTriadFace
      (fun frequency ↦ velocityMode velocity frequency targetTime) address)]

section Audit

#print axioms hasDerivAt_regularizedComplexModulus
#print axioms regularizedComplexModulusRate_add_clock_le
#print axioms regularizedComplexModulus_compact_payment
#print axioms complexModulus_compact_payment_of_clockedODE
#print axioms openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_modulus_payment
#print axioms openPeriodicSolutionOn_physicalH2VelocityExchangedTriad_clock_mul_integral_modulus_le

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2TriadModulusPayment
