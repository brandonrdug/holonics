import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin

/-!
# Clocked physical-H2 triad normal form

This owner differentiates one signed, actual velocity-triad face of an admitted unforced open
periodic solution.  The construction first derives the missing pressure-free velocity-mode ODE by
applying the Fourier Leray passage to the actual strong modal equation.  It then differentiates the
three addressed mode occurrences before any norm or real-part receiver is taken.

The result exposes the exact Stokes clock

`nu * (lambda(p) + lambda(q) + lambda(r))`

beside the three nonlinear source-insertion residues.  The Leray construction treats the zero
mode by its identity branch, so no inverse curl or division by a zero frequency is used.  This is a
strict-interior differential identity together with its compact-interval integral normal form; it
makes no continuation claim.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The Leray passage as an actual linear receiver -/

/-- The modewise Leray face is complex-linear, including its identity branch at frequency zero. -/
def lerayProjectModeLinearMap (frequency : SpatialFrequency) :
    ComplexVector →ₗ[ℂ] ComplexVector where
  toFun := lerayProjectMode frequency
  map_add' left right := by
    by_cases hfrequency : frequency = 0
    · subst frequency
      simp
    · ext component
      simp only [lerayProjectMode, if_neg hfrequency, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      simp only [complexDot, dotProduct_add]
      ring
  map_smul' scale mode := by
    by_cases hfrequency : frequency = 0
    · subst frequency
      simp
    · ext component
      simp only [lerayProjectMode, if_neg hfrequency, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
      simp only [complexDot, dotProduct_smul]
      simp only [RingHom.id_apply]
      ring

/-- The finite-dimensional continuous-linear Leray receiver over the complex carrier. -/
def lerayProjectModeCLM (frequency : SpatialFrequency) :
    ComplexVector →L[ℂ] ComplexVector :=
  LinearMap.toContinuousLinearMap (lerayProjectModeLinearMap frequency)

@[simp]
theorem lerayProjectModeCLM_apply
    (frequency : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectModeCLM frequency mode = lerayProjectMode frequency mode := rfl

/-- The same receiver restricted to real scalars for differentiation along physical time. -/
def lerayProjectModeRealCLM (frequency : SpatialFrequency) :
    ComplexVector →L[ℝ] ComplexVector :=
  (lerayProjectModeCLM frequency).restrictScalars ℝ

@[simp]
theorem lerayProjectModeRealCLM_apply
    (frequency : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectModeRealCLM frequency mode = lerayProjectMode frequency mode := rfl

/-- A transverse mode is fixed by the Leray receiver.  The frequency-zero branch is discharged
without division. -/
theorem lerayProjectMode_eq_self_of_complexDot_eq_zero
    (frequency : SpatialFrequency) (mode : ComplexVector)
    (htransverse :
      complexDot (complexFrequencyVector frequency) mode = 0) :
    lerayProjectMode frequency mode = mode := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    simp
  · rw [lerayProjectMode, if_neg hfrequency, htransverse]
    simp

/-- Every longitudinal mode lies in the Leray radical.  Nonzero frequencies use the exact
frequency-square identity; the zero branch is again handled without division. -/
theorem lerayProjectMode_smul_complexFrequencyVector_eq_zero
    (frequency : SpatialFrequency) (scale : ℂ) :
    lerayProjectMode frequency
        (scale • complexFrequencyVector frequency) = 0 := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [lerayProjectMode_zero]
    ext component
    simp [complexFrequencyVector]
  · have hfrequencySquared : (frequencySquared frequency : ℂ) ≠ 0 := by
      exact_mod_cast (frequencySquared_pos hfrequency).ne'
    rw [lerayProjectMode, if_neg hfrequency]
    have hdot :
        complexDot (complexFrequencyVector frequency)
            (scale • complexFrequencyVector frequency) =
          scale * (frequencySquared frequency : ℂ) := by
      simp only [complexDot, dotProduct_smul, smul_eq_mul]
      change scale * complexDot (complexFrequencyVector frequency)
        (complexFrequencyVector frequency) = _
      rw [complexDot_frequency_self]
    rw [hdot]
    ext component
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    field_simp
    ring_nf

/-! ## Exact pressure-free velocity-mode ODE -/

/-- The actual pressure-gradient coefficient is longitudinal.  Its scalar coefficient is retained
as a reconstruction witness rather than being identified with the vector mode. -/
theorem openPressureGradientMode_is_longitudinal
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    ∃ scale : ℂ, openPressureGradientMode solution t frequency =
      scale • complexFrequencyVector frequency := by
  let scalarMode := scalarFourierMode (fun x ↦ pressure x t.1)
    (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2).continuous
    (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) frequency
  refine ⟨unitTorusCurlScale * scalarMode, ?_⟩
  rw [openPressureGradientMode,
    vectorSpatialFourierCoeff_gradient_eq_frequency
      (fun x ↦ pressure x t.1)
      (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2)
      (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) frequency]
  ext component
  simp only [Pi.smul_apply, smul_eq_mul, complexFrequencyVector]
  dsimp [scalarMode]
  simp only [unitTorusCurlScale]
  simp [frequencyCurlMultiplier, complexCross, crossProduct, complexFrequencyVector]
  ring

/-- Leray annihilates the actual pressure-gradient coefficient at every frequency, including the
mean mode. -/
theorem lerayProjectMode_openPressureGradientMode_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    lerayProjectMode frequency (openPressureGradientMode solution t frequency) = 0 := by
  obtain ⟨scale, hscale⟩ :=
    openPressureGradientMode_is_longitudinal solution t frequency
  rw [hscale, lerayProjectMode_smul_complexFrequencyVector_eq_zero]

/-- The signed nonlinear insertion in the pressure-free velocity equation.  It is the literal
Leray projection of the actual open-solution advection coefficient. -/
def openProjectedVelocityNonlinearMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) : ComplexVector :=
  -lerayProjectMode frequency (openActualAdvectionMode solution t frequency)

/-- **Actual pressure-free velocity-mode ODE.**  It is derived from the strong modal derivative,
not postulated.  No inverse-curl chart is used, so the identity includes the zero mode. -/
theorem openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    HasDerivAt (velocityMode velocity frequency)
      (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
          velocityMode velocity frequency t.1 +
        openProjectedVelocityNonlinearMode solution t frequency) t.1 := by
  have hraw := openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced
    solution t.2 frequency
  have hprojected :=
    (lerayProjectModeRealCLM frequency).hasFDerivAt.comp_hasDerivAt t.1 hraw
  have hfunction :
      Filter.EventuallyEq (nhds t.1)
        (velocityMode velocity frequency)
        ((lerayProjectModeRealCLM frequency) ∘ velocityMode velocity frequency) := by
    filter_upwards [Ioo_mem_nhds t.2.1 t.2.2] with τ hτ
    exact (lerayProjectMode_eq_self_of_complexDot_eq_zero frequency
      (velocityMode velocity frequency τ)
      (openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
        solution ⟨τ, hτ⟩ frequency)).symm
  have hphysical := hprojected.congr_of_eventuallyEq hfunction
  have hpressure :=
    lerayProjectMode_openPressureGradientMode_eq_zero solution t frequency
  have hvalue :
      lerayProjectMode frequency
          (unforcedMomentumMode nu velocity pressure frequency t.1) =
        (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
            velocityMode velocity frequency t.1 +
          openProjectedVelocityNonlinearMode solution t frequency) := by
    have hfree := pressureFreeMomentumMode_eq_viscous_sub_advection
      solution t frequency
    have hlaplacian := openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes
      solution t frequency
    have hpressureFree :
        lerayProjectMode frequency
            (unforcedMomentumMode nu velocity pressure frequency t.1) =
          lerayProjectMode frequency (pressureFreeMomentumMode solution t frequency) := by
      rw [pressureFreeMomentumMode]
      change lerayProjectModeRealCLM frequency
          (unforcedMomentumMode nu velocity pressure frequency t.1) =
        lerayProjectModeRealCLM frequency
          (unforcedMomentumMode nu velocity pressure frequency t.1 +
            openPressureGradientMode solution t frequency)
      rw [map_add]
      simp only [lerayProjectModeRealCLM_apply, hpressure, add_zero]
    rw [hpressureFree, hfree, hlaplacian]
    change lerayProjectModeCLM frequency
        ((nu : ℂ) • (-(torusStokesEigenvalue frequency : ℂ) •
          velocityMode velocity frequency t.1) - openAdvectionMode solution t frequency) = _
    rw [map_sub, map_smul, map_smul]
    rw [lerayProjectModeCLM_apply,
      lerayProjectMode_eq_self_of_complexDot_eq_zero frequency
        (velocityMode velocity frequency t.1)
        (openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
          solution t frequency)]
    rw [openAdvectionMode_eq_openActualAdvectionMode]
    simp only [openProjectedVelocityNonlinearMode, lerayProjectModeCLM_apply]
    ext component
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    push_cast
    ring
  change HasDerivAt (velocityMode velocity frequency)
    (lerayProjectMode frequency
      (unforcedMomentumMode nu velocity pressure frequency t.1)) t.1 at hphysical
  rw [hvalue] at hphysical
  exact hphysical

/-! ## Differentiating the addressed trilinear face -/

/-- The complex dot receiver with its left occurrence fixed. -/
def complexDotRightLinearMap (left : ComplexVector) : ComplexVector →ₗ[ℂ] ℂ where
  toFun := complexDot left
  map_add' first second := by
    simp [complexDot, dotProduct_add]
  map_smul' scale mode := by
    simp [complexDot, dotProduct_smul]

/-- Continuous-linear form of the fixed-left complex dot receiver. -/
def complexDotRightCLM (left : ComplexVector) : ComplexVector →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (complexDotRightLinearMap left)

/-- The complex dot receiver as a continuous bilinear passage. -/
def complexDotBilinearLinearMap :
    ComplexVector →ₗ[ℂ] (ComplexVector →L[ℂ] ℂ) where
  toFun := complexDotRightCLM
  map_add' first second := by
    ext mode
    change complexDot (first + second) mode =
      complexDot first mode + complexDot second mode
    simp [complexDot, add_dotProduct]
  map_smul' scale mode := by
    ext right
    change complexDot (scale • mode) right = scale * complexDot mode right
    simp [complexDot, smul_dotProduct]

/-- Continuous bilinear complex dot passage. -/
def complexDotBilinearCLM :
    ComplexVector →L[ℂ] (ComplexVector →L[ℂ] ℂ) :=
  LinearMap.toContinuousLinearMap complexDotBilinearLinearMap

@[simp]
theorem complexDotBilinearCLM_apply_apply
    (left right : ComplexVector) :
    complexDotBilinearCLM left right = complexDot left right := rfl

/-- Product rule for the bilinear complex dot receiver along real time. -/
theorem hasDerivAt_complexDot
    {left right : ℝ → ComplexVector} {left' right' : ComplexVector} {t : ℝ}
    (hleft : HasDerivAt left left' t) (hright : HasDerivAt right right' t) :
    HasDerivAt (fun τ ↦ complexDot (left τ) (right τ))
      (complexDot left' (right t) + complexDot (left t) right') t := by
  let B : ComplexVector →L[ℝ] (ComplexVector →L[ℝ] ℂ) :=
    complexDotBilinearCLM.bilinearRestrictScalars ℝ
  have hoperator : HasDerivAt (fun τ ↦ B (left τ)) (B left') t := by
    change HasDerivAt (B ∘ left) (B left') t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        (B.hasFDerivAt.comp t hleft.hasFDerivAt).hasDerivAt
  have hdot := hoperator.clm_apply hright
  simpa only [B, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    complexDotBilinearCLM_apply_apply] using hdot

/-- The primitive character current used by the algebraic advective interaction, written without
choosing a raw transcendental scalar as a public identity. -/
theorem complexAdvectiveInteraction_eq_unitTorusCurlScale
    (p q : SpatialFrequency) (advecting transported : ComplexVector) :
    complexAdvectiveInteraction p q advecting transported =
      (unitTorusCurlScale *
        complexDot (complexFrequencyVector q) advecting) • transported := by
  simp [complexAdvectiveInteraction, unitTorusCurlScale,
    frequencyCurlMultiplier, complexCross, crossProduct, complexFrequencyVector]

/-- The advective interaction with its advecting occurrence fixed. -/
def complexAdvectiveInteractionRightLinearMap
    (p q : SpatialFrequency) (advecting : ComplexVector) :
    ComplexVector →ₗ[ℂ] ComplexVector where
  toFun := complexAdvectiveInteraction p q advecting
  map_add' first second := by
    simp [complexAdvectiveInteraction, smul_add]
  map_smul' scale mode := by
    simp [complexAdvectiveInteraction, smul_smul]
    module

/-- Continuous-linear form of the fixed-advecting interaction. -/
def complexAdvectiveInteractionRightCLM
    (p q : SpatialFrequency) (advecting : ComplexVector) :
    ComplexVector →L[ℂ] ComplexVector :=
  LinearMap.toContinuousLinearMap
    (complexAdvectiveInteractionRightLinearMap p q advecting)

/-- The advective interaction as a continuous bilinear passage. -/
def complexAdvectiveInteractionBilinearLinearMap
    (p q : SpatialFrequency) :
    ComplexVector →ₗ[ℂ] (ComplexVector →L[ℂ] ComplexVector) where
  toFun := complexAdvectiveInteractionRightCLM p q
  map_add' first second := by
    ext transported component
    change complexAdvectiveInteraction p q (first + second) transported component =
      (complexAdvectiveInteraction p q first transported +
        complexAdvectiveInteraction p q second transported) component
    simp only [complexAdvectiveInteraction, Pi.add_apply, Pi.smul_apply,
      complexDot, dotProduct_add, smul_eq_mul]
    ring
  map_smul' scale mode := by
    ext transported component
    change complexAdvectiveInteraction p q (scale • mode) transported component =
      (scale • complexAdvectiveInteraction p q mode transported) component
    simp only [complexAdvectiveInteraction, Pi.smul_apply,
      complexDot, dotProduct_smul, smul_eq_mul]
    ring

/-- Continuous bilinear advective interaction. -/
def complexAdvectiveInteractionBilinearCLM
    (p q : SpatialFrequency) :
    ComplexVector →L[ℂ] (ComplexVector →L[ℂ] ComplexVector) :=
  LinearMap.toContinuousLinearMap
    (complexAdvectiveInteractionBilinearLinearMap p q)

@[simp]
theorem complexAdvectiveInteractionBilinearCLM_apply_apply
    (p q : SpatialFrequency) (advecting transported : ComplexVector) :
    complexAdvectiveInteractionBilinearCLM p q advecting transported =
      complexAdvectiveInteraction p q advecting transported := rfl

/-- Product rule for the actual bilinear advective interaction. -/
theorem hasDerivAt_complexAdvectiveInteraction
    (p q : SpatialFrequency)
    {advecting transported : ℝ → ComplexVector}
    {advecting' transported' : ComplexVector} {t : ℝ}
    (hadvecting : HasDerivAt advecting advecting' t)
    (htransported : HasDerivAt transported transported' t) :
    HasDerivAt
      (fun τ ↦ complexAdvectiveInteraction p q
        (advecting τ) (transported τ))
      (complexAdvectiveInteraction p q advecting' (transported t) +
        complexAdvectiveInteraction p q (advecting t) transported') t := by
  let B : ComplexVector →L[ℝ] (ComplexVector →L[ℝ] ComplexVector) :=
    (complexAdvectiveInteractionBilinearCLM p q).bilinearRestrictScalars ℝ
  have hoperator : HasDerivAt (fun τ ↦ B (advecting τ)) (B advecting') t := by
    change HasDerivAt (B ∘ advecting) (B advecting') t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        (B.hasFDerivAt.comp t hadvecting.hasFDerivAt).hasDerivAt
  have hinteraction := hoperator.clm_apply htransported
  simpa only [B, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    complexAdvectiveInteractionBilinearCLM_apply_apply] using hinteraction

/-- Full three-leg product rule for the signed triadic energy face, before any norm or real part. -/
theorem hasDerivAt_triadicEnergyFace
    (p q : SpatialFrequency)
    {advecting transported receiver : ℝ → ComplexVector}
    {advecting' transported' receiver' : ComplexVector} {t : ℝ}
    (hadvecting : HasDerivAt advecting advecting' t)
    (htransported : HasDerivAt transported transported' t)
    (hreceiver : HasDerivAt receiver receiver' t) :
    HasDerivAt
      (fun τ ↦ triadicEnergyFace p q
        (advecting τ) (transported τ) (receiver τ))
      (triadicEnergyFace p q advecting' (transported t) (receiver t) +
        triadicEnergyFace p q (advecting t) transported' (receiver t) +
        triadicEnergyFace p q (advecting t) (transported t) receiver') t := by
  have hinteraction := hasDerivAt_complexAdvectiveInteraction p q
    hadvecting htransported
  have hdot := hasDerivAt_complexDot hinteraction hreceiver
  unfold triadicEnergyFace
  simpa [complexDot, dotProduct_add, add_assoc] using hdot

/-! ## The clocked actual physical-H2 face -/

/-- The three-mode Stokes clock carried by one addressed transport triangle. -/
def physicalH2TriadStokesClock
    (nu : ℝ) (address : CompleteTransportAddress) : ℝ :=
  nu * (torusStokesEigenvalue address.1 +
    torusStokesEigenvalue address.2 +
    torusStokesEigenvalue (completeTransportReceiver address))

/-- A positive viscosity gives a strictly positive triad clock at every nontrivial address.  The
receipt excludes exactly the pair `(0, 0)`; no claim is made that an individual pin is nonzero. -/
theorem physicalH2TriadStokesClock_pos_of_address_ne_zero
    {nu : ℝ} (hnu : 0 < nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) :
    0 < physicalH2TriadStokesClock nu address := by
  unfold physicalH2TriadStokesClock
  apply mul_pos hnu
  by_cases hp : address.1 = 0
  · have hq : address.2 ≠ 0 := by
      intro hq
      apply haddress
      exact Prod.ext hp hq
    linarith [torusStokesEigenvalue_nonneg address.1,
      torusStokesEigenvalue_pos hq,
      torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  · linarith [torusStokesEigenvalue_pos hp,
      torusStokesEigenvalue_nonneg address.2,
      torusStokesEigenvalue_nonneg (completeTransportReceiver address)]

/-- The receiver-weighted physical-H2 face with the nonlinear source inserted at each of its
three addressed occurrences. -/
def receiverWeightedPhysicalH2VelocitySourceInsertion
    (velocityMode sourceMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
    (triadicEnergyFace address.1 address.2
        (sourceMode address.1)
        (velocityMode address.2)
        (velocityMode (completeTransportReceiver address)) +
      triadicEnergyFace address.1 address.2
        (velocityMode address.1)
        (sourceMode address.2)
        (velocityMode (completeTransportReceiver address)) +
      triadicEnergyFace address.1 address.2
        (velocityMode address.1)
        (velocityMode address.2)
        (sourceMode (completeTransportReceiver address)))

/-- **Clocked Pantographic Swing for one actual physical-H2 receiver-weighted triad.**  The
signed face derivative plus its three-mode Stokes clock is exactly the sum of the three nonlinear
source insertions. -/
theorem openPeriodicSolutionOn_hasDerivAt_receiverWeightedPhysicalH2VelocityAdvectionFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteTransportAddress) :
    HasDerivAt
      (fun τ ↦ receiverWeightedPhysicalH2VelocityAdvectionFace
        (fun frequency ↦ velocityMode velocity frequency τ) address)
      (receiverWeightedPhysicalH2VelocitySourceInsertion
          (fun frequency ↦ velocityMode velocity frequency t.1)
          (openProjectedVelocityNonlinearMode solution t) address -
        ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) *
          receiverWeightedPhysicalH2VelocityAdvectionFace
            (fun frequency ↦ velocityMode velocity frequency t.1) address) t.1 := by
  let receiverFrequency := completeTransportReceiver address
  have hp := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t address.1
  have hq := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t address.2
  have hr := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t receiverFrequency
  have hface := hasDerivAt_triadicEnergyFace address.1 address.2 hp hq hr
  have hweighted := hface.const_mul
    (physicalH2CurlEnergyMultiplier receiverFrequency)
  unfold receiverWeightedPhysicalH2VelocityAdvectionFace
  convert hweighted using 1
  · rfl
  · unfold receiverWeightedPhysicalH2VelocitySourceInsertion
      physicalH2TriadStokesClock receiverFrequency
    simp only [triadicEnergyFace, complexAdvectiveInteraction, complexDot,
      dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    push_cast
    ring

/-! ## The completed exchanged physical-H2 swing -/

/-- The exact completed exchanged multiplier carried by one transport address. -/
def physicalH2ExchangedTriadMultiplier
    (address : CompleteTransportAddress) : ℂ :=
  (((torusStokesEigenvalue address.2 -
      torusStokesEigenvalue (completeTransportReceiver address)) *
    (1 + torusStokesEigenvalue address.2 +
      torusStokesEigenvalue (completeTransportReceiver address)) : ℝ) : ℂ)

/-- The completed exchanged multiplier with the nonlinear source inserted successively at all
three addressed mode occurrences. -/
def physicalH2VelocityExchangedSourceInsertion
    (velocityMode sourceMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2ExchangedTriadMultiplier address *
    (triadicEnergyFace address.1 address.2
        (sourceMode address.1)
        (velocityMode address.2)
        (velocityMode (completeTransportReceiver address)) +
      triadicEnergyFace address.1 address.2
        (velocityMode address.1)
        (sourceMode address.2)
        (velocityMode (completeTransportReceiver address)) +
      triadicEnergyFace address.1 address.2
        (velocityMode address.1)
        (velocityMode address.2)
        (sourceMode (completeTransportReceiver address)))

/-- **Clocked completed physical-H2 exchange swing.**  The derivative of the literal exchanged
face plus its three-mode Stokes clock is the signed three-leg nonlinear insertion.  The proof uses
the actual divergence receipt in a time neighbourhood; no nonzero-frequency or inverse-curl
hypothesis is introduced. -/
theorem openPeriodicSolutionOn_hasDerivAt_physicalH2VelocityExchangedTriadFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteTransportAddress) :
    HasDerivAt
      (fun τ ↦ physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency τ) address)
      (physicalH2VelocityExchangedSourceInsertion
          (fun frequency ↦ velocityMode velocity frequency t.1)
          (openProjectedVelocityNonlinearMode solution t) address -
        ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) *
          physicalH2VelocityExchangedTriadFace
            (fun frequency ↦ velocityMode velocity frequency t.1) address) t.1 := by
  let receiverFrequency := completeTransportReceiver address
  have hp := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t address.1
  have hq := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t address.2
  have hr := openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
    solution t receiverFrequency
  have hface := hasDerivAt_triadicEnergyFace address.1 address.2 hp hq hr
  have hweighted := hface.const_mul (physicalH2ExchangedTriadMultiplier address)
  have heventually : Filter.EventuallyEq (nhds t.1)
      (fun τ ↦ physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency τ) address)
      (fun τ ↦ physicalH2ExchangedTriadMultiplier address *
        triadicEnergyFace address.1 address.2
          (velocityMode velocity address.1 τ)
          (velocityMode velocity address.2 τ)
          (velocityMode velocity receiverFrequency τ)) := by
    filter_upwards [Ioo_mem_nhds t.2.1 t.2.2] with τ hτ
    unfold physicalH2VelocityExchangedTriadFace
    rw [physicalH2ExchangedTriadTransfer_eq_factorized]
    · rfl
    · exact openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
        solution ⟨τ, hτ⟩ address.1
  have hactual := hweighted.congr_of_eventuallyEq heventually
  have hfactorAt :
      physicalH2VelocityExchangedTriadFace
          (fun frequency ↦ velocityMode velocity frequency t.1) address =
        physicalH2ExchangedTriadMultiplier address *
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 t.1)
            (velocityMode velocity address.2 t.1)
            (velocityMode velocity receiverFrequency t.1) := by
    unfold physicalH2VelocityExchangedTriadFace
    rw [physicalH2ExchangedTriadTransfer_eq_factorized]
    · rfl
    · exact openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
        solution t address.1
  convert hactual using 1
  · rfl
  · unfold physicalH2VelocityExchangedSourceInsertion
      physicalH2TriadStokesClock receiverFrequency
    rw [hfactorAt]
    simp only [triadicEnergyFace, complexAdvectiveInteraction, complexDot,
      dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    push_cast
    ring

/-! ## Compact strict-interior time integration -/

/-- A fixed actual velocity mode is continuous on every compact interval strictly inside the open
lifespan. -/
theorem continuousOn_velocityMode_compactInterior
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (_htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (frequency : SpatialFrequency) :
    ContinuousOn (velocityMode velocity frequency) (Icc sourceTime targetTime) := by
  intro τ hτ
  exact (openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray solution
    ⟨τ, hsource.trans_le hτ.1, hτ.2.trans_lt htarget⟩ frequency).continuousAt.continuousWithinAt

/-- Compact-time totalization of the actual signed projected velocity source. -/
def compactOpenProjectedVelocityNonlinearMode
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (frequency : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  openProjectedVelocityNonlinearMode solution
    (compactInteriorTime hsource htimes htarget τ) frequency

/-- The compactly totalized actual projected source is continuous in real time. -/
theorem continuous_compactOpenProjectedVelocityNonlinearMode
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (frequency : SpatialFrequency) :
    Continuous (compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency) := by
  have hadvection : Continuous (fun τ : ℝ ↦
      openActualAdvectionMode solution
        (compactInteriorTime hsource htimes htarget τ) frequency) := by
    have hnamed := (continuous_openAdvectionMode solution frequency).comp
      (continuous_compactInteriorTime hsource htimes htarget)
    exact hnamed.congr (fun τ ↦
      openAdvectionMode_eq_openActualAdvectionMode solution
        (compactInteriorTime hsource htimes htarget τ) frequency)
  change Continuous (fun τ ↦
    -lerayProjectMode frequency
      (openActualAdvectionMode solution
        (compactInteriorTime hsource htimes htarget τ) frequency))
  exact continuous_neg.comp
    ((lerayProjectModeCLM frequency).continuous.comp hadvection)

/-- Continuity of the trilinear face under three continuous addressed currents. -/
theorem continuousOn_triadicEnergyFace
    {s : Set ℝ} (p q : SpatialFrequency)
    {advecting transported receiver : ℝ → ComplexVector}
    (hadvecting : ContinuousOn advecting s)
    (htransported : ContinuousOn transported s)
    (hreceiver : ContinuousOn receiver s) :
    ContinuousOn (fun τ ↦ triadicEnergyFace p q
      (advecting τ) (transported τ) (receiver τ)) s := by
  let B : ComplexVector →L[ℝ] (ComplexVector →L[ℝ] ComplexVector) :=
    (complexAdvectiveInteractionBilinearCLM p q).bilinearRestrictScalars ℝ
  let D : ComplexVector →L[ℝ] (ComplexVector →L[ℝ] ℂ) :=
    complexDotBilinearCLM.bilinearRestrictScalars ℝ
  have hinteraction : ContinuousOn (fun τ ↦ B (advecting τ) (transported τ)) s :=
    (B.continuous.comp_continuousOn hadvecting).clm_apply htransported
  have hface : ContinuousOn (fun τ ↦
      D (B (advecting τ) (transported τ)) (receiver τ)) s :=
    (D.continuous.comp_continuousOn hinteraction).clm_apply hreceiver
  simpa only [triadicEnergyFace, B, D,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    complexAdvectiveInteractionBilinearCLM_apply_apply,
    complexDotBilinearCLM_apply_apply] using hface

/-- Compact-time source-insertion current for one actual completed exchanged face. -/
def compactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (τ : ℝ) : ℂ :=
  physicalH2VelocityExchangedSourceInsertion
    (fun frequency ↦ velocityMode velocity frequency τ)
    (fun frequency ↦ compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency τ) address

/-- The actual compact source-insertion current is interval-integrable. -/
theorem intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    IntervalIntegrable
      (compactPhysicalH2VelocityExchangedSourceInsertion
        solution hsource htimes htarget address) volume sourceTime targetTime := by
  let interval := Icc sourceTime targetTime
  have hv (frequency : SpatialFrequency) :
      ContinuousOn (velocityMode velocity frequency) interval :=
    continuousOn_velocityMode_compactInterior solution hsource htimes htarget frequency
  have hs (frequency : SpatialFrequency) : ContinuousOn
      (compactOpenProjectedVelocityNonlinearMode
        solution hsource htimes htarget frequency) interval :=
    (continuous_compactOpenProjectedVelocityNonlinearMode
      solution hsource htimes htarget frequency).continuousOn
  have hfirst := continuousOn_triadicEnergyFace address.1 address.2
    (hs address.1) (hv address.2) (hv (completeTransportReceiver address))
  have hsecond := continuousOn_triadicEnergyFace address.1 address.2
    (hv address.1) (hs address.2) (hv (completeTransportReceiver address))
  have hthird := continuousOn_triadicEnergyFace address.1 address.2
    (hv address.1) (hv address.2) (hs (completeTransportReceiver address))
  have hsum := (hfirst.add hsecond).add hthird
  have hscaled :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ ↦ physicalH2ExchangedTriadMultiplier address) interval).mul hsum
  change ContinuousOn (fun τ ↦
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.1 τ)
            (velocityMode velocity address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (velocityMode velocity address.2 τ)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget
                (completeTransportReceiver address) τ))) interval at hscaled
  change IntervalIntegrable (fun τ ↦
    physicalH2ExchangedTriadMultiplier address *
      (triadicEnergyFace address.1 address.2
          (compactOpenProjectedVelocityNonlinearMode
            solution hsource htimes htarget address.1 τ)
          (velocityMode velocity address.2 τ)
          (velocityMode velocity (completeTransportReceiver address) τ) +
        triadicEnergyFace address.1 address.2
          (velocityMode velocity address.1 τ)
          (compactOpenProjectedVelocityNonlinearMode
            solution hsource htimes htarget address.2 τ)
          (velocityMode velocity (completeTransportReceiver address) τ) +
        triadicEnergyFace address.1 address.2
          (velocityMode velocity address.1 τ)
          (velocityMode velocity address.2 τ)
          (compactOpenProjectedVelocityNonlinearMode
            solution hsource htimes htarget
              (completeTransportReceiver address) τ)))
      volume sourceTime targetTime
  have hscaled' : ContinuousOn (fun τ ↦
      physicalH2ExchangedTriadMultiplier address *
        (triadicEnergyFace address.1 address.2
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.1 τ)
            (velocityMode velocity address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (velocityMode velocity address.2 τ)
            (compactOpenProjectedVelocityNonlinearMode
              solution hsource htimes htarget
                (completeTransportReceiver address) τ)))
      (uIcc sourceTime targetTime) := by
    simpa only [interval, uIcc_of_le htimes] using hscaled
  exact hscaled'.intervalIntegrable

/-- The actual exchanged face itself is interval-integrable on a compact interior clock. -/
theorem intervalIntegrable_physicalH2VelocityExchangedTriadFace
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    IntervalIntegrable
      (fun τ ↦ physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency τ) address)
      volume sourceTime targetTime := by
  have hp := continuousOn_velocityMode_compactInterior
    solution hsource htimes htarget address.1
  have hq := continuousOn_velocityMode_compactInterior
    solution hsource htimes htarget address.2
  have hr := continuousOn_velocityMode_compactInterior
    solution hsource htimes htarget (completeTransportReceiver address)
  have hface := continuousOn_triadicEnergyFace address.1 address.2 hp hq hr
  have hexchanged := continuousOn_triadicEnergyFace address.1
    (completeTransportReceiver address) hp hr hq
  have hweightedTransported :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ ↦ physicalH2CurlEnergyMultiplier address.2)
      (Icc sourceTime targetTime)).mul hface
  have hweightedReceiver :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ ↦
        physicalH2CurlEnergyMultiplier (completeTransportReceiver address))
      (Icc sourceTime targetTime)).mul hexchanged
  have hcurrentIcc := hweightedTransported.add hweightedReceiver
  change ContinuousOn (fun τ ↦
      physicalH2CurlEnergyMultiplier address.2 *
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (velocityMode velocity address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
        physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
          triadicEnergyFace address.1 (completeTransportReceiver address)
            (velocityMode velocity address.1 τ)
            (velocityMode velocity (completeTransportReceiver address) τ)
            (velocityMode velocity address.2 τ))
      (Icc sourceTime targetTime) at hcurrentIcc
  change IntervalIntegrable (fun τ ↦
    physicalH2CurlEnergyMultiplier address.2 *
        triadicEnergyFace address.1 address.2
          (velocityMode velocity address.1 τ)
          (velocityMode velocity address.2 τ)
          (velocityMode velocity (completeTransportReceiver address) τ) +
      physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
        triadicEnergyFace address.1 (completeTransportReceiver address)
          (velocityMode velocity address.1 τ)
          (velocityMode velocity (completeTransportReceiver address) τ)
          (velocityMode velocity address.2 τ))
      volume sourceTime targetTime
  have hcurrent : ContinuousOn (fun τ ↦
      physicalH2CurlEnergyMultiplier address.2 *
          triadicEnergyFace address.1 address.2
            (velocityMode velocity address.1 τ)
            (velocityMode velocity address.2 τ)
            (velocityMode velocity (completeTransportReceiver address) τ) +
        physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
          triadicEnergyFace address.1 (completeTransportReceiver address)
            (velocityMode velocity address.1 τ)
            (velocityMode velocity (completeTransportReceiver address) τ)
            (velocityMode velocity address.2 τ))
      (uIcc sourceTime targetTime) := by
    simpa only [uIcc_of_le htimes] using hcurrentIcc
  exact hcurrent.intervalIntegrable

/-- Compactly totalized clocked rate of one actual signed exchanged face. -/
def compactClockedPhysicalH2VelocityExchangedTriadRate
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) (τ : ℝ) : ℂ :=
  compactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address τ -
    ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) *
      physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency τ) address

/-- On the selected compact interval, the totalized clocked rate is the actual derivative of the
signed physical-`H2` exchanged face. -/
theorem openPeriodicSolutionOn_hasDerivAt_compactClockedPhysicalH2VelocityExchangedTriadRate
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) {τ : ℝ}
    (hτ : τ ∈ Icc sourceTime targetTime) (address : CompleteTransportAddress) :
    HasDerivAt
      (fun time ↦ physicalH2VelocityExchangedTriadFace
        (fun frequency ↦ velocityMode velocity frequency time) address)
      (compactClockedPhysicalH2VelocityExchangedTriadRate
        solution hsource htimes htarget address τ) τ := by
  let t : Ioo (0 : ℝ) T :=
    ⟨τ, hsource.trans_le hτ.1, hτ.2.trans_lt htarget⟩
  have htime : compactInteriorTime hsource htimes htarget τ = t := by
    apply Subtype.ext
    exact compactInteriorTime_eq hsource htimes htarget hτ
  have hpoint :=
    openPeriodicSolutionOn_hasDerivAt_physicalH2VelocityExchangedTriadFace
      solution t address
  unfold compactClockedPhysicalH2VelocityExchangedTriadRate
    compactPhysicalH2VelocityExchangedSourceInsertion
    compactOpenProjectedVelocityNonlinearMode
  rw [htime]
  simpa only [t] using hpoint

/-- **Integrated clocked physical `H2` swing normal form.**  On every compact interval strictly
inside the open lifespan, the actual signed exchanged face changes by exactly the integral of its
three projected nonlinear source insertions minus its Stokes-triad clock.  No reciprocal clock is
taken, so addresses containing a zero frequency remain lawful without a hidden nonzero receipt. -/
theorem intervalIntegral_clockedPhysicalH2VelocityExchangedTriadFace_eq_endpointDifference
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (address : CompleteTransportAddress) :
    ∫ τ in sourceTime..targetTime,
        (compactPhysicalH2VelocityExchangedSourceInsertion
            solution hsource htimes htarget address τ -
          ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) *
            physicalH2VelocityExchangedTriadFace
              (fun frequency ↦ velocityMode velocity frequency τ) address) =
      physicalH2VelocityExchangedTriadFace
          (fun frequency ↦ velocityMode velocity frequency targetTime) address -
        physicalH2VelocityExchangedTriadFace
          (fun frequency ↦ velocityMode velocity frequency sourceTime) address := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    have hτIcc : τ ∈ Icc sourceTime targetTime := by
      simpa only [uIcc_of_le htimes] using hτ
    exact
      openPeriodicSolutionOn_hasDerivAt_compactClockedPhysicalH2VelocityExchangedTriadRate
        solution hsource htimes htarget hτIcc address
  · exact
      (intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
          solution hsource htimes htarget address).sub
        ((intervalIntegrable_physicalH2VelocityExchangedTriadFace
            solution hsource htimes htarget address).const_mul
          ((physicalH2TriadStokesClock nu address : ℝ) : ℂ))

/-- **Reciprocal clock normal form at a nontrivial address.**  Once positive viscosity and the
exact nonzero-address receipt establish a positive Stokes-triad clock, the integrated signed face
is recovered from the three-source current and the endpoint difference.  This theorem is kept
separate from the all-address identity above so the zero clock is never silently inverted. -/
theorem intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_invClock_mul_source_sub_endpoint
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hsource : 0 < sourceTime)
    (htimes : sourceTime ≤ targetTime) (htarget : targetTime < T)
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0)) :
    ∫ τ in sourceTime..targetTime,
        physicalH2VelocityExchangedTriadFace
          (fun frequency ↦ velocityMode velocity frequency τ) address =
      (((physicalH2TriadStokesClock nu address : ℝ) : ℂ)⁻¹) *
        ((∫ τ in sourceTime..targetTime,
            compactPhysicalH2VelocityExchangedSourceInsertion
              solution hsource htimes htarget address τ) -
          (physicalH2VelocityExchangedTriadFace
              (fun frequency ↦ velocityMode velocity frequency targetTime) address -
            physicalH2VelocityExchangedTriadFace
              (fun frequency ↦ velocityMode velocity frequency sourceTime) address)) := by
  have hsourceIntegrable :=
    intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
      solution hsource htimes htarget address
  have hfaceIntegrable :=
    intervalIntegrable_physicalH2VelocityExchangedTriadFace
      solution hsource htimes htarget address
  have hftc :=
    intervalIntegral_clockedPhysicalH2VelocityExchangedTriadFace_eq_endpointDifference
      solution hsource htimes htarget address
  rw [intervalIntegral.integral_sub hsourceIntegrable
      (hfaceIntegrable.const_mul
        ((physicalH2TriadStokesClock nu address : ℝ) : ℂ)),
    intervalIntegral.integral_const_mul] at hftc
  have hclockPos :=
    physicalH2TriadStokesClock_pos_of_address_ne_zero hnu address haddress
  have hclockNe : ((physicalH2TriadStokesClock nu address : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hclockPos.ne'
  field_simp [hclockNe]
  linear_combination -hftc

/-! ## Actual finite common-cube current -/

/-- The clocked signed rate summed over the actual finite three-pin common-cube population. -/
def compactFiniteClockedPhysicalH2VelocityExchangedTriadRate
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) : ℝ → ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    compactClockedPhysicalH2VelocityExchangedTriadRate
      solution hsource htimes htarget address

/-- **Finite common-cube integrated clocked normal form.**  The actual finite signed exchanged
current changes by the integral of the addresswise three-source residues minus their own Stokes
triad clocks.  This finite sum is taken before any norm.  It uses the all-address law, hence keeps
the zero address without division rather than deleting it from the population. -/
theorem intervalIntegral_compactFiniteClockedPhysicalH2VelocityExchangedTriadRate_eq_endpoints
    {T nu sourceTime targetTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hsource : 0 < sourceTime) (htimes : sourceTime ≤ targetTime)
    (htarget : targetTime < T) (radius : ℕ) :
    ∫ τ in sourceTime..targetTime,
        compactFiniteClockedPhysicalH2VelocityExchangedTriadRate
          solution hsource htimes htarget radius τ =
      finitePhysicalH2VelocityExchangedTriadCurrent radius
          (fun frequency ↦ velocityMode velocity frequency targetTime) -
        finitePhysicalH2VelocityExchangedTriadCurrent radius
          (fun frequency ↦ velocityMode velocity frequency sourceTime) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    have hτIcc : τ ∈ Icc sourceTime targetTime := by
      simpa only [uIcc_of_le htimes] using hτ
    unfold finitePhysicalH2VelocityExchangedTriadCurrent
      compactFiniteClockedPhysicalH2VelocityExchangedTriadRate
    simpa only [Finset.sum_apply] using
      HasDerivAt.fun_sum (u := physicalH2VelocityTriadAperture radius)
      (fun address _haddress ↦
        openPeriodicSolutionOn_hasDerivAt_compactClockedPhysicalH2VelocityExchangedTriadRate
          solution hsource htimes htarget hτIcc address)
  · unfold compactFiniteClockedPhysicalH2VelocityExchangedTriadRate
    have hsum := IntervalIntegrable.sum (physicalH2VelocityTriadAperture radius)
      (fun address _haddress ↦
        (intervalIntegrable_compactPhysicalH2VelocityExchangedSourceInsertion
            solution hsource htimes htarget address).sub
          ((intervalIntegrable_physicalH2VelocityExchangedTriadFace
              solution hsource htimes htarget address).const_mul
            ((physicalH2TriadStokesClock nu address : ℝ) : ℂ)))
    exact hsum


section Audit

#print axioms lerayProjectMode_eq_self_of_complexDot_eq_zero
#print axioms lerayProjectMode_openPressureGradientMode_eq_zero
#print axioms openPeriodicSolutionOn_hasDerivAt_velocityMode_stokesLeray
#print axioms hasDerivAt_triadicEnergyFace
#print axioms openPeriodicSolutionOn_hasDerivAt_receiverWeightedPhysicalH2VelocityAdvectionFace
#print axioms openPeriodicSolutionOn_hasDerivAt_physicalH2VelocityExchangedTriadFace
#print axioms intervalIntegral_clockedPhysicalH2VelocityExchangedTriadFace_eq_endpointDifference
#print axioms intervalIntegral_physicalH2VelocityExchangedTriadFace_eq_invClock_mul_source_sub_endpoint
#print axioms intervalIntegral_compactFiniteClockedPhysicalH2VelocityExchangedTriadRate_eq_endpoints

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
