import ElementaryHolonics.Millennium.NavierStokesPairCompatibleApertureConvergence
import ElementaryHolonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
import Mathlib.Data.Complex.BigOperators

/-!
# Smooth dyadic vorticity-band energy evolution

**[proved-derived; formal-checked]**  The actual open-slab Navier--Stokes vorticity equation is
tested against one finite smooth Hodge band without discarding phase.  The resulting quadratic
receiver has an exact pointwise-in-time derivative.  Its nonlinear work retains the
corrected signed population

`- filtered transport + (- commutator + stretching) + cofinal residual`.

The viscous part is exactly the spectral band dissipation, and the two-shell support of the smooth
multiplier gives unconditional parabolic coercivity at rate `4^scale`.  These are finite-band PDE
laws, not a terminal packing estimate.  Passing from their `L2` coefficient control to the
terminal spacetime `l1` smooth-band packing still requires a scale-summable nonlinear-work or
Carleson estimate.
-/

noncomputable section

open Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution

set_option backward.isDefEq.respectTransparency.types false

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Finite band receivers -/

/-- The finite native frequency aperture of one smooth direct band. -/
def smoothDyadicBandNativeAperture (scale : ℕ) : Finset SpatialFrequency :=
  frequencyCube (dyadicHodgeOuterCutoff (scale + 1))

/-- Euclidean coefficient square of a complex three-vector.  `ComplexVector` itself carries the
finite-product supremum norm, so the quadratic PDE receiver must keep this coordinate sum
explicit rather than silently installing an incompatible inner-product norm. -/
def complexVectorEuclideanSquare (coefficient : ComplexVector) : ℝ :=
  ∑ component : Fin 3, Complex.normSq (coefficient component)

/-- The exact complex Hermitian coefficient pairing. -/
def complexVectorHermitianPairing
    (left right : ComplexVector) : ℂ :=
  ∑ component : Fin 3, (starRingEnd ℂ) (left component) * right component

/-- The symmetric phase work returned by a real-time derivative.  It is kept as a complex
quantity with an exact zero-imaginary-part fibre below, avoiding any change of the native finite
product norm on `ComplexVector`. -/
def complexVectorSymmetricPhasePairing
    (left right : ComplexVector) : ℂ :=
  (1 / 2 : ℂ) *
    (complexVectorHermitianPairing left right +
      complexVectorHermitianPairing right left)

/-- The Hermitian square is the complex chart of the real Euclidean coefficient square. -/
theorem complexVectorHermitianPairing_self_eq
    (coefficient : ComplexVector) :
    complexVectorHermitianPairing coefficient coefficient =
      (complexVectorEuclideanSquare coefficient : ℂ) := by
  unfold complexVectorHermitianPairing complexVectorEuclideanSquare
  rw [Complex.ofReal_sum (Finset.univ : Finset (Fin 3))]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  exact Complex.normSq_eq_conj_mul_self.symm

private theorem complexVectorHermitianPairing_add_right
    (left first second : ComplexVector) :
    complexVectorHermitianPairing left (first + second) =
      complexVectorHermitianPairing left first +
        complexVectorHermitianPairing left second := by
  unfold complexVectorHermitianPairing
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem complexVectorHermitianPairing_add_left
    (first second right : ComplexVector) :
    complexVectorHermitianPairing (first + second) right =
      complexVectorHermitianPairing first right +
        complexVectorHermitianPairing second right := by
  unfold complexVectorHermitianPairing
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem complexVectorHermitianPairing_smul_right
    (left right : ComplexVector) (scalar : ℂ) :
    complexVectorHermitianPairing left (scalar • right) =
      scalar * complexVectorHermitianPairing left right := by
  unfold complexVectorHermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem complexVectorHermitianPairing_smul_left
    (left right : ComplexVector) (scalar : ℂ) :
    complexVectorHermitianPairing (scalar • left) right =
      (starRingEnd ℂ) scalar * complexVectorHermitianPairing left right := by
  unfold complexVectorHermitianPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem complexVectorSymmetricPhasePairing_add_right
    (left first second : ComplexVector) :
    complexVectorSymmetricPhasePairing left (first + second) =
      complexVectorSymmetricPhasePairing left first +
        complexVectorSymmetricPhasePairing left second := by
  unfold complexVectorSymmetricPhasePairing
  rw [complexVectorHermitianPairing_add_right,
    complexVectorHermitianPairing_add_left]
  ring

/-- Half the squared coefficient mass of one actual smooth vorticity band. -/
def openSmoothDyadicBandCoefficientEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) (time : ℝ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    (1 / 2 : ℂ) * complexVectorHermitianPairing
      (openFilteredVorticityMode solution scale k time)
      (openFilteredVorticityMode solution scale k time)

/-- The actual coefficient mass of one smooth vorticity band at an interior time. -/
def openSmoothDyadicBandCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    complexVectorEuclideanSquare
      (openFilteredVorticityCoefficient solution t scale k)

/-- Spectral viscous service before multiplication by the positive viscosity. -/
def openSmoothDyadicBandSpectralDissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    (torusStokesEigenvalue k : ℂ) * complexVectorHermitianPairing
      (openFilteredVorticityCoefficient solution t scale k)
      (openFilteredVorticityCoefficient solution t scale k)

/-- Real nonnegative face of the spectral dissipation. -/
def openSmoothDyadicBandSpectralDissipationMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    torusStokesEigenvalue k * complexVectorEuclideanSquare
      (openFilteredVorticityCoefficient solution t scale k)

theorem openSmoothDyadicBandSpectralDissipation_eq_realFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicBandSpectralDissipation solution t scale =
      (openSmoothDyadicBandSpectralDissipationMass solution t scale : ℂ) := by
  unfold openSmoothDyadicBandSpectralDissipation
    openSmoothDyadicBandSpectralDissipationMass
  rw [Complex.ofReal_sum (smoothDyadicBandNativeAperture scale)]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [complexVectorHermitianPairing_self_eq]
  push_cast
  rfl

theorem openSmoothDyadicBandSpectralDissipationMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    0 ≤ openSmoothDyadicBandSpectralDissipationMass solution t scale := by
  unfold openSmoothDyadicBandSpectralDissipationMass
  exact Finset.sum_nonneg fun k _hk ↦ mul_nonneg
    (torusStokesEigenvalue_nonneg k)
    (Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _)

/-- The corrected finite signed source plus the complete residual fibre.  The aperture is kept
explicit: no finite interaction population is identified with the complete convolution. -/
def openFilteredVorticitySignedSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  -finiteOpenFilteredVorticityTransportCoefficient
      solution t scale aperture k +
    finiteOpenVorticityFluxCoefficient solution t scale aperture k +
    finiteOpenProjectedVorticitySourceResidual solution t scale aperture k

/-- The finite signed population plus its complete residual is exactly the actual projected PDE
source, for every aperture.  Thus the retained residual makes the source aperture-independent;
no limit or finite/infinite identification is used. -/
theorem openFilteredVorticitySignedSource_eq_actual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    openFilteredVorticitySignedSource solution t scale aperture k =
      (dyadicHodgeBandWeight scale k : ℂ) •
        vorticityNonlinearMode solution t k := by
  unfold openFilteredVorticitySignedSource
  calc
    -finiteOpenFilteredVorticityTransportCoefficient
          solution t scale aperture k +
        finiteOpenVorticityFluxCoefficient solution t scale aperture k +
        finiteOpenProjectedVorticitySourceResidual solution t scale aperture k =
      finiteOpenProjectedVorticityNonlinearCoefficient
          solution t scale aperture k +
        finiteOpenProjectedVorticitySourceResidual solution t scale aperture k := by
          rw [finiteOpenProjectedVorticityNonlinearCoefficient_eq
            solution t scale aperture k]
    _ = _ := (projectedVorticityNonlinearMode_eq_finite_add_residual
      solution t scale aperture k).symm

/-- Phase-sensitive nonlinear work of the corrected signed source on the actual smooth band. -/
def openSmoothDyadicBandSignedWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    complexVectorSymmetricPhasePairing
      (openFilteredVorticityCoefficient solution t scale k)
      (openFilteredVorticitySignedSource solution t scale aperture k)

theorem openSmoothDyadicBandSignedWork_aperture_independent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (first second : Finset SpatialFrequency) :
    openSmoothDyadicBandSignedWork solution t scale first =
      openSmoothDyadicBandSignedWork solution t scale second := by
  unfold openSmoothDyadicBandSignedWork
  apply Finset.sum_congr rfl
  intro k _hk
  rw [openFilteredVorticitySignedSource_eq_actual,
    openFilteredVorticitySignedSource_eq_actual]

/-! ## Exact differential law -/

/-- The derivative of the Hermitian square along real time is twice the symmetric complex phase
pairing. -/
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
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply_one,
          ContinuousLinearMap.proj_apply] at hcoordinate
    have hconjugate :=
      (Complex.conjCLE.hasFDerivAt.comp time hcoordinate.hasFDerivAt).hasDerivAt
    convert! hconjugate.mul hcoordinate using 1 <;>
      simp only [Function.comp_apply, Complex.conjCLE_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one,
        ContinuousLinearMap.proj_apply] <;> rfl
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    fun component _hcomponent ↦ hcomponent component
  simpa only [Finset.sum_add_distrib] using hsum

/-- The viscous coefficient contributes exactly minus viscosity times spectral dissipation. -/
private theorem symmetricPhasePairing_filtered_viscous_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openFilteredVorticityCoefficient solution t scale k)
        (openFilteredVorticityViscousCoefficient solution t scale k) =
      (-(nu : ℂ)) * (torusStokesEigenvalue k : ℂ) *
        complexVectorHermitianPairing
          (openFilteredVorticityCoefficient solution t scale k)
          (openFilteredVorticityCoefficient solution t scale k) := by
  unfold complexVectorSymmetricPhasePairing
  unfold openFilteredVorticityViscousCoefficient
  rw [complexVectorHermitianPairing_smul_right,
    complexVectorHermitianPairing_smul_left]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.ofReal_neg,
    Complex.ofReal_mul]
  ring

/-- **Exact actual-PDE smooth-band energy derivative.**  The nonlinear term is not replaced by a
norm bound: its real inner product retains the phase cancellation, the corrected flux sign, and
the explicit finite-aperture residual. -/
theorem openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandCoefficientEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency) :
    HasDerivAt (openSmoothDyadicBandCoefficientEnergy solution scale)
      (-(nu : ℂ) * openSmoothDyadicBandSpectralDissipation solution t scale +
        openSmoothDyadicBandSignedWork solution t scale aperture) t.1 := by
  unfold openSmoothDyadicBandCoefficientEnergy
  have hmode : ∀ k ∈ smoothDyadicBandNativeAperture scale,
      HasDerivAt
        (fun time : ℝ ↦
          (1 / 2 : ℂ) * complexVectorHermitianPairing
            (openFilteredVorticityMode solution scale k time)
            (openFilteredVorticityMode solution scale k time))
        (complexVectorSymmetricPhasePairing
          (openFilteredVorticityCoefficient solution t scale k)
          (openFilteredVorticityViscousCoefficient solution t scale k +
            openFilteredVorticitySignedSource solution t scale aperture k)) t.1 := by
    intro k _hk
    have hprojected :=
      openPeriodicSolutionOn_hasDerivAt_filteredVorticityMode
        solution t scale aperture k
    have hderivative :
        openFilteredVorticityViscousCoefficient solution t scale k -
              finiteOpenFilteredVorticityTransportCoefficient
                solution t scale aperture k +
            finiteOpenVorticityFluxCoefficient solution t scale aperture k +
          finiteOpenProjectedVorticitySourceResidual
              solution t scale aperture k =
        openFilteredVorticityViscousCoefficient solution t scale k +
          openFilteredVorticitySignedSource solution t scale aperture k := by
      unfold openFilteredVorticitySignedSource
      abel
    rw [hderivative] at hprojected
    have hsquare := hasDerivAt_complexVectorHermitianSquare hprojected
    have hhalf := hsquare.const_mul (1 / 2 : ℂ)
    rw [openFilteredVorticityMode_eq_coefficient solution t scale k] at hhalf
    apply hhalf.congr_deriv
    unfold complexVectorSymmetricPhasePairing
    rw [add_comm]
  have hsum := HasDerivAt.fun_sum (u := smoothDyadicBandNativeAperture scale)
    fun k hk ↦ hmode k hk
  apply hsum.congr_deriv
  unfold openSmoothDyadicBandSpectralDissipation openSmoothDyadicBandSignedWork
  have hadd : ∀ k : SpatialFrequency,
      complexVectorSymmetricPhasePairing
          (openFilteredVorticityCoefficient solution t scale k)
          (openFilteredVorticityViscousCoefficient solution t scale k +
            openFilteredVorticitySignedSource solution t scale aperture k) =
        complexVectorSymmetricPhasePairing
          (openFilteredVorticityCoefficient solution t scale k)
          (openFilteredVorticityViscousCoefficient solution t scale k) +
        complexVectorSymmetricPhasePairing
          (openFilteredVorticityCoefficient solution t scale k)
          (openFilteredVorticitySignedSource solution t scale aperture k) := by
    intro k
    exact complexVectorSymmetricPhasePairing_add_right _ _ _
  simp_rw [hadd, symmetricPhasePairing_filtered_viscous_eq]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-! ## Unconditional shell-clock coercivity -/

private theorem dyadicShellClockCost_mono
    {inner outer : ℕ} (hscale : inner ≤ outer) :
    dyadicShellClockCost inner ≤ dyadicShellClockCost outer := by
  have hradius : dyadicRadius inner ≤ dyadicRadius outer := by
    unfold dyadicRadius
    exact Nat.pow_le_pow_right (by norm_num) hscale
  have hlinear : (dyadicRadius inner + 1 : ℝ) ≤
      (dyadicRadius outer + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hradius 1
  unfold dyadicShellClockCost dyadicShellBoundaryFrequency torusStokesEigenvalue
  rw [frequencySquared_exteriorBoundaryFrequency,
    frequencySquared_exteriorBoundaryFrequency]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hlinear 2) (sq_nonneg (2 * Real.pi))

/-- Every nonzero coefficient in a smooth direct band is serviced by at least the clock of the
lower adjacent sharp shell.  The zero-weight fibre is retained explicitly. -/
private theorem dyadicShellClockCost_le_mode_of_filtered_ne_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency)
    (hcoefficient : openFilteredVorticityCoefficient solution t scale k ≠ 0) :
    dyadicShellClockCost scale ≤ torusStokesEigenvalue k := by
  have hweight : dyadicHodgeBandWeight scale k ≠ 0 := by
    intro hzero
    apply hcoefficient
    unfold openFilteredVorticityCoefficient
    simp [hzero]
  have hsupport :=
    mem_two_sharp_shells_of_dyadicHodgeBandWeight_ne_zero scale hweight
  rw [Finset.mem_union] at hsupport
  rcases hsupport with hcurrent | hnext
  · exact dyadicShellClockCost_le_mode hcurrent
  · exact (dyadicShellClockCost_mono (Nat.le_succ scale)).trans
      (dyadicShellClockCost_le_mode hnext)

/-- **Unconditional smooth-band dissipative payment.**  The real spectral dissipation controls
the complete smooth-band coefficient mass at the lower adjacent shell clock. -/
theorem dyadicShellClockCost_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    dyadicShellClockCost scale *
        openSmoothDyadicBandCoefficientMass solution t scale ≤
      openSmoothDyadicBandSpectralDissipationMass solution t scale := by
  unfold openSmoothDyadicBandCoefficientMass
    openSmoothDyadicBandSpectralDissipationMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _hk
  by_cases hcoefficient :
      openFilteredVorticityCoefficient solution t scale k = 0
  · simp [hcoefficient, complexVectorEuclideanSquare]
  · exact mul_le_mul_of_nonneg_right
      (dyadicShellClockCost_le_mode_of_filtered_ne_zero
        solution t scale k hcoefficient)
      (Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _)

/-- The coarser public parabolic scale follows from the exact shell-clock payment. -/
theorem four_pow_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    (4 : ℝ) ^ scale *
        openSmoothDyadicBandCoefficientMass solution t scale ≤
      openSmoothDyadicBandSpectralDissipationMass solution t scale := by
  refine (mul_le_mul_of_nonneg_right (four_pow_le_dyadicShellClockCost scale) ?_).trans
    (dyadicShellClockCost_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
      solution t scale)
  unfold openSmoothDyadicBandCoefficientMass
  exact Finset.sum_nonneg fun k _hk ↦
    Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _

section Audit

#print axioms openFilteredVorticitySignedSource_eq_actual
#print axioms openSmoothDyadicBandSignedWork_aperture_independent
#print axioms openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandCoefficientEnergy
#print axioms openSmoothDyadicBandSpectralDissipation_eq_realFace
#print axioms dyadicShellClockCost_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
#print axioms four_pow_mul_openSmoothDyadicBandCoefficientMass_le_dissipation

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
