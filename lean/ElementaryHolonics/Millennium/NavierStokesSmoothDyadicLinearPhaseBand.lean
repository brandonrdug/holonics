import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeBandPositivity
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation

/-!
# Linear-multiplier smooth dyadic phase bands

**[proved-derived; formal-checked]**  The existing smooth-band energy places the dyadic
multiplier on both coefficient slots and therefore presents the square of the multiplier to its
quadratic receiver.  That is the correct storage for the norm of the filtered field, but it is
not the presentation seen by the signed triad cancellation law.

This owner retains a second, linear-multiplier presentation.  A multiplier is attached once to
the complete Hermitian storage or phase-sensitive nonlinear work.  Finite sums of these
presentations therefore commute exactly with the dyadic partition: adjacent exchanged transport
faces cancel on a common sharp shell, and an arbitrary finite scale population returns only the
two low-pass boundary multipliers.

No norm is taken in these statements.  In particular, no source-envelope summability, terminal
estimate, or Navier--Stokes regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## One-copy multiplier storage and work -/

/-- A real scalar may cross the symmetric phase pairing without changing its orientation.  This
is the exact reason a real dyadic multiplier can be presented either on the nonlinear source or
on the complete signed-work occurrence. -/
theorem complexVectorSymmetricPhasePairing_real_smul_right
    (left right : ComplexVector) (weight : ℝ) :
    complexVectorSymmetricPhasePairing left ((weight : ℂ) • right) =
      (weight : ℂ) * complexVectorSymmetricPhasePairing left right := by
  have hright :
      complexVectorHermitianPairing left ((weight : ℂ) • right) =
        (weight : ℂ) * complexVectorHermitianPairing left right := by
    unfold complexVectorHermitianPairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro component _hcomponent
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hleft :
      complexVectorHermitianPairing ((weight : ℂ) • right) left =
        (weight : ℂ) * complexVectorHermitianPairing right left := by
    unfold complexVectorHermitianPairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro component _hcomponent
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    ring
  unfold complexVectorSymmetricPhasePairing
  rw [hright, hleft]
  ring

/-- Hermitian coefficient storage with one addressed multiplier occurrence.  The aperture is
explicit so several scales may be compared without silently changing their mode population. -/
def linearMultiplierCoefficientStorage
    (multiplier : SpatialFrequency → ℂ)
    (aperture : Finset SpatialFrequency)
    (coefficient : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ frequency ∈ aperture,
    (1 / 2 : ℂ) * multiplier frequency *
      complexVectorHermitianPairing (coefficient frequency) (coefficient frequency)

/-- Phase-sensitive coefficient work with one addressed multiplier occurrence.  The complete
symmetric pairing is formed before any magnitude receiver is applied. -/
def linearMultiplierCoefficientWork
    (multiplier : SpatialFrequency → ℂ)
    (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ frequency ∈ aperture,
    multiplier frequency *
      complexVectorSymmetricPhasePairing
        (coefficient frequency) (source frequency)

/-- For a real multiplier population, the linear work is exactly the sum obtained by attaching
the multiplier to the source before the phase pairing. -/
theorem linearMultiplierCoefficientWork_real_eq_weightedSourcePairing
    (multiplier : SpatialFrequency → ℝ)
    (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector) :
    linearMultiplierCoefficientWork
        (fun frequency ↦ (multiplier frequency : ℂ))
        aperture coefficient source =
      ∑ frequency ∈ aperture,
        complexVectorSymmetricPhasePairing (coefficient frequency)
          ((multiplier frequency : ℂ) • source frequency) := by
  unfold linearMultiplierCoefficientWork
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [complexVectorSymmetricPhasePairing_real_smul_right]

/-- The direct smooth dyadic storage with one, rather than two, copies of its band weight. -/
def smoothDyadicLinearCoefficientStorage
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient : SpatialFrequency → ComplexVector) : ℂ :=
  linearMultiplierCoefficientStorage
    (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ))
    aperture coefficient

/-- The direct smooth dyadic signed work with one copy of its band weight. -/
def smoothDyadicLinearCoefficientWork
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector) : ℂ :=
  linearMultiplierCoefficientWork
    (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ))
    aperture coefficient source

/-- Actual open-solution vorticity storage in the linear smooth-band presentation. -/
def openSmoothDyadicLinearBandCoefficientStorage
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℂ :=
  smoothDyadicLinearCoefficientStorage scale
    (smoothDyadicBandNativeAperture scale)
    (openPeriodicVorticityFourierMode solution t)

/-- Actual nonlinear vorticity work in the same one-copy smooth-band presentation. -/
def openSmoothDyadicLinearBandActualSignedWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℂ :=
  smoothDyadicLinearCoefficientWork scale
    (smoothDyadicBandNativeAperture scale)
    (openPeriodicVorticityFourierMode solution t)
    (vorticityNonlinearMode solution t)

/-- The linear storage retains the exact real Euclidean coefficient square in each weighted
incidence. -/
theorem openSmoothDyadicLinearBandCoefficientStorage_eq_realSquares
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicLinearBandCoefficientStorage solution t scale =
      ∑ frequency ∈ smoothDyadicBandNativeAperture scale,
        (1 / 2 : ℂ) * (dyadicHodgeBandWeight scale frequency : ℂ) *
          (complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) : ℂ) := by
  unfold openSmoothDyadicLinearBandCoefficientStorage
    smoothDyadicLinearCoefficientStorage linearMultiplierCoefficientStorage
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [complexVectorHermitianPairing_self_eq]

/-! ## Analytic bridge to the squared smooth-band receiver -/

/-- The real-time chart of the unfiltered vorticity mode.  The solution argument retains the
source owner and lifespan even though the chart itself is written through the velocity mode. -/
def openLinearVorticityMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (_solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (frequency : SpatialFrequency) (time : ℝ) : ComplexVector :=
  frequencyCurlMultiplier frequency (velocityMode velocity frequency time)

theorem openLinearVorticityMode_eq_actual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    openLinearVorticityMode solution frequency t.1 =
      openPeriodicVorticityFourierMode solution t frequency := by
  exact frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution t frequency

/-- Real coefficient mass with one copy of the smooth multiplier. -/
def openSmoothDyadicLinearBandCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℝ :=
  ∑ frequency ∈ smoothDyadicBandNativeAperture scale,
    dyadicHodgeBandWeight scale frequency *
      complexVectorEuclideanSquare
        (openPeriodicVorticityFourierMode solution t frequency)

/-- Half the one-copy coefficient mass, matching the normalization of the quadratic PDE
receiver. -/
def openSmoothDyadicLinearBandRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℝ :=
  (1 / 2 : ℝ) * openSmoothDyadicLinearBandCoefficientMass solution t scale

/-- Real-time complex chart of the one-copy coefficient storage. -/
def openSmoothDyadicLinearBandCoefficientEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) (time : ℝ) : ℂ :=
  smoothDyadicLinearCoefficientStorage scale
    (smoothDyadicBandNativeAperture scale)
    (fun frequency ↦ openLinearVorticityMode solution frequency time)

theorem openSmoothDyadicLinearBandCoefficientEnergy_eq_realEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicLinearBandCoefficientEnergy solution scale t.1 =
      (openSmoothDyadicLinearBandRealEnergy solution t scale : ℂ) := by
  unfold openSmoothDyadicLinearBandCoefficientEnergy
    smoothDyadicLinearCoefficientStorage linearMultiplierCoefficientStorage
    openSmoothDyadicLinearBandRealEnergy
    openSmoothDyadicLinearBandCoefficientMass
  rw [Complex.ofReal_mul, Complex.ofReal_sum
    (smoothDyadicBandNativeAperture scale), Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [openLinearVorticityMode_eq_actual,
    complexVectorHermitianPairing_self_eq]
  ring

/-- A real scalar square may be read outside the Euclidean coefficient receiver. -/
theorem complexVectorEuclideanSquare_real_smul
    (weight : ℝ) (coefficient : ComplexVector) :
    complexVectorEuclideanSquare ((weight : ℂ) • coefficient) =
      weight ^ 2 * complexVectorEuclideanSquare coefficient := by
  unfold complexVectorEuclideanSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring

/-- On any addressed population where `0 ≤ w ≤ 1`, the usual two-copy filtered mass is
dominated by the one-copy mass.  The hypothesis is explicit: no positivity of a generic band
difference is smuggled into the analytic receiver. -/
theorem openSmoothDyadicBandCoefficientMass_le_linearMass_of_weight_mem_unitInterval
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ)
    (hweight : ∀ frequency ∈ smoothDyadicBandNativeAperture scale,
      0 ≤ dyadicHodgeBandWeight scale frequency ∧
        dyadicHodgeBandWeight scale frequency ≤ 1) :
    openSmoothDyadicBandCoefficientMass solution t scale ≤
      openSmoothDyadicLinearBandCoefficientMass solution t scale := by
  unfold openSmoothDyadicBandCoefficientMass
    openSmoothDyadicLinearBandCoefficientMass
    openFilteredVorticityCoefficient
  apply Finset.sum_le_sum
  intro frequency hfrequency
  rw [complexVectorEuclideanSquare_real_smul]
  obtain ⟨hweightNonneg, hweightOne⟩ := hweight frequency hfrequency
  have hsquare : 0 ≤ complexVectorEuclideanSquare
      (openPeriodicVorticityFourierMode solution t frequency) :=
    Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _
  have hfactor : 0 ≤
      dyadicHodgeBandWeight scale frequency *
        (1 - dyadicHodgeBandWeight scale frequency) *
        complexVectorEuclideanSquare
          (openPeriodicVorticityFourierMode solution t frequency) :=
    mul_nonneg (mul_nonneg hweightNonneg (sub_nonneg.mpr hweightOne)) hsquare
  nlinarith

/-- The same dominance in the half-energy normalization used by the differential law. -/
theorem openSmoothDyadicBandRealEnergy_le_linearRealEnergy_of_weight_mem_unitInterval
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ)
    (hweight : ∀ frequency ∈ smoothDyadicBandNativeAperture scale,
      0 ≤ dyadicHodgeBandWeight scale frequency ∧
        dyadicHodgeBandWeight scale frequency ≤ 1) :
    openSmoothDyadicBandRealEnergy solution t scale ≤
      openSmoothDyadicLinearBandRealEnergy solution t scale := by
  unfold openSmoothDyadicBandRealEnergy
    openSmoothDyadicLinearBandRealEnergy
  exact mul_le_mul_of_nonneg_left
    (openSmoothDyadicBandCoefficientMass_le_linearMass_of_weight_mem_unitInterval
      solution t scale hweight) (by norm_num)

/-- Unconditional actual dyadic mass dominance, discharging the unit-interval premise with the
direct multiplier positivity owner. -/
theorem openSmoothDyadicBandCoefficientMass_le_linearMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicBandCoefficientMass solution t scale ≤
      openSmoothDyadicLinearBandCoefficientMass solution t scale :=
  openSmoothDyadicBandCoefficientMass_le_linearMass_of_weight_mem_unitInterval
    solution t scale fun frequency _hfrequency ↦
      dyadicHodgeBandWeight_mem_unitInterval scale frequency

/-- Unconditional actual dyadic dominance in the half-energy normalization. -/
theorem openSmoothDyadicBandRealEnergy_le_linearRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicBandRealEnergy solution t scale ≤
      openSmoothDyadicLinearBandRealEnergy solution t scale :=
  openSmoothDyadicBandRealEnergy_le_linearRealEnergy_of_weight_mem_unitInterval
    solution t scale fun frequency _hfrequency ↦
      dyadicHodgeBandWeight_mem_unitInterval scale frequency

theorem openSmoothDyadicLinearBandCoefficientMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    0 ≤ openSmoothDyadicLinearBandCoefficientMass solution t scale := by
  unfold openSmoothDyadicLinearBandCoefficientMass
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    mul_nonneg (dyadicHodgeBandWeight_nonneg scale frequency)
      (Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _)

/-! ## Exact one-copy differential law -/

/-- Spectral viscous service retaining one copy of the smooth multiplier. -/
def openSmoothDyadicLinearBandSpectralDissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℂ :=
  ∑ frequency ∈ smoothDyadicBandNativeAperture scale,
    (torusStokesEigenvalue frequency : ℂ) *
      (dyadicHodgeBandWeight scale frequency : ℂ) *
      complexVectorHermitianPairing
        (openPeriodicVorticityFourierMode solution t frequency)
        (openPeriodicVorticityFourierMode solution t frequency)

/-- Real face of the one-copy spectral service. -/
def openSmoothDyadicLinearBandSpectralDissipationMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℝ :=
  ∑ frequency ∈ smoothDyadicBandNativeAperture scale,
    torusStokesEigenvalue frequency *
      dyadicHodgeBandWeight scale frequency *
      complexVectorEuclideanSquare
        (openPeriodicVorticityFourierMode solution t frequency)

theorem openSmoothDyadicLinearBandSpectralDissipation_eq_realFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicLinearBandSpectralDissipation solution t scale =
      (openSmoothDyadicLinearBandSpectralDissipationMass solution t scale : ℂ) := by
  unfold openSmoothDyadicLinearBandSpectralDissipation
    openSmoothDyadicLinearBandSpectralDissipationMass
  rw [Complex.ofReal_sum (smoothDyadicBandNativeAperture scale)]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [complexVectorHermitianPairing_self_eq]
  push_cast
  rfl

/-- Real rate of the phase-sensitive one-copy nonlinear work. -/
def openSmoothDyadicLinearBandActualSignedWorkRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) : ℝ :=
  (openSmoothDyadicLinearBandActualSignedWork solution t scale).re

private theorem complexVectorSymmetricPhasePairing_add_right
    (left first second : ComplexVector) :
    complexVectorSymmetricPhasePairing left (first + second) =
      complexVectorSymmetricPhasePairing left first +
        complexVectorSymmetricPhasePairing left second := by
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  simp only [Pi.add_apply, mul_add, map_add, add_mul, Finset.sum_add_distrib]
  ring

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
    convert! hconjugate.mul hcoordinate using 1 <;>
      simp only [Function.comp_apply, Complex.conjCLE_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one,
        ContinuousLinearMap.proj_apply] <;> rfl
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    fun component _hcomponent ↦ hcomponent component
  simpa only [Finset.sum_add_distrib] using hsum

private theorem symmetricPhasePairing_unfiltered_viscous_eq
    (coefficient : ComplexVector) (nu eigenvalue : ℝ) :
    complexVectorSymmetricPhasePairing coefficient
        (((-(nu * eigenvalue) : ℝ) : ℂ) • coefficient) =
      (-(nu : ℂ)) * (eigenvalue : ℂ) *
        complexVectorHermitianPairing coefficient coefficient := by
  rw [complexVectorSymmetricPhasePairing_real_smul_right]
  unfold complexVectorSymmetricPhasePairing
  simp only [Complex.ofReal_neg, Complex.ofReal_mul]
  ring

/-- Exact derivative of the one-copy storage.  The phase-sensitive nonlinear work remains signed
and is assembled before any norm receiver. -/
theorem openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicLinearBandCoefficientEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    HasDerivAt (openSmoothDyadicLinearBandCoefficientEnergy solution scale)
      (-(nu : ℂ) *
          openSmoothDyadicLinearBandSpectralDissipation solution t scale +
        openSmoothDyadicLinearBandActualSignedWork solution t scale) t.1 := by
  unfold openSmoothDyadicLinearBandCoefficientEnergy
    smoothDyadicLinearCoefficientStorage linearMultiplierCoefficientStorage
  have hmode : ∀ frequency ∈ smoothDyadicBandNativeAperture scale,
      HasDerivAt
        (fun time : ℝ ↦
          (1 / 2 : ℂ) * (dyadicHodgeBandWeight scale frequency : ℂ) *
            complexVectorHermitianPairing
              (openLinearVorticityMode solution frequency time)
              (openLinearVorticityMode solution frequency time))
        ((dyadicHodgeBandWeight scale frequency : ℂ) *
          complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t frequency)
            (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
                openPeriodicVorticityFourierMode solution t frequency +
              vorticityNonlinearMode solution t frequency)) t.1 := by
    intro frequency _hfrequency
    have hcoefficient :=
      openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes
        solution t frequency
    change HasDerivAt (openLinearVorticityMode solution frequency)
      (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
          openLinearVorticityMode solution frequency t.1 +
        vorticityNonlinearMode solution t frequency) t.1 at hcoefficient
    have hsquare := hasDerivAt_complexVectorHermitianSquare hcoefficient
    have hweighted := hsquare.const_mul
      ((1 / 2 : ℂ) * (dyadicHodgeBandWeight scale frequency : ℂ))
    rw [openLinearVorticityMode_eq_actual solution t frequency] at hweighted
    apply hweighted.congr_deriv
    unfold complexVectorSymmetricPhasePairing
    ring
  have hsum := HasDerivAt.fun_sum
    (u := smoothDyadicBandNativeAperture scale) fun frequency hfrequency ↦
      hmode frequency hfrequency
  apply hsum.congr_deriv
  unfold openSmoothDyadicLinearBandSpectralDissipation
    openSmoothDyadicLinearBandActualSignedWork
    smoothDyadicLinearCoefficientWork linearMultiplierCoefficientWork
  have hadd : ∀ frequency : SpatialFrequency,
      complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t frequency)
          (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
              openPeriodicVorticityFourierMode solution t frequency +
            vorticityNonlinearMode solution t frequency) =
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t frequency)
          (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
            openPeriodicVorticityFourierMode solution t frequency) +
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t frequency)
          (vorticityNonlinearMode solution t frequency) := by
    intro frequency
    exact complexVectorSymmetricPhasePairing_add_right _ _ _
  simp_rw [hadd, symmetricPhasePairing_unfiltered_viscous_eq]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  ring

/-- Real pointwise form of the exact one-copy PDE law. -/
theorem openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicLinearBandRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    HasDerivAt
      (fun time : ℝ ↦
        (openSmoothDyadicLinearBandCoefficientEnergy solution scale time).re)
      (-nu * openSmoothDyadicLinearBandSpectralDissipationMass solution t scale +
        openSmoothDyadicLinearBandActualSignedWorkRate solution t scale) t.1 := by
  have hcomplex :=
    openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicLinearBandCoefficientEnergy
      solution t scale
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t.1 hcomplex
  rw [openSmoothDyadicLinearBandSpectralDissipation_eq_realFace] at hreal
  have hreal' : HasDerivAt
      (fun time : ℝ ↦
        (openSmoothDyadicLinearBandCoefficientEnergy solution scale time).re)
      ((-(nu : ℂ) *
          (openSmoothDyadicLinearBandSpectralDissipationMass
            solution t scale : ℂ) +
        openSmoothDyadicLinearBandActualSignedWork solution t scale).re) t.1 := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using hreal
  apply hreal'.congr_deriv
  simp [openSmoothDyadicLinearBandActualSignedWorkRate]

/-! ## Compact-interior integral chart -/

theorem continuous_openSmoothDyadicLinearBandActualSignedWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicLinearBandActualSignedWork solution · scale) := by
  unfold openSmoothDyadicLinearBandActualSignedWork
    smoothDyadicLinearCoefficientWork linearMultiplierCoefficientWork
  apply continuous_finsetSum
  intro frequency _hfrequency
  apply Continuous.mul continuous_const
  have hcoefficient :=
    continuous_openPeriodicVorticityFourierMode solution frequency
  have hsource := continuous_vorticityNonlinearMode solution frequency
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  apply Continuous.mul continuous_const
  apply Continuous.add <;>
    apply continuous_finsetSum <;> intro component _hcomponent
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hcoefficient)).mul
        ((continuous_apply component).comp hsource)
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hsource)).mul
        ((continuous_apply component).comp hcoefficient)

theorem continuous_openSmoothDyadicLinearBandActualSignedWorkRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicLinearBandActualSignedWorkRate solution · scale) :=
  Complex.continuous_re.comp
    (continuous_openSmoothDyadicLinearBandActualSignedWork solution scale)

theorem continuous_openSmoothDyadicLinearBandSpectralDissipationMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous
      (openSmoothDyadicLinearBandSpectralDissipationMass solution · scale) := by
  unfold openSmoothDyadicLinearBandSpectralDissipationMass
    complexVectorEuclideanSquare
  apply continuous_finsetSum
  intro frequency _hfrequency
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro component _hcomponent
  apply Complex.continuous_normSq.comp
  exact (continuous_apply component).comp
    (continuous_openPeriodicVorticityFourierMode solution frequency)

/-- Compact clamping of the real one-copy signed work. -/
def compactOpenSmoothDyadicLinearBandActualSignedWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicLinearBandActualSignedWorkRate solution
    (compactInteriorTime ha hab hbT time) scale

/-- Compact clamping of the real one-copy spectral service. -/
def compactOpenSmoothDyadicLinearBandSpectralDissipationMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicLinearBandSpectralDissipationMass solution
    (compactInteriorTime ha hab hbT time) scale

theorem compactOpenSmoothDyadicLinearBandActualSignedWorkRate_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicLinearBandActualSignedWorkRate
        solution ha hab hbT scale) volume a b :=
  ((continuous_openSmoothDyadicLinearBandActualSignedWorkRate solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)).intervalIntegrable _ _

theorem compactOpenSmoothDyadicLinearBandSpectralDissipationMass_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicLinearBandSpectralDissipationMass
        solution ha hab hbT scale) volume a b :=
  ((continuous_openSmoothDyadicLinearBandSpectralDissipationMass solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)).intervalIntegrable _ _

/-- Exact compact-interior balance for the one-copy phase receiver.  It is a finite-band
identity; no positivity, terminal passage, or scale summability is inferred from it. -/
theorem openPeriodicSolutionOn_openSmoothDyadicLinearBand_integrated_balance
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    openSmoothDyadicLinearBandRealEnergy solution
        ⟨b, ha.trans_le hab, hbT⟩ scale +
        nu * ∫ time in a..b,
          compactOpenSmoothDyadicLinearBandSpectralDissipationMass
            solution ha hab hbT scale time =
      openSmoothDyadicLinearBandRealEnergy solution
          ⟨a, ha, hab.trans_lt hbT⟩ scale +
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
            solution ha hab hbT scale time := by
  have hderivative : ∀ time ∈ uIcc a b,
      HasDerivAt
        (fun time : ℝ ↦
          (openSmoothDyadicLinearBandCoefficientEnergy solution scale time).re)
        (-nu * compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time +
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
              solution ha hab hbT scale time) time := by
    intro time htime
    rw [uIcc_of_le hab] at htime
    let ti : Set.Ioo (0 : ℝ) T :=
      ⟨time, ha.trans_le htime.1, htime.2.trans_lt hbT⟩
    have h :=
      openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicLinearBandRealEnergy
        solution ti scale
    have hcompact : compactInteriorTime ha hab hbT time = ti := by
      apply Subtype.ext
      exact compactInteriorTime_eq ha hab hbT htime
    simpa [compactOpenSmoothDyadicLinearBandSpectralDissipationMass,
      compactOpenSmoothDyadicLinearBandActualSignedWorkRate, hcompact] using h
  have hintegrable : IntervalIntegrable
      (fun time ↦
        -nu * compactOpenSmoothDyadicLinearBandSpectralDissipationMass
              solution ha hab hbT scale time +
          compactOpenSmoothDyadicLinearBandActualSignedWorkRate
              solution ha hab hbT scale time) volume a b :=
    ((compactOpenSmoothDyadicLinearBandSpectralDissipationMass_intervalIntegrable
      solution ha hab hbT scale).const_mul (-nu)).add
      (compactOpenSmoothDyadicLinearBandActualSignedWorkRate_intervalIntegrable
        solution ha hab hbT scale)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderivative hintegrable
  rw [intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul] at hftc
  · have haEnergy :=
      openSmoothDyadicLinearBandCoefficientEnergy_eq_realEnergy
        solution ⟨a, ha, hab.trans_lt hbT⟩ scale
    have hbEnergy :=
      openSmoothDyadicLinearBandCoefficientEnergy_eq_realEnergy
        solution ⟨b, ha.trans_le hab, hbT⟩ scale
    have haReal := congrArg Complex.re haEnergy
    have hbReal := congrArg Complex.re hbEnergy
    simp only [Complex.ofReal_re] at haReal hbReal
    rw [haReal, hbReal] at hftc
    linear_combination -hftc
  · exact
      (compactOpenSmoothDyadicLinearBandSpectralDissipationMass_intervalIntegrable
        solution ha hab hbT scale).const_mul (-nu)
  · exact compactOpenSmoothDyadicLinearBandActualSignedWorkRate_intervalIntegrable
      solution ha hab hbT scale

/-! ## Finite scale population returns only its multiplier boundary -/

/-- Native smooth-band apertures are nested in scale. -/
theorem smoothDyadicBandNativeAperture_subset_of_lt
    {scale depth : ℕ} (hscale : scale < depth) :
    smoothDyadicBandNativeAperture scale ⊆
      smoothDyadicBandNativeAperture depth := by
  unfold smoothDyadicBandNativeAperture
  apply frequencyCube_mono
  rw [dyadicHodgeOuterCutoff_eq, dyadicHodgeOuterCutoff_eq]
  apply Nat.sub_le_sub_right
  unfold dyadicRadius
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- Enlarging a scale's native aperture changes no one-copy storage because the multiplier
vanishes on every newly admitted pin. -/
theorem smoothDyadicLinearCoefficientStorage_eq_of_native_subset
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient : SpatialFrequency → ComplexVector)
    (hsubset : smoothDyadicBandNativeAperture scale ⊆ aperture) :
    smoothDyadicLinearCoefficientStorage scale
        (smoothDyadicBandNativeAperture scale) coefficient =
      smoothDyadicLinearCoefficientStorage scale aperture coefficient := by
  unfold smoothDyadicLinearCoefficientStorage
    linearMultiplierCoefficientStorage
  apply Finset.sum_subset hsubset
  intro frequency _haperture hnotNative
  have hweight : dyadicHodgeBandWeight scale frequency = 0 :=
    dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale (by
      simpa only [smoothDyadicBandNativeAperture] using hnotNative)
  simp [hweight]

/-- The same native-support passage for the complete signed work. -/
theorem smoothDyadicLinearCoefficientWork_eq_of_native_subset
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector)
    (hsubset : smoothDyadicBandNativeAperture scale ⊆ aperture) :
    smoothDyadicLinearCoefficientWork scale
        (smoothDyadicBandNativeAperture scale) coefficient source =
      smoothDyadicLinearCoefficientWork scale aperture coefficient source := by
  unfold smoothDyadicLinearCoefficientWork linearMultiplierCoefficientWork
  apply Finset.sum_subset hsubset
  intro frequency _haperture hnotNative
  have hweight : dyadicHodgeBandWeight scale frequency = 0 :=
    dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale (by
      simpa only [smoothDyadicBandNativeAperture] using hnotNative)
  simp [hweight]

/-- The complex multiplier left after summing the first `depth` direct smooth bands. -/
def smoothDyadicCumulativeBoundaryMultiplier
    (depth : ℕ) (frequency : SpatialFrequency) : ℂ :=
  (tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency : ℂ) -
    (tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency : ℂ)

/-- A finite population of linear smooth-band storages is exactly the storage seen by the two
retained low-pass boundary faces. -/
theorem sum_smoothDyadicLinearCoefficientStorage_eq_lowPass_boundary
    (depth : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient : SpatialFrequency → ComplexVector) :
    (∑ scale ∈ Finset.range depth,
        smoothDyadicLinearCoefficientStorage scale aperture coefficient) =
      linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth) aperture coefficient := by
  unfold smoothDyadicLinearCoefficientStorage
    linearMultiplierCoefficientStorage
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  have hweight :=
    sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary depth frequency
  calc
    (∑ scale ∈ Finset.range depth,
        (1 / 2 : ℂ) * (dyadicHodgeBandWeight scale frequency : ℂ) *
          complexVectorHermitianPairing
            (coefficient frequency) (coefficient frequency)) =
      (1 / 2 : ℂ) *
          (∑ scale ∈ Finset.range depth,
            (dyadicHodgeBandWeight scale frequency : ℂ)) *
          complexVectorHermitianPairing
            (coefficient frequency) (coefficient frequency) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = (1 / 2 : ℂ) * smoothDyadicCumulativeBoundaryMultiplier depth frequency *
          complexVectorHermitianPairing
            (coefficient frequency) (coefficient frequency) := by
      rw [hweight]
      rfl

/-- The same boundary law holds for the complete phase-sensitive work, before any absolute
value is taken. -/
theorem sum_smoothDyadicLinearCoefficientWork_eq_lowPass_boundary
    (depth : ℕ) (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector) :
    (∑ scale ∈ Finset.range depth,
        smoothDyadicLinearCoefficientWork scale aperture coefficient source) =
      linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        aperture coefficient source := by
  unfold smoothDyadicLinearCoefficientWork linearMultiplierCoefficientWork
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  have hweight :=
    sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary depth frequency
  calc
    (∑ scale ∈ Finset.range depth,
        (dyadicHodgeBandWeight scale frequency : ℂ) *
          complexVectorSymmetricPhasePairing
            (coefficient frequency) (source frequency)) =
      (∑ scale ∈ Finset.range depth,
          (dyadicHodgeBandWeight scale frequency : ℂ)) *
        complexVectorSymmetricPhasePairing
          (coefficient frequency) (source frequency) := by
        rw [Finset.sum_mul]
    _ = smoothDyadicCumulativeBoundaryMultiplier depth frequency *
        complexVectorSymmetricPhasePairing
          (coefficient frequency) (source frequency) := by
      rw [hweight]
      rfl

/-- The actual varying native apertures may be enlarged to the depth aperture, so their finite
storage sum inherits the exact low-pass boundary law. -/
theorem sum_openSmoothDyadicLinearBandCoefficientStorage_eq_lowPass_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandCoefficientStorage solution t scale) =
      linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t) := by
  calc
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandCoefficientStorage solution t scale) =
      ∑ scale ∈ Finset.range depth,
        smoothDyadicLinearCoefficientStorage scale
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution t) := by
        apply Finset.sum_congr rfl
        intro scale hscale
        unfold openSmoothDyadicLinearBandCoefficientStorage
        exact smoothDyadicLinearCoefficientStorage_eq_of_native_subset
          scale (smoothDyadicBandNativeAperture depth)
            (openPeriodicVorticityFourierMode solution t)
            (smoothDyadicBandNativeAperture_subset_of_lt
              (Finset.mem_range.mp hscale))
    _ = _ := sum_smoothDyadicLinearCoefficientStorage_eq_lowPass_boundary
      depth (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)

/-- The actual varying-aperture nonlinear work also inherits the exact finite-scale boundary law
before any absolute value is taken. -/
theorem sum_openSmoothDyadicLinearBandActualSignedWork_eq_lowPass_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandActualSignedWork solution t scale) =
      linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t) := by
  calc
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandActualSignedWork solution t scale) =
      ∑ scale ∈ Finset.range depth,
        smoothDyadicLinearCoefficientWork scale
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution t)
          (vorticityNonlinearMode solution t) := by
        apply Finset.sum_congr rfl
        intro scale hscale
        unfold openSmoothDyadicLinearBandActualSignedWork
        exact smoothDyadicLinearCoefficientWork_eq_of_native_subset
          scale (smoothDyadicBandNativeAperture depth)
            (openPeriodicVorticityFourierMode solution t)
            (vorticityNonlinearMode solution t)
            (smoothDyadicBandNativeAperture_subset_of_lt
              (Finset.mem_range.mp hscale))
    _ = _ := sum_smoothDyadicLinearCoefficientWork_eq_lowPass_boundary
      depth (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t)

/-! ## Exact compatibility with signed exchanged triad transport -/

/-- The exchanged transport contribution observed by the linear smooth-band work. -/
def smoothDyadicLinearTransportTriadWork
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  (dyadicHodgeBandWeight scale triad.transported : ℂ) *
      triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode +
    (dyadicHodgeBandWeight scale triad.receiver : ℂ) *
      triadicEnergyFace triad.advecting triad.receiver
        advectingMode receiverMode transportedMode

/-- The new linear work face is literally the already-founded exchanged triad transfer. -/
theorem smoothDyadicLinearTransportTriadWork_eq_exchanged
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    smoothDyadicLinearTransportTriadWork scale triad
        advectingMode transportedMode receiverMode =
      smoothDyadicExchangedTriadTransfer scale triad
        advectingMode transportedMode receiverMode := by
  rfl

/-- Adjacent linear-multiplier bands cancel an exchanged transport face exactly when its two
carried pins lie in their common sharp shell. -/
theorem adjacent_smoothDyadicLinearTransportTriadWorks_cancel
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported : triad.transported ∈ dyadicFrequencyShell (scale + 1))
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell (scale + 1)) :
    smoothDyadicLinearTransportTriadWork scale triad
        advectingMode transportedMode receiverMode +
      smoothDyadicLinearTransportTriadWork (scale + 1) triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [smoothDyadicLinearTransportTriadWork_eq_exchanged,
    smoothDyadicLinearTransportTriadWork_eq_exchanged]
  exact adjacent_smoothDyadicExchangedTriadTransfers_cancel_of_same_sharpShell
    scale triad advectingMode transportedMode receiverMode
      hdivergence htransported hreceiver

/-- Every finite scale population of linear-multiplier exchanged transport work is the exact
low-pass boundary flux. -/
theorem sum_smoothDyadicLinearTransportTriadWork_eq_lowPass_boundary_flux
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    (∑ scale ∈ Finset.range depth,
        smoothDyadicLinearTransportTriadWork scale triad
          advectingMode transportedMode receiverMode) =
      (((tensorValleePoussinWeight (dyadicHodgeParameter depth) triad.transported : ℂ) -
          (tensorValleePoussinWeight (dyadicHodgeParameter 0) triad.transported : ℂ)) -
        ((tensorValleePoussinWeight (dyadicHodgeParameter depth) triad.receiver : ℂ) -
          (tensorValleePoussinWeight (dyadicHodgeParameter 0) triad.receiver : ℂ))) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  simp_rw [smoothDyadicLinearTransportTriadWork_eq_exchanged]
  exact sum_smoothDyadicExchangedTriadTransfer_eq_lowPass_boundary_flux
    depth triad advectingMode transportedMode receiverMode hdivergence

section Audit

#print axioms complexVectorSymmetricPhasePairing_real_smul_right
#print axioms linearMultiplierCoefficientWork_real_eq_weightedSourcePairing
#print axioms openSmoothDyadicLinearBandCoefficientStorage_eq_realSquares
#print axioms openSmoothDyadicBandCoefficientMass_le_linearMass
#print axioms openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicLinearBandCoefficientEnergy
#print axioms openPeriodicSolutionOn_openSmoothDyadicLinearBand_integrated_balance
#print axioms sum_smoothDyadicLinearCoefficientStorage_eq_lowPass_boundary
#print axioms sum_smoothDyadicLinearCoefficientWork_eq_lowPass_boundary
#print axioms sum_openSmoothDyadicLinearBandActualSignedWork_eq_lowPass_boundary
#print axioms adjacent_smoothDyadicLinearTransportTriadWorks_cancel
#print axioms sum_smoothDyadicLinearTransportTriadWork_eq_lowPass_boundary_flux

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
