import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution

/-!
# Compact-interior smooth dyadic band balance

**[proved-derived; formal-checked]** The exact smooth-band differential law is integrated on an
arbitrary compact interval strictly inside the open lifespan.  The nonlinear work is the actual,
aperture-independent projected vorticity source.  Compact clamping supplies a continuous exterior
chart for integration without assigning any value to the open solution outside its native time
carrier.

For positive viscosity, the exact balance and the spectral shell clock give an unconditional
finite-scale estimate for the time-integrated coefficient mass.  The estimate deliberately retains
the absolute signed-work integral.  Summing it uniformly over all scales is the remaining analytic
obligation; no terminal or global regularity claim is made here.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance

set_option backward.isDefEq.respectTransparency.types false

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The actual aperture-independent work -/

/-- The complex signed work of the actual projected nonlinear vorticity source on one smooth
band.  Unlike a finite-aperture presentation, this definition has no residual coordinate: the
complete source is already the receiver. -/
def openSmoothDyadicBandActualSignedWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture scale,
    complexVectorSymmetricPhasePairing
      (openFilteredVorticityCoefficient solution t scale k)
      ((dyadicHodgeBandWeight scale k : ℂ) •
        vorticityNonlinearMode solution t k)

/-- The real signed-work rate carried by the actual source. -/
def openSmoothDyadicBandActualSignedWorkRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  (openSmoothDyadicBandActualSignedWork solution t scale).re

/-- Every corrected finite-aperture presentation, including its reconstruction residual, returns
the same actual work. -/
theorem openSmoothDyadicBandSignedWork_eq_actual
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency) :
    openSmoothDyadicBandSignedWork solution t scale aperture =
      openSmoothDyadicBandActualSignedWork solution t scale := by
  unfold openSmoothDyadicBandSignedWork openSmoothDyadicBandActualSignedWork
  apply Finset.sum_congr rfl
  intro k _hk
  rw [openFilteredVorticitySignedSource_eq_actual]

/-- The actual smooth-band work varies continuously on the native open time carrier. -/
theorem continuous_openSmoothDyadicBandActualSignedWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicBandActualSignedWork solution · scale) := by
  unfold openSmoothDyadicBandActualSignedWork
  apply continuous_finsetSum
  intro k _hk
  have hcoefficient : Continuous
      (fun t : Ioo (0 : ℝ) T ↦
        openFilteredVorticityCoefficient solution t scale k) := by
    unfold openFilteredVorticityCoefficient
    exact (show Continuous (fun _ : Ioo (0 : ℝ) T ↦
        (dyadicHodgeBandWeight scale k : ℂ)) from continuous_const).smul
      (continuous_openPeriodicVorticityFourierMode solution k)
  have hsource : Continuous
      (fun t : Ioo (0 : ℝ) T ↦
        (dyadicHodgeBandWeight scale k : ℂ) •
          vorticityNonlinearMode solution t k) :=
    (show Continuous (fun _ : Ioo (0 : ℝ) T ↦
        (dyadicHodgeBandWeight scale k : ℂ)) from continuous_const).smul
      (continuous_vorticityNonlinearMode solution k)
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  apply Continuous.mul continuous_const
  apply Continuous.add <;> apply continuous_finsetSum <;> intro component _hcomponent
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hcoefficient)).mul
        ((continuous_apply component).comp hsource)
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hsource)).mul
        ((continuous_apply component).comp hcoefficient)

/-- The real actual signed-work rate is continuous on the native open time carrier. -/
theorem continuous_openSmoothDyadicBandActualSignedWorkRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicBandActualSignedWorkRate solution · scale) := by
  exact Complex.continuous_re.comp
    (continuous_openSmoothDyadicBandActualSignedWork solution scale)

/-! ## Real differential law and compact charts -/

/-- Half the actual smooth-band coefficient mass, the real storage face of the complex quadratic
receiver. -/
def openSmoothDyadicBandRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  (1 / 2 : ℝ) * openSmoothDyadicBandCoefficientMass solution t scale

theorem openSmoothDyadicBandCoefficientEnergy_eq_realEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openSmoothDyadicBandCoefficientEnergy solution scale t.1 =
      (openSmoothDyadicBandRealEnergy solution t scale : ℂ) := by
  unfold openSmoothDyadicBandCoefficientEnergy openSmoothDyadicBandRealEnergy
    openSmoothDyadicBandCoefficientMass
  rw [Complex.ofReal_mul, Complex.ofReal_sum
    (smoothDyadicBandNativeAperture scale), Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k _hk
  rw [openFilteredVorticityMode_eq_coefficient,
    complexVectorHermitianPairing_self_eq]

theorem openSmoothDyadicBandRealEnergy_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    0 ≤ openSmoothDyadicBandRealEnergy solution t scale := by
  unfold openSmoothDyadicBandRealEnergy openSmoothDyadicBandCoefficientMass
  exact mul_nonneg (by norm_num) <|
    Finset.sum_nonneg fun k _hk ↦
      Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _

/-- Real form of the exact pointwise smooth-band PDE law. -/
theorem openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    HasDerivAt
      (fun time : ℝ ↦
        (openSmoothDyadicBandCoefficientEnergy solution scale time).re)
      (-nu * openSmoothDyadicBandSpectralDissipationMass solution t scale +
        openSmoothDyadicBandActualSignedWorkRate solution t scale) t.1 := by
  have hcomplex :=
    openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandCoefficientEnergy
      solution t scale (∅ : Finset SpatialFrequency)
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t.1 hcomplex
  rw [openSmoothDyadicBandSpectralDissipation_eq_realFace,
    openSmoothDyadicBandSignedWork_eq_actual] at hreal
  have hreal' : HasDerivAt
      (fun time : ℝ ↦
        (openSmoothDyadicBandCoefficientEnergy solution scale time).re)
      ((-(nu : ℂ) *
          (openSmoothDyadicBandSpectralDissipationMass solution t scale : ℂ) +
        openSmoothDyadicBandActualSignedWork solution t scale).re) t.1 := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using hreal
  apply hreal'.congr_deriv
  simp [openSmoothDyadicBandActualSignedWorkRate]

/-- Compact clamping of the actual signed-work rate.  It is only a chart for integration: on the
addressed interval it is definitionally the open solution's native work rate. -/
def compactOpenSmoothDyadicBandActualSignedWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicBandActualSignedWorkRate solution
    (compactInteriorTime ha hab hbT time) scale

/-- Compact clamping of the real spectral dissipation. -/
def compactOpenSmoothDyadicBandSpectralDissipationMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicBandSpectralDissipationMass solution
    (compactInteriorTime ha hab hbT time) scale

/-- Compact clamping of the coefficient mass. -/
def compactOpenSmoothDyadicBandCoefficientMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicBandCoefficientMass solution
    (compactInteriorTime ha hab hbT time) scale

theorem continuous_openSmoothDyadicBandSpectralDissipationMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicBandSpectralDissipationMass solution · scale) := by
  unfold openSmoothDyadicBandSpectralDissipationMass complexVectorEuclideanSquare
  apply continuous_finsetSum
  intro k _hk
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro component _hcomponent
  apply Complex.continuous_normSq.comp
  exact (continuous_apply component).comp <|
    (show Continuous (fun _ : Ioo (0 : ℝ) T ↦
        (dyadicHodgeBandWeight scale k : ℂ)) from continuous_const).smul
      (continuous_openPeriodicVorticityFourierMode solution k)

theorem continuous_openSmoothDyadicBandCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (scale : ℕ) :
    Continuous (openSmoothDyadicBandCoefficientMass solution · scale) := by
  unfold openSmoothDyadicBandCoefficientMass complexVectorEuclideanSquare
  apply continuous_finsetSum
  intro k _hk
  apply continuous_finsetSum
  intro component _hcomponent
  apply Complex.continuous_normSq.comp
  exact (continuous_apply component).comp <|
    (show Continuous (fun _ : Ioo (0 : ℝ) T ↦
        (dyadicHodgeBandWeight scale k : ℂ)) from continuous_const).smul
      (continuous_openPeriodicVorticityFourierMode solution k)

theorem continuous_compactOpenSmoothDyadicBandActualSignedWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous
      (compactOpenSmoothDyadicBandActualSignedWorkRate solution ha hab hbT scale) :=
  (continuous_openSmoothDyadicBandActualSignedWorkRate solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)

theorem continuous_compactOpenSmoothDyadicBandSpectralDissipationMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous
      (compactOpenSmoothDyadicBandSpectralDissipationMass solution ha hab hbT scale) :=
  (continuous_openSmoothDyadicBandSpectralDissipationMass solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)

theorem continuous_compactOpenSmoothDyadicBandCoefficientMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous
      (compactOpenSmoothDyadicBandCoefficientMass solution ha hab hbT scale) :=
  (continuous_openSmoothDyadicBandCoefficientMass solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)

theorem compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicBandActualSignedWorkRate solution ha hab hbT scale)
      volume a b :=
  (continuous_compactOpenSmoothDyadicBandActualSignedWorkRate
    solution ha hab hbT scale).intervalIntegrable _ _

theorem compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicBandSpectralDissipationMass solution ha hab hbT scale)
      volume a b :=
  (continuous_compactOpenSmoothDyadicBandSpectralDissipationMass
    solution ha hab hbT scale).intervalIntegrable _ _

theorem compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicBandCoefficientMass solution ha hab hbT scale)
      volume a b :=
  (continuous_compactOpenSmoothDyadicBandCoefficientMass
    solution ha hab hbT scale).intervalIntegrable _ _

/-! ## Exact integrated balance and finite-scale payment -/

/-- **Exact compact-interior smooth-band energy balance.** -/
theorem openPeriodicSolutionOn_openSmoothDyadicBand_integrated_balance
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    openSmoothDyadicBandRealEnergy solution
        ⟨b, ha.trans_le hab, hbT⟩ scale +
        nu * ∫ time in a..b,
          compactOpenSmoothDyadicBandSpectralDissipationMass
            solution ha hab hbT scale time =
      openSmoothDyadicBandRealEnergy solution
          ⟨a, ha, hab.trans_lt hbT⟩ scale +
        ∫ time in a..b,
          compactOpenSmoothDyadicBandActualSignedWorkRate
            solution ha hab hbT scale time := by
  have hderivative : ∀ time ∈ uIcc a b,
      HasDerivAt
        (fun time : ℝ ↦
          (openSmoothDyadicBandCoefficientEnergy solution scale time).re)
        (-nu * compactOpenSmoothDyadicBandSpectralDissipationMass
              solution ha hab hbT scale time +
          compactOpenSmoothDyadicBandActualSignedWorkRate
              solution ha hab hbT scale time) time := by
    intro time htime
    rw [uIcc_of_le hab] at htime
    let ti : Ioo (0 : ℝ) T :=
      ⟨time, ha.trans_le htime.1, htime.2.trans_lt hbT⟩
    have h := openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandRealEnergy
      solution ti scale
    have hcompact : compactInteriorTime ha hab hbT time = ti := by
      apply Subtype.ext
      exact compactInteriorTime_eq ha hab hbT htime
    simpa [compactOpenSmoothDyadicBandSpectralDissipationMass,
      compactOpenSmoothDyadicBandActualSignedWorkRate, hcompact] using h
  have hintegrable : IntervalIntegrable
      (fun time ↦
        -nu * compactOpenSmoothDyadicBandSpectralDissipationMass
              solution ha hab hbT scale time +
          compactOpenSmoothDyadicBandActualSignedWorkRate
              solution ha hab hbT scale time) volume a b :=
    ((compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
      solution ha hab hbT scale).const_mul (-nu)).add
      (compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
        solution ha hab hbT scale)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderivative hintegrable
  rw [intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul] at hftc
  · have haEnergy := openSmoothDyadicBandCoefficientEnergy_eq_realEnergy
      solution ⟨a, ha, hab.trans_lt hbT⟩ scale
    have hbEnergy := openSmoothDyadicBandCoefficientEnergy_eq_realEnergy
      solution ⟨b, ha.trans_le hab, hbT⟩ scale
    have haReal := congrArg Complex.re haEnergy
    have hbReal := congrArg Complex.re hbEnergy
    simp only [Complex.ofReal_re] at haReal hbReal
    rw [haReal, hbReal] at hftc
    linear_combination -hftc
  · exact
      (compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
        solution ha hab hbT scale).const_mul (-nu)
  · exact compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
      solution ha hab hbT scale

/-- Positive viscosity pays the integrated spectral dissipation by initial band storage plus the
absolute actual signed work. -/
theorem openPeriodicSolutionOn_integral_smoothDyadicBandSpectralDissipationMass_le
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    nu * ∫ time in a..b,
        compactOpenSmoothDyadicBandSpectralDissipationMass
          solution ha hab hbT scale time ≤
      openSmoothDyadicBandRealEnergy solution
          ⟨a, ha, hab.trans_lt hbT⟩ scale +
        ∫ time in a..b,
          |compactOpenSmoothDyadicBandActualSignedWorkRate
            solution ha hab hbT scale time| := by
  have hbalance := openPeriodicSolutionOn_openSmoothDyadicBand_integrated_balance
    solution ha hab hbT scale
  have hterminal := openSmoothDyadicBandRealEnergy_nonneg solution
    ⟨b, ha.trans_le hab, hbT⟩ scale
  have hwork := intervalIntegral.integral_mono_on hab
    (compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
      solution ha hab hbT scale)
    ((compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
      solution ha hab hbT scale).abs)
    (fun time _htime ↦ le_abs_self _)
  linarith

/-- The exact shell clock converts the integrated dissipative payment into an unconditional
finite-scale coefficient-mass estimate. -/
theorem openPeriodicSolutionOn_four_pow_mul_integral_smoothDyadicBandCoefficientMass_le
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu) (scale : ℕ) :
    (4 : ℝ) ^ scale * ∫ time in a..b,
        compactOpenSmoothDyadicBandCoefficientMass
          solution ha hab hbT scale time ≤
      (openSmoothDyadicBandRealEnergy solution
          ⟨a, ha, hab.trans_lt hbT⟩ scale +
        ∫ time in a..b,
          |compactOpenSmoothDyadicBandActualSignedWorkRate
            solution ha hab hbT scale time|) / nu := by
  have hpointwise : ∀ time ∈ Icc a b,
      (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time ≤
        compactOpenSmoothDyadicBandSpectralDissipationMass
          solution ha hab hbT scale time := by
    intro time htime
    exact four_pow_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
      solution (compactInteriorTime ha hab hbT time) scale
  have hintegral := intervalIntegral.integral_mono_on hab
    ((compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
      solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))
    (compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
      solution ha hab hbT scale)
    hpointwise
  rw [intervalIntegral.integral_const_mul] at hintegral
  have hdiss :=
    openPeriodicSolutionOn_integral_smoothDyadicBandSpectralDissipationMass_le
      solution ha hab hbT scale
  apply (le_div_iff₀ hnu).2
  nlinarith

section Audit

#print axioms openSmoothDyadicBandSignedWork_eq_actual
#print axioms continuous_openSmoothDyadicBandActualSignedWorkRate
#print axioms openPeriodicSolutionOn_hasDerivAt_openSmoothDyadicBandRealEnergy
#print axioms openPeriodicSolutionOn_openSmoothDyadicBand_integrated_balance
#print axioms openPeriodicSolutionOn_integral_smoothDyadicBandSpectralDissipationMass_le
#print axioms openPeriodicSolutionOn_four_pow_mul_integral_smoothDyadicBandCoefficientMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
