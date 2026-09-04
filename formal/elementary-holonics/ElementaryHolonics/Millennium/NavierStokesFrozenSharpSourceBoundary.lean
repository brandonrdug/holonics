import ElementaryHolonics.Millennium.NavierStokesCriticalTimeReflection

/-!
# Frozen sharp source as a finite heat-semigroup boundary action

**[proved-derived; formal-checked]**  Freeze the actual sharp nonlinear source at one strict-
interior target time and integrate its heat-transported curl over a finite elapsed interval.
Before any coefficient norm is taken, the complete frequency/component population is exactly the
boundary action `(I - S_h)` transported through the inverse nonzero Stokes generator.

The zero frequency is retained and vanishes through the curl receiver.  No Dini finiteness and no
terminal-time control is assumed.  Integrating these frozen boundary populations over target time
still requires time integrability of the actual weighted `H2` nonlinear-source norm (or of the
standing quadratic weighted `H3` velocity majorant).
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact finite boundary/resolvent action -/

/-- The finite heat boundary scalar.  At zero generator it is totalized by the field inverse;
the subsequent curl coefficient vanishes there. -/
def finiteHeatBoundaryResolventScalar
    (nu horizon : ℝ) (k : SpatialFrequency) : ℝ :=
  (1 - heatStokesMultiplier nu horizon k) *
    (nu * torusStokesEigenvalue k)⁻¹

/-- Complete frequency-indexed curl boundary action of one frozen native weighted `H2` source.
This is the coefficient chart of `(I - S_h)(nu A)⁻¹ curl(source)`. -/
def frozenH2SourceCurlBoundaryAction
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) : ComplexVector :=
  (finiteHeatBoundaryResolventScalar nu horizon k : ℂ) •
    heatTransportedH2SourceCurlCoefficient nu 0 source k

/-- The standing heat clock factors as a scalar orbit multiplying the untransported curl
coefficient. -/
theorem heatTransportedH2SourceCurlCoefficient_eq_clock_smul_zero
    (nu elapsed : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient nu elapsed source k =
      (heatStokesMultiplier nu elapsed k : ℂ) •
        heatTransportedH2SourceCurlCoefficient nu 0 source k := by
  change frequencyCurlMultiplierCLM k
      (heatTransportedH2SourceCoefficient nu elapsed source k) = _
  have hclock : heatTransportedH2SourceCoefficient nu elapsed source k =
      (heatStokesMultiplier nu elapsed k : ℂ) •
        heatTransportedH2SourceCoefficient nu 0 source k := by
    ext component
    simp [heatTransportedH2SourceCoefficient]
  rw [hclock]
  exact (frequencyCurlMultiplierCLM k).map_smul
    (heatStokesMultiplier nu elapsed k : ℂ)
    (heatTransportedH2SourceCoefficient nu 0 source k)

/-- Exact scalar integral of one nonzero heat/Stokes orbit. -/
theorem intervalIntegral_heatStokesMultiplier_eq_boundary
    {nu : ℝ} (hnu : 0 < nu) (horizon : ℝ)
    {k : SpatialFrequency} (hk : k ≠ 0) :
    (∫ elapsed in 0..horizon, heatStokesMultiplier nu elapsed k) =
      finiteHeatBoundaryResolventScalar nu horizon k := by
  let rate : ℝ := nu * torusStokesEigenvalue k
  have hrate : 0 < rate := mul_pos hnu (torusStokesEigenvalue_pos hk)
  let primitive : ℝ → ℝ := fun elapsed ↦
    -rate⁻¹ * Real.exp (-rate * elapsed)
  have hderiv (elapsed : ℝ) :
      HasDerivAt primitive (heatStokesMultiplier nu elapsed k) elapsed := by
    have hinner : HasDerivAt (fun r : ℝ ↦ -rate * r) (-rate) elapsed := by
      simpa using (hasDerivAt_id elapsed).const_mul (-rate)
    have hexp := (Real.hasDerivAt_exp (-rate * elapsed)).comp elapsed hinner
    have hscaled := hexp.const_mul (-rate⁻¹)
    have hscaled' : HasDerivAt primitive
        ((-rate⁻¹) * (Real.exp (-rate * elapsed) * (-rate))) elapsed := by
      simpa [primitive] using hscaled
    convert hscaled' using 1
    rw [heatStokesMultiplier]
    dsimp [rate]
    field_simp [hrate.ne', (torusStokesEigenvalue_pos hk).ne']
  have hderivEq : deriv primitive =
      fun elapsed ↦ heatStokesMultiplier nu elapsed k := by
    funext elapsed
    exact (hderiv elapsed).deriv
  calc
    (∫ elapsed in 0..horizon, heatStokesMultiplier nu elapsed k) =
        primitive horizon - primitive 0 :=
      intervalIntegral.integral_deriv_eq_sub' primitive hderivEq
        (fun elapsed _ ↦ (hderiv elapsed).differentiableAt) (by
          exact (show Continuous (fun elapsed ↦
            heatStokesMultiplier nu elapsed k) by
              unfold heatStokesMultiplier
              fun_prop).continuousOn)
    _ = finiteHeatBoundaryResolventScalar nu horizon k := by
      simp only [primitive, finiteHeatBoundaryResolventScalar,
        heatStokesMultiplier, rate]
      field_simp [hrate.ne', (torusStokesEigenvalue_pos hk).ne']
      simp
      abel

/-- The elapsed integral of the frozen curl is exactly the finite boundary/resolvent action,
frequency by frequency and before every absolute-mass receiver. -/
theorem intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
    {nu : ℝ} (hnu : 0 < nu) (horizon : ℝ)
    (source : PeriodicVectorWeightedSobolev 2) (k : SpatialFrequency) :
    (∫ elapsed in 0..horizon,
        heatTransportedH2SourceCurlCoefficient nu elapsed source k) =
      frozenH2SourceCurlBoundaryAction nu horizon source k := by
  by_cases hk : k = 0
  · subst k
    simp [frozenH2SourceCurlBoundaryAction,
      finiteHeatBoundaryResolventScalar,
      heatTransportedH2SourceCurlCoefficient,
      frequencyCurlMultiplier_zero]
  · have hclock : (fun elapsed ↦
        heatTransportedH2SourceCurlCoefficient nu elapsed source k) =
      (fun elapsed ↦ (heatStokesMultiplier nu elapsed k : ℂ) •
        heatTransportedH2SourceCurlCoefficient nu 0 source k) := by
        funext elapsed
        exact heatTransportedH2SourceCurlCoefficient_eq_clock_smul_zero
          nu elapsed source k
    rw [hclock]
    rw [intervalIntegral.integral_smul_const]
    let realClock : ℝ → ℝ := fun elapsed ↦
      heatStokesMultiplier nu elapsed k
    let realClockIntegral : ℝ :=
      ∫ elapsed in 0..horizon, realClock elapsed
    have hcoe :
        (∫ elapsed in 0..horizon,
          (realClock elapsed : ℂ)) =
        (realClockIntegral : ℂ) := by
      dsimp only [realClockIntegral]
      exact RCLike.intervalIntegral_ofReal (𝕜 := ℂ)
        (f := realClock)
    change ((∫ elapsed in 0..horizon, (realClock elapsed : ℂ)) •
      heatTransportedH2SourceCurlCoefficient nu 0 source k) = _
    rw [hcoe]
    dsimp only [realClockIntegral, realClock]
    rw [intervalIntegral_heatStokesMultiplier_eq_boundary hnu horizon hk]
    rfl

/-! ## Direct cancellation-sensitive spectral reconstruction -/

/-- Every nonzero lattice mode has at least unit Stokes spectral cost. -/
theorem one_le_torusStokesEigenvalue_of_ne_zero
    {k : SpatialFrequency} (hk : k ≠ 0) :
    1 ≤ torusStokesEigenvalue k := by
  obtain ⟨coordinate, hcoordinate⟩ := Function.ne_iff.mp hk
  have habsInt : (1 : ℤ) ≤ |k coordinate| := Int.one_le_abs hcoordinate
  have habsReal : (1 : ℝ) ≤ |(k coordinate : ℝ)| := by
    exact_mod_cast habsInt
  have hcoordinateSq : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  have hfrequency : 1 ≤ frequencySquared k := by
    nlinarith [sq_abs (k coordinate : ℝ)]
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  rw [torusStokesEigenvalue]
  nlinarith

/-- Cancellation-sensitive coefficient multiplier for the finite boundary action, with the
native weighted `H2` reconstruction factor included. -/
def frozenH2CurlBoundarySpectralFactor
    (nu horizon : ℝ) (k : SpatialFrequency) : ℝ :=
  |finiteHeatBoundaryResolventScalar nu horizon k| *
    Real.sqrt (torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 2 k)

theorem frozenH2CurlBoundarySpectralFactor_nonneg
    (nu horizon : ℝ) (k : SpatialFrequency) :
    0 ≤ frozenH2CurlBoundarySpectralFactor nu horizon k := by
  unfold frozenH2CurlBoundarySpectralFactor
  positivity

/-- The exact finite-boundary spectral factor has a summable square.  The proof uses the
nonzero lattice gap and keeps the actual cancellation factor in the constructed carrier. -/
theorem frozenH2CurlBoundarySpectralFactor_sq_le
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (k : SpatialFrequency) :
    frozenH2CurlBoundarySpectralFactor nu horizon k ^ 2 ≤
      2 * nu⁻¹ ^ 2 * (periodicSobolevWeight 3 k)⁻¹ := by
  by_cases hk : k = 0
  · subst k
    simp [frozenH2CurlBoundarySpectralFactor,
      finiteHeatBoundaryResolventScalar]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sq_nonneg nu)))
      (inv_nonneg.mpr (periodicSobolevWeight_nonneg 3 0))
  · have hlambda : 0 < torusStokesEigenvalue k :=
      torusStokesEigenvalue_pos hk
    have hlambdaOne : 1 ≤ torusStokesEigenvalue k :=
      one_le_torusStokesEigenvalue_of_ne_zero hk
    have hclock := heatStokesMultiplier_mem_unitInterval hnu.le hhorizon k
    have honeMinus : 0 ≤ 1 - heatStokesMultiplier nu horizon k := by
      linarith [hclock.2]
    have honeMinusLe : 1 - heatStokesMultiplier nu horizon k ≤ 1 := by
      linarith [hclock.1]
    have hnuLambda : 0 < nu * torusStokesEigenvalue k :=
      mul_pos hnu hlambda
    have hweightTwo : 0 < periodicSobolevWeight 2 k :=
      periodicSobolevWeight_pos 2 k
    have hweightThree : 0 < periodicSobolevWeight 3 k :=
      periodicSobolevWeight_pos 3 k
    have hboundaryNonneg :
        0 ≤ finiteHeatBoundaryResolventScalar nu horizon k := by
      unfold finiteHeatBoundaryResolventScalar
      exact mul_nonneg honeMinus (inv_nonneg.mpr hnuLambda.le)
    have honeMinusSq :
        (1 - heatStokesMultiplier nu horizon k) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (1 - heatStokesMultiplier nu horizon k)]
    have hkey :
        (1 - heatStokesMultiplier nu horizon k) ^ 2 *
            (1 + torusStokesEigenvalue k) ≤
          2 * torusStokesEigenvalue k := by
      calc
        (1 - heatStokesMultiplier nu horizon k) ^ 2 *
            (1 + torusStokesEigenvalue k) ≤
            1 * (1 + torusStokesEigenvalue k) :=
          mul_le_mul_of_nonneg_right honeMinusSq (by positivity)
        _ ≤ 2 * torusStokesEigenvalue k := by linarith
    rw [frozenH2CurlBoundarySpectralFactor,
      abs_of_nonneg hboundaryNonneg, div_pow, mul_pow,
      Real.sq_sqrt (torusStokesEigenvalue_nonneg k),
      Real.sq_sqrt (periodicSobolevWeight_nonneg 2 k)]
    unfold finiteHeatBoundaryResolventScalar periodicSobolevWeight
    field_simp [hnu.ne', hlambda.ne', hweightTwo.ne', hweightThree.ne']
    nlinarith [hkey]

/-- The actual cancellation-sensitive boundary multiplier as a complete square-summable
spectral reconstruction population. -/
def frozenH2CurlBoundarySpectralKernel
    (nu horizon : ℝ) (hnu : 0 < nu) (hhorizon : 0 ≤ horizon) :
    PeriodicRealFourierL2 :=
  ⟨fun k ↦ frozenH2CurlBoundarySpectralFactor nu horizon k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hmajor := summable_periodicSobolevWeight_three_inv.mul_left
      (2 * nu⁻¹ ^ 2)
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (frozenH2CurlBoundarySpectralFactor_nonneg nu horizon _)] using
      Summable.of_nonneg_of_le
        (fun k ↦ sq_nonneg (frozenH2CurlBoundarySpectralFactor nu horizon k))
        (frozenH2CurlBoundarySpectralFactor_sq_le hnu hhorizon) hmajor⟩

/-- Named finite reconstruction constant of the exact boundary multiplier.  Unlike the elapsed
triangle majorant, this norm retains cancellation in `I - S_h`. -/
def frozenH2CurlBoundarySpectralConstant
    (nu horizon : ℝ) (hnu : 0 < nu) (hhorizon : 0 ≤ horizon) : ℝ :=
  ‖frozenH2CurlBoundarySpectralKernel nu horizon hnu hhorizon‖

theorem frozenH2CurlBoundarySpectralConstant_nonneg
    (nu horizon : ℝ) (hnu : 0 < nu) (hhorizon : 0 ≤ horizon) :
    0 ≤ frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon :=
  norm_nonneg _

private theorem frozenH2CurlBoundarySpectralFactor_mul_stateNorm_eq
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (k : SpatialFrequency) :
    frozenH2CurlBoundarySpectralFactor nu horizon k * ‖source component k‖ =
      |finiteHeatBoundaryResolventScalar nu horizon k| *
        Real.sqrt (torusStokesEigenvalue k) *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 2 k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos 2 k)
  rw [weightedSobolevRawCoefficients_apply, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  unfold frozenH2CurlBoundarySpectralFactor
  field_simp

private theorem boundaryDerivativeTerm_le_spectralProduct
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (k : SpatialFrequency) :
    |finiteHeatBoundaryResolventScalar nu horizon k| *
        ‖heatTransportedFirstDerivativeCoefficient
          nu 0 source component coordinate k‖ ≤
      frozenH2CurlBoundarySpectralFactor nu horizon k *
        ‖source component k‖ := by
  have hderivative :
      ‖heatTransportedFirstDerivativeCoefficient
          nu 0 source component coordinate k‖ ≤
        Real.sqrt (torusStokesEigenvalue k) *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖ := by
    unfold heatTransportedFirstDerivativeCoefficient
    rw [heatStokesMultiplier_zero_time, Complex.ofReal_one, mul_one, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_orderedFirstDerivativeMultiplier_le_sqrt_stokes coordinate k)
      (norm_nonneg _)
  rw [frozenH2CurlBoundarySpectralFactor_mul_stateNorm_eq]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hderivative
      (abs_nonneg (finiteHeatBoundaryResolventScalar nu horizon k))

/-- One finite derivative-occurrence population is controlled directly by the exact boundary
spectral constant, with no elapsed-time triangle estimate. -/
theorem finiteBoundaryDerivativeMass_le_spectralConstant
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (source : PeriodicVectorWeightedSobolev 2)
    (modes : Finset SpatialFrequency) (component coordinate : Fin 3) :
    (∑ k ∈ modes,
      |finiteHeatBoundaryResolventScalar nu horizon k| *
        ‖heatTransportedFirstDerivativeCoefficient
          nu 0 source component coordinate k‖) ≤
      frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon * ‖source‖ := by
  let kernel := frozenH2CurlBoundarySpectralKernel nu horizon hnu hhorizon
  let stateAbsolute := weightedStateAbsolute 2 (source component)
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hproduct := lp.summable_mul hholder kernel stateAbsolute
  have hmajor : Summable fun k : SpatialFrequency ↦
      frozenH2CurlBoundarySpectralFactor nu horizon k *
        ‖source component k‖ := by
    apply hproduct.congr
    intro k
    simp only [kernel, frozenH2CurlBoundarySpectralKernel,
      stateAbsolute, weightedStateAbsolute, Real.norm_eq_abs,
      abs_of_nonneg (frozenH2CurlBoundarySpectralFactor_nonneg nu horizon k),
      abs_of_nonneg (norm_nonneg (source component k))]
  have hcs := lp.tsum_mul_le_mul_norm' hholder kernel stateAbsolute
  have hmajorBound :
      (∑' k : SpatialFrequency,
        frozenH2CurlBoundarySpectralFactor nu horizon k *
          ‖source component k‖) ≤
        frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
          ‖source component‖ := by
    calc
      (∑' k : SpatialFrequency,
          frozenH2CurlBoundarySpectralFactor nu horizon k *
            ‖source component k‖) =
          ∑' k : SpatialFrequency, ‖kernel k‖ * ‖stateAbsolute k‖ := by
        apply tsum_congr
        intro k
        simp only [kernel, frozenH2CurlBoundarySpectralKernel,
          stateAbsolute, weightedStateAbsolute, Real.norm_eq_abs,
          abs_of_nonneg (frozenH2CurlBoundarySpectralFactor_nonneg nu horizon k),
          abs_of_nonneg (norm_nonneg (source component k))]
      _ ≤ ‖kernel‖ * ‖stateAbsolute‖ := hcs
      _ = frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
          ‖source component‖ := by
        rw [norm_weightedStateAbsolute]
        rfl
  calc
    (∑ k ∈ modes,
      |finiteHeatBoundaryResolventScalar nu horizon k| *
        ‖heatTransportedFirstDerivativeCoefficient
          nu 0 source component coordinate k‖) ≤
        ∑ k ∈ modes,
          frozenH2CurlBoundarySpectralFactor nu horizon k *
            ‖source component k‖ := by
      exact Finset.sum_le_sum fun k _hk ↦
        boundaryDerivativeTerm_le_spectralProduct
          nu horizon source component coordinate k
    _ ≤ ∑' k : SpatialFrequency,
        frozenH2CurlBoundarySpectralFactor nu horizon k *
          ‖source component k‖ := by
      exact hmajor.sum_le_tsum modes (fun k _ ↦
        mul_nonneg
          (frozenH2CurlBoundarySpectralFactor_nonneg nu horizon k)
          (norm_nonneg _))
    _ ≤ frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
        ‖source component‖ := hmajorBound
    _ ≤ frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
        ‖source‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm source component)
        (frozenH2CurlBoundarySpectralConstant_nonneg nu horizon hnu hhorizon)

private theorem complexVectorL1_frozenH2SourceCurlBoundaryAction_le
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    complexVectorL1 (frozenH2SourceCurlBoundaryAction nu horizon source k) ≤
      |finiteHeatBoundaryResolventScalar nu horizon k| *
        complexCurlEntryMass
          (heatTransportedFirstDerivativeJacobianCoefficient nu 0 source k) := by
  rw [frozenH2SourceCurlBoundaryAction, complexVectorL1_smul]
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
  exact complexVectorL1_complexCurlFromJacobian_le _

/-! ## Finite apertures and the complete mass fibre -/

/-- Finite-aperture absolute coefficient mass of the already-integrated boundary action. -/
def finiteFrozenH2SourceCurlBoundaryMass
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (modes : Finset SpatialFrequency) : ℝ :=
  ∑ k ∈ modes, complexVectorL1
    (frozenH2SourceCurlBoundaryAction nu horizon source k)

/-- **Direct cancellation-sensitive finite boundary estimate.**  Absolute mass is taken only
after the finite semigroup difference has acted.  The named spectral constant retains the
`I - S_h` cancellation and is finite by its genuine square-summable carrier. -/
theorem finiteFrozenH2SourceCurlBoundaryMass_le_directSpectral
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (source : PeriodicVectorWeightedSobolev 2)
    (modes : Finset SpatialFrequency) :
    finiteFrozenH2SourceCurlBoundaryMass nu horizon source modes ≤
      6 * frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon * ‖source‖ := by
  let C := frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon
  have h21 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 2 1
  have h12 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 1 2
  have h02 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 0 2
  have h20 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 2 0
  have h10 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 1 0
  have h01 := finiteBoundaryDerivativeMass_le_spectralConstant
    hnu hhorizon source modes 0 1
  calc
    finiteFrozenH2SourceCurlBoundaryMass nu horizon source modes ≤
        ∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            complexCurlEntryMass
              (heatTransportedFirstDerivativeJacobianCoefficient
                nu 0 source k) := by
      unfold finiteFrozenH2SourceCurlBoundaryMass
      exact Finset.sum_le_sum fun k _hk ↦
        complexVectorL1_frozenH2SourceCurlBoundaryAction_le
          nu horizon source k
    _ =
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 2 1 k‖) +
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 1 2 k‖) +
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 0 2 k‖) +
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 2 0 k‖) +
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 1 0 k‖) +
        (∑ k ∈ modes,
          |finiteHeatBoundaryResolventScalar nu horizon k| *
            ‖heatTransportedFirstDerivativeCoefficient nu 0 source 0 1 k‖) := by
      simp only [complexCurlEntryMass,
        heatTransportedFirstDerivativeJacobianCoefficient, mul_add,
        Finset.sum_add_distrib]
    _ ≤ 6 * C * ‖source‖ := by
      dsimp only [C]
      linarith
    _ = 6 * frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
        ‖source‖ := rfl

/-- The remaining owned source service: the sharp first-derivative clock integrated only after
the frozen boundary action has been identified exactly. -/
def frozenH2SourceBoundaryServiceRate
    (nu : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (elapsed : ℝ) : ℝ :=
  6 * sharpHeatFirstDerivativeH2Constant *
    clockedFirstDerivativeH2ServiceKernel nu elapsed * ‖source‖

theorem continuous_heatTransportedH2SourceCurlCoefficient
    (nu : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    Continuous (fun elapsed ↦
      heatTransportedH2SourceCurlCoefficient nu elapsed source k) := by
  rw [show (fun elapsed ↦
      heatTransportedH2SourceCurlCoefficient nu elapsed source k) =
    (fun elapsed ↦ (heatStokesMultiplier nu elapsed k : ℂ) •
      heatTransportedH2SourceCurlCoefficient nu 0 source k) by
      funext elapsed
      exact heatTransportedH2SourceCurlCoefficient_eq_clock_smul_zero
        nu elapsed source k]
  unfold heatStokesMultiplier
  fun_prop

theorem continuous_complexVectorL1_heatTransportedH2SourceCurlCoefficient
    (nu : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    Continuous (fun elapsed ↦ complexVectorL1
      (heatTransportedH2SourceCurlCoefficient nu elapsed source k)) := by
  have h := continuous_heatTransportedH2SourceCurlCoefficient nu source k
  unfold complexVectorL1
  fun_prop

/-- At every positive elapsed face of a local heat aperture, every finite frequency population
is bounded by the actual complete occurrence mass and hence by the weighted `H2` source norm. -/
theorem finite_heatTransportedH2SourceCurlMass_le_serviceRate
    {nu horizon elapsed : ℝ} (hnu : 0 < nu)
    (hlocal : 2 * (nu * horizon) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2)
    (modes : Finset SpatialFrequency) (helapsed : elapsed ∈ Ioo 0 horizon) :
    (∑ k ∈ modes, complexVectorL1
      (heatTransportedH2SourceCurlCoefficient nu elapsed source k)) ≤
        frozenH2SourceBoundaryServiceRate nu source elapsed := by
  have hnuElapsed : 0 < nu * elapsed := mul_pos hnu helapsed.1
  have hlocalElapsed : 2 * (nu * elapsed) ≤ 1 := by
    have hstep : 2 * (nu * elapsed) ≤ 2 * (nu * horizon) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left helapsed.2.le hnu.le) (by norm_num)
    exact hstep.trans hlocal
  have hsummable := summable_heatTransportedH2SourceCurlEntryMass
    nu elapsed hnuElapsed source
  calc
    (∑ k ∈ modes, complexVectorL1
        (heatTransportedH2SourceCurlCoefficient nu elapsed source k)) ≤
      ∑ k ∈ modes, complexCurlEntryMass
        (heatTransportedFirstDerivativeJacobianCoefficient
          nu elapsed source k) := by
        gcongr with k hk
        rw [heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
        exact complexVectorL1_complexCurlFromJacobian_le _
    _ ≤ heatTransportedH2SourceCurlOccurrenceMass nu elapsed source := by
      exact hsummable.sum_le_tsum modes (fun _ _ ↦ by
        unfold complexCurlEntryMass
        positivity)
    _ ≤ frozenH2SourceBoundaryServiceRate nu source elapsed := by
      simpa [frozenH2SourceBoundaryServiceRate,
        clockedFirstDerivativeH2ServiceKernel, mul_assoc] using
        (heatTransportedH2SourceCurlOccurrenceMass_le
          nu elapsed hnuElapsed hlocalElapsed source)

/-- The service rate is interval-integrable on every positive finite aperture. -/
theorem intervalIntegrable_frozenH2SourceBoundaryServiceRate
    (nu horizon : ℝ) (hnu : 0 < nu) (hhorizon : 0 < horizon)
    (source : PeriodicVectorWeightedSobolev 2) :
    IntervalIntegrable (frozenH2SourceBoundaryServiceRate nu source)
      volume 0 horizon := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hhorizon.le]
  unfold frozenH2SourceBoundaryServiceRate
  have hscaled := (integrableOn_clockedFirstDerivativeH2ServiceKernel
    nu horizon hnu hhorizon).const_mul
      ((6 * sharpHeatFirstDerivativeH2Constant) * ‖source‖)
  exact hscaled.congr (Filter.Eventually.of_forall fun elapsed ↦ by ring)

/-- **Uniform finite-aperture boundary estimate.**  The exact integrated boundary population is
bounded by one integrable clock service times the literal weighted `H2` source norm. -/
theorem finiteFrozenH2SourceCurlBoundaryMass_le_integral_service
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 < horizon)
    (hlocal : 2 * (nu * horizon) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2)
    (modes : Finset SpatialFrequency) :
    finiteFrozenH2SourceCurlBoundaryMass nu horizon source modes ≤
      ∫ elapsed in 0..horizon,
        frozenH2SourceBoundaryServiceRate nu source elapsed := by
  let finiteRate : ℝ → ℝ := fun elapsed ↦
    ∑ k ∈ modes, complexVectorL1
      (heatTransportedH2SourceCurlCoefficient nu elapsed source k)
  have hfiniteContinuous : Continuous finiteRate := by
    unfold finiteRate complexVectorL1
    apply continuous_finsetSum modes
    intro k _hk
    have hmode := continuous_heatTransportedH2SourceCurlCoefficient
      nu source k
    exact (((Continuous.norm
      ((ContinuousLinearMap.proj (R := ℂ) 0).continuous.comp hmode)).add
      (Continuous.norm
        ((ContinuousLinearMap.proj (R := ℂ) 1).continuous.comp hmode))).add
      (Continuous.norm
        ((ContinuousLinearMap.proj (R := ℂ) 2).continuous.comp hmode)))
  have hfiniteIntegrable : IntervalIntegrable finiteRate volume 0 horizon :=
    hfiniteContinuous.intervalIntegrable 0 horizon
  have hserviceIntegrable := intervalIntegrable_frozenH2SourceBoundaryServiceRate
    nu horizon hnu hhorizon source
  calc
    finiteFrozenH2SourceCurlBoundaryMass nu horizon source modes =
        ∑ k ∈ modes, complexVectorL1
          (∫ elapsed in 0..horizon,
            heatTransportedH2SourceCurlCoefficient nu elapsed source k) := by
      unfold finiteFrozenH2SourceCurlBoundaryMass
      apply Finset.sum_congr rfl
      intro k _hk
      rw [intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
        hnu horizon source k]
    _ ≤ ∑ k ∈ modes, ∫ elapsed in 0..horizon,
        complexVectorL1
          (heatTransportedH2SourceCurlCoefficient nu elapsed source k) := by
      gcongr with k hk
      exact complexVectorL1_intervalIntegral_le hhorizon.le
        (continuous_heatTransportedH2SourceCurlCoefficient nu source k)
    _ = ∫ elapsed in 0..horizon, finiteRate elapsed := by
      dsimp [finiteRate]
      rw [intervalIntegral.integral_finsetSum]
      intro k _hk
      exact (continuous_complexVectorL1_heatTransportedH2SourceCurlCoefficient
        nu source k).intervalIntegrable 0 horizon
    _ ≤ ∫ elapsed in 0..horizon,
        frozenH2SourceBoundaryServiceRate nu source elapsed := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo hhorizon.le
        hfiniteIntegrable hserviceIntegrable
        (fun elapsed helapsed ↦
          finite_heatTransportedH2SourceCurlMass_le_serviceRate
            hnu hlocal source modes helapsed)

/-- Extended complete reconstruction fibre of the integrated frozen boundary population. -/
def completeFrozenH2SourceCurlBoundaryMass
    (nu horizon : ℝ) (source : PeriodicVectorWeightedSobolev 2) : ℝ≥0∞ :=
  ⨆ modes : Finset SpatialFrequency,
    ENNReal.ofReal
      (finiteFrozenH2SourceCurlBoundaryMass nu horizon source modes)

/-- The complete coefficient fibre inherits the same direct finite-semigroup boundary estimate.
This is the cancellation-sensitive alternative to integrating coefficient mass over elapsed
time. -/
theorem completeFrozenH2SourceCurlBoundaryMass_le_directSpectral
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (source : PeriodicVectorWeightedSobolev 2) :
    completeFrozenH2SourceCurlBoundaryMass nu horizon source ≤
      ENNReal.ofReal
        (6 * frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
          ‖source‖) := by
  unfold completeFrozenH2SourceCurlBoundaryMass
  apply iSup_le
  intro modes
  exact ENNReal.ofReal_le_ofReal
    (finiteFrozenH2SourceCurlBoundaryMass_le_directSpectral
      hnu hhorizon source modes)

/-- The complete coefficient fibre is finite whenever the literal source has its already-owned
weighted `H2` norm.  This is a frozen-time statement, not target-time integrability. -/
theorem completeFrozenH2SourceCurlBoundaryMass_le_integral_service
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 < horizon)
    (hlocal : 2 * (nu * horizon) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2) :
    completeFrozenH2SourceCurlBoundaryMass nu horizon source ≤
      ENNReal.ofReal
        (∫ elapsed in 0..horizon,
          frozenH2SourceBoundaryServiceRate nu source elapsed) := by
  unfold completeFrozenH2SourceCurlBoundaryMass
  apply iSup_le
  intro modes
  exact ENNReal.ofReal_le_ofReal
    (finiteFrozenH2SourceCurlBoundaryMass_le_integral_service
      hnu hhorizon hlocal source modes)

/-! ## The actual frozen nonlinear source -/

/-- Complete boundary action of the literal sharp nonlinear source frozen at one actual open
solution slice. -/
def openFrozenSharpSourceCurlBoundaryAction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (targetTime : Ioo (0 : ℝ) T) (horizon : ℝ)
    (k : SpatialFrequency) : ComplexVector :=
  frozenH2SourceCurlBoundaryAction nu horizon
    (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime)) k

/-- Complete absolute coefficient-mass fibre of the literal sharp nonlinear source frozen at
one actual open-solution slice. -/
def openFrozenSharpSourceCurlBoundaryMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (targetTime : Ioo (0 : ℝ) T) (horizon : ℝ) : ℝ≥0∞ :=
  completeFrozenH2SourceCurlBoundaryMass nu horizon
    (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime))

/-- **Actual full reconstruction fibre.**  The equality retains every spatial frequency and all
three curl components; no coefficient is discarded and no norm has yet been taken. -/
theorem openFrozenSharpSourceCurlBoundaryAction_eq_elapsedIntegral
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (targetTime : Ioo (0 : ℝ) T) (horizon : ℝ) :
    openFrozenSharpSourceCurlBoundaryAction solution targetTime horizon =
      fun k ↦ ∫ elapsed in 0..horizon,
        heatTransportedH2SourceCurlCoefficient nu elapsed
          (sharpNonlinearSource
            (openVelocityWeightedH3State solution targetTime)) k := by
  funext k
  exact (intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
    hnu horizon
      (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime)) k).symm

/-- The actual frozen complete boundary population is paid by the finite elapsed service of its
literal weighted `H2` nonlinear-source norm.  No target-time integrability is asserted. -/
theorem openFrozenSharpSourceCurlBoundaryMass_le_integral_service
    {T nu horizon : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hhorizon : 0 < horizon)
    (hlocal : 2 * (nu * horizon) ≤ 1)
    (targetTime : Ioo (0 : ℝ) T) :
    openFrozenSharpSourceCurlBoundaryMass solution targetTime horizon ≤
      ENNReal.ofReal
        (∫ elapsed in 0..horizon,
          frozenH2SourceBoundaryServiceRate nu
            (sharpNonlinearSource
              (openVelocityWeightedH3State solution targetTime)) elapsed) := by
  exact completeFrozenH2SourceCurlBoundaryMass_le_integral_service
    hnu hhorizon hlocal
      (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime))

/-- **Actual cancellation-sensitive full-fibre estimate.**  The literal frozen nonlinear source
is controlled directly after `(I - S_h)` acts.  The remaining target-time quantity is exactly its
weighted `H2` norm. -/
theorem openFrozenSharpSourceCurlBoundaryMass_le_directSpectral
    {T nu horizon : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (targetTime : Ioo (0 : ℝ) T) :
    openFrozenSharpSourceCurlBoundaryMass solution targetTime horizon ≤
      ENNReal.ofReal
        (6 * frozenH2CurlBoundarySpectralConstant nu horizon hnu hhorizon *
          ‖sharpNonlinearSource
            (openVelocityWeightedH3State solution targetTime)‖) := by
  exact completeFrozenH2SourceCurlBoundaryMass_le_directSpectral
    hnu hhorizon
      (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime))

section Audit

#print axioms heatTransportedH2SourceCurlCoefficient_eq_clock_smul_zero
#print axioms intervalIntegral_heatStokesMultiplier_eq_boundary
#print axioms intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
#print axioms openFrozenSharpSourceCurlBoundaryAction_eq_elapsedIntegral
#print axioms frozenH2CurlBoundarySpectralFactor_sq_le
#print axioms finiteFrozenH2SourceCurlBoundaryMass_le_directSpectral
#print axioms completeFrozenH2SourceCurlBoundaryMass_le_directSpectral
#print axioms finiteFrozenH2SourceCurlBoundaryMass_le_integral_service
#print axioms completeFrozenH2SourceCurlBoundaryMass_le_integral_service
#print axioms openFrozenSharpSourceCurlBoundaryMass_le_integral_service
#print axioms openFrozenSharpSourceCurlBoundaryMass_le_directSpectral

end Audit

end Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
