import ElementaryHolonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
import ElementaryHolonics.Millennium.NavierStokesOpenCompactWeightedPath
import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
import ElementaryHolonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
import ElementaryHolonics.Millennium.NavierStokesTerminalEnergySeparation
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay

/-!
# Square/absolute ownership of the adaptive reciprocal-clock nonlinear source

**[proved-derived; formal-checked]** The reciprocal-clock Fubini passage leaves an actual
unclocked vorticity-source population on two adjacent dyadic shells.  This module pays that
population from the genuine native weighted `H2` norm of `sharpNonlinearSource`, using finite
shell Cauchy--Schwarz before the standing quadratic weighted-`H3` source estimate.

The full vector coefficient is identified before taking its norm.  The six oriented derivative
occurrences provide a magnitude receiver only; the orthogonal-output direction remainder from the
imported separator is retained as the exact unpaid reconstruction fibre.  No material or
co-rotating factorization is asserted for that fibre.

The resulting finite scale word has no depth factor on every ordered compact interval strictly
inside the open lifespan.  Its cost is the compact-time integral of the actual weighted-`H3`
square current.  This current is not replaced by energy or enstrophy, and no terminal-uniform
claim is made.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceClockBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTerminalEnergySeparation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction

set_option maxHeartbeats 2400000

/-! ## The actual finite two-shell population -/

/-- Actual two-shell mode population presented to one smooth dyadic band. -/
def dyadicNonlinearSourceModes (scale : ℕ) : Finset SpatialFrequency :=
  dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)

theorem dyadicNonlinearSourceModes_subset_outerCube (scale : ℕ) :
    dyadicNonlinearSourceModes scale ⊆ frequencyCube (dyadicRadius (scale + 2)) := by
  intro frequency hfrequency
  rw [dyadicNonlinearSourceModes, Finset.mem_union] at hfrequency
  rcases hfrequency with hfrequency | hfrequency
  · exact frequencyCube_mono (by
      simp only [dyadicRadius]
      exact Nat.pow_le_pow_right (by norm_num) (by omega))
        ((mem_dyadicFrequencyShell_iff scale frequency).mp hfrequency).1
  · simpa only [show scale + 1 + 1 = scale + 2 by omega] using
      ((mem_dyadicFrequencyShell_iff (scale + 1) frequency).mp hfrequency).1

/-- The actual adjacent-shell population has at most `729 R^3` modes at radius `R = 2^j`.
The constant retains the full integer cube, including boundary and zero faces. -/
theorem card_dyadicNonlinearSourceModes_le (scale : ℕ) :
    ((dyadicNonlinearSourceModes scale).card : ℝ) ≤
      729 * (dyadicRadius scale : ℝ) ^ 3 := by
  have hcardNat : (dyadicNonlinearSourceModes scale).card ≤
      (frequencyCube (dyadicRadius (scale + 2))).card :=
    Finset.card_le_card (dyadicNonlinearSourceModes_subset_outerCube scale)
  rw [card_frequencyCube] at hcardNat
  have hcardReal : ((dyadicNonlinearSourceModes scale).card : ℝ) ≤
      ((2 * dyadicRadius (scale + 2) + 1) ^ 3 : ℕ) := by
    exact_mod_cast hcardNat
  have hradius : 1 ≤ (dyadicRadius scale : ℝ) := by
    exact_mod_cast Nat.one_le_pow scale 2 (by norm_num)
  have hstep : (dyadicRadius (scale + 2) : ℝ) =
      4 * (dyadicRadius scale : ℝ) := by
    simp [dyadicRadius, pow_add]
    ring
  have hlinear : ((2 * dyadicRadius (scale + 2) + 1 : ℕ) : ℝ) ≤
      9 * (dyadicRadius scale : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hstep]
    linarith
  calc
    ((dyadicNonlinearSourceModes scale).card : ℝ) ≤
        (((2 * dyadicRadius (scale + 2) + 1 : ℕ) : ℝ) ^ 3) := by
      norm_num only [Nat.cast_pow] at hcardReal ⊢
      exact hcardReal
    _ ≤ (9 * (dyadicRadius scale : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hlinear 3
    _ = 729 * (dyadicRadius scale : ℝ) ^ 3 := by ring

/-! ## Square ownership of one derivative occurrence -/

/-- Modewise `H2` reconstruction factor of one unclocked spatial derivative. -/
def dyadicH2FirstDerivativeKernelFactor
    (coordinate : Fin 3) (frequency : SpatialFrequency) : ℝ :=
  ‖orderedDerivativeMultiplier 1 (![coordinate]) frequency‖ /
    Real.sqrt (periodicSobolevWeight 2 frequency)

theorem dyadicH2FirstDerivativeKernelFactor_nonneg
    (coordinate : Fin 3) (frequency : SpatialFrequency) :
    0 ≤ dyadicH2FirstDerivativeKernelFactor coordinate frequency := by
  exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- The inhomogeneous `H2` weight pays one unclocked derivative modewise. -/
theorem dyadicH2FirstDerivativeKernelFactor_le_one
    (coordinate : Fin 3) (frequency : SpatialFrequency) :
    dyadicH2FirstDerivativeKernelFactor coordinate frequency ≤ 1 := by
  let lambda := torusStokesEigenvalue frequency
  have hlambda : 0 ≤ lambda := torusStokesEigenvalue_nonneg frequency
  have hsqrtLambda : Real.sqrt lambda ≤ 1 + lambda := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg lambda) (by linarith)).mp
    rw [Real.sq_sqrt hlambda]
    nlinarith [sq_nonneg lambda]
  have hmultiplier :
      ‖orderedDerivativeMultiplier 1 (![coordinate]) frequency‖ ≤ 1 + lambda :=
    (norm_orderedFirstDerivativeMultiplier_le_sqrt_stokes coordinate frequency).trans
      hsqrtLambda
  have hweightSqrt : Real.sqrt (periodicSobolevWeight 2 frequency) = 1 + lambda := by
    unfold periodicSobolevWeight
    rw [Real.sqrt_sq (by linarith)]
  unfold dyadicH2FirstDerivativeKernelFactor
  rw [hweightSqrt]
  exact (div_le_one (by linarith)).2 hmultiplier

/-- At zero heat time, one derivative occurrence is exactly its `H2` reconstruction factor
times the native weighted coefficient magnitude. -/
theorem norm_heatTransportedFirstDerivativeCoefficient_one_zero_eq_kernel
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (frequency : SpatialFrequency) :
    ‖heatTransportedFirstDerivativeCoefficient
        1 0 source component coordinate frequency‖ =
      dyadicH2FirstDerivativeKernelFactor coordinate frequency *
        ‖source component frequency‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 2 frequency) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos 2 frequency)
  unfold heatTransportedFirstDerivativeCoefficient
    dyadicH2FirstDerivativeKernelFactor
  rw [heatStokesMultiplier_zero_time, weightedSobolevRawCoefficients_apply]
  simp only [Complex.ofReal_one, mul_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  field_simp

/-- A finite native weighted coefficient square population is paid by the complete `L2` norm. -/
theorem finite_weightedCoefficientSquareMass_le_norm_sq
    (state : PeriodicWeightedSobolev 2) (modes : Finset SpatialFrequency) :
    (∑ frequency ∈ modes, ‖state frequency‖ ^ 2) ≤ ‖state‖ ^ 2 := by
  have hsummable : Summable (fun frequency : SpatialFrequency ↦
      ‖state frequency‖ ^ 2) := by
    have h := (lp.memℓp state).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hfinite := hsummable.sum_le_tsum modes
    (fun frequency _hfrequency ↦ sq_nonneg ‖state frequency‖)
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) state
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  simp only [Real.rpow_two] at hnorm
  exact hfinite.trans_eq hnorm.symm

/-- Finite-shell Cauchy--Schwarz pays one complete derivative occurrence by the square root of
the actual shell cardinality times the native `H2` component norm. -/
theorem finite_dyadicH2FirstDerivativeOccurrenceMass_le
    (scale : ℕ) (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) :
    (∑ frequency ∈ dyadicNonlinearSourceModes scale,
      ‖heatTransportedFirstDerivativeCoefficient
        1 0 source component coordinate frequency‖) ≤
      Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ‖source component‖ := by
  let modes := dyadicNonlinearSourceModes scale
  let kernel : SpatialFrequency → ℝ := fun frequency ↦
    dyadicH2FirstDerivativeKernelFactor coordinate frequency
  let coefficient : SpatialFrequency → ℝ := fun frequency ↦
    ‖source component frequency‖
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt modes kernel coefficient
  have hkernelSquare : (∑ frequency ∈ modes, kernel frequency ^ 2) ≤
      (modes.card : ℝ) := by
    calc
      (∑ frequency ∈ modes, kernel frequency ^ 2) ≤
          ∑ _frequency ∈ modes, (1 : ℝ) := by
        exact Finset.sum_le_sum fun frequency _hfrequency ↦ by
          exact pow_le_one₀
            (dyadicH2FirstDerivativeKernelFactor_nonneg coordinate frequency)
            (dyadicH2FirstDerivativeKernelFactor_le_one coordinate frequency)
      _ = (modes.card : ℝ) := by simp
  have hcoefficientSquare :
      (∑ frequency ∈ modes, coefficient frequency ^ 2) ≤
        ‖source component‖ ^ 2 := by
    exact finite_weightedCoefficientSquareMass_le_norm_sq
      (source component) modes
  have hsqrtKernel :
      Real.sqrt (∑ frequency ∈ modes, kernel frequency ^ 2) ≤
        Real.sqrt (modes.card : ℝ) := Real.sqrt_le_sqrt hkernelSquare
  have hsqrtCoefficient :
      Real.sqrt (∑ frequency ∈ modes, coefficient frequency ^ 2) ≤
        ‖source component‖ := by
    calc
      Real.sqrt (∑ frequency ∈ modes, coefficient frequency ^ 2) ≤
          Real.sqrt (‖source component‖ ^ 2) := Real.sqrt_le_sqrt hcoefficientSquare
      _ = ‖source component‖ := Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (norm_nonneg _))
  calc
    (∑ frequency ∈ dyadicNonlinearSourceModes scale,
      ‖heatTransportedFirstDerivativeCoefficient
        1 0 source component coordinate frequency‖) =
        ∑ frequency ∈ modes, kernel frequency * coefficient frequency := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      exact norm_heatTransportedFirstDerivativeCoefficient_one_zero_eq_kernel
        source component coordinate frequency
    _ ≤ Real.sqrt (∑ frequency ∈ modes, kernel frequency ^ 2) *
        Real.sqrt (∑ frequency ∈ modes, coefficient frequency ^ 2) := hcs
    _ ≤ Real.sqrt (modes.card : ℝ) * ‖source component‖ :=
      mul_le_mul hsqrtKernel hsqrtCoefficient
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## Full vector reconstruction and its magnitude receiver -/

/-- Complete six-occurrence square/absolute owner on the actual adjacent-shell population. -/
def finiteDyadicH2CurlOccurrenceMass
    (scale : ℕ) (source : PeriodicVectorWeightedSobolev 2) : ℝ :=
  ∑ frequency ∈ dyadicNonlinearSourceModes scale,
    complexCurlEntryMass
      (heatTransportedFirstDerivativeJacobianCoefficient 1 0 source frequency)

/-- Six shell-local derivative occurrences pay the curl-vector magnitude receiver. -/
theorem finiteDyadicH2CurlOccurrenceMass_le
    (scale : ℕ) (source : PeriodicVectorWeightedSobolev 2) :
    finiteDyadicH2CurlOccurrenceMass scale source ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) * ‖source‖ := by
  let C := Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ)
  have h21 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 2 1
  have h12 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 1 2
  have h02 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 0 2
  have h20 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 2 0
  have h10 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 1 0
  have h01 := finite_dyadicH2FirstDerivativeOccurrenceMass_le scale source 0 1
  have hcomponent (component : Fin 3) : C * ‖source component‖ ≤ C * ‖source‖ :=
    mul_le_mul_of_nonneg_left (norm_le_pi_norm source component) (Real.sqrt_nonneg _)
  have h21' := h21.trans (hcomponent 2)
  have h12' := h12.trans (hcomponent 1)
  have h02' := h02.trans (hcomponent 0)
  have h20' := h20.trans (hcomponent 2)
  have h10' := h10.trans (hcomponent 1)
  have h01' := h01.trans (hcomponent 0)
  unfold finiteDyadicH2CurlOccurrenceMass complexCurlEntryMass
    heatTransportedFirstDerivativeJacobianCoefficient
  simp only [Finset.sum_add_distrib]
  dsimp only [C] at h21' h12' h02' h20' h10' h01' ⊢
  linarith

/-- On the addressed compact interval, the full actual nonlinear vorticity vector is exactly
the negative unclocked curl reconstruction of the native sharp source.  This identity precedes
the magnitude quotient below. -/
theorem compactVorticityNonlinearMode_eq_neg_unclockedSharpSourceCurl
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (hsourceTime : sourceTime ∈ Icc a b) :
    compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime =
      -heatTransportedH2SourceCurlCoefficient 1 0
        (sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨sourceTime, ha.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt hbT⟩)) frequency := by
  let interior : Ioo (0 : ℝ) T :=
    ⟨sourceTime, ha.trans_le hsourceTime.1, hsourceTime.2.trans_lt hbT⟩
  rw [compactVorticityNonlinearMode_eq_actual
    solution ha hab hbT frequency hsourceTime]
  rw [vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient]
  congr 2
  ext component
  simp [heatTransportedH2SourceCoefficient,
    unweightedSharpNonlinearSourceCoefficient,
    weightedSobolevCoefficients]

/-- The smooth Hodge weight and vector norm collapse the full reconstruction only after its
exact identity is available; the right side retains all six derivative occurrences. -/
theorem weighted_norm_compactVorticityNonlinearMode_le_curlOccurrenceMass
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (frequency : SpatialFrequency)
    (hsourceTime : sourceTime ∈ Icc a b) :
    |dyadicHodgeBandWeight scale frequency| *
        ‖compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime‖ ≤
      complexCurlEntryMass
        (heatTransportedFirstDerivativeJacobianCoefficient 1 0
          (sharpNonlinearSource
            (openVelocityWeightedH3State solution
              ⟨sourceTime, ha.trans_le hsourceTime.1,
                hsourceTime.2.trans_lt hbT⟩)) frequency) := by
  rw [compactVorticityNonlinearMode_eq_neg_unclockedSharpSourceCurl
    solution ha hab hbT frequency hsourceTime, norm_neg]
  have hweight : |dyadicHodgeBandWeight scale frequency| ≤ 1 := by
    rw [abs_of_nonneg (dyadicHodgeBandWeight_nonneg scale frequency)]
    exact dyadicHodgeBandWeight_le_one scale frequency
  exact (mul_le_of_le_one_left (norm_nonneg _) hweight).trans
    (norm_heatTransportedH2SourceCurlCoefficient_le_entryMass
      1 0 _ frequency)

/-- Unconditional one-shell magnitude estimate for the actual source slice.  The complete vector
identity is retained by the preceding theorem; this theorem is only its absolute receiver. -/
theorem compactSmoothDyadicVorticityNonlinearSourceMassAt_le_squareOwner
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (hsourceTime : sourceTime ∈ Icc a b) :
    compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ‖sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨sourceTime, ha.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt hbT⟩)‖ := by
  unfold compactSmoothDyadicVorticityNonlinearSourceMassAt
  change (∑ frequency ∈ dyadicNonlinearSourceModes scale,
      |dyadicHodgeBandWeight scale frequency| *
        ‖compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime‖) ≤ _
  exact (Finset.sum_le_sum fun frequency _hfrequency ↦
      weighted_norm_compactVorticityNonlinearMode_le_curlOccurrenceMass
        solution ha hab hbT scale frequency hsourceTime).trans
    (finiteDyadicH2CurlOccurrenceMass_le scale _)

/-! ## Compact-time H3 square current -/

/-- Actual native weighted-`H3` square current on the compact interior chart. -/
def compactOpenVelocityWeightedH3SquareCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) : ℝ :=
  ‖openVelocityWeightedH3State solution
      (compactInteriorTime ha hab hbT time)‖ ^ 2

theorem continuous_compactOpenVelocityWeightedH3SquareCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Continuous (compactOpenVelocityWeightedH3SquareCurrent
      solution ha hab hbT) := by
  have hstate : Continuous (fun time : ℝ ↦
      compactOpenVelocityWeightedH3State solution ha hbT
        (Set.projIcc a b hab time)) :=
    (continuous_compactOpenVelocityWeightedH3State
      solution ha hab hbT).comp continuous_projIcc
  unfold compactOpenVelocityWeightedH3SquareCurrent
  exact hstate.norm.pow 2

theorem compactOpenVelocityWeightedH3SquareCurrent_nonneg
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    0 ≤ compactOpenVelocityWeightedH3SquareCurrent
      solution ha hab hbT time := sq_nonneg _

/-- The actual nonlinear shell mass is quadratically paid by the actual native `H3` slice. -/
theorem compactSmoothDyadicVorticityNonlinearSourceMassAt_le_H3Square
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (scale : ℕ) (hsourceTime : sourceTime ∈ Icc a b) :
    compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ((23328 * periodicH3EmbeddingConstant) *
          compactOpenVelocityWeightedH3SquareCurrent
            solution ha hab hbT sourceTime) := by
  have hbase := compactSmoothDyadicVorticityNonlinearSourceMassAt_le_squareOwner
    solution ha hab hbT scale hsourceTime
  have hsource := norm_sharpNonlinearSource_le
    (openVelocityWeightedH3State solution
      ⟨sourceTime, ha.trans_le hsourceTime.1, hsourceTime.2.trans_lt hbT⟩)
  have hfactor : 0 ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ‖sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨sourceTime, ha.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt hbT⟩)‖ := hbase
    _ ≤ 6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ((23328 * periodicH3EmbeddingConstant) *
          ‖openVelocityWeightedH3State solution
            ⟨sourceTime, ha.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt hbT⟩‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsource hfactor
    _ = 6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
        ((23328 * periodicH3EmbeddingConstant) *
          compactOpenVelocityWeightedH3SquareCurrent
            solution ha hab hbT sourceTime) := by
      have hinterior :
          (⟨sourceTime, ha.trans_le hsourceTime.1,
            hsourceTime.2.trans_lt hbT⟩ : Ioo (0 : ℝ) T) =
            compactInteriorTime ha hab hbT sourceTime := by
        apply Subtype.ext
        exact compactInteriorTime_eq ha hab hbT hsourceTime |>.symm
      unfold compactOpenVelocityWeightedH3SquareCurrent
      rw [hinterior]

/-- Scale density created by the square/absolute owner after the reciprocal heat clock is spent. -/
def adaptiveNonlinearSourceSquareDensity (nu : ℝ) (scale : ℕ) : ℝ :=
  6 * dyadicParabolicClockBudget nu scale *
    Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ)

theorem adaptiveNonlinearSourceSquareDensity_nonneg
    {nu : ℝ} (hnu : 0 < nu) (scale : ℕ) :
    0 ≤ adaptiveNonlinearSourceSquareDensity nu scale := by
  unfold adaptiveNonlinearSourceSquareDensity dyadicParabolicClockBudget
  positivity

/-- One adaptive reciprocal-clock source contribution is paid by its genuine square density
times the compact-time integral of the actual native `H3` square current. -/
theorem compactAdaptiveReciprocalClockNonlinearSourceContribution_le_H3SquareCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactAdaptiveReciprocalClockNonlinearSourceContribution
        solution ha hab hbT scale ≤
      adaptiveNonlinearSourceSquareDensity nu scale *
        (23328 * periodicH3EmbeddingConstant) *
          ∫ sourceTime in a..b,
            compactOpenVelocityWeightedH3SquareCurrent
              solution ha hab hbT sourceTime := by
  let horizon := adaptiveSmoothDyadicTerminalWindowStart a b scale
  let current := compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT
  let C := 23328 * periodicH3EmbeddingConstant
  have hah : a ≤ horizon := le_adaptiveSmoothDyadicTerminalWindowStart hab scale
  have hhb : horizon ≤ b := adaptiveSmoothDyadicTerminalWindowStart_le hab scale
  have hbudget : 0 ≤ dyadicParabolicClockBudget nu scale := by
    unfold dyadicParabolicClockBudget
    positivity
  have hpoint (sourceTime : ℝ) (hsourceTime : sourceTime ∈ Icc a horizon) :
      compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale sourceTime ≤
        6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
          (C * current sourceTime) := by
    exact compactSmoothDyadicVorticityNonlinearSourceMassAt_le_H3Square
      solution ha hab hbT scale ⟨hsourceTime.1, hsourceTime.2.trans hhb⟩
  have hintegralHorizon :
      (∫ sourceTime in a..horizon,
        compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale sourceTime) ≤
        ∫ sourceTime in a..horizon,
          6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
            (C * current sourceTime) := by
    have hleftInt : IntervalIntegrable
        (compactSmoothDyadicVorticityNonlinearSourceMassAt
          solution ha hab hbT scale) volume a horizon :=
      (continuous_compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale).intervalIntegrable a horizon
    have hrightInt : IntervalIntegrable
        (fun sourceTime : ℝ ↦
          6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
            (C * current sourceTime)) volume a horizon :=
      (((continuous_compactOpenVelocityWeightedH3SquareCurrent
        solution ha hab hbT).const_mul C).const_mul
          (6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ))).intervalIntegrable
            a horizon
    exact intervalIntegral.integral_mono_on hah hleftInt hrightInt hpoint
  have hcurrentNonneg (sourceTime : ℝ) : 0 ≤ current sourceTime :=
    compactOpenVelocityWeightedH3SquareCurrent_nonneg
      solution ha hab hbT sourceTime
  have hC : 0 ≤ C := mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
  have hfactor : 0 ≤
      6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) * C :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hC
  have hextend :
      (∫ sourceTime in a..horizon, current sourceTime) ≤
        ∫ sourceTime in a..b, current sourceTime := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_compactOpenVelocityWeightedH3SquareCurrent
        solution ha hab hbT).intervalIntegrable a horizon)
      ((continuous_compactOpenVelocityWeightedH3SquareCurrent
        solution ha hab hbT).intervalIntegrable horizon b)]
    linarith [intervalIntegral.integral_nonneg (μ := volume) hhb
      (fun sourceTime _hsourceTime ↦ hcurrentNonneg sourceTime)]
  unfold compactAdaptiveReciprocalClockNonlinearSourceContribution
  calc
    dyadicParabolicClockBudget nu scale *
        (∫ sourceTime in a..horizon,
          compactSmoothDyadicVorticityNonlinearSourceMassAt
            solution ha hab hbT scale sourceTime) ≤
      dyadicParabolicClockBudget nu scale *
        (∫ sourceTime in a..horizon,
          6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
            (C * current sourceTime)) :=
      mul_le_mul_of_nonneg_left hintegralHorizon hbudget
    _ = adaptiveNonlinearSourceSquareDensity nu scale * C *
        (∫ sourceTime in a..horizon, current sourceTime) := by
      rw [show (fun sourceTime : ℝ ↦
          6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) *
            (C * current sourceTime)) =
          (fun sourceTime : ℝ ↦
            (6 * Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) * C) *
              current sourceTime) by
        funext sourceTime
        ring]
      rw [intervalIntegral.integral_const_mul]
      unfold adaptiveNonlinearSourceSquareDensity
      ring
    _ ≤ adaptiveNonlinearSourceSquareDensity nu scale * C *
        (∫ sourceTime in a..b, current sourceTime) :=
      mul_le_mul_of_nonneg_left hextend
        (mul_nonneg (adaptiveNonlinearSourceSquareDensity_nonneg hnu scale) hC)
    _ = adaptiveNonlinearSourceSquareDensity nu scale *
        (23328 * periodicH3EmbeddingConstant) *
          ∫ sourceTime in a..b,
            compactOpenVelocityWeightedH3SquareCurrent
              solution ha hab hbT sourceTime := rfl

/-! ## Depth-independent scale summation -/

/-- The square root of the actual mode count retains its exact three-dimensional shell power. -/
theorem sqrt_card_dyadicNonlinearSourceModes_le (scale : ℕ) :
    Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) ≤
      27 * (dyadicRadius scale : ℝ) *
        Real.sqrt (dyadicRadius scale : ℝ) := by
  let R : ℝ := dyadicRadius scale
  have hR : 0 ≤ R := by positivity
  have hcard := card_dyadicNonlinearSourceModes_le scale
  have hright : 0 ≤ 27 * R * Real.sqrt R := by positivity
  rw [Real.sqrt_le_iff]
  constructor
  · exact hright
  · calc
      ((dyadicNonlinearSourceModes scale).card : ℝ) ≤ 729 * R ^ 3 := hcard
      _ = (27 * R * Real.sqrt R) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hR]
        ring

/-- The exact square density is geometrically dominated by inverse square-root dyadic radius.
This is the sharp mode-count test: three-dimensional cardinality contributes `R^(3/2)` while
the reciprocal parabolic clock returns `R^(-2)`. -/
theorem adaptiveNonlinearSourceSquareDensity_le_geometric
    {nu : ℝ} (hnu : 0 < nu) (scale : ℕ) :
    adaptiveNonlinearSourceSquareDensity nu scale ≤
      (162 * nu⁻¹) / Real.sqrt (dyadicRadius scale : ℝ) := by
  let R : ℝ := dyadicRadius scale
  have hR : 0 < R := by
    dsimp [R, dyadicRadius]
    positivity
  have hsqrtR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hbudget : 0 ≤ dyadicParabolicClockBudget nu scale := by
    unfold dyadicParabolicClockBudget
    positivity
  calc
    adaptiveNonlinearSourceSquareDensity nu scale =
        6 * dyadicParabolicClockBudget nu scale *
          Real.sqrt ((dyadicNonlinearSourceModes scale).card : ℝ) := rfl
    _ ≤ 6 * dyadicParabolicClockBudget nu scale *
        (27 * R * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left
        (sqrt_card_dyadicNonlinearSourceModes_le scale)
        (mul_nonneg (by norm_num) hbudget)
    _ = (162 * nu⁻¹) / Real.sqrt (dyadicRadius scale : ℝ) := by
      rw [dyadicParabolicClockBudget_eq_viscosityInv_mul_quarterPow]
      rw [inv_pow]
      have hfour : (4 : ℝ) ^ scale = R ^ 2 := by
        dsimp [R]
        calc
          (4 : ℝ) ^ scale = ((2 : ℝ) * 2) ^ scale := by norm_num
          _ = (2 : ℝ) ^ scale * (2 : ℝ) ^ scale := by rw [mul_pow]
          _ = (dyadicRadius scale : ℝ) ^ 2 := by
            simp [dyadicRadius, pow_two]
      rw [hfour]
      dsimp [R] at hR hsqrtR ⊢
      field_simp [hR.ne', hsqrtR.ne']
      rw [Real.sq_sqrt hR.le]
      ring

/-- The reciprocal-clock square densities are summable over all scales. -/
theorem summable_adaptiveNonlinearSourceSquareDensity
    {nu : ℝ} (hnu : 0 < nu) :
    Summable (adaptiveNonlinearSourceSquareDensity nu) := by
  exact Summable.of_nonneg_of_le
    (fun scale ↦ adaptiveNonlinearSourceSquareDensity_nonneg hnu scale)
    (adaptiveNonlinearSourceSquareDensity_le_geometric hnu)
    (summable_const_div_sqrt_dyadicRadius (162 * nu⁻¹))

/-- Complete depth-independent mass of the actual square/absolute scale owner. -/
def adaptiveNonlinearSourceSquareDensityMass (nu : ℝ) : ℝ :=
  ∑' scale : ℕ, adaptiveNonlinearSourceSquareDensity nu scale

theorem adaptiveNonlinearSourceSquareDensityPrefix_le_mass
    {nu : ℝ} (hnu : 0 < nu) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
      adaptiveNonlinearSourceSquareDensity nu scale) ≤
        adaptiveNonlinearSourceSquareDensityMass nu := by
  exact (summable_adaptiveNonlinearSourceSquareDensity hnu).sum_le_tsum
    (Finset.range depth)
    (fun scale _hscale ↦ adaptiveNonlinearSourceSquareDensity_nonneg hnu scale)

/-- The entire finite reciprocal-clock source word is paid without a depth multiplier by one
summable scale density and the compact-time actual `H3` square current. -/
theorem compactAdaptiveReciprocalClockNonlinearSourcePrefix_le_H3SquareCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactAdaptiveReciprocalClockNonlinearSourcePrefix
        solution ha hab hbT depth ≤
      adaptiveNonlinearSourceSquareDensityMass nu *
        (23328 * periodicH3EmbeddingConstant) *
          ∫ sourceTime in a..b,
            compactOpenVelocityWeightedH3SquareCurrent
              solution ha hab hbT sourceTime := by
  let payment : ℝ := (23328 * periodicH3EmbeddingConstant) *
    ∫ sourceTime in a..b,
      compactOpenVelocityWeightedH3SquareCurrent
        solution ha hab hbT sourceTime
  have hcurrentIntegral : 0 ≤
      ∫ sourceTime in a..b,
        compactOpenVelocityWeightedH3SquareCurrent
          solution ha hab hbT sourceTime :=
    intervalIntegral.integral_nonneg (μ := volume) hab
      (fun sourceTime _hsourceTime ↦
        compactOpenVelocityWeightedH3SquareCurrent_nonneg
          solution ha hab hbT sourceTime)
  have hpayment : 0 ≤ payment :=
    mul_nonneg (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
      hcurrentIntegral
  unfold compactAdaptiveReciprocalClockNonlinearSourcePrefix
  calc
    (∑ scale ∈ Finset.range depth,
      compactAdaptiveReciprocalClockNonlinearSourceContribution
        solution ha hab hbT scale) ≤
      ∑ scale ∈ Finset.range depth,
        adaptiveNonlinearSourceSquareDensity nu scale * payment := by
      exact Finset.sum_le_sum fun scale _hscale ↦ by
        simpa only [payment, mul_assoc] using
          (compactAdaptiveReciprocalClockNonlinearSourceContribution_le_H3SquareCurrent
            solution hnu ha hab hbT scale)
    _ = (∑ scale ∈ Finset.range depth,
        adaptiveNonlinearSourceSquareDensity nu scale) * payment := by
      rw [Finset.sum_mul]
    _ ≤ adaptiveNonlinearSourceSquareDensityMass nu * payment :=
      mul_le_mul_of_nonneg_right
        (adaptiveNonlinearSourceSquareDensityPrefix_le_mass hnu depth) hpayment
    _ = adaptiveNonlinearSourceSquareDensityMass nu *
        (23328 * periodicH3EmbeddingConstant) *
          ∫ sourceTime in a..b,
            compactOpenVelocityWeightedH3SquareCurrent
              solution ha hab hbT sourceTime := by
      dsimp [payment]
      ring

/-! ## Joined off-diagonal passage and the exact terminal separator -/

/-- The complete adaptive off-diagonal fibre is now paid by the restart population and the
depth-independent square/absolute source owner.  The last term is precisely the retained compact
`H3` square reconstruction fibre, not an unweighted terminal receiver. -/
theorem compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restart_add_H3SquareCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveOffDiagonalReconstructionFiber
        solution ha hab hbT depth ≤
      nu⁻¹ * smoothRestartCoefficientPayment solution ha (hab.trans_lt hbT) +
        adaptiveNonlinearSourceSquareDensityMass nu *
          (23328 * periodicH3EmbeddingConstant) *
            ∫ sourceTime in a..b,
              compactOpenVelocityWeightedH3SquareCurrent
                solution ha hab hbT sourceTime := by
  exact (compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restartPayment_add_reciprocalClockSourcePrefix
    solution hnu ha hab hbT depth).trans
      (add_le_add le_rfl
        (compactAdaptiveReciprocalClockNonlinearSourcePrefix_le_H3SquareCurrent
          solution hnu ha hab hbT depth))

/-- Exact singleton scaling identity behind the endpoint test: order three equals the product of
orders one and two on one addressed Fourier occurrence. -/
theorem sobolevMass_three_singleFrequencyPopulation_eq_one_mul_two
    (frequency : SpatialFrequency) :
    sobolevMass 3 (singleFrequencyPopulation frequency) =
      sobolevMass 1 (singleFrequencyPopulation frequency) *
        sobolevMass 2 (singleFrequencyPopulation frequency) := by
  rw [sobolevMass_singleFrequencyPopulation,
    sobolevMass_singleFrequencyPopulation,
    sobolevMass_singleFrequencyPopulation]
  unfold periodicSobolevWeight
  ring

/-- Enstrophy-order testimony cannot uniformly pay the retained `H3` square fibre.  This
single-frequency separator explains why compact-interior integrability does not automatically
become a terminal-uniform estimate. -/
theorem no_uniform_orderOne_bound_for_orderThree_singleFrequencyPopulations :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      sobolevMass 3 (singleFrequencyPopulation (axialFrequency n)) ≤
        C * sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have htwo : C <
      sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) :=
    hn.trans_le (natCast_le_sobolevMass_two_singleFrequencyPopulation_axial n)
  have hone : 0 <
      sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) := by
    rw [sobolevMass_singleFrequencyPopulation]
    exact zero_lt_one.trans_le
      (one_le_periodicSobolevWeight 1 (axialFrequency n))
  have hsep :
      C * sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) <
        sobolevMass 3 (singleFrequencyPopulation (axialFrequency n)) := by
    rw [sobolevMass_three_singleFrequencyPopulation_eq_one_mul_two]
    calc
      C * sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) =
          sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) * C := by ring
      _ < sobolevMass 1 (singleFrequencyPopulation (axialFrequency n)) *
          sobolevMass 2 (singleFrequencyPopulation (axialFrequency n)) :=
        mul_lt_mul_of_pos_left htwo hone
  exact (not_lt_of_ge (hC n)) hsep

/-! ## Audit -/

section Audit

#print axioms card_dyadicNonlinearSourceModes_le
#print axioms finite_dyadicH2FirstDerivativeOccurrenceMass_le
#print axioms compactVorticityNonlinearMode_eq_neg_unclockedSharpSourceCurl
#print axioms compactSmoothDyadicVorticityNonlinearSourceMassAt_le_squareOwner
#print axioms summable_adaptiveNonlinearSourceSquareDensity
#print axioms compactAdaptiveReciprocalClockNonlinearSourcePrefix_le_H3SquareCurrent
#print axioms compactOpenSmoothDyadicAdaptiveOffDiagonalFiber_le_restart_add_H3SquareCurrent
#print axioms no_uniform_orderOne_bound_for_orderThree_singleFrequencyPopulations

end Audit

end Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
