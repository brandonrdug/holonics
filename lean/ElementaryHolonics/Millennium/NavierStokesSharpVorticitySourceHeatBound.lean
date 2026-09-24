import ElementaryHolonics.Millennium.NavierStokesSharpNonlinearSource
import ElementaryHolonics.Millennium.NavierStokesOpenFourierExteriorMildBound
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# Sharp positive-time heat control of the nonlinear vorticity source

**[proved-derived]** One spatial derivative of a native weighted `H2` source has a strictly
better positive-heat-time coefficient kernel than the already available two-derivative receiver.
Its squared kernel is dominated by the standing periodic spectral resolvent, hence its complete
absolute coefficient mass has the locally integrable `elapsed^(-1/4)` scale.

The public statements retain `heatStokesMultiplier`, `torusStokesEigenvalue`, the weighted
reconstruction coefficients, and the existing named sharp constant.  Closed-form realization
coordinates are used only inside proofs.  Instantiating the source with `sharpNonlinearSource`
returns an unconditional quadratic weighted-`H3` bound; no terminal control is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierExteriorMildBound
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Squared spectral kernel for one spatial derivative of weighted `H2` data.  The clock is the
standing heat/Stokes action, presented at doubled elapsed parameter after squaring. -/
def heatFirstDerivativeH2KernelMass (a : ℝ) : ℝ :=
  ∑' k : SpatialFrequency,
    torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
      periodicSobolevWeight 2 k

private theorem heatFirstDerivativeH2KernelTerm_nonneg
    (a : ℝ) (k : SpatialFrequency) :
    0 ≤ torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
      periodicSobolevWeight 2 k := by
  exact div_nonneg
    (mul_nonneg (torusStokesEigenvalue_nonneg k) (by
      unfold heatStokesMultiplier
      positivity))
    (periodicSobolevWeight_nonneg 2 k)

private theorem heatFirstDerivativeH2KernelTerm_le_resolvent
    (a : ℝ) (k : SpatialFrequency) :
    torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
        periodicSobolevWeight 2 k ≤
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        (1 + torusStokesEigenvalue k) := by
  let x := torusStokesEigenvalue k
  have hx : 0 ≤ x := torusStokesEigenvalue_nonneg k
  have hbase : 0 < 1 + x := by linarith
  have hclock : heatStokesMultiplier 1 (2 * a) k =
      Real.exp (-(2 * a) * x) := by
    unfold heatStokesMultiplier
    congr 1
    dsimp [x]
    ring
  rw [hclock, periodicSobolevWeight]
  change x * Real.exp (-(2 * a) * x) / (1 + x) ^ 2 ≤
    Real.exp (-(2 * a) * x) / (1 + x)
  rw [div_le_div_iff₀ (pow_pos hbase 2) hbase]
  nlinarith [Real.exp_pos (-(2 * a) * x)]

theorem summable_heatFirstDerivativeH2Kernel {a : ℝ} (ha : 0 < a) :
    Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
        periodicSobolevWeight 2 k := by
  exact Summable.of_nonneg_of_le
    (heatFirstDerivativeH2KernelTerm_nonneg a)
    (heatFirstDerivativeH2KernelTerm_le_resolvent a)
    (summable_periodicGaussianResolvent ha)

private theorem heatFirstDerivativeH2KernelMass_le_realization
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1) :
    heatFirstDerivativeH2KernelMass a ≤
      (8 * gaussianLineUnitMass ^ 3) *
        (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
          (2 * a) ^ (-1 / 2 : ℝ) := by
  unfold heatFirstDerivativeH2KernelMass
  calc
    (∑' k : SpatialFrequency,
        torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
          periodicSobolevWeight 2 k) ≤ periodicGaussianResolventMass a := by
      unfold periodicGaussianResolventMass
      exact (summable_heatFirstDerivativeH2Kernel ha).tsum_le_tsum
        (heatFirstDerivativeH2KernelTerm_le_resolvent a)
        (summable_periodicGaussianResolvent ha)
    _ ≤ _ := periodicGaussianResolventMass_le a ha haLocal

/-- Exact complete absolute coefficient population of one spectral derivative after the standing
heat/Stokes clock acts on a weighted `H2` source. -/
def heatFirstDerivativeH2CoefficientMass
    (a : ℝ) (source : PeriodicWeightedSobolev 2) : ℝ :=
  ∑' k : SpatialFrequency,
    Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k *
      ‖weightedSobolevRawCoefficients 2 source k‖

/-- The named sharp constant for the one-derivative `H2` clock edge. -/
def sharpHeatFirstDerivativeH2Constant : ℝ :=
  sharpHeatSecondDerivativeH3Constant

/-- The squared first-derivative `H2` clock kernel is controlled by the named sharp spectral
receiver.  Its conventional calibration is kept behind `sharpHeatFirstDerivativeH2Constant`. -/
theorem heatFirstDerivativeH2KernelMass_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1) :
    heatFirstDerivativeH2KernelMass a ≤
      sharpHeatFirstDerivativeH2Constant ^ 2 *
        (2 * a) ^ (-1 / 2 : ℝ) := by
  have hC : 0 ≤ (8 * gaussianLineUnitMass ^ 3) *
      (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) := by
    have hpi : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3))
      (by linarith)
  calc
    heatFirstDerivativeH2KernelMass a ≤
        (8 * gaussianLineUnitMass ^ 3) *
          (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
            (2 * a) ^ (-1 / 2 : ℝ) :=
      heatFirstDerivativeH2KernelMass_le_realization a ha haLocal
    _ = sharpHeatFirstDerivativeH2Constant ^ 2 *
        (2 * a) ^ (-1 / 2 : ℝ) := by
      unfold sharpHeatFirstDerivativeH2Constant
        sharpHeatSecondDerivativeH3Constant
      rw [Real.sq_sqrt hC]

private theorem norm_heatFirstDerivativeH2KernelTerm_sq
    (a : ℝ) (k : SpatialFrequency) :
    ‖Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k /
        Real.sqrt (periodicSobolevWeight 2 k)‖ ^ 2 =
      torusStokesEigenvalue k * heatStokesMultiplier 1 (2 * a) k /
        periodicSobolevWeight 2 k := by
  have hlambda : 0 ≤ torusStokesEigenvalue k := torusStokesEigenvalue_nonneg k
  have hweight : 0 ≤ periodicSobolevWeight 2 k :=
    periodicSobolevWeight_nonneg 2 k
  have hclock : 0 ≤ heatStokesMultiplier 1 a k := by
    unfold heatStokesMultiplier
    positivity
  have hterm : 0 ≤ Real.sqrt (torusStokesEigenvalue k) *
      heatStokesMultiplier 1 a k / Real.sqrt (periodicSobolevWeight 2 k) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hclock) (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hterm, div_pow, mul_pow,
    Real.sq_sqrt hlambda, Real.sq_sqrt hweight]
  rw [pow_two, ← heatStokesMultiplier_add]
  congr 2
  ring_nf

/-- The first-derivative `H2` clock kernel as an actual complete square-summable population. -/
def heatFirstDerivativeH2Kernel (a : ℝ) (ha : 0 < a) :
    PeriodicRealFourierL2 :=
  ⟨fun k ↦ Real.sqrt (torusStokesEigenvalue k) *
      heatStokesMultiplier 1 a k / Real.sqrt (periodicSobolevWeight 2 k), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two, norm_heatFirstDerivativeH2KernelTerm_sq] using
      summable_heatFirstDerivativeH2Kernel ha⟩

theorem norm_heatFirstDerivativeH2Kernel_sq (a : ℝ) (ha : 0 < a) :
    ‖heatFirstDerivativeH2Kernel a ha‖ ^ 2 =
      heatFirstDerivativeH2KernelMass a := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (heatFirstDerivativeH2Kernel a ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    heatFirstDerivativeH2Kernel, heatFirstDerivativeH2KernelMass,
    norm_heatFirstDerivativeH2KernelTerm_sq] using hnorm

private theorem heatFirstDerivativeKernel_mul_stateNorm_eq_receiverTerm
    (a : ℝ) (source : PeriodicWeightedSobolev 2)
    (k : SpatialFrequency) :
    ‖Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k /
        Real.sqrt (periodicSobolevWeight 2 k)‖ * ‖source k‖ =
      Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k *
        ‖weightedSobolevRawCoefficients 2 source k‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 2 k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos 2 k)
  have hclock : 0 ≤ heatStokesMultiplier 1 a k := by
    unfold heatStokesMultiplier
    positivity
  have hkernel : 0 ≤ Real.sqrt (torusStokesEigenvalue k) *
      heatStokesMultiplier 1 a k / Real.sqrt (periodicSobolevWeight 2 k) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hclock) hsqrt.le
  rw [weightedSobolevRawCoefficients_apply, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg hkernel]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  field_simp

private theorem heatFirstDerivativeH2CoefficientMass_le_kernelNorm_mul
    (a : ℝ) (ha : 0 < a) (source : PeriodicWeightedSobolev 2) :
    heatFirstDerivativeH2CoefficientMass a source ≤
      ‖heatFirstDerivativeH2Kernel a ha‖ * ‖source‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hcs := lp.tsum_mul_le_mul_norm' hholder
    (heatFirstDerivativeH2Kernel a ha) (weightedStateAbsolute 2 source)
  calc
    heatFirstDerivativeH2CoefficientMass a source =
        ∑' k : SpatialFrequency,
          ‖heatFirstDerivativeH2Kernel a ha k‖ *
            ‖weightedStateAbsolute 2 source k‖ := by
      unfold heatFirstDerivativeH2CoefficientMass
      apply tsum_congr
      intro k
      rw [show ‖weightedStateAbsolute 2 source k‖ = ‖source k‖ by
        simp only [weightedStateAbsolute, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)] ]
      exact (heatFirstDerivativeKernel_mul_stateNorm_eq_receiverTerm a source k).symm
    _ ≤ ‖heatFirstDerivativeH2Kernel a ha‖ *
        ‖weightedStateAbsolute 2 source‖ := hcs
    _ = ‖heatFirstDerivativeH2Kernel a ha‖ * ‖source‖ := by
      rw [norm_weightedStateAbsolute]

private theorem sqrt_mul_rpow_neg_half
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 < x) :
    Real.sqrt (C * x ^ (-1 / 2 : ℝ)) =
      Real.sqrt C * x ^ (-1 / 4 : ℝ) := by
  rw [Real.sqrt_mul hC]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1
  norm_num

/-- **Sharp one-derivative `H2` heat edge.**  The complete spectral first-derivative
coefficient population has the locally integrable positive-time scale, expressed only through
the standing heat clock, spectral eigenvalue, and named calibration receiver. -/
theorem heatFirstDerivativeH2CoefficientMass_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1)
    (source : PeriodicWeightedSobolev 2) :
    heatFirstDerivativeH2CoefficientMass a source ≤
      sharpHeatFirstDerivativeH2Constant * (2 * a) ^ (-1 / 4 : ℝ) *
        ‖source‖ := by
  have hcs := heatFirstDerivativeH2CoefficientMass_le_kernelNorm_mul a ha source
  have hconstant : 0 ≤ sharpHeatFirstDerivativeH2Constant := by
    unfold sharpHeatFirstDerivativeH2Constant sharpHeatSecondDerivativeH3Constant
    positivity
  have hkernel : ‖heatFirstDerivativeH2Kernel a ha‖ ≤
      sharpHeatFirstDerivativeH2Constant * (2 * a) ^ (-1 / 4 : ℝ) := by
    calc
      ‖heatFirstDerivativeH2Kernel a ha‖ =
          Real.sqrt (‖heatFirstDerivativeH2Kernel a ha‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt (heatFirstDerivativeH2KernelMass a) := by
        rw [norm_heatFirstDerivativeH2Kernel_sq]
      _ ≤ Real.sqrt (sharpHeatFirstDerivativeH2Constant ^ 2 *
          (2 * a) ^ (-1 / 2 : ℝ)) :=
        Real.sqrt_le_sqrt (heatFirstDerivativeH2KernelMass_le a ha haLocal)
      _ = Real.sqrt (sharpHeatFirstDerivativeH2Constant ^ 2) *
          (2 * a) ^ (-1 / 4 : ℝ) := by
        exact sqrt_mul_rpow_neg_half _ _ (sq_nonneg _)
          (mul_pos (by norm_num) ha)
      _ = sharpHeatFirstDerivativeH2Constant *
          (2 * a) ^ (-1 / 4 : ℝ) := by
        rw [Real.sqrt_sq hconstant]
  exact hcs.trans (mul_le_mul_of_nonneg_right hkernel (norm_nonneg source))

/-- The sharp first-derivative clock kernel is locally integrable at zero elapsed time. -/
theorem integrableOn_sharpHeatFirstDerivativeH2_timeKernel
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun a : ℝ ↦ (2 * a) ^ (-1 / 4 : ℝ)) (Ioo 0 T) :=
  integrableOn_sharpHeatSecondDerivativeH3_timeKernel T hT

/-- Rebase viscosity and elapsed time into the single spectral-clock parameter without exposing
the clock's realization chart. -/
theorem heatStokesMultiplier_eq_unitClock_mul
    (nu dt : ℝ) (k : SpatialFrequency) :
    heatStokesMultiplier nu dt k = heatStokesMultiplier 1 (nu * dt) k := by
  unfold heatStokesMultiplier
  congr 1
  ring

/-- One addressed Fourier coefficient of the actual reconstructed first derivative after positive
heat transport. -/
def heatTransportedFirstDerivativeCoefficient
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (k : SpatialFrequency) : ℂ :=
  orderedDerivativeMultiplier 1 (![coordinate]) k *
    (heatStokesMultiplier nu dt k : ℂ) *
      weightedSobolevRawCoefficients 2 (source component) k

/-- This coefficient is exactly the coefficient returned by the standing finite-order physical
reconstruction, not a symbol-only surrogate. -/
theorem heatTransportedFirstDerivativeCoefficient_eq_reconstruction
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (k : SpatialFrequency) :
    heatTransportedFirstDerivativeCoefficient (nu : ℝ) (dt : ℝ)
        source component coordinate k =
      (weightedSobolevCoefficients 3
        (finiteOrderVectorDerivativeToThree 2 1 (by omega) (![coordinate])
          (vectorHeatH2ToH5 nu dt h source) component)).1 k := by
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedCoefficients_vectorHeatH2ToH5]
  change orderedDerivativeMultiplier 1 (![coordinate]) k *
      (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        weightedSobolevRawCoefficients 2 (source component) k =
    orderedDerivativeMultiplier 1 (![coordinate]) k *
      ((heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        weightedSobolevRawCoefficients 2 (source component) k)
  ring

/-- Exact complete coefficient `ℓ1` population of one reconstructed derivative face. -/
def heatTransportedFirstDerivativeCoefficientMass
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) : ℝ :=
  ∑' k : SpatialFrequency,
    ‖heatTransportedFirstDerivativeCoefficient
      nu dt source component coordinate k‖

/-- One addressed coordinate derivative symbol is dominated by the intrinsic square root of the
Stokes spectral cost. -/
theorem norm_orderedFirstDerivativeMultiplier_le_sqrt_stokes
    (coordinate : Fin 3) (k : SpatialFrequency) :
    ‖orderedDerivativeMultiplier 1 (![coordinate]) k‖ ≤
      Real.sqrt (torusStokesEigenvalue k) := by
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  have hlambda : 0 ≤ torusStokesEigenvalue k := torusStokesEigenvalue_nonneg k
  simp only [orderedDerivativeMultiplier, Fin.prod_univ_one,
    Matrix.cons_val_zero, coordinateFourierMultiplier, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_ofNat, Complex.norm_intCast]
  apply (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.pi * |(k coordinate : ℝ)|)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hlambda]
  unfold torusStokesEigenvalue
  nlinarith [sq_abs (k coordinate : ℝ), sq_nonneg (2 * Real.pi)]

private theorem summable_heatFirstDerivativeH2CoefficientTerm
    (a : ℝ) (ha : 0 < a) (source : PeriodicWeightedSobolev 2) :
    Summable fun k : SpatialFrequency ↦
      Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k *
        ‖weightedSobolevRawCoefficients 2 source k‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hsum := lp.summable_mul hholder
    (heatFirstDerivativeH2Kernel a ha) (weightedStateAbsolute 2 source)
  apply hsum.congr
  intro k
  rw [show ‖weightedStateAbsolute 2 source k‖ = ‖source k‖ by
    simp only [weightedStateAbsolute, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] ]
  change ‖Real.sqrt (torusStokesEigenvalue k) * heatStokesMultiplier 1 a k /
      Real.sqrt (periodicSobolevWeight 2 k)‖ * ‖source k‖ = _
  exact heatFirstDerivativeKernel_mul_stateNorm_eq_receiverTerm a source k

private theorem norm_heatTransportedFirstDerivativeCoefficient_le
    (nu dt : ℝ)
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (k : SpatialFrequency) :
    ‖heatTransportedFirstDerivativeCoefficient
        nu dt source component coordinate k‖ ≤
      Real.sqrt (torusStokesEigenvalue k) *
        heatStokesMultiplier 1 (nu * dt) k *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖ := by
  have hclock : 0 ≤ heatStokesMultiplier 1 (nu * dt) k := by
    unfold heatStokesMultiplier
    positivity
  have hclockNu : 0 ≤ heatStokesMultiplier nu dt k := by
    unfold heatStokesMultiplier
    positivity
  unfold heatTransportedFirstDerivativeCoefficient
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hclockNu, heatStokesMultiplier_eq_unitClock_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (norm_orderedFirstDerivativeMultiplier_le_sqrt_stokes coordinate k)
      hclock)
    (norm_nonneg _)

theorem summable_norm_heatTransportedFirstDerivativeCoefficient
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) :
    Summable fun k : SpatialFrequency ↦
      ‖heatTransportedFirstDerivativeCoefficient
        nu dt source component coordinate k‖ := by
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_heatTransportedFirstDerivativeCoefficient_le
      nu dt source component coordinate)
    (summable_heatFirstDerivativeH2CoefficientTerm
      (nu * dt) h (source component))

theorem heatTransportedFirstDerivativeCoefficientMass_le_spectralMass
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) :
    heatTransportedFirstDerivativeCoefficientMass
        nu dt source component coordinate ≤
      heatFirstDerivativeH2CoefficientMass (nu * dt) (source component) := by
  have hspectral := summable_heatFirstDerivativeH2CoefficientTerm
    (nu * dt) h (source component)
  have hexact : Summable fun k : SpatialFrequency ↦
      ‖heatTransportedFirstDerivativeCoefficient
        nu dt source component coordinate k‖ :=
    summable_norm_heatTransportedFirstDerivativeCoefficient
      nu dt h source component coordinate
  unfold heatTransportedFirstDerivativeCoefficientMass
    heatFirstDerivativeH2CoefficientMass
  exact hexact.tsum_le_tsum
    (norm_heatTransportedFirstDerivativeCoefficient_le
      nu dt source component coordinate) hspectral

/-- Sharp positive-elapsed coefficient bound for one reconstructed derivative of any native
weighted `H2` vector source. -/
theorem heatTransportedFirstDerivativeCoefficientMass_le
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) :
    heatTransportedFirstDerivativeCoefficientMass
        nu dt source component coordinate ≤
      sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ) * ‖source component‖ :=
  (heatTransportedFirstDerivativeCoefficientMass_le_spectralMass
    nu dt h source component coordinate).trans
      (heatFirstDerivativeH2CoefficientMass_le
        (nu * dt) h hlocal (source component))

/-- **Unconditional nonlinear vorticity-source edge.**  One reconstructed derivative of the
exact native Leray--divergence source has an integrable positive-time kernel and is quadratically
controlled by the native weighted `H3` velocity norm. -/
theorem heatTransportedSharpNonlinearSourceFirstDerivativeCoefficientMass_le
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (u : PeriodicVectorWeightedSobolev 3)
    (component coordinate : Fin 3) :
    heatTransportedFirstDerivativeCoefficientMass
        nu dt (sharpNonlinearSource u) component coordinate ≤
      sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2) := by
  have hbase := heatTransportedFirstDerivativeCoefficientMass_le
    nu dt h hlocal (sharpNonlinearSource u) component coordinate
  have hfactor : 0 ≤ sharpHeatFirstDerivativeH2Constant *
      (2 * (nu * dt)) ^ (-1 / 4 : ℝ) := by
    exact mul_nonneg (by
      unfold sharpHeatFirstDerivativeH2Constant
        sharpHeatSecondDerivativeH3Constant
      positivity) (Real.rpow_nonneg (by positivity) _)
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (norm_sharpNonlinearSource_component_le u component) hfactor)

/-- Heat-transported unweighted coefficient vector of a native `H2` source. -/
def heatTransportedH2SourceCoefficient
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) : ComplexVector :=
  fun component ↦ (heatStokesMultiplier nu dt k : ℂ) *
    weightedSobolevRawCoefficients 2 (source component) k

/-- The complete transported first-derivative Jacobian coefficient. -/
def heatTransportedFirstDerivativeJacobianCoefficient
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) : ComplexJacobianArray :=
  fun component coordinate ↦
    heatTransportedFirstDerivativeCoefficient
      nu dt source component coordinate k

/-- The reconstructed derivative array is exactly the standard Fourier Jacobian of the
heat-transported source coefficient. -/
theorem heatTransportedFirstDerivativeJacobianCoefficient_eq_fourierJacobianMode
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedFirstDerivativeJacobianCoefficient nu dt source k =
      fourierJacobianMode k (heatTransportedH2SourceCoefficient nu dt source k) := by
  ext component coordinate
  simp [heatTransportedFirstDerivativeJacobianCoefficient,
    heatTransportedFirstDerivativeCoefficient,
    heatTransportedH2SourceCoefficient, fourierJacobianMode,
    orderedDerivativeMultiplier, coordinateFourierMultiplier]
  ring

/-- Actual heat-transported curl coefficient of the native `H2` source. -/
def heatTransportedH2SourceCurlCoefficient
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) : ComplexVector :=
  frequencyCurlMultiplier k (heatTransportedH2SourceCoefficient nu dt source k)

theorem heatTransportedH2SourceCurlCoefficient_eq_complexCurl
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient nu dt source k =
      complexCurlFromJacobian
        (heatTransportedFirstDerivativeJacobianCoefficient nu dt source k) := by
  rw [heatTransportedH2SourceCurlCoefficient,
    heatTransportedFirstDerivativeJacobianCoefficient_eq_fourierJacobianMode,
    complexCurl_fourierJacobianMode]

/-- Every actual transported curl coefficient is controlled by its complete six oriented
derivative occurrences. -/
theorem norm_heatTransportedH2SourceCurlCoefficient_le_entryMass
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    ‖heatTransportedH2SourceCurlCoefficient nu dt source k‖ ≤
      complexCurlEntryMass
        (heatTransportedFirstDerivativeJacobianCoefficient nu dt source k) := by
  rw [heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
  exact (norm_complexVector_le_complexVectorL1 _).trans
    (complexVectorL1_complexCurlFromJacobian_le _)

/-- Exact complete six-occurrence coefficient population of the transported curl source. -/
def heatTransportedH2SourceCurlOccurrenceMass
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2) : ℝ :=
  ∑' k : SpatialFrequency,
    complexCurlEntryMass
      (heatTransportedFirstDerivativeJacobianCoefficient nu dt source k)

theorem summable_heatTransportedH2SourceCurlEntryMass
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2) :
    Summable fun k : SpatialFrequency ↦
      complexCurlEntryMass
        (heatTransportedFirstDerivativeJacobianCoefficient nu dt source k) := by
  have h21 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 2 1
  have h12 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 1 2
  have h02 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 0 2
  have h20 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 2 0
  have h10 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 1 0
  have h01 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 0 1
  simpa only [complexCurlEntryMass,
    heatTransportedFirstDerivativeJacobianCoefficient] using
      (((((h21.add h12).add h02).add h20).add h10).add h01)

/-- The exact curl-occurrence population is the sum of its six reconstructed derivative-face
populations. -/
theorem heatTransportedH2SourceCurlOccurrenceMass_eq
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2) :
    heatTransportedH2SourceCurlOccurrenceMass nu dt source =
      heatTransportedFirstDerivativeCoefficientMass nu dt source 2 1 +
      heatTransportedFirstDerivativeCoefficientMass nu dt source 1 2 +
      heatTransportedFirstDerivativeCoefficientMass nu dt source 0 2 +
      heatTransportedFirstDerivativeCoefficientMass nu dt source 2 0 +
      heatTransportedFirstDerivativeCoefficientMass nu dt source 1 0 +
      heatTransportedFirstDerivativeCoefficientMass nu dt source 0 1 := by
  unfold heatTransportedH2SourceCurlOccurrenceMass complexCurlEntryMass
    heatTransportedFirstDerivativeJacobianCoefficient
    heatTransportedFirstDerivativeCoefficientMass
  have h21 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 2 1
  have h12 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 1 2
  have h02 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 0 2
  have h20 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 2 0
  have h10 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 1 0
  have h01 := summable_norm_heatTransportedFirstDerivativeCoefficient
    nu dt h source 0 1
  rw [(((((h21.add h12).add h02).add h20).add h10).tsum_add h01),
    ((((h21.add h12).add h02).add h20).tsum_add h10),
    (((h21.add h12).add h02).tsum_add h20),
    ((h21.add h12).tsum_add h02), h21.tsum_add h12]

private theorem heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) :
    heatTransportedFirstDerivativeCoefficientMass
        nu dt source component coordinate ≤
      sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ) * ‖source‖ := by
  have hfactor : 0 ≤ sharpHeatFirstDerivativeH2Constant *
      (2 * (nu * dt)) ^ (-1 / 4 : ℝ) := by
    exact mul_nonneg (by
      unfold sharpHeatFirstDerivativeH2Constant
        sharpHeatSecondDerivativeH3Constant
      positivity) (Real.rpow_nonneg (by positivity) _)
  exact (heatTransportedFirstDerivativeCoefficientMass_le
      nu dt h hlocal source component coordinate).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm source component) hfactor)

/-- The six oriented derivative occurrences controlling the actual curl have one common sharp
positive-elapsed `H2` source bound. -/
theorem heatTransportedH2SourceCurlOccurrenceMass_le
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2) :
    heatTransportedH2SourceCurlOccurrenceMass nu dt source ≤
      6 * (sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ)) * ‖source‖ := by
  rw [heatTransportedH2SourceCurlOccurrenceMass_eq nu dt h source]
  have h21 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 2 1
  have h12 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 1 2
  have h02 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 0 2
  have h20 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 2 0
  have h10 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 1 0
  have h01 := heatTransportedFirstDerivativeCoefficientMass_le_vectorNorm
    nu dt h hlocal source 0 1
  linarith

/-- Complete `ℓ1` population of the genuine heat-transported curl-vector coefficients. -/
def heatTransportedH2SourceCurlCoefficientMass
    (nu dt : ℝ) (source : PeriodicVectorWeightedSobolev 2) : ℝ :=
  ∑' k : SpatialFrequency,
    ‖heatTransportedH2SourceCurlCoefficient nu dt source k‖

theorem summable_norm_heatTransportedH2SourceCurlCoefficient
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2) :
    Summable fun k : SpatialFrequency ↦
      ‖heatTransportedH2SourceCurlCoefficient nu dt source k‖ := by
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_heatTransportedH2SourceCurlCoefficient_le_entryMass nu dt source)
    (summable_heatTransportedH2SourceCurlEntryMass nu dt h source)

/-- The actual curl-vector coefficient population is paid by the complete six-occurrence
population, without replacing the curl by an assumed spectral source. -/
theorem heatTransportedH2SourceCurlCoefficientMass_le_occurrenceMass
    (nu dt : ℝ) (h : 0 < nu * dt)
    (source : PeriodicVectorWeightedSobolev 2) :
    heatTransportedH2SourceCurlCoefficientMass nu dt source ≤
      heatTransportedH2SourceCurlOccurrenceMass nu dt source := by
  unfold heatTransportedH2SourceCurlCoefficientMass
    heatTransportedH2SourceCurlOccurrenceMass
  exact (summable_norm_heatTransportedH2SourceCurlCoefficient nu dt h source).tsum_le_tsum
    (norm_heatTransportedH2SourceCurlCoefficient_le_entryMass nu dt source)
    (summable_heatTransportedH2SourceCurlEntryMass nu dt h source)

/-- Sharp positive-elapsed bound for the genuine curl-vector coefficient population of an
arbitrary native weighted `H2` source. -/
theorem heatTransportedH2SourceCurlCoefficientMass_le
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2) :
    heatTransportedH2SourceCurlCoefficientMass nu dt source ≤
      6 * (sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ)) * ‖source‖ :=
  (heatTransportedH2SourceCurlCoefficientMass_le_occurrenceMass
    nu dt h source).trans
      (heatTransportedH2SourceCurlOccurrenceMass_le nu dt h hlocal source)

/-- **Unconditional transported nonlinear vorticity-source bound.**  The genuine curl of the
heat-transported native Leray--divergence source has a complete coefficient `ℓ1` population with
the locally integrable positive-elapsed kernel and quadratic native weighted-`H3` cost. -/
theorem heatTransportedSharpNonlinearVorticitySourceCoefficientMass_le
    (nu dt : ℝ) (h : 0 < nu * dt) (hlocal : 2 * (nu * dt) ≤ 1)
    (u : PeriodicVectorWeightedSobolev 3) :
    heatTransportedH2SourceCurlCoefficientMass
        nu dt (sharpNonlinearSource u) ≤
      6 * (sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ)) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2) := by
  have hbase := heatTransportedH2SourceCurlCoefficientMass_le
    nu dt h hlocal (sharpNonlinearSource u)
  have hfactor : 0 ≤ 6 * (sharpHeatFirstDerivativeH2Constant *
      (2 * (nu * dt)) ^ (-1 / 4 : ℝ)) := by
    exact mul_nonneg (by norm_num) (mul_nonneg (by
      unfold sharpHeatFirstDerivativeH2Constant
        sharpHeatSecondDerivativeH3Constant
      positivity) (Real.rpow_nonneg (by positivity) _))
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (norm_sharpNonlinearSource_le u) hfactor)

/-- The exact quadratic majorant for the genuine transported nonlinear vorticity source is
locally integrable at zero elapsed time for every positive viscosity. -/
theorem integrableOn_heatTransportedSharpNonlinearVorticitySourceMajorant
    (nu T : ℝ) (hnu : 0 < nu) (hT : 0 < T)
    (u : PeriodicVectorWeightedSobolev 3) :
    IntegrableOn (fun dt : ℝ ↦
      6 * (sharpHeatFirstDerivativeH2Constant *
        (2 * (nu * dt)) ^ (-1 / 4 : ℝ)) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2)) (Ioo 0 T) := by
  have hbase : IntegrableOn (fun dt : ℝ ↦ dt ^ (-1 / 4 : ℝ)) (Ioo 0 T) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  let C := 6 * (sharpHeatFirstDerivativeH2Constant *
    (2 * nu) ^ (-1 / 4 : ℝ)) *
      ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2)
  have hscaled := hbase.const_mul C
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
  intro dt hdt
  dsimp [C]
  rw [show 2 * (nu * dt) = (2 * nu) * dt by ring,
    Real.mul_rpow (by positivity) hdt.1.le]
  ring

section Audit

#print axioms heatFirstDerivativeH2KernelMass_le
#print axioms heatFirstDerivativeH2CoefficientMass_le
#print axioms heatTransportedFirstDerivativeCoefficient_eq_reconstruction
#print axioms heatTransportedH2SourceCurlCoefficientMass_le
#print axioms heatTransportedSharpNonlinearVorticitySourceCoefficientMass_le
#print axioms integrableOn_heatTransportedSharpNonlinearVorticitySourceMajorant

end Audit

end Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
