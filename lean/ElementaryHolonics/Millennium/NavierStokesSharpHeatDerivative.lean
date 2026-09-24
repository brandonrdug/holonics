import ElementaryHolonics.Millennium.NavierStokesH3BilinearNorm
import ElementaryHolonics.Millennium.NavierStokesWeightedHeatSemigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Sharp periodic heat control of the second spatial derivative

**[proved-derived]** This module supplies the first analytic Fourier edge between the complete
weighted Sobolev carriers and the canonical second-spatial-derivative receiver.  The proof keeps
the complete integer-frequency population.  Its two sharp kernel masses are

`sum_k lambda_k^2 exp (-2 a lambda_k) / (1 + lambda_k)^3 = O(a^(-1/2))`

and

`sum_k lambda_k^2 exp (-2 a lambda_k) / (1 + lambda_k)^2 = O(a^(-3/2))`.

Fourier Cauchy--Schwarz therefore gives the unsquared `a^(-1/4)` bound from weighted `H3`
initial data and the `a^(-3/4)` bound from a weighted `H2` Duhamel source.  The receiver returned
here is the absolute coefficient mass of the Laplace-symbol second derivative.  Identifying that
mass with the compact-map norm of the physical `D omega = D^2 u` chart still requires the
coefficient-to-physical reconstruction square; no such equality is manufactured here.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal lp

namespace Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## A quantitative Gaussian lattice owner -/

/-- One-dimensional Gaussian lattice current. -/
def gaussianLineMass (a : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-a * (n : ℝ) ^ 2)

theorem summable_gaussianLine {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ ↦ Real.exp (-a * (n : ℝ) ^ 2) := by
  have hparameter : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 hparameter).summable
  refine h.congr fun n ↦ ?_
  congr 1
  simp only [add_zero]
  field_simp [Real.pi_ne_zero]

/-- The Gaussian line is the zero-characteristic even Hurwitz kernel. -/
theorem gaussianLineMass_eq_evenKernel (a : ℝ) (ha : 0 < a) :
    gaussianLineMass a = HurwitzZeta.evenKernel 0 (a / Real.pi) := by
  have hparameter : 0 < a / Real.pi := div_pos ha Real.pi_pos
  unfold gaussianLineMass
  calc
    (∑' n : ℤ, Real.exp (-a * (n : ℝ) ^ 2)) =
        ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * (a / Real.pi)) := by
      apply tsum_congr
      intro n
      congr 1
      simp only [add_zero]
      field_simp [Real.pi_ne_zero]
    _ = HurwitzZeta.evenKernel 0 (a / Real.pi) :=
      (HurwitzZeta.hasSum_int_evenKernel 0 hparameter).tsum_eq

/-- Increasing the positive Gaussian parameter decreases the complete line mass. -/
theorem gaussianLineMass_antitone
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gaussianLineMass b ≤ gaussianLineMass a := by
  have hb : 0 < b := ha.trans_le hab
  unfold gaussianLineMass
  exact (summable_gaussianLine hb).tsum_le_tsum (fun n ↦ by
    rw [Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg (n : ℝ))])
    (summable_gaussianLine ha)

/-- Poisson/Hurwitz self-reciprocity of the integer Gaussian line. -/
theorem gaussianLineMass_reciprocal (a : ℝ) (ha : 0 < a) :
    gaussianLineMass a =
      1 / (a / Real.pi) ^ (1 / 2 : ℝ) *
        gaussianLineMass (Real.pi ^ 2 / a) := by
  have hparameter : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have hdual : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  rw [gaussianLineMass_eq_evenKernel a ha,
    HurwitzZeta.evenKernel_functional_equation]
  rw [← congrFun HurwitzZeta.evenKernel_eq_cosKernel_of_zero
    (1 / (a / Real.pi))]
  rw [gaussianLineMass_eq_evenKernel (Real.pi ^ 2 / a) hdual]
  congr 2
  field_simp [Real.pi_ne_zero, ha.ne']

/-- The sharp small-parameter Gaussian line bound, with a fixed finite lattice constant. -/
theorem gaussianLineMass_le_sharp
    (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1) :
    gaussianLineMass a ≤
      1 / (a / Real.pi) ^ (1 / 2 : ℝ) * gaussianLineMass 1 := by
  rw [gaussianLineMass_reciprocal a ha]
  have hdual : 1 ≤ Real.pi ^ 2 / a := by
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    apply (le_div_iff₀ ha).2
    simpa using haOne.trans hpi
  have hmass := gaussianLineMass_antitone (by norm_num : (0 : ℝ) < 1) hdual
  exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Complete three-dimensional periodic Gaussian mass in the Stokes eigenvalue chart. -/
def periodicGaussianMass (a : ℝ) : ℝ :=
  ∑' k : SpatialFrequency, Real.exp (-a * torusStokesEigenvalue k)

private theorem periodicGaussianTerm_factor
    (a : ℝ) (k : SpatialFrequency) :
    Real.exp (-a * torusStokesEigenvalue k) =
      Real.exp (-(a * (2 * Real.pi) ^ 2) * (k 0 : ℝ) ^ 2) *
        Real.exp (-(a * (2 * Real.pi) ^ 2) * (k 1 : ℝ) ^ 2) *
          Real.exp (-(a * (2 * Real.pi) ^ 2) * (k 2 : ℝ) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [torusStokesEigenvalue, frequencySquared, Fin.sum_univ_three]
  ring

theorem summable_periodicGaussian {a : ℝ} (ha : 0 < a) :
    Summable fun k : SpatialFrequency ↦ Real.exp (-a * torusStokesEigenvalue k) := by
  let b : ℝ := a * (2 * Real.pi) ^ 2
  have hb : 0 < b := mul_pos ha (sq_pos_of_pos (by positivity))
  let line : ℤ → ℝ := fun n ↦ Real.exp (-b * (n : ℝ) ^ 2)
  have hline : Summable line := summable_gaussianLine hb
  have hpair : Summable fun p : ℤ × ℤ ↦ line p.1 * line p.2 := by
    exact hline.mul_of_nonneg hline (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ (Real.exp_pos _).le)
  have htriple : Summable fun p : (ℤ × ℤ) × ℤ ↦
      (line p.1.1 * line p.1.2) * line p.2 := by
    exact hpair.mul_of_nonneg hline (fun _ ↦ by positivity)
      (fun _ ↦ (Real.exp_pos _).le)
  have htranslated := frequencyTripleEquiv.summable_iff.mpr htriple
  refine htranslated.congr fun k ↦ ?_
  change
    line (k 0) * line (k 1) * line (k 2) =
      Real.exp (-a * torusStokesEigenvalue k)
  simpa [line, b] using (periodicGaussianTerm_factor a k).symm

theorem periodicGaussianMass_eq_cube (a : ℝ) (ha : 0 < a) :
    periodicGaussianMass a = (gaussianLineMass (a * (2 * Real.pi) ^ 2)) ^ 3 := by
  let b : ℝ := a * (2 * Real.pi) ^ 2
  have hb : 0 < b := mul_pos ha (sq_pos_of_pos (by positivity))
  let line : ℤ → ℝ := fun n ↦ Real.exp (-b * (n : ℝ) ^ 2)
  have hline : Summable line := summable_gaussianLine hb
  have hpair : Summable fun p : ℤ × ℤ ↦ line p.1 * line p.2 := by
    exact hline.mul_of_nonneg hline (fun _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ (Real.exp_pos _).le)
  have htriple : Summable fun p : (ℤ × ℤ) × ℤ ↦
      (line p.1.1 * line p.1.2) * line p.2 := by
    exact hpair.mul_of_nonneg hline (fun _ ↦ by positivity)
      (fun _ ↦ (Real.exp_pos _).le)
  have hpairProduct := hline.hasSum.mul_eq hline.hasSum hpair.hasSum
  have htripleProduct := hpair.hasSum.mul_eq hline.hasSum htriple.hasSum
  calc
    periodicGaussianMass a =
        ∑' p : (ℤ × ℤ) × ℤ,
          (line p.1.1 * line p.1.2) * line p.2 := by
      unfold periodicGaussianMass
      rw [← frequencyTripleEquiv.symm.tsum_eq
        (fun k : SpatialFrequency ↦ Real.exp (-a * torusStokesEigenvalue k))]
      apply tsum_congr
      rintro ⟨⟨p₀, p₁⟩, p₂⟩
      simpa [frequencyTripleEquiv, line, b] using
        periodicGaussianTerm_factor a (![p₀, p₁, p₂] : SpatialFrequency)
    _ = (∑' p : ℤ × ℤ, line p.1 * line p.2) * (∑' n, line n) :=
      htripleProduct.symm
    _ = ((∑' n, line n) * (∑' n, line n)) * (∑' n, line n) := by
      rw [← hpairProduct]
    _ = (gaussianLineMass b) ^ 3 := by
      rw [show (∑' n, line n) = gaussianLineMass b by rfl]
      ring
    _ = (gaussianLineMass (a * (2 * Real.pi) ^ 2)) ^ 3 := rfl

/-- The fixed unit-scale Gaussian line mass. -/
def gaussianLineUnitMass : ℝ := gaussianLineMass 1

theorem gaussianLineUnitMass_nonneg : 0 ≤ gaussianLineUnitMass := by
  unfold gaussianLineUnitMass gaussianLineMass
  exact tsum_nonneg fun _ ↦ (Real.exp_pos _).le

private theorem gaussianReciprocalScale_eq (a : ℝ) (ha : 0 < a) :
    1 / (a / Real.pi) ^ (1 / 2 : ℝ) =
      (Real.pi / a) ^ (1 / 2 : ℝ) := by
  rw [Real.div_rpow ha.le Real.pi_pos.le,
    Real.div_rpow Real.pi_pos.le ha.le]
  have haPow : a ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_ne_zero ha.le (by norm_num)).2 ha.ne'
  have hpiPow : Real.pi ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_ne_zero Real.pi_pos.le (by norm_num)).2 Real.pi_ne_zero
  field_simp [haPow, hpiPow]

/-- A universal line envelope: the fixed unit mass plus the exact reciprocal square-root
small-time scale. -/
theorem gaussianLineMass_le_envelope (a : ℝ) (ha : 0 < a) :
    gaussianLineMass a ≤ gaussianLineUnitMass *
      (1 + (Real.pi / a) ^ (1 / 2 : ℝ)) := by
  have hM : 0 ≤ gaussianLineUnitMass := gaussianLineUnitMass_nonneg
  have hx : 0 ≤ (Real.pi / a) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases haOne : a ≤ 1
  · have hsharp := gaussianLineMass_le_sharp a ha haOne
    rw [gaussianReciprocalScale_eq a ha] at hsharp
    unfold gaussianLineUnitMass
    calc
      gaussianLineMass a ≤
          (Real.pi / a) ^ (1 / 2 : ℝ) * gaussianLineMass 1 := hsharp
      _ ≤ gaussianLineMass 1 * (1 + (Real.pi / a) ^ (1 / 2 : ℝ)) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) hM
  · have hone : 1 ≤ a := le_of_not_ge haOne
    have hlarge := gaussianLineMass_antitone (by norm_num : (0 : ℝ) < 1) hone
    calc
      gaussianLineMass a ≤ gaussianLineMass 1 := hlarge
      _ ≤ gaussianLineMass 1 * (1 + (Real.pi / a) ^ (1 / 2 : ℝ)) := by
        exact le_mul_of_one_le_right hM (by linarith)

private theorem one_add_cube_le_eight (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ 3 ≤ 8 * (1 + x ^ 3) := by
  by_cases hxOne : x ≤ 1
  · have hsum : 1 + x ≤ 2 := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + x) hsum 3
    nlinarith [pow_nonneg hx 3]
  · have hone : 1 ≤ x := le_of_not_ge hxOne
    have hsum : 1 + x ≤ 2 * x := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + x) hsum 3
    calc
      (1 + x) ^ 3 ≤ (2 * x) ^ 3 := hpow
      _ = 8 * x ^ 3 := by ring
      _ ≤ 8 * (1 + x ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- Universal three-dimensional periodic Gaussian estimate.  Its only singular term is the
sharp dimensional scale `a^(-3/2)`. -/
theorem periodicGaussianMass_le_envelope (a : ℝ) (ha : 0 < a) :
    periodicGaussianMass a ≤
      8 * gaussianLineUnitMass ^ 3 *
        (1 + (Real.pi / a) ^ (3 / 2 : ℝ)) := by
  let b : ℝ := a * (2 * Real.pi) ^ 2
  have hb : 0 < b := mul_pos ha (sq_pos_of_pos (by positivity))
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hab : a ≤ b := by
    dsimp [b]
    exact le_mul_of_one_le_right ha.le hscale
  have hlineMono := gaussianLineMass_antitone ha hab
  have hlineEnvelope := gaussianLineMass_le_envelope a ha
  let x : ℝ := (Real.pi / a) ^ (1 / 2 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hM : 0 ≤ gaussianLineUnitMass := gaussianLineUnitMass_nonneg
  have hcube : x ^ 3 = (Real.pi / a) ^ (3 / 2 : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ Real.pi / a)]
    norm_num
  calc
    periodicGaussianMass a = gaussianLineMass b ^ 3 := by
      simpa [b] using periodicGaussianMass_eq_cube a ha
    _ ≤ gaussianLineMass a ^ 3 :=
      pow_le_pow_left₀ (by
        unfold gaussianLineMass
        exact tsum_nonneg fun _ ↦ (Real.exp_pos _).le) hlineMono 3
    _ ≤ (gaussianLineUnitMass * (1 + x)) ^ 3 :=
      pow_le_pow_left₀ (by
        unfold gaussianLineMass
        exact tsum_nonneg fun _ ↦ (Real.exp_pos _).le) hlineEnvelope 3
    _ = gaussianLineUnitMass ^ 3 * (1 + x) ^ 3 := by ring
    _ ≤ gaussianLineUnitMass ^ 3 * (8 * (1 + x ^ 3)) :=
      mul_le_mul_of_nonneg_left (one_add_cube_le_eight x hx) (pow_nonneg hM 3)
    _ = 8 * gaussianLineUnitMass ^ 3 *
        (1 + (Real.pi / a) ^ (3 / 2 : ℝ)) := by rw [hcube]; ring

/-- On the local parabolic range, the periodic Gaussian has its pure dimensional
`a^(-3/2)` scale. -/
theorem periodicGaussianMass_le_smallTime
    (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1) :
    periodicGaussianMass a ≤
      8 * gaussianLineUnitMass ^ 3 * (1 + Real.pi ^ (3 / 2 : ℝ)) *
        a ^ (-3 / 2 : ℝ) := by
  have haInv : 1 ≤ a⁻¹ := (one_le_inv₀ ha).2 haOne
  have haPower : 1 ≤ a ^ (-3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg ha.le, ← Real.inv_rpow ha.le]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) haInv (by norm_num)
  have hpiPower : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
  have hdiv : (Real.pi / a) ^ (3 / 2 : ℝ) =
      Real.pi ^ (3 / 2 : ℝ) * a ^ (-3 / 2 : ℝ) := by
    rw [Real.div_rpow Real.pi_pos.le ha.le,
      show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg ha.le]
    ring
  have hbracket : 1 + (Real.pi / a) ^ (3 / 2 : ℝ) ≤
      (1 + Real.pi ^ (3 / 2 : ℝ)) * a ^ (-3 / 2 : ℝ) := by
    rw [hdiv]
    nlinarith
  calc
    periodicGaussianMass a ≤
        8 * gaussianLineUnitMass ^ 3 *
          (1 + (Real.pi / a) ^ (3 / 2 : ℝ)) :=
      periodicGaussianMass_le_envelope a ha
    _ ≤ 8 * gaussianLineUnitMass ^ 3 *
        ((1 + Real.pi ^ (3 / 2 : ℝ)) * a ^ (-3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbracket
        (mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3))
    _ = 8 * gaussianLineUnitMass ^ 3 * (1 + Real.pi ^ (3 / 2 : ℝ)) *
        a ^ (-3 / 2 : ℝ) := by ring

/-! ## Sharp squared kernels -/

/-- Squared Fourier kernel for a second spatial derivative fed by weighted `H2` data. -/
def heatSecondDerivativeH2KernelMass (a : ℝ) : ℝ :=
  ∑' k : SpatialFrequency,
    torusStokesEigenvalue k ^ 2 *
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        periodicSobolevWeight 2 k

private theorem heatSecondDerivativeH2KernelTerm_nonneg
    (a : ℝ) (k : SpatialFrequency) :
    0 ≤ torusStokesEigenvalue k ^ 2 *
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        periodicSobolevWeight 2 k := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (periodicSobolevWeight_nonneg 2 k)

private theorem heatSecondDerivativeH2KernelTerm_le_gaussian
    (a : ℝ) (k : SpatialFrequency) :
    torusStokesEigenvalue k ^ 2 *
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          periodicSobolevWeight 2 k ≤
      Real.exp (-(2 * a) * torusStokesEigenvalue k) := by
  let x := torusStokesEigenvalue k
  have hx : 0 ≤ x := torusStokesEigenvalue_nonneg k
  have hden : 0 < periodicSobolevWeight 2 k := periodicSobolevWeight_pos 2 k
  rw [div_le_iff₀ hden]
  rw [periodicSobolevWeight]
  have hexp : 0 < Real.exp (-(2 * a) * x) := Real.exp_pos _
  dsimp [x] at hx hexp ⊢
  nlinarith [sq_nonneg (1 + torusStokesEigenvalue k)]

theorem summable_heatSecondDerivativeH2Kernel {a : ℝ} (ha : 0 < a) :
    Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k ^ 2 *
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          periodicSobolevWeight 2 k := by
  apply Summable.of_nonneg_of_le
  · exact heatSecondDerivativeH2KernelTerm_nonneg a
  · exact heatSecondDerivativeH2KernelTerm_le_gaussian a
  · simpa [mul_assoc] using summable_periodicGaussian (mul_pos (by norm_num) ha)

/-- The weighted `H2` squared second-derivative heat kernel has the sharp
three-dimensional `a^(-3/2)` scale. -/
theorem heatSecondDerivativeH2KernelMass_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1) :
    heatSecondDerivativeH2KernelMass a ≤
      8 * gaussianLineUnitMass ^ 3 * (1 + Real.pi ^ (3 / 2 : ℝ)) *
        (2 * a) ^ (-3 / 2 : ℝ) := by
  unfold heatSecondDerivativeH2KernelMass
  calc
    (∑' k : SpatialFrequency,
        torusStokesEigenvalue k ^ 2 *
          Real.exp (-(2 * a) * torusStokesEigenvalue k) /
            periodicSobolevWeight 2 k) ≤
        periodicGaussianMass (2 * a) := by
      unfold periodicGaussianMass
      exact (summable_heatSecondDerivativeH2Kernel ha).tsum_le_tsum
        (heatSecondDerivativeH2KernelTerm_le_gaussian a)
        (summable_periodicGaussian (mul_pos (by norm_num) ha))
    _ ≤ 8 * gaussianLineUnitMass ^ 3 * (1 + Real.pi ^ (3 / 2 : ℝ)) *
        (2 * a) ^ (-3 / 2 : ℝ) :=
      periodicGaussianMass_le_smallTime (2 * a) (mul_pos (by norm_num) ha) haLocal

private theorem integral_shifted_three_halves (c : ℝ) (hc : 0 < c) :
    (∫ r : ℝ in Set.Ioi 0, (c + r) ^ (-3 / 2 : ℝ)) =
      2 * c ^ (-1 / 2 : ℝ) := by
  let primitive : ℝ → ℝ := fun r ↦ -2 * (c + r) ^ (-1 / 2 : ℝ)
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivAt primitive ((c + r) ^ (-3 / 2 : ℝ)) r := by
    intro r hr
    have hcr : c + r ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hc hr)
    have hd := (((hasDerivAt_const r c).add (hasDerivAt_id r)).rpow_const
      (p := (-1 / 2 : ℝ)) (Or.inl hcr)).const_mul (-2)
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] at hd
    simp only [Pi.add_apply, Pi.zero_apply, id_eq, zero_add, one_mul] at hd
    have hcoefficient :
        -2 * ((-1 / 2 : ℝ) * (c + r) ^ (-3 / 2 : ℝ)) =
          (c + r) ^ (-3 / 2 : ℝ) := by ring
    rw [hcoefficient] at hd
    exact hd
  have hintegrable : IntegrableOn (fun r : ℝ ↦ (c + r) ^ (-3 / 2 : ℝ))
      (Set.Ioi 0) :=
    by simpa [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (a := -3 / 2) (c := 0) (m := c)
        (by norm_num) (by simpa using hc))
  have htendsto : Tendsto primitive atTop (nhds 0) := by
    dsimp [primitive]
    have hpower : Tendsto (fun r : ℝ ↦ r ^ (-1 / 2 : ℝ)) atTop (nhds 0) := by
      convert tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num) using 1 <;>
        norm_num
    have hbase : Tendsto (fun r : ℝ ↦ (c + r) ^ (-1 / 2 : ℝ)) atTop (nhds 0) := by
      have hshift : Tendsto (fun r : ℝ ↦ c + r) atTop atTop := by
        simpa [add_comm] using tendsto_atTop_add_const_right atTop c tendsto_id
      change Tendsto ((fun r : ℝ ↦ r ^ (-1 / 2 : ℝ)) ∘ fun r ↦ c + r)
        atTop (nhds 0)
      exact hpower.comp hshift
    simpa using hbase.const_mul (-2)
  have hfundamental := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hintegrable htendsto
  dsimp [primitive] at hfundamental
  convert hfundamental using 1 <;> ring

/-- Gaussian mass with one elliptic resolvent factor; this is the squared-kernel
majorant which distinguishes weighted `H3` from weighted `H2`. -/
def periodicGaussianResolventMass (a : ℝ) : ℝ :=
  ∑' k : SpatialFrequency,
    Real.exp (-(2 * a) * torusStokesEigenvalue k) /
      (1 + torusStokesEigenvalue k)

private theorem gaussianResolventTerm_nonneg (a : ℝ) (k : SpatialFrequency) :
    0 ≤ Real.exp (-(2 * a) * torusStokesEigenvalue k) /
      (1 + torusStokesEigenvalue k) := by
  exact div_nonneg (Real.exp_pos _).le (by linarith [torusStokesEigenvalue_nonneg k])

private theorem gaussianResolventTerm_le_gaussian (a : ℝ) (k : SpatialFrequency) :
    Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        (1 + torusStokesEigenvalue k) ≤
      Real.exp (-(2 * a) * torusStokesEigenvalue k) := by
  have hden : 0 < 1 + torusStokesEigenvalue k := by
    linarith [torusStokesEigenvalue_nonneg k]
  rw [div_le_iff₀ hden]
  nlinarith [Real.exp_pos (-(2 * a) * torusStokesEigenvalue k),
    torusStokesEigenvalue_nonneg k]

theorem summable_periodicGaussianResolvent {a : ℝ} (ha : 0 < a) :
    Summable fun k : SpatialFrequency ↦
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        (1 + torusStokesEigenvalue k) := by
  exact Summable.of_nonneg_of_le (gaussianResolventTerm_nonneg a)
    (gaussianResolventTerm_le_gaussian a)
    (summable_periodicGaussian (mul_pos (by norm_num) ha))

private theorem gaussianResolventTerm_eq_integral
    (a : ℝ) (k : SpatialFrequency) :
    Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        (1 + torusStokesEigenvalue k) =
      ∫ r : ℝ in Set.Ioi 0,
        Real.exp (-(2 * a) * torusStokesEigenvalue k) *
          Real.exp (-(1 + torusStokesEigenvalue k) * r) := by
  have hnegative : -(1 + torusStokesEigenvalue k) < 0 := by
    linarith [torusStokesEigenvalue_nonneg k]
  rw [integral_const_mul,
    integral_exp_mul_Ioi hnegative 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

private theorem integrableOn_gaussianResolventIntegrand
    (a : ℝ) (k : SpatialFrequency) :
    IntegrableOn
      (fun r : ℝ ↦ Real.exp (-(2 * a) * torusStokesEigenvalue k) *
        Real.exp (-(1 + torusStokesEigenvalue k) * r))
      (Set.Ioi 0) := by
  have hnegative : -(1 + torusStokesEigenvalue k) < 0 := by
    linarith [torusStokesEigenvalue_nonneg k]
  exact (integrableOn_exp_mul_Ioi hnegative 0).const_mul
    (Real.exp (-(2 * a) * torusStokesEigenvalue k))

/-- The elliptic resolvent factor is exactly an additional positive heat-time integral. -/
theorem periodicGaussianResolventMass_eq_integral (a : ℝ) (ha : 0 < a) :
    periodicGaussianResolventMass a =
      ∫ r : ℝ in Set.Ioi 0,
        Real.exp (-r) * periodicGaussianMass (2 * a + r) := by
  let F : SpatialFrequency → ℝ → ℝ := fun k r ↦
    Real.exp (-(2 * a) * torusStokesEigenvalue k) *
      Real.exp (-(1 + torusStokesEigenvalue k) * r)
  have hFint : ∀ k : SpatialFrequency,
      Integrable (F k) (volume.restrict (Set.Ioi 0)) := by
    intro k
    exact integrableOn_gaussianResolventIntegrand a k
  have hFnormIntegral : ∀ k : SpatialFrequency,
      (∫ r : ℝ in Set.Ioi 0, ‖F k r‖) =
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          (1 + torusStokesEigenvalue k) := by
    intro k
    have hnonneg : ∀ r : ℝ, 0 ≤ F k r := fun r ↦ by
      dsimp [F]
      positivity
    rw [show (fun r : ℝ ↦ ‖F k r‖) = F k by
      funext r
      exact Real.norm_of_nonneg (hnonneg r)]
    exact (gaussianResolventTerm_eq_integral a k).symm
  have hFnormSummable : Summable fun k : SpatialFrequency ↦
      ∫ r : ℝ in Set.Ioi 0, ‖F k r‖ := by
    apply (summable_periodicGaussianResolvent ha).congr
    intro k
    exact (hFnormIntegral k).symm
  have hswap := integral_tsum_of_summable_integral_norm hFint hFnormSummable
  calc
    periodicGaussianResolventMass a =
        ∑' k : SpatialFrequency, ∫ r : ℝ in Set.Ioi 0, F k r := by
      unfold periodicGaussianResolventMass
      apply tsum_congr
      intro k
      exact gaussianResolventTerm_eq_integral a k
    _ = ∫ r : ℝ in Set.Ioi 0, ∑' k : SpatialFrequency, F k r := hswap
    _ = ∫ r : ℝ in Set.Ioi 0,
        Real.exp (-r) * periodicGaussianMass (2 * a + r) := by
      apply integral_congr_ae
      filter_upwards with r
      calc
        (∑' k : SpatialFrequency, F k r) =
            ∑' k : SpatialFrequency,
              Real.exp (-r) *
                Real.exp (-(2 * a + r) * torusStokesEigenvalue k) := by
          apply tsum_congr
          intro k
          dsimp [F]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ = Real.exp (-r) *
            ∑' k : SpatialFrequency,
              Real.exp (-(2 * a + r) * torusStokesEigenvalue k) := tsum_mul_left
        _ = Real.exp (-r) * periodicGaussianMass (2 * a + r) := rfl

private theorem gaussianResolventIntegrand_le_majorant
    (a r : ℝ) (ha : 0 < a) (hr : r ∈ Set.Ioi (0 : ℝ)) :
    Real.exp (-r) * periodicGaussianMass (2 * a + r) ≤
      (8 * gaussianLineUnitMass ^ 3) *
        (Real.exp (-r) + Real.pi ^ (3 / 2 : ℝ) *
          (2 * a + r) ^ (-3 / 2 : ℝ)) := by
  have hrPos : 0 < r := hr
  have htime : 0 < 2 * a + r := by linarith
  have hgaussian := periodicGaussianMass_le_envelope (2 * a + r) htime
  have hdiv : (Real.pi / (2 * a + r)) ^ (3 / 2 : ℝ) =
      Real.pi ^ (3 / 2 : ℝ) * (2 * a + r) ^ (-3 / 2 : ℝ) := by
    rw [Real.div_rpow Real.pi_pos.le htime.le,
      show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg htime.le]
    ring
  have hexpNonneg : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have hconstantNonneg : 0 ≤ 8 * gaussianLineUnitMass ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3)
  calc
    Real.exp (-r) * periodicGaussianMass (2 * a + r) ≤
        Real.exp (-r) * ((8 * gaussianLineUnitMass ^ 3) *
          (1 + (Real.pi / (2 * a + r)) ^ (3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hgaussian hexpNonneg
    _ = (8 * gaussianLineUnitMass ^ 3) *
        (Real.exp (-r) + Real.exp (-r) * Real.pi ^ (3 / 2 : ℝ) *
          (2 * a + r) ^ (-3 / 2 : ℝ)) := by rw [hdiv]; ring
    _ ≤ (8 * gaussianLineUnitMass ^ 3) *
        (Real.exp (-r) + Real.pi ^ (3 / 2 : ℝ) *
          (2 * a + r) ^ (-3 / 2 : ℝ)) := by
      have hexpLe : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hpi : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
      have hpower : 0 ≤ (2 * a + r) ^ (-3 / 2 : ℝ) :=
        Real.rpow_nonneg htime.le _
      have hsingular : Real.exp (-r) *
          (Real.pi ^ (3 / 2 : ℝ) * (2 * a + r) ^ (-3 / 2 : ℝ)) ≤
          1 * (Real.pi ^ (3 / 2 : ℝ) * (2 * a + r) ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hexpLe (mul_nonneg hpi hpower)
      apply mul_le_mul_of_nonneg_left _ hconstantNonneg
      nlinarith

/-- The resolvent Gaussian mass has the sharp local `a^(-1/2)` squared-kernel scale. -/
theorem periodicGaussianResolventMass_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1) :
    periodicGaussianResolventMass a ≤
      (8 * gaussianLineUnitMass ^ 3) *
        (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
          (2 * a) ^ (-1 / 2 : ℝ) := by
  let target : ℝ → ℝ := fun r ↦
    Real.exp (-r) * periodicGaussianMass (2 * a + r)
  let majorant : ℝ → ℝ := fun r ↦
    (8 * gaussianLineUnitMass ^ 3) *
      (Real.exp (-r) + Real.pi ^ (3 / 2 : ℝ) *
        (2 * a + r) ^ (-3 / 2 : ℝ))
  have hExp : IntegrableOn (fun r : ℝ ↦ Real.exp (-r)) (Set.Ioi 0) :=
    integrableOn_exp_neg_Ioi 0
  have hPower : IntegrableOn
      (fun r : ℝ ↦ (2 * a + r) ^ (-3 / 2 : ℝ)) (Set.Ioi 0) := by
    simpa [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (a := -3 / 2) (c := 0) (m := 2 * a)
        (by norm_num) (by linarith))
  have hPiPower : IntegrableOn
      (fun r : ℝ ↦ Real.pi ^ (3 / 2 : ℝ) *
        (2 * a + r) ^ (-3 / 2 : ℝ)) (Set.Ioi 0) :=
    hPower.const_mul (Real.pi ^ (3 / 2 : ℝ))
  have hMajorant : IntegrableOn majorant (Set.Ioi 0) := by
    dsimp [majorant]
    exact (hExp.add hPiPower).const_mul (8 * gaussianLineUnitMass ^ 3)
  have hTargetMeasurable : Measurable target := by
    dsimp [target, periodicGaussianMass]
    fun_prop
  have hTargetNonneg : ∀ r : ℝ, 0 ≤ target r := by
    intro r
    dsimp [target, periodicGaussianMass]
    exact mul_nonneg (Real.exp_pos _).le
      (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
  have hTarget : IntegrableOn target (Set.Ioi 0) := by
    apply hMajorant.mono' hTargetMeasurable.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (hTargetNonneg r)]
    exact gaussianResolventIntegrand_le_majorant a r ha hr
  have hIntegralBound :
      (∫ r : ℝ in Set.Ioi 0, target r) ≤
        (8 * gaussianLineUnitMass ^ 3) *
          (1 + 2 * Real.pi ^ (3 / 2 : ℝ) *
            (2 * a) ^ (-1 / 2 : ℝ)) := by
    calc
      (∫ r : ℝ in Set.Ioi 0, target r) ≤
          ∫ r : ℝ in Set.Ioi 0, majorant r := by
        exact setIntegral_mono_on hTarget hMajorant measurableSet_Ioi
          (fun r hr ↦ gaussianResolventIntegrand_le_majorant a r ha hr)
      _ = (8 * gaussianLineUnitMass ^ 3) *
          (1 + 2 * Real.pi ^ (3 / 2 : ℝ) *
            (2 * a) ^ (-1 / 2 : ℝ)) := by
        dsimp [majorant]
        rw [integral_const_mul, integral_add hExp hPiPower,
          integral_exp_neg_Ioi_zero, integral_const_mul,
          integral_shifted_three_halves (2 * a) (mul_pos (by norm_num) ha)]
        ring
  have hInv : 1 ≤ (2 * a)⁻¹ :=
    (one_le_inv₀ (mul_pos (by norm_num) ha)).2 haLocal
  have hScale : 1 ≤ (2 * a) ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (mul_nonneg (by norm_num) ha.le),
      ← Real.inv_rpow (mul_nonneg (by norm_num) ha.le)]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hInv (by norm_num)
  rw [periodicGaussianResolventMass_eq_integral a ha]
  change (∫ r : ℝ in Set.Ioi 0, target r) ≤ _
  calc
    (∫ r : ℝ in Set.Ioi 0, target r) ≤
        (8 * gaussianLineUnitMass ^ 3) *
          (1 + 2 * Real.pi ^ (3 / 2 : ℝ) *
            (2 * a) ^ (-1 / 2 : ℝ)) := hIntegralBound
    _ ≤ (8 * gaussianLineUnitMass ^ 3) *
        (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
          (2 * a) ^ (-1 / 2 : ℝ) := by
      have hC : 0 ≤ 8 * gaussianLineUnitMass ^ 3 :=
        mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3)
      have hPi : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
      nlinarith

/-- Squared Fourier kernel for a second spatial derivative fed by weighted `H3` data. -/
def heatSecondDerivativeH3KernelMass (a : ℝ) : ℝ :=
  ∑' k : SpatialFrequency,
    torusStokesEigenvalue k ^ 2 *
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        periodicSobolevWeight 3 k

private theorem heatSecondDerivativeH3KernelTerm_nonneg
    (a : ℝ) (k : SpatialFrequency) :
    0 ≤ torusStokesEigenvalue k ^ 2 *
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        periodicSobolevWeight 3 k := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (periodicSobolevWeight_nonneg 3 k)

private theorem heatSecondDerivativeH3KernelTerm_le_resolvent
    (a : ℝ) (k : SpatialFrequency) :
    torusStokesEigenvalue k ^ 2 *
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          periodicSobolevWeight 3 k ≤
      Real.exp (-(2 * a) * torusStokesEigenvalue k) /
        (1 + torusStokesEigenvalue k) := by
  let x := torusStokesEigenvalue k
  have hx : 0 ≤ x := torusStokesEigenvalue_nonneg k
  have hbase : 0 < 1 + x := by linarith
  have hcube : periodicSobolevWeight 3 k = (1 + x) ^ 3 := by
    simp only [periodicSobolevWeight]
    rfl
  rw [hcube]
  have hcubePos : 0 < (1 + x) ^ 3 := pow_pos hbase 3
  have hexp : 0 < Real.exp (-(2 * a) * x) := Real.exp_pos _
  rw [div_le_iff₀ hcubePos]
  dsimp [x] at hx hbase hcubePos hexp ⊢
  field_simp [hbase.ne']
  nlinarith [sq_nonneg (1 + torusStokesEigenvalue k)]

theorem summable_heatSecondDerivativeH3Kernel {a : ℝ} (ha : 0 < a) :
    Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k ^ 2 *
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          periodicSobolevWeight 3 k := by
  exact Summable.of_nonneg_of_le (heatSecondDerivativeH3KernelTerm_nonneg a)
    (heatSecondDerivativeH3KernelTerm_le_resolvent a)
    (summable_periodicGaussianResolvent ha)

/-- The weighted `H3` squared second-derivative heat kernel has the sharp
`a^(-1/2)` scale. -/
theorem heatSecondDerivativeH3KernelMass_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1) :
    heatSecondDerivativeH3KernelMass a ≤
      (8 * gaussianLineUnitMass ^ 3) *
        (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
          (2 * a) ^ (-1 / 2 : ℝ) := by
  unfold heatSecondDerivativeH3KernelMass
  calc
    (∑' k : SpatialFrequency,
        torusStokesEigenvalue k ^ 2 *
          Real.exp (-(2 * a) * torusStokesEigenvalue k) /
            periodicSobolevWeight 3 k) ≤
        periodicGaussianResolventMass a := by
      unfold periodicGaussianResolventMass
      exact (summable_heatSecondDerivativeH3Kernel ha).tsum_le_tsum
        (heatSecondDerivativeH3KernelTerm_le_resolvent a)
        (summable_periodicGaussianResolvent ha)
    _ ≤ (8 * gaussianLineUnitMass ^ 3) *
        (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) *
          (2 * a) ^ (-1 / 2 : ℝ) := periodicGaussianResolventMass_le a ha haLocal

/-! ## Weighted coefficient receivers -/

/-- Absolute Fourier coefficient mass of the Laplace-symbol second derivative after heat time
`a`.  This is an honest complete coefficient receiver, not a completion wrapper. -/
def heatSecondDerivativeCoefficientMass
    (order : ℕ) (a : ℝ) (state : PeriodicWeightedSobolev order) : ℝ :=
  ∑' k : SpatialFrequency,
    torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
      ‖weightedSobolevRawCoefficients order state k‖

private theorem norm_heatSecondDerivativeKernelTerm_sq
    (order : ℕ) (a : ℝ) (k : SpatialFrequency) :
    ‖torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
        Real.sqrt (periodicSobolevWeight order k)‖ ^ 2 =
      torusStokesEigenvalue k ^ 2 *
        Real.exp (-(2 * a) * torusStokesEigenvalue k) /
          periodicSobolevWeight order k := by
  have hweight : 0 ≤ periodicSobolevWeight order k :=
    periodicSobolevWeight_nonneg order k
  have hnonneg : 0 ≤ torusStokesEigenvalue k *
      Real.exp (-a * torusStokesEigenvalue k) /
        Real.sqrt (periodicSobolevWeight order k) :=
    div_nonneg (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le)
      (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, div_pow, mul_pow,
    Real.sq_sqrt hweight]
  have hexpSq : Real.exp (-a * torusStokesEigenvalue k) ^ 2 =
      Real.exp (-(2 * a) * torusStokesEigenvalue k) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexpSq]

/-- The sharp real `H3` heat kernel as an actual ℓ2 population. -/
def heatSecondDerivativeH3Kernel (a : ℝ) (ha : 0 < a) : PeriodicRealFourierL2 :=
  ⟨fun k ↦ torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 3 k), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two, norm_heatSecondDerivativeKernelTerm_sq] using
      summable_heatSecondDerivativeH3Kernel ha⟩

/-- The sharp real `H2` heat kernel as an actual ℓ2 population. -/
def heatSecondDerivativeH2Kernel (a : ℝ) (ha : 0 < a) : PeriodicRealFourierL2 :=
  ⟨fun k ↦ torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 2 k), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two, norm_heatSecondDerivativeKernelTerm_sq] using
      summable_heatSecondDerivativeH2Kernel ha⟩

theorem norm_heatSecondDerivativeH3Kernel_sq (a : ℝ) (ha : 0 < a) :
    ‖heatSecondDerivativeH3Kernel a ha‖ ^ 2 =
      heatSecondDerivativeH3KernelMass a := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (heatSecondDerivativeH3Kernel a ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    heatSecondDerivativeH3Kernel, heatSecondDerivativeH3KernelMass,
    norm_heatSecondDerivativeKernelTerm_sq] using hnorm

theorem norm_heatSecondDerivativeH2Kernel_sq (a : ℝ) (ha : 0 < a) :
    ‖heatSecondDerivativeH2Kernel a ha‖ ^ 2 =
      heatSecondDerivativeH2KernelMass a := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (heatSecondDerivativeH2Kernel a ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    heatSecondDerivativeH2Kernel, heatSecondDerivativeH2KernelMass,
    norm_heatSecondDerivativeKernelTerm_sq] using hnorm

private theorem heatKernel_mul_stateNorm_eq_receiverTerm
    (order : ℕ) (a : ℝ) (state : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    ‖torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
        Real.sqrt (periodicSobolevWeight order k)‖ * ‖state k‖ =
      torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients order state k‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight order k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos order k)
  have hkernelNonneg : 0 ≤ torusStokesEigenvalue k *
      Real.exp (-a * torusStokesEigenvalue k) /
        Real.sqrt (periodicSobolevWeight order k) :=
    div_nonneg (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le)
      hsqrt.le
  rw [weightedSobolevRawCoefficients_apply, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg hkernelNonneg]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  field_simp

/-- Taking pointwise complex norms retains the exact ℓ2 norm of a weighted state. -/
def weightedStateAbsolute (order : ℕ) (state : PeriodicWeightedSobolev order) :
    PeriodicRealFourierL2 :=
  ⟨fun k ↦ ‖state k‖, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have h := (lp.memℓp state).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h⟩

theorem norm_weightedStateAbsolute
    (order : ℕ) (state : PeriodicWeightedSobolev order) :
    ‖weightedStateAbsolute order state‖ = ‖state‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weightedStateAbsolute order state)
  have hright := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) state
  norm_num only [ENNReal.toReal_ofNat] at hleft hright
  simp only [Real.rpow_two] at hleft hright
  have hsquares : ‖weightedStateAbsolute order state‖ ^ 2 = ‖state‖ ^ 2 := by
    calc
      ‖weightedStateAbsolute order state‖ ^ 2 =
          ∑' k : SpatialFrequency, ‖weightedStateAbsolute order state k‖ ^ 2 := hleft
      _ = ∑' k : SpatialFrequency, ‖state k‖ ^ 2 := by
        apply tsum_congr
        intro k
        simp only [weightedStateAbsolute, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
      _ = ‖state‖ ^ 2 := hright.symm
  nlinarith [norm_nonneg (weightedStateAbsolute order state), norm_nonneg state]

private theorem coefficientMass_le_kernelNorm_mul
    (order : ℕ) (a : ℝ) (state : PeriodicWeightedSobolev order)
    (kernel : PeriodicRealFourierL2)
    (hkernel : ∀ k : SpatialFrequency,
      kernel k = torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
        Real.sqrt (periodicSobolevWeight order k)) :
    heatSecondDerivativeCoefficientMass order a state ≤ ‖kernel‖ * ‖state‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hcs := lp.tsum_mul_le_mul_norm' hholder kernel
    (weightedStateAbsolute order state)
  calc
    heatSecondDerivativeCoefficientMass order a state =
        ∑' k : SpatialFrequency, ‖kernel k‖ *
          ‖weightedStateAbsolute order state k‖ := by
      unfold heatSecondDerivativeCoefficientMass
      apply tsum_congr
      intro k
      rw [hkernel k]
      rw [show ‖weightedStateAbsolute order state k‖ = ‖state k‖ by
        simp only [weightedStateAbsolute, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]]
      exact (heatKernel_mul_stateNorm_eq_receiverTerm order a state k).symm
    _ ≤ ‖kernel‖ * ‖weightedStateAbsolute order state‖ := hcs
    _ = ‖kernel‖ * ‖state‖ := by rw [norm_weightedStateAbsolute]

/-- Fixed constant in the sharp weighted `H3` second-derivative heat estimate. -/
def sharpHeatSecondDerivativeH3Constant : ℝ :=
  Real.sqrt ((8 * gaussianLineUnitMass ^ 3) *
    (1 + 2 * Real.pi ^ (3 / 2 : ℝ)))

/-- Fixed constant in the sharp weighted `H2` second-derivative heat estimate. -/
def sharpHeatSecondDerivativeH2Constant : ℝ :=
  Real.sqrt (8 * gaussianLineUnitMass ^ 3 *
    (1 + Real.pi ^ (3 / 2 : ℝ)))

private theorem sqrt_mul_rpow_neg_half
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 < x) :
    Real.sqrt (C * x ^ (-1 / 2 : ℝ)) =
      Real.sqrt C * x ^ (-1 / 4 : ℝ) := by
  rw [Real.sqrt_mul hC]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1
  norm_num

private theorem sqrt_mul_rpow_neg_three_halves
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 < x) :
    Real.sqrt (C * x ^ (-3 / 2 : ℝ)) =
      Real.sqrt C * x ^ (-3 / 4 : ℝ) := by
  rw [Real.sqrt_mul hC]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1
  norm_num

/-- **Sharp weighted H3 heat edge.**  The complete absolute coefficient mass of the
Laplace-symbol second spatial derivative is controlled by the weighted `H3` state with the
three-dimensional `a^(-1/4)` rate. -/
theorem heatSecondDerivativeCoefficientMass_from_weightedH3_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1)
    (state : PeriodicWeightedSobolev 3) :
    heatSecondDerivativeCoefficientMass 3 a state ≤
      sharpHeatSecondDerivativeH3Constant * (2 * a) ^ (-1 / 4 : ℝ) *
        ‖state‖ := by
  have hcs := coefficientMass_le_kernelNorm_mul 3 a state
    (heatSecondDerivativeH3Kernel a ha) (fun _ ↦ rfl)
  have hC : 0 ≤ (8 * gaussianLineUnitMass ^ 3) *
      (1 + 2 * Real.pi ^ (3 / 2 : ℝ)) := by
    have hpi : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3))
      (by linarith)
  have hkernel : ‖heatSecondDerivativeH3Kernel a ha‖ ≤
      sharpHeatSecondDerivativeH3Constant * (2 * a) ^ (-1 / 4 : ℝ) := by
    calc
      ‖heatSecondDerivativeH3Kernel a ha‖ =
          Real.sqrt (‖heatSecondDerivativeH3Kernel a ha‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt (heatSecondDerivativeH3KernelMass a) := by
        rw [norm_heatSecondDerivativeH3Kernel_sq]
      _ ≤ Real.sqrt (((8 * gaussianLineUnitMass ^ 3) *
          (1 + 2 * Real.pi ^ (3 / 2 : ℝ))) *
            (2 * a) ^ (-1 / 2 : ℝ)) :=
        Real.sqrt_le_sqrt (heatSecondDerivativeH3KernelMass_le a ha haLocal)
      _ = sharpHeatSecondDerivativeH3Constant *
          (2 * a) ^ (-1 / 4 : ℝ) := by
        exact sqrt_mul_rpow_neg_half _ _ hC (mul_pos (by norm_num) ha)
  calc
    heatSecondDerivativeCoefficientMass 3 a state ≤
        ‖heatSecondDerivativeH3Kernel a ha‖ * ‖state‖ := hcs
    _ ≤ (sharpHeatSecondDerivativeH3Constant *
        (2 * a) ^ (-1 / 4 : ℝ)) * ‖state‖ :=
      mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)
    _ = sharpHeatSecondDerivativeH3Constant * (2 * a) ^ (-1 / 4 : ℝ) *
        ‖state‖ := rfl

/-- **Sharp weighted H2 Duhamel edge.**  The complete absolute coefficient mass of the
Laplace-symbol second spatial derivative is controlled by a weighted `H2` source with the
integrable three-dimensional `a^(-3/4)` rate. -/
theorem heatSecondDerivativeCoefficientMass_from_weightedH2_le
    (a : ℝ) (ha : 0 < a) (haLocal : 2 * a ≤ 1)
    (source : PeriodicWeightedSobolev 2) :
    heatSecondDerivativeCoefficientMass 2 a source ≤
      sharpHeatSecondDerivativeH2Constant * (2 * a) ^ (-3 / 4 : ℝ) *
        ‖source‖ := by
  have hcs := coefficientMass_le_kernelNorm_mul 2 a source
    (heatSecondDerivativeH2Kernel a ha) (fun _ ↦ rfl)
  have hC : 0 ≤ 8 * gaussianLineUnitMass ^ 3 *
      (1 + Real.pi ^ (3 / 2 : ℝ)) := by
    have hpi : 0 ≤ Real.pi ^ (3 / 2 : ℝ) := Real.rpow_nonneg Real.pi_pos.le _
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg gaussianLineUnitMass_nonneg 3))
      (by linarith)
  have hkernel : ‖heatSecondDerivativeH2Kernel a ha‖ ≤
      sharpHeatSecondDerivativeH2Constant * (2 * a) ^ (-3 / 4 : ℝ) := by
    calc
      ‖heatSecondDerivativeH2Kernel a ha‖ =
          Real.sqrt (‖heatSecondDerivativeH2Kernel a ha‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt (heatSecondDerivativeH2KernelMass a) := by
        rw [norm_heatSecondDerivativeH2Kernel_sq]
      _ ≤ Real.sqrt ((8 * gaussianLineUnitMass ^ 3 *
          (1 + Real.pi ^ (3 / 2 : ℝ))) *
            (2 * a) ^ (-3 / 2 : ℝ)) :=
        Real.sqrt_le_sqrt (heatSecondDerivativeH2KernelMass_le a ha haLocal)
      _ = sharpHeatSecondDerivativeH2Constant *
          (2 * a) ^ (-3 / 4 : ℝ) := by
        exact sqrt_mul_rpow_neg_three_halves _ _ hC (mul_pos (by norm_num) ha)
  calc
    heatSecondDerivativeCoefficientMass 2 a source ≤
        ‖heatSecondDerivativeH2Kernel a ha‖ * ‖source‖ := hcs
    _ ≤ (sharpHeatSecondDerivativeH2Constant *
        (2 * a) ^ (-3 / 4 : ℝ)) * ‖source‖ :=
      mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)
    _ = sharpHeatSecondDerivativeH2Constant * (2 * a) ^ (-3 / 4 : ℝ) *
        ‖source‖ := rfl

/-- The sharp `H3` time singularity is locally integrable at the Duhamel endpoint. -/
theorem integrableOn_sharpHeatSecondDerivativeH3_timeKernel
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun a : ℝ ↦ (2 * a) ^ (-1 / 4 : ℝ)) (Set.Ioo 0 T) := by
  have hbase : IntegrableOn (fun a : ℝ ↦ a ^ (-1 / 4 : ℝ)) (Set.Ioo 0 T) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  have hscaled := hbase.const_mul (2 ^ (-1 / 4 : ℝ))
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
  intro a ha
  dsimp
  exact (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.1.le).symm

/-- The sharp `H2` source singularity `a^(-3/4)` is locally integrable, so it is the
coefficient-level Duhamel kernel required by the endpoint argument. -/
theorem integrableOn_sharpHeatSecondDerivativeH2_timeKernel
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun a : ℝ ↦ (2 * a) ^ (-3 / 4 : ℝ)) (Set.Ioo 0 T) := by
  have hbase : IntegrableOn (fun a : ℝ ↦ a ^ (-3 / 4 : ℝ)) (Set.Ioo 0 T) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  have hscaled := hbase.const_mul (2 ^ (-3 / 4 : ℝ))
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
  intro a ha
  dsimp
  exact (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.1.le).symm

/-! ## Axiom audit -/

#print axioms heatSecondDerivativeH3KernelMass_le
#print axioms heatSecondDerivativeH2KernelMass_le
#print axioms heatSecondDerivativeCoefficientMass_from_weightedH3_le
#print axioms heatSecondDerivativeCoefficientMass_from_weightedH2_le
#print axioms integrableOn_sharpHeatSecondDerivativeH2_timeKernel

end Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
