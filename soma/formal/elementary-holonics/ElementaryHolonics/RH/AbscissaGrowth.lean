import ElementaryHolonics.RH.GrowthDefect
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# From pointwise growth to translated-circle growth

`GrowthDefect.TheAbscissaGrowthOfXi` is the correctly shaped Jensen input: a circle about `c`
must pay for the abscissae reached by both its centre and its radius.  The estimates already in
`Growth`, `GammaBound`, and `MellinHorizon` are pointwise.  This file owns the missing receiver
passage from a pointwise order-one envelope to the boundary average.

No placement statement about zeros is used or obtained here.  The consequence is an honest
weighted Jensen count through `GrowthDefect.theCountIsBoundedGivenTheAbscissaGrowth`.
-/

noncomputable section

namespace Soma.Holonics.RH.AbscissaGrowth

open Complex Metric Set Real MeromorphicOn
open Soma.Holonics.RH.Jensen Soma.Holonics.RH.GrowthDefect
open Soma.Holonics.RH.GammaBound
open Soma.Holonics.RH.Growth Soma.Holonics.RH.MellinHorizon
open Soma.Holonics.RH.WeightSymmetry

/-- The pointwise form of order-one growth, with a positive shift keeping the logarithmic
envelope away from its singular endpoint. -/
def PointwiseAbscissaGrowthOfXi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
    Real.log ‖completedRiemannZeta₀ z‖
      ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3)

/-- `x log x` is monotone once both arguments are at least one.  This elementary comparison is
the scalar hinge in transporting a pointwise radial envelope to a larger receiver circle. -/
theorem mulLog_mono_on_one {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * Real.log x ≤ y * Real.log y := by
  have hy : 1 ≤ y := hx.trans hxy
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log (by positivity) hxy
  calc
    x * Real.log x ≤ y * Real.log x := mul_le_mul_of_nonneg_right hxy hlogx
    _ ≤ y * Real.log y := mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Increasing the shifted radius by one costs at most a factor four once the original radius is
at least two.  The loose constant keeps reflection and translated-circle transport explicit and
division-free. -/
theorem addOne_mulLog_le_four {x : ℝ} (hx : 2 ≤ x) :
    (x + 1) * Real.log (x + 1) ≤ 4 * (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxx : x + 1 ≤ 2 * x := by linarith
  have hlog2x : Real.log (x + 1) ≤ Real.log (2 * x) :=
    Real.log_le_log (by linarith) hxx
  have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
  have hlog2 : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlogbound : Real.log (x + 1) ≤ 2 * Real.log x := by
    rw [hlogmul] at hlog2x
    linarith
  have hlognonneg : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have htwolognonneg : 0 ≤ 2 * Real.log x :=
    mul_nonneg (by norm_num) (Real.log_nonneg hx1)
  calc
    (x + 1) * Real.log (x + 1)
        ≤ (2 * x) * (2 * Real.log x) :=
          mul_le_mul hxx hlogbound hlognonneg (by positivity)
    _ = 4 * (x * Real.log x) := by ring

/-- A constant plus an exponential times a real Gamma factor has an order-one logarithmic
envelope.  The proof deliberately uses only `Γ(x) ≤ ⌈x⌉! ≤ ⌈x⌉^⌈x⌉`; no asymptotic Stirling
theorem is hidden in the statement. -/
theorem gammaEnvelope_isOrderOne {W C p : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      Real.log (W + C * (1 / p) ^ x * Real.Gamma x)
        ≤ K * (x + 2) * Real.log (x + 2) := by
  let q : ℝ := max 1 (1 / p)
  let D : ℝ := max 1 (max W C)
  let A : ℝ := Real.log 2 + Real.log D + Real.log q
  let K : ℝ := 2 * A + 1
  have hq : 1 ≤ q := le_max_left _ _
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hWD : W ≤ D := le_trans (le_max_left W C) (le_max_right 1 (max W C))
  have hCD : C ≤ D := le_trans (le_max_right W C) (le_max_right 1 (max W C))
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2),
      Real.log_nonneg hD, Real.log_nonneg hq]
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K, hK, fun x hx => ?_⟩
  let n : ℕ := ⌈x⌉₊
  have hn : 2 ≤ n := by
    have : (2 : ℝ) ≤ (n : ℝ) := le_trans hx (Nat.le_ceil x)
    exact_mod_cast this
  have hnx : x ≤ (n : ℝ) := Nat.le_ceil x
  have hnx' : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hfac : Real.Gamma x ≤ (Nat.factorial n : ℝ) :=
    theRealGammaIsBoundedByAFactorial hx
  have hfacpow : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast theFactorialIsBoundedByThePower n
  have hgamma : Real.Gamma x ≤ (n : ℝ) ^ n := hfac.trans hfacpow
  have hbasepos : 0 < 1 / p := one_div_pos.mpr hp
  have hbase : 1 / p ≤ q := le_max_right _ _
  have hrpow : (1 / p) ^ x ≤ q ^ x :=
    Real.rpow_le_rpow hbasepos.le hbase (by linarith)
  have hqpow : 1 ≤ q ^ x := Real.one_le_rpow hq (by linarith)
  have hnpow : 1 ≤ (n : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  have hcommon_pos : 0 < D * q ^ x * (n : ℝ) ^ n := by positivity
  have hWterm : W ≤ D * q ^ x * (n : ℝ) ^ n := by
    calc
      W ≤ D := hWD
      _ ≤ D * q ^ x := by nlinarith [le_trans zero_le_one hD, hqpow]
      _ ≤ D * q ^ x * (n : ℝ) ^ n := by
        calc
          D * q ^ x = D * q ^ x * 1 := by ring
          _ ≤ D * q ^ x * (n : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hnpow
              (mul_nonneg (le_trans zero_le_one hD) (Real.rpow_nonneg hqpos.le x))
  have hCterm : C * (1 / p) ^ x * Real.Gamma x
      ≤ D * q ^ x * (n : ℝ) ^ n := by
    have hCr : C * (1 / p) ^ x ≤ D * q ^ x :=
      mul_le_mul hCD hrpow (Real.rpow_nonneg hbasepos.le x) (le_trans zero_le_one hD)
    calc
      C * (1 / p) ^ x * Real.Gamma x
          ≤ D * q ^ x * Real.Gamma x :=
            mul_le_mul_of_nonneg_right hCr (Real.Gamma_nonneg_of_nonneg (by linarith))
      _ ≤ D * q ^ x * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hgamma
          (mul_nonneg (le_trans zero_le_one hD) (Real.rpow_nonneg hqpos.le x))
  have henvelope : W + C * (1 / p) ^ x * Real.Gamma x
      ≤ 2 * (D * q ^ x * (n : ℝ) ^ n) := by linarith
  have hT : 4 ≤ x + 2 := by linarith
  have hlogT : 1 ≤ Real.log (x + 2) := by
    exact (Real.le_log_iff_exp_le (by linarith : 0 < x + 2)).2
      (Real.exp_one_lt_three.le.trans (by linarith))
  have hnT : (n : ℝ) ≤ x + 2 := by linarith
  have hlogn : Real.log (n : ℝ) ≤ Real.log (x + 2) :=
    Real.log_le_log (by positivity) hnT
  have hmuln : (n : ℝ) * Real.log (n : ℝ)
      ≤ (x + 2) * Real.log (x + 2) :=
    mulLog_mono_on_one (by exact_mod_cast (show 1 ≤ n by omega)) hnT
  have hlogenv :
      Real.log (2 * (D * q ^ x * (n : ℝ) ^ n))
        = Real.log 2 + Real.log D + x * Real.log q
            + (n : ℝ) * Real.log (n : ℝ) := by
    rw [show 2 * (D * q ^ x * (n : ℝ) ^ n)
        = ((2 * D) * q ^ x) * (n : ℝ) ^ n by ring]
    rw [Real.log_mul (by positivity : (2 * D) * q ^ x ≠ 0) (by positivity),
      Real.log_mul (by positivity : 2 * D ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDpos.ne',
      Real.log_rpow hqpos, Real.log_pow]
  have hy0 : 0 ≤ W + C * (1 / p) ^ x * Real.Gamma x :=
    add_nonneg hW (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hbasepos.le x))
      (Real.Gamma_nonneg_of_nonneg (by linarith)))
  rcases eq_or_lt_of_le hy0 with hzero | hpositive
  · rw [← hzero, Real.log_zero]
    exact mul_nonneg (mul_nonneg hK.le (by linarith)) (Real.log_nonneg (by linarith))
  · calc
      Real.log (W + C * (1 / p) ^ x * Real.Gamma x)
          ≤ Real.log (2 * (D * q ^ x * (n : ℝ) ^ n)) :=
            Real.log_le_log hpositive henvelope
      _ = Real.log 2 + Real.log D + x * Real.log q
            + (n : ℝ) * Real.log (n : ℝ) := hlogenv
      _ ≤ K * (x + 2) * Real.log (x + 2) := by
        have hconst : Real.log 2 + Real.log D + Real.log q = A := rfl
        have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
        have hxT : x ≤ x + 2 := by linarith
        have h1 : Real.log 2 + Real.log D + x * Real.log q
              ≤ A * (x + 2) := by
          rw [← hconst]
          nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2),
            Real.log_nonneg hD, hlogq]
        have hTnonneg : 0 ≤ x + 2 := by linarith
        have hBnonneg : 0 ≤ (x + 2) * Real.log (x + 2) :=
          mul_nonneg hTnonneg (le_trans zero_le_one hlogT)
        have hTB : x + 2 ≤ (x + 2) * Real.log (x + 2) := by
          nlinarith
        have hAB : A * (x + 2) ≤ A * ((x + 2) * Real.log (x + 2)) :=
          mul_le_mul_of_nonneg_left hTB hA
        dsimp [K]
        calc
          Real.log 2 + Real.log D + x * Real.log q
                + (n : ℝ) * Real.log (n : ℝ)
              ≤ A * (x + 2) + (x + 2) * Real.log (x + 2) :=
                add_le_add h1 hmuln
          _ ≤ A * ((x + 2) * Real.log (x + 2))
                + (x + 2) * Real.log (x + 2) := add_le_add hAB le_rfl
          _ = (A + 1) * ((x + 2) * Real.log (x + 2)) := by ring
          _ ≤ (2 * A + 1) * ((x + 2) * Real.log (x + 2)) := by
                exact mul_le_mul_of_nonneg_right (by linarith) hBnonneg
          _ = (2 * A + 1) * (x + 2) * Real.log (x + 2) := by ring

/-- **THE CORRECTED POINTWISE GROWTH HOLDS.**  The right half-plane is the Gamma envelope just
proved; a fixed middle strip is uniformly bounded by the Mellin representation; the left
half-plane returns through `Λ₀(1-z)=Λ₀(z)`.  The shift by three is exactly the one unit spent by
that reflection. -/
theorem thePointwiseAbscissaGrowthHolds : PointwiseAbscissaGrowthOfXi := by
  obtain ⟨W, C, p, hp, hC, hW, hgamma⟩ := theCompletedZetaHasGammaGrowth
  obtain ⟨K, hK, henv⟩ := gammaEnvelope_isOrderOne hp hC hW
  let B : ℝ :=
    (mellinWeight ker ((-3 : ℝ) / 2) + mellinWeight ker ((4 : ℝ) / 2)) / 2
  let M : ℝ := max 1 B
  let J : ℝ := max 1 (Real.log M)
  let C₀ : ℝ := max K J
  have hM : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hJ : 1 ≤ J := le_max_left _ _
  have hJpos : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hlogMJ : Real.log M ≤ J := le_max_right _ _
  have hKC : K ≤ C₀ := le_max_left _ _
  have hJC : J ≤ C₀ := le_max_right _ _
  have hC₀ : 0 < C₀ := hK.trans_le hKC
  have hstrip : ∀ z : ℂ, -3 ≤ z.re → z.re ≤ 4 → ‖completedRiemannZeta₀ z‖ ≤ B := by
    intro z hz₁ hz₂
    dsimp [B]
    exact theCompletedZetaIsBoundedOnAStrip (a := -3) (b := 4) hz₁ hz₂
  have hright : ∀ z : ℂ, 4 ≤ z.re →
      Real.log ‖completedRiemannZeta₀ z‖
        ≤ K * (‖z‖ + 2) * Real.log (‖z‖ + 2) := by
    intro z hz
    have hx : 2 ≤ z.re / 2 := by linarith
    have hg := hgamma z (by linarith)
    have he := henv (z.re / 2) hx
    rcases eq_or_ne (completedRiemannZeta₀ z) 0 with hz0 | hz0
    · rw [hz0, norm_zero, Real.log_zero]
      have hT : 1 ≤ ‖z‖ + 2 := by nlinarith [norm_nonneg z]
      exact mul_nonneg (mul_nonneg hK.le (by linarith)) (Real.log_nonneg hT)
    have hlog : Real.log ‖completedRiemannZeta₀ z‖
        ≤ Real.log (W + C * (1 / p) ^ (z.re / 2) * Real.Gamma (z.re / 2)) := by
      exact Real.log_le_log (norm_pos_iff.mpr hz0) hg
    have hreach : z.re / 2 + 2 ≤ ‖z‖ + 2 := by
      nlinarith [Complex.re_le_norm z]
    have hmono : (z.re / 2 + 2) * Real.log (z.re / 2 + 2)
        ≤ (‖z‖ + 2) * Real.log (‖z‖ + 2) :=
      mulLog_mono_on_one (by linarith) hreach
    exact hlog.trans (he.trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmono hK.le))
  refine ⟨C₀, hC₀, fun z => ?_⟩
  rcases lt_or_ge z.re (-3) with hzleft | hznotleft
  · let w : ℂ := 1 - z
    have hwre : 4 ≤ w.re := by
      change 4 ≤ 1 - z.re
      linarith
    have hw := hright w hwre
    have hvalue : completedRiemannZeta₀ w = completedRiemannZeta₀ z := by
      dsimp [w]
      exact completedRiemannZeta₀_one_sub z
    rw [hvalue] at hw
    have hwnorm : ‖w‖ ≤ 1 + ‖z‖ := by
      dsimp [w]
      calc
        ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ := by simp
    have hreach : ‖w‖ + 2 ≤ ‖z‖ + 3 := by linarith
    have hmono : (‖w‖ + 2) * Real.log (‖w‖ + 2)
        ≤ (‖z‖ + 3) * Real.log (‖z‖ + 3) :=
      mulLog_mono_on_one (by nlinarith [norm_nonneg w]) hreach
    have hF : 0 ≤ (‖z‖ + 3) * Real.log (‖z‖ + 3) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [norm_nonneg z]))
    calc
      Real.log ‖completedRiemannZeta₀ z‖
          ≤ K * (‖w‖ + 2) * Real.log (‖w‖ + 2) := hw
      _ ≤ K * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmono hK.le
      _ ≤ C₀ * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) :=
        mul_le_mul_of_nonneg_right hKC hF
      _ = C₀ * (‖z‖ + 3) * Real.log (‖z‖ + 3) := by ring
  · rcases le_total z.re 4 with hzmid | hzright
    · have hnB := hstrip z hznotleft hzmid
      have hnM : ‖completedRiemannZeta₀ z‖ ≤ M := hnB.trans (le_max_right 1 B)
      have hlog : Real.log ‖completedRiemannZeta₀ z‖ ≤ Real.log M := by
        rcases eq_or_ne (completedRiemannZeta₀ z) 0 with hz0 | hz0
        · rw [hz0, norm_zero, Real.log_zero]
          exact Real.log_nonneg hM
        · exact Real.log_le_log (norm_pos_iff.mpr hz0) hnM
      have hlogT : 1 ≤ Real.log (‖z‖ + 3) := by
        exact (Real.le_log_iff_exp_le (by positivity : 0 < ‖z‖ + 3)).2
          (Real.exp_one_lt_three.le.trans (by nlinarith [norm_nonneg z]))
      have hF : 1 ≤ (‖z‖ + 3) * Real.log (‖z‖ + 3) := by
        nlinarith [norm_nonneg z]
      calc
        Real.log ‖completedRiemannZeta₀ z‖ ≤ Real.log M := hlog
        _ ≤ J := hlogMJ
        _ ≤ C₀ := hJC
        _ ≤ C₀ * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) := by
          nlinarith [hC₀.le]
        _ = C₀ * (‖z‖ + 3) * Real.log (‖z‖ + 3) := by ring
    · have hr := hright z hzright
      have hreach : ‖z‖ + 2 ≤ ‖z‖ + 3 := by linarith
      have hmono : (‖z‖ + 2) * Real.log (‖z‖ + 2)
          ≤ (‖z‖ + 3) * Real.log (‖z‖ + 3) :=
        mulLog_mono_on_one (by nlinarith [norm_nonneg z]) hreach
      have hF : 0 ≤ (‖z‖ + 3) * Real.log (‖z‖ + 3) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [norm_nonneg z]))
      calc
        Real.log ‖completedRiemannZeta₀ z‖
            ≤ K * (‖z‖ + 2) * Real.log (‖z‖ + 2) := hr
        _ ≤ K * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmono hK.le
        _ ≤ C₀ * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) :=
          mul_le_mul_of_nonneg_right hKC hF
        _ = C₀ * (‖z‖ + 3) * Real.log (‖z‖ + 3) := by ring

/-- A point on the circle about `c` of radius `R ≥ 0` has norm at most `‖c‖ + R`. -/
theorem norm_le_center_add_radius {c z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ sphere c |R|) :
    ‖z‖ ≤ ‖c‖ + R := by
  have hdist : dist z c = R := by
    have := (mem_sphere.mp hz)
    simpa [abs_of_nonneg hR] using this
  calc
    ‖z‖ = ‖(z - c) + c‖ := by ring_nf
    _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    _ = ‖c‖ + R := by rw [← Complex.dist_eq, hdist, add_comm]

/-- **THE POINTWISE RECEIVER DESCENDS TO THE CORRECTED JENSEN RECEIVER.**  A translated circle
never reaches beyond `‖c‖ + R`; monotonicity of `x log x` then makes one constant control its
complete boundary average. -/
theorem thePointwiseGrowthGivesTheAbscissaGrowth
    (hP : PointwiseAbscissaGrowthOfXi) : TheAbscissaGrowthOfXi := by
  obtain ⟨C, hC, hpoint⟩ := hP
  refine ⟨4 * C, mul_pos (by norm_num) hC, fun c R hR => ?_⟩
  apply circleAverage_mono_on_of_le_circle
  · exact circleIntegrable_log_norm_meromorphicOn
      (theXiIsMeromorphicOn (sphere c |R|))
  intro z hz
  have hR0 : 0 ≤ R := by linarith
  have hnorm : ‖z‖ + 3 ≤ (‖c‖ + R + 2) + 1 := by
    linarith [norm_le_center_add_radius hR0 hz]
  have hmono₁ : (‖z‖ + 3) * Real.log (‖z‖ + 3)
      ≤ ((‖c‖ + R + 2) + 1) * Real.log ((‖c‖ + R + 2) + 1) :=
    mulLog_mono_on_one (by nlinarith [norm_nonneg z]) hnorm
  have hmono₂ : ((‖c‖ + R + 2) + 1) * Real.log ((‖c‖ + R + 2) + 1)
      ≤ 4 * ((‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)) :=
    addOne_mulLog_le_four (by nlinarith [norm_nonneg c])
  exact (hpoint z).trans (by
    have := mul_le_mul_of_nonneg_left (hmono₁.trans hmono₂) hC.le
    nlinarith)

/-- Consequently the corrected weighted Jensen count follows from the pointwise envelope, with
no additional analytic hypothesis. -/
theorem theWeightedCountFollowsFromPointwiseGrowth
    (hP : PointwiseAbscissaGrowthOfXi) {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : completedRiemannZeta₀ c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)
            - Real.log ‖completedRiemannZeta₀ c‖ :=
  theCountIsBoundedGivenTheAbscissaGrowth
    (thePointwiseGrowthGivesTheAbscissaGrowth hP) hR hc

/-- **THE CORRECTED ABSCISSA GROWTH INPUT IS DISCHARGED.** -/
theorem theAbscissaGrowthOfXiHolds : TheAbscissaGrowthOfXi :=
  thePointwiseGrowthGivesTheAbscissaGrowth thePointwiseAbscissaGrowthHolds

/-- Hence every translated disc of radius at least one, centred away from a zero, has the corrected
weighted zero-count bound unconditionally. -/
theorem theCorrectedWeightedZeroCount {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : completedRiemannZeta₀ c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)
            - Real.log ‖completedRiemannZeta₀ c‖ :=
  theCountIsBoundedGivenTheAbscissaGrowth theAbscissaGrowthOfXiHolds hR hc

end Soma.Holonics.RH.AbscissaGrowth
