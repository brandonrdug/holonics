import ElementaryHolonics.Millennium.FamilyTheta
import ElementaryHolonics.Millennium.FamilyThetaOdd
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.Tactic

/-!
# FamilyDuplication: the duplication identity at every split prime

**The theta transformation law of the congruent-number family, as finite arithmetic.**
At five, the fifty weighted `sinKernel`–`cosKernel` products at scale `y` equal `−800`
times the fifty weighted `oddKernel`–`evenKernel` products at scale `800y`, and the
sign `−1 = χ₅(2)` was deposited by the lattice fold.  That computation was never about
five.  This file proves it at **every** prime `p ≡ 1 (mod 4)`:

* **`theFamilyDuplicationIdentity`** — the `2p²` weighted `sinKernel`–`cosKernel`
  products at scale `y` equal `32p²·χ_p(2)` times the `2p²` weighted
  `oddKernel`–`evenKernel` products at scale `32p²y`.  The phases collapse through
  the family eigen-identity (`FamilyTheta`), the lattice folds exactly as at level
  one, and the fold deposits the **family sign `χ_p(2)`** — the root number dial of
  the congruent-number family, returned by finite arithmetic with the modulus a
  parameter.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyDuplication

open Real HurwitzZeta Complex
open Soma.Holonics.Millennium.FamilyTheta

/-! ## 1. The family character on the integers -/

/-- The quadratic character mod `p`, read on the integers. -/
def XP (p : ℕ) [Fact p.Prime] (k : ℤ) : ℤ :=
  quadraticChar (ZMod p) ((k : ZMod p))

lemma XP_congr (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : a ≡ b [ZMOD (p : ℤ)]) :
    XP p a = XP p b := by
  unfold XP
  congr 1
  rwa [ZMod.intCast_eq_intCast_iff']

lemma XP_mul (p : ℕ) [Fact p.Prime] (a b : ℤ) : XP p (a * b) = XP p a * XP p b := by
  unfold XP
  rw [Int.cast_mul, map_mul]

lemma XP_abs_le (p : ℕ) [Fact p.Prime] (k : ℤ) : |XP p k| ≤ 1 := by
  unfold XP
  rcases (quadraticChar_isQuadratic (ZMod p)) ((k : ZMod p)) with h | h | h <;>
    rw [h] <;> norm_num

/-- The grid weight: `χ_p((4e+1)² + 4d²)·(−1)^d`. -/
def wP (p : ℕ) [Fact p.Prime] (e d : ℕ) : ℤ :=
  XP p ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) * (-1) ^ d

private lemma norm_XP_le (p : ℕ) [Fact p.Prime] (N : ℤ) : ‖((XP p N : ℤ) : ℂ)‖ ≤ 1 := by
  have h := XP_abs_le p N
  rw [show ((XP p N : ℤ) : ℂ) = ((XP p N : ℝ) : ℂ) from by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast h

private lemma norm_oddInd_le (m : ℤ) : ‖oddInd m‖ ≤ 1 := by
  unfold oddInd
  split_ifs <;> simp

private lemma norm_quarter_phase (p : ℕ) (n : ℤ) :
    ‖cexp (π * I * (p * n) / 2)‖ = 1 := by
  rw [show (π : ℂ) * I * ((p : ℂ) * n) / 2 = ((π * p * n / 2 : ℝ) : ℂ) * I from by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-! ## 2. Summability spine (modulus-free) -/

private lemma summable_gauss_weight (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => |(n : ℝ)| * rexp (-π * c * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_oddKernel 0 hc).summable.norm
  have h0 : Summable fun n : ℤ => |(n : ℝ) + 0| * rexp (-π * ((n : ℝ) + 0) ^ 2 * c) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using h
  refine h0.congr fun n => ?_
  rw [add_zero]
  ring_nf

private lemma summable_gauss (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => rexp (-π * c * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 hc).summable
  refine h.congr fun n => ?_
  rw [add_zero]
  ring_nf

set_option maxHeartbeats 1000000 in
private lemma summable_master {c : ℝ} (hc : 0 < c) :
    Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * rexp (-π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hw := summable_gauss_weight c hc
  have hg := summable_gauss c hc
  have h1 : Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| * rexp (-π * c * (p.1 : ℝ) ^ 2)) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hw.mul_of_nonneg hg (Pi.le_def.mpr fun n => by positivity)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  have h2 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * (|(p.2 : ℝ)| * rexp (-π * c * (p.2 : ℝ) ^ 2)) :=
    hg.mul_of_nonneg hw (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => by positivity)
  have h3 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hg.mul_of_nonneg hg (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  refine ((h1.add h2).add h3).congr fun p => ?_
  rw [show -π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      = -π * c * (p.1 : ℝ) ^ 2 + -π * c * (p.2 : ℝ) ^ 2 from by ring, Real.exp_add]
  ring

/-- The pre-fold Gaussian envelope. -/
private def envP (y : ℝ) (u v : ℤ) : ℝ := rexp (-π * y * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2))

/-- The post-fold Gaussian envelope. -/
def envF (y : ℝ) (u v : ℤ) : ℝ := rexp (-2 * π * y * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2))

private lemma envP_nonneg (y : ℝ) (u v : ℤ) : 0 ≤ envP y u v := Real.exp_nonneg _
lemma envF_nonneg (y : ℝ) (u v : ℤ) : 0 ≤ envF y u v := Real.exp_nonneg _

private lemma summable_envP {y : ℝ} (hy : 0 < y) :
    Summable fun p : ℤ × ℤ => (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envP y p.1 p.2 :=
  (summable_master hy).congr fun p => rfl

private lemma summable_envF {y : ℝ} (hy : 0 < y) :
    Summable fun p : ℤ × ℤ => (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envF y p.1 p.2 := by
  refine (summable_master (show (0 : ℝ) < 2 * y by positivity)).congr fun p => ?_
  unfold envF
  congr 2
  ring

private lemma summable_of_le_envP {y C : ℝ} (hy : 0 < y) {f : ℤ × ℤ → ℂ}
    (hb : ∀ p : ℤ × ℤ, ‖f p‖ ≤ C * ((|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envP y p.1 p.2)) :
    Summable f :=
  Summable.of_norm_bounded ((summable_envP hy).mul_left C) hb

private lemma summable_of_le_envF {y C : ℝ} (hy : 0 < y) {f : ℤ × ℤ → ℂ}
    (hb : ∀ p : ℤ × ℤ, ‖f p‖ ≤ C * ((|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envF y p.1 p.2)) :
    Summable f :=
  Summable.of_norm_bounded ((summable_envF hy).mul_left C) hb

/-! ## 3. The dual side: the grid products collapse onto one lattice family -/

/-- The `sinKernel` summand at shift `(4e+1)/(4p)`. -/
private def sinT (p : ℕ) (y : ℝ) (e : ℕ) (n : ℤ) : ℂ :=
  -I * n * cexp (2 * π * I * (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : ℂ) * n) *
    rexp (-π * n ^ 2 * y)

/-- The `cosKernel` summand at shift `d/(2p)`. -/
private def cosT (p : ℕ) (y : ℝ) (d : ℕ) (m : ℤ) : ℂ :=
  cexp (2 * π * I * (((d : ℝ) / (2 * p) : ℝ) : ℂ) * m) * rexp (-π * m ^ 2 * y)

/-- The collapsed dual family: weight `n`, quarter-turn phase, odd indicator in `m`,
the twist character, and the pre-fold envelope. -/
private def dualP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  -I * q.1 * (2 * (p : ℂ) * cexp (π * I * (p * q.1) / 2) * oddInd q.2 *
      ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℂ)) *
    ((envP y q.1 q.2 : ℝ) : ℂ)

private lemma norm_dualP_le (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) :
    ‖dualP p y q‖ ≤ (2 * p) * ((|(q.1 : ℝ)| + |(q.2 : ℝ)| + 1) * envP y q.1 q.2) := by
  obtain ⟨n, m⟩ := q
  unfold dualP
  simp only [norm_mul]
  have h1 : ‖(-I : ℂ)‖ = 1 := by simp
  have h2 : ‖((n : ℤ) : ℂ)‖ = |(n : ℝ)| := by
    rw [show ((n : ℤ) : ℂ) = ((n : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  have h3 : ‖((envP y n m : ℝ) : ℂ)‖ = envP y n m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envP_nonneg y n m)]
  have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h4p : ‖((p : ℕ) : ℂ)‖ = (p : ℝ) := by
    rw [show ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1, h2, h3, h4, h4p, norm_quarter_phase]
  have hb : |(n : ℝ)| ≤ |(n : ℝ)| + |(m : ℝ)| + 1 := by
    have := abs_nonneg (m : ℝ); linarith
  have hoi := norm_oddInd_le m
  have hch := norm_XP_le p (n ^ 2 + m ^ 2)
  have he := envP_nonneg y n m
  have hn := abs_nonneg (n : ℝ)
  have hp0 : (0 : ℝ) ≤ 2 * p := by positivity
  have h5 : 2 * (p : ℝ) * 1 * ‖oddInd m‖ * ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖
      ≤ 2 * p := by
    have hoi0 := norm_nonneg (oddInd m)
    have hch0 := norm_nonneg ((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)
    have hab : ‖oddInd m‖ * ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hoi hch0
      rw [one_mul] at h
      linarith
    calc 2 * (p : ℝ) * 1 * ‖oddInd m‖ * ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖
        = (2 * p) * (‖oddInd m‖ * ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖) := by ring
      _ ≤ (2 * p) * 1 := mul_le_mul_of_nonneg_left hab hp0
      _ = 2 * p := by ring
  calc 1 * |(n : ℝ)| * (2 * (p : ℝ) * 1 * ‖oddInd m‖ *
        ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖) * envP y n m
      = |(n : ℝ)| * envP y n m * (2 * (p : ℝ) * 1 * ‖oddInd m‖ *
          ‖((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖) := by ring
    _ ≤ |(n : ℝ)| * envP y n m * (2 * p) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg hn he)
    _ = (2 * p) * (|(n : ℝ)| * envP y n m) := by ring
    _ ≤ (2 * p) * ((|(n : ℝ)| + |(m : ℝ)| + 1) * envP y n m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb he) hp0

private lemma summable_dualP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (dualP p y) :=
  summable_of_le_envP hy (norm_dualP_le p y)

private lemma summable_sinT (p : ℕ) {y : ℝ} (hy : 0 < y) (e : ℕ) :
    Summable (sinT p y e) :=
  (HurwitzZeta.hasSum_int_sinKernel ((4 * (e : ℝ) + 1) / (4 * p)) hy).summable

private lemma summable_cosT (p : ℕ) {y : ℝ} (hy : 0 < y) (d : ℕ) :
    Summable (cosT p y d) :=
  (HurwitzZeta.hasSum_int_cosKernel ((d : ℝ) / (2 * p)) hy).summable

private lemma summable_sinT_cosT (p : ℕ) {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    Summable fun q : ℤ × ℤ => sinT p y e q.1 * cosT p y d q.2 :=
  summable_norm_iff.mp
    ((summable_norm_iff.mpr (summable_sinT p hy e)).mul_norm
      (summable_norm_iff.mpr (summable_cosT p hy d)))

/-- One kernel product expands to the lattice double sum. -/
private lemma kernel_product_eq (p : ℕ) (y : ℝ) (hy : 0 < y) (e d : ℕ) :
    ((sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
        ((cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ)
      = ∑' q : ℤ × ℤ, sinT p y e q.1 * cosT p y d q.2 :=
  (HurwitzZeta.hasSum_int_sinKernel ((4 * (e : ℝ) + 1) / (4 * p)) hy).mul_eq
    (HurwitzZeta.hasSum_int_cosKernel ((d : ℝ) / (2 * p)) hy)
    (summable_sinT_cosT p hy e d).hasSum

/-- The pointwise collapse: the grid-weighted lattice terms at one `(n, m)` return the
single `dualP` term. -/
private lemma pointwise_collapse (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (y : ℝ) (q : ℤ × ℤ) :
    ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
        ((wP p e d : ℤ) : ℂ) * (sinT p y e q.1 * cosT p y d q.2)
      = dualP p y q := by
  obtain ⟨n, m⟩ := q
  have hphase : ∀ e d : ℕ, ((wP p e d : ℤ) : ℂ) * (sinT p y e n * cosT p y d m)
      = (-I * n * (rexp (-π * n ^ 2 * y) : ℝ) * (rexp (-π * m ^ 2 * y) : ℝ)) *
          phaseTerm p n m e d := by
    intro e d
    unfold wP sinT cosT
    unfold FamilyTheta.phaseTerm
    have hA : cexp (2 * π * I * (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : ℂ) * n)
        = cexp (2 * π * I * ((4 * (e : ℤ) + 1) * n) / (4 * p)) := by
      congr 1
      push_cast
      ring
    have hB : cexp (2 * π * I * (((d : ℝ) / (2 * p) : ℝ) : ℂ) * m)
        = cexp (2 * π * I * ((d : ℤ) * m) / (2 * p)) := by
      congr 1
      push_cast
      ring
    rw [hA, hB]
    unfold XP
    push_cast
    ring
  rw [Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => hphase e d]
  have hsum : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      (-I * (n : ℂ) * ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) *
        ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)) * phaseTerm p n m e d
      = (-I * (n : ℂ) * ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) *
        ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)) *
          ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), phaseTerm p n m e d := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hsum, FamilyThetaOdd.theFamilyPhaseCollapseAtEveryOddPrime hp2 n m]
  show _ = dualP p y (n, m)
  unfold dualP
  have henv : ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) * ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)
      = ((envP y n m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    unfold envP
    norm_cast
    congr 1
    push_cast
    ring
  have hXcast : ((quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ)
      = ((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ) := by
    unfold XP
    norm_num
  rw [hXcast] at *
  linear_combination (-I * (n : ℂ) * (2 * (p : ℂ) * cexp (π * I * (p * n) / 2) *
    oddInd m * ((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ))) * henv

/-- The dual side of the duplication: the grid-weighted `sinKernel`–`cosKernel`
products equal the sum of the collapsed lattice family. -/
private lemma dual_side_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {y : ℝ}
    (hy : 0 < y) :
    ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
        ((wP p e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
      = ∑' q : ℤ × ℤ, dualP p y q := by
  have hstep : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range (2 * p),
      ((wP p e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
        = ∑' q : ℤ × ℤ, ((wP p e d : ℤ) : ℂ) * (sinT p y e q.1 * cosT p y d q.2) := by
    intro e _ d _
    rw [kernel_product_eq p y hy e d, ← tsum_mul_left]
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hstep e he d hd]
  have hswap : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      ∑' q : ℤ × ℤ, ((wP p e d : ℤ) : ℂ) * (sinT p y e q.1 * cosT p y d q.2)
      = ∑' q : ℤ × ℤ, ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
          ((wP p e d : ℤ) : ℂ) * (sinT p y e q.1 * cosT p y d q.2) := by
    rw [Summable.tsum_finsetSum fun e _ => summable_sum fun d _ =>
      ((summable_sinT_cosT p hy e d).mul_left _)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Summable.tsum_finsetSum fun d _ => (summable_sinT_cosT p hy e d).mul_left _]
  rw [hswap]
  exact tsum_congr fun q => pointwise_collapse p hp2 y q

/-! ## 4. The ladder: from the collapsed dual family to the folded classes -/

/-- The quartic sign. -/
private def sgn4 (w : ℤ) : ℂ := if w % 4 = 1 then 1 else if w % 4 = 3 then -1 else 0

/-- The doubled cosine sign. -/
def cs4 (v : ℤ) : ℂ := if v % 4 = 0 then 1 else if v % 4 = 2 then -1 else 0

private lemma norm_sgn4_le (w : ℤ) : ‖sgn4 w‖ ≤ 1 := by
  unfold sgn4; split_ifs <;> simp

private lemma norm_cs4_le (v : ℤ) : ‖cs4 v‖ ≤ 1 := by
  unfold cs4; split_ifs <;> simp

private def dualPEven (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 2 = 0 then dualP p y q else 0

private def dualPOdd (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 2 = 0 then 0 else dualP p y q

/-- After the fold: weight `u+v`, quartic sign, twist character at `2(u²+v²)`. -/
private def gLadderP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  2 * (p : ℂ) * ((q.1 + q.2 : ℤ) : ℂ) * sgn4 (q.1 + q.2) *
    ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) * ((envF y q.1 q.2 : ℝ) : ℂ)

private def gEvenP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.2 % 2 = 0 then gLadderP p y q else 0

private def gOddVP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.2 % 2 = 0 then 0 else gLadderP p y q

private def hHalfP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.2 % 2 = 0 then
    2 * (p : ℂ) * (q.1 : ℂ) * sgn4 (q.1 + q.2) *
      ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) * ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

def hPlusP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
    2 * (p : ℂ) * (q.1 : ℂ) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

private def hMinusP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if (q.1 + q.2) % 4 = 3 ∧ q.2 % 2 = 0 then
    2 * (p : ℂ) * (q.1 : ℂ) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

def hFinalP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 4 = 1 then
    8 * (p : ℂ) * (q.1 : ℂ) * cs4 q.2 * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

private def aPieceP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 4 = 1 ∧ q.2 % 4 = 0 then
    2 * (p : ℂ) * (q.1 : ℂ) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

private def bPieceP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 4 = 3 ∧ q.2 % 4 = 2 then
    2 * (p : ℂ) * (q.1 : ℂ) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

private def bMirrorP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if q.1 % 4 = 1 ∧ q.2 % 4 = 2 then
    2 * (p : ℂ) * (q.1 : ℂ) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y q.1 q.2 : ℝ) : ℂ)
  else 0

/-! ## 5. Index maps -/

private def bothOddEmb (q : ℤ × ℤ) : ℤ × ℤ := (2 * q.1 + 1, 2 * q.2 + 1)

private def foldMap (q : ℤ × ℤ) : ℤ × ℤ := (q.1 + q.2 + 1, q.1 - q.2)

def gridEmb (q : ℤ × ℤ) : ℤ × ℤ := (4 * q.1 + 1, 2 * q.2)

private lemma bothOddEmb_injective : Function.Injective bothOddEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [bothOddEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma foldMap_injective : Function.Injective foldMap := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [foldMap, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

lemma gridEmb_injective : Function.Injective gridEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [gridEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

/-! ## 6. Summability along the ladder -/

private lemma norm_weight_le (p : ℕ) (y : ℝ) (u v w : ℤ) (c : ℝ) (s : ℂ) (hs : ‖s‖ ≤ 1)
    (hc : 0 ≤ c)
    (hw : c * |(w : ℝ)| ≤ (8 * p) * (|(u : ℝ)| + |(v : ℝ)| + 1)) :
    ‖(c : ℂ) * ((w : ℤ) : ℂ) * s * ((envF y u v : ℝ) : ℂ)‖
      ≤ (8 * p) * ((|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v) := by
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖((w : ℤ) : ℂ)‖ = |(w : ℝ)| := by
    rw [show ((w : ℤ) : ℂ) = ((w : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : ‖((envF y u v : ℝ) : ℂ)‖ = envF y u v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envF_nonneg y u v)]
  have h3 : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [h1, h2, h3]
  have he := envF_nonneg y u v
  have hwn := abs_nonneg (w : ℝ)
  have hsn := norm_nonneg s
  calc c * |(w : ℝ)| * ‖s‖ * envF y u v
      ≤ c * |(w : ℝ)| * 1 * envF y u v := by
        apply mul_le_mul_of_nonneg_right _ he
        exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = c * |(w : ℝ)| * envF y u v := by ring
    _ ≤ (8 * p) * (|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v :=
        mul_le_mul_of_nonneg_right hw he
    _ = (8 * p) * ((|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v) := by ring

private lemma norm_sgn_XP_le (p : ℕ) [Fact p.Prime] (a N : ℤ) :
    ‖sgn4 a * ((XP p N : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have h1 := norm_sgn4_le a
  have h2 := norm_XP_le p N
  have h3 := norm_nonneg (sgn4 a)
  have h4 := norm_nonneg ((XP p N : ℤ) : ℂ)
  nlinarith

private lemma norm_cs_XP_le (p : ℕ) [Fact p.Prime] (a N : ℤ) :
    ‖cs4 a * ((XP p N : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have h1 := norm_cs4_le a
  have h2 := norm_XP_le p N
  have h3 := norm_nonneg (cs4 a)
  have h4 := norm_nonneg ((XP p N : ℤ) : ℂ)
  nlinarith

private lemma weight_sum_le (p : ℕ) (u v : ℤ) :
    (2 * (p : ℝ)) * |((u + v : ℤ) : ℝ)| ≤ (8 * p) * (|(u : ℝ)| + |(v : ℝ)| + 1) := by
  have h : |((u + v : ℤ) : ℝ)| ≤ |(u : ℝ)| + |(v : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  have h1 := abs_nonneg (u : ℝ)
  have h2 := abs_nonneg (v : ℝ)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

private lemma weight_fst_le (p : ℕ) (u v : ℤ) (c : ℝ) (hc : 0 ≤ c)
    (hc' : c ≤ 8 * p) :
    c * |(u : ℝ)| ≤ (8 * p) * (|(u : ℝ)| + |(v : ℝ)| + 1) := by
  have h1 := abs_nonneg (u : ℝ)
  have h2 := abs_nonneg (v : ℝ)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

private lemma summable_gLadderP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (gLadderP p y) := by
  refine summable_of_le_envF (C := 8 * p) hy fun q => ?_
  obtain ⟨u, v⟩ := q
  show ‖2 * (p : ℂ) * ((u + v : ℤ) : ℂ) * sgn4 (u + v) *
      ((XP p (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) * ((envF y u v : ℝ) : ℂ)‖ ≤ _
  rw [show (2 : ℂ) * (p : ℂ) * ((u + v : ℤ) : ℂ) * sgn4 (u + v) *
        ((XP p (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) * ((envF y u v : ℝ) : ℂ)
      = ((2 * (p : ℝ) : ℝ) : ℂ) * ((u + v : ℤ) : ℂ) *
        (sgn4 (u + v) * ((XP p (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ)) *
        ((envF y u v : ℝ) : ℂ) from by push_cast; ring]
  exact norm_weight_le p y u v (u + v) (2 * p) _ (norm_sgn_XP_le p _ _) (by positivity)
    (weight_sum_le p u v)

private lemma summable_piece (p : ℕ) {y : ℝ} (hy : 0 < y) (c : ℝ) (hc : 0 ≤ c)
    (hc' : c ≤ 8 * p)
    (P : ℤ × ℤ → Prop) [DecidablePred P] (S : ℤ × ℤ → ℂ) (hS : ∀ q, ‖S q‖ ≤ 1) :
    Summable fun q : ℤ × ℤ =>
      if P q then (c : ℂ) * (q.1 : ℂ) * S q * ((envF y q.1 q.2 : ℝ) : ℂ) else 0 := by
  refine summable_of_le_envF (C := 8 * p) hy fun q => ?_
  obtain ⟨u, v⟩ := q
  split_ifs
  · exact norm_weight_le p y u v u c _ (hS _) hc (weight_fst_le p u v c hc hc')
  · simp only [norm_zero]
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h8 : (0 : ℝ) ≤ 8 * p := by positivity
    exact mul_nonneg h8
      (mul_nonneg (by positivity) (envF_nonneg y u v))

private lemma two_p_le (p : ℕ) : (2 : ℝ) * p ≤ 8 * p := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith

private lemma summable_hHalfP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (hHalfP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => q.2 % 2 = 0)
    (fun q => sgn4 (q.1 + q.2) * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_sgn_XP_le p _ _)
  refine h.congr fun q => ?_
  unfold hHalfP
  split_ifs <;> push_cast <;> ring

private lemma summable_gEvenP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (gEvenP p y) := by
  refine Summable.of_norm_bounded (summable_gLadderP p hy).norm fun q => ?_
  unfold gEvenP
  split_ifs
  · exact le_rfl
  · simp

private lemma summable_gOddVP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (gOddVP p y) := by
  refine Summable.of_norm_bounded (summable_gLadderP p hy).norm fun q => ?_
  unfold gOddVP
  split_ifs
  · simp
  · exact le_rfl

lemma summable_hPlusP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (hPlusP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0)
    (fun q => ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_XP_le p _)
  refine h.congr fun q => ?_
  unfold hPlusP
  split_ifs <;> push_cast <;> ring

private lemma summable_hMinusP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (hMinusP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => (q.1 + q.2) % 4 = 3 ∧ q.2 % 2 = 0)
    (fun q => ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_XP_le p _)
  refine h.congr fun q => ?_
  unfold hMinusP
  split_ifs <;> push_cast <;> ring

private lemma summable_aPieceP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (aPieceP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => q.1 % 4 = 1 ∧ q.2 % 4 = 0)
    (fun q => ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_XP_le p _)
  refine h.congr fun q => ?_
  unfold aPieceP
  split_ifs <;> push_cast <;> ring

private lemma summable_bPieceP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (bPieceP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => q.1 % 4 = 3 ∧ q.2 % 4 = 2)
    (fun q => ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_XP_le p _)
  refine h.congr fun q => ?_
  unfold bPieceP
  split_ifs <;> push_cast <;> ring

private lemma summable_bMirrorP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (bMirrorP p y) := by
  have h := summable_piece p hy (2 * p) (by positivity) (two_p_le p)
    (fun q : ℤ × ℤ => q.1 % 4 = 1 ∧ q.2 % 4 = 2)
    (fun q => ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_XP_le p _)
  refine h.congr fun q => ?_
  unfold bMirrorP
  split_ifs <;> push_cast <;> ring

private lemma summable_dualPEven (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (dualPEven p y) := by
  refine Summable.of_norm_bounded (summable_dualP p hy).norm fun q => ?_
  unfold dualPEven
  split_ifs
  · exact le_rfl
  · simp

private lemma summable_dualPOdd (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (dualPOdd p y) := by
  refine Summable.of_norm_bounded (summable_dualP p hy).norm fun q => ?_
  unfold dualPOdd
  split_ifs
  · simp
  · exact le_rfl

/-! ## 7. Pointwise identities along the ladder -/

private lemma envF_neg_snd (y : ℝ) (u v : ℤ) : envF y u (-v) = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma envF_neg_both (y : ℝ) (u v : ℤ) : envF y (-u) (-v) = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma envF_swap (y : ℝ) (u v : ℤ) : envF y v u = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma quarter_phase_odd {p k : ℕ} (hpk : p = 2 * k + 1) (t : ℤ) :
    -I * cexp (π * I * ((p : ℂ) * ((2 * t + 1 : ℤ) : ℂ)) / 2)
      = ((-1 : ℂ)) ^ k * sgn4 (2 * t + 1) := by
  have hpc : (p : ℂ) = 2 * (k : ℂ) + 1 := by exact_mod_cast hpk
  have hexp : cexp (π * I * ((p : ℂ) * ((2 * t + 1 : ℤ) : ℂ)) / 2)
      = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ t * I) := by
    rw [show (π : ℂ) * I * ((p : ℂ) * ((2 * t + 1 : ℤ) : ℂ)) / 2
        = (((k : ℤ) * t) : ℂ) * (2 * π * I) + (π * I * ((k : ℕ) : ℂ)
            + (π * I * ((t : ℤ) : ℂ) + π / 2 * I)) from by
      rw [hpc]
      push_cast
      ring]
    rw [Complex.exp_add, show ((((k : ℤ) * t) : ℂ)) = (((k : ℤ) * t : ℤ) : ℂ) from by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
      Complex.exp_add, Complex.exp_pi_div_two_mul_I]
    have hk : cexp (π * I * ((k : ℕ) : ℂ)) = (-1 : ℂ) ^ (k : ℕ) := by
      have h := neg_one_zpow_exp ((k : ℕ) : ℤ)
      rw [show (π : ℂ) * I * ((k : ℕ) : ℂ) = π * I * (((k : ℕ) : ℤ) : ℂ) from by
        push_cast; ring, h, zpow_natCast]
    have ht : cexp (π * I * ((t : ℤ) : ℂ)) = (-1 : ℂ) ^ t := neg_one_zpow_exp t
    rw [hk, ht]
  rw [hexp]
  have hsgn : sgn4 (2 * t + 1) = (-1 : ℂ) ^ t := by
    rcases Int.even_or_odd t with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [show sgn4 (2 * (r + r) + 1) = 1 from by unfold sgn4; rw [if_pos (by omega)],
        show (r : ℤ) + r = 2 * r from by ring, zpow_mul]
      norm_num
    · rw [show sgn4 (2 * (2 * r + 1) + 1) = -1 from by
        unfold sgn4; rw [if_neg (by omega), if_pos (by omega)],
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
      norm_num
  rw [hsgn]
  linear_combination (-(((-1 : ℂ)) ^ k * ((-1 : ℂ)) ^ t)) * Complex.I_mul_I

private lemma quarter_phase_neg_even {p : ℕ} {n : ℤ} (hn : n % 2 = 0) :
    cexp (π * I * ((p : ℂ) * ((-n : ℤ) : ℂ)) / 2)
      = cexp (π * I * ((p : ℂ) * ((n : ℤ) : ℂ)) / 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
  rw [show (π : ℂ) * I * ((p : ℂ) * ((-(2 * r) : ℤ) : ℂ)) / 2
        = π * I * ((p : ℂ) * ((2 * r : ℤ) : ℂ)) / 2
          + ((-(p : ℤ) * r : ℤ) : ℂ) * (2 * π * I) from by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The even part of the dual family dies under the involution `n ↦ −n`. -/
private lemma tsum_dualPEven_eq_zero (p : ℕ) [Fact p.Prime] (y : ℝ) :
    ∑' q : ℤ × ℤ, dualPEven p y q = 0 := by
  have h1 : ∑' q : ℤ × ℤ, dualPEven p y (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) q)
      = ∑' q : ℤ × ℤ, dualPEven p y q :=
    ((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)).tsum_eq (dualPEven p y)
  have h2 : ∀ q : ℤ × ℤ, dualPEven p y (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) q)
      = -dualPEven p y q := by
    rintro ⟨n, m⟩
    show dualPEven p y (-n, m) = -dualPEven p y (n, m)
    by_cases hn : n % 2 = 0
    · simp only [dualPEven]
      rw [if_pos (show (-n) % 2 = 0 by omega), if_pos hn]
      show dualP p y (-n, m) = -dualP p y (n, m)
      unfold dualP
      show -I * ((-n : ℤ) : ℂ) *
          (2 * (p : ℂ) * cexp (π * I * ((p : ℂ) * ((-n : ℤ) : ℂ)) / 2) *
          oddInd m * ((XP p ((-n) ^ 2 + m ^ 2) : ℤ) : ℂ)) * ((envP y (-n) m : ℝ) : ℂ) = _
      rw [quarter_phase_neg_even hn,
        show ((-n : ℤ) : ℂ) = -((n : ℤ) : ℂ) from by push_cast; ring,
        show XP p ((-n) ^ 2 + m ^ 2) = XP p (n ^ 2 + m ^ 2) from by ring_nf,
        show envP y (-n) m = envP y n m from by unfold envP; congr 1; push_cast; ring]
      ring
    · simp only [dualPEven]
      rw [if_neg (show ¬((-n) % 2 = 0) by omega), if_neg hn, neg_zero]
  have h3 : ∑' q : ℤ × ℤ, dualPEven p y q = -∑' q : ℤ × ℤ, dualPEven p y q := by
    conv_lhs => rw [← h1, tsum_congr h2]
    exact tsum_neg
  linear_combination h3 / 2

/-- The odd part transports through `(t, s) ↦ (2t+1, 2s+1)` and the fold. -/
private lemma dualPOdd_comp_bothOdd (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hpk : p = 2 * k + 1) (y : ℝ) (q : ℤ × ℤ) :
    dualPOdd p y (bothOddEmb q) = ((-1 : ℂ)) ^ k * gLadderP p y (foldMap q) := by
  obtain ⟨t, s⟩ := q
  show dualPOdd p y (2 * t + 1, 2 * s + 1)
    = ((-1 : ℂ)) ^ k * gLadderP p y (t + s + 1, t - s)
  simp only [dualPOdd]
  rw [if_neg (show ¬((2 * t + 1) % 2 = 0) by omega)]
  show dualP p y (2 * t + 1, 2 * s + 1) = _
  unfold dualP gLadderP
  show -I * ((2 * t + 1 : ℤ) : ℂ) *
      (2 * (p : ℂ) * cexp (π * I * ((p : ℂ) * ((2 * t + 1 : ℤ) : ℂ)) / 2) *
      oddInd (2 * s + 1) * ((XP p ((2 * t + 1) ^ 2 + (2 * s + 1) ^ 2) : ℤ) : ℂ)) *
      ((envP y (2 * t + 1) (2 * s + 1) : ℝ) : ℂ) = _
  have hoi : oddInd (2 * s + 1) = 1 := by
    unfold oddInd
    rw [if_neg (by omega)]
  have hchi : XP p ((2 * t + 1) ^ 2 + (2 * s + 1) ^ 2)
      = XP p (2 * ((t + s + 1) ^ 2 + (t - s) ^ 2)) := by
    rw [show (2 * t + 1) ^ 2 + (2 * s + 1) ^ 2 = 2 * ((t + s + 1) ^ 2 + (t - s) ^ 2) from
      by ring]
  have henv : envP y (2 * t + 1) (2 * s + 1) = envF y (t + s + 1) (t - s) := by
    unfold envP envF
    congr 1
    push_cast
    ring
  rw [hoi, hchi, henv, show (t + s + 1) + (t - s) = 2 * t + 1 from by ring]
  have hq := quarter_phase_odd hpk t
  linear_combination (2 * (p : ℂ) * ((2 * t + 1 : ℤ) : ℂ) *
    ((XP p (2 * ((t + s + 1) ^ 2 + (t - s) ^ 2)) : ℤ) : ℂ) *
    ((envF y (t + s + 1) (t - s) : ℝ) : ℂ)) * hq

private lemma tsum_dualPOdd_eq_gLadderP (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hpk : p = 2 * k + 1) (y : ℝ) :
    ∑' q : ℤ × ℤ, dualPOdd p y q
      = ((-1 : ℂ)) ^ k * ∑' q : ℤ × ℤ, gLadderP p y q := by
  have h1 : ∑' q : ℤ × ℤ, dualPOdd p y (bothOddEmb q) = ∑' q : ℤ × ℤ, dualPOdd p y q := by
    refine bothOddEmb_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨n, m⟩ hne
    have hn : ¬(n % 2 = 0) := by
      intro h
      apply hne
      simp only [dualPOdd]
      rw [if_pos h]
    have hm : ¬(m % 2 = 0) := by
      intro h
      apply hne
      simp only [dualPOdd]
      rw [if_neg hn]
      unfold dualP
      show -I * (n : ℂ) * (2 * (p : ℂ) * cexp (π * I * ((p : ℂ) * (n : ℂ)) / 2) *
          oddInd m * ((XP p (n ^ 2 + m ^ 2) : ℤ) : ℂ)) * ((envP y n m : ℝ) : ℂ) = 0
      rw [show oddInd m = 0 from by unfold oddInd; rw [if_pos h]]
      ring
    exact ⟨((n - 1) / 2, (m - 1) / 2), by
      simp only [bothOddEmb, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  have h2 : ∑' q : ℤ × ℤ, gLadderP p y (foldMap q) = ∑' q : ℤ × ℤ, gLadderP p y q := by
    refine foldMap_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨u, v⟩ hne
    have hodd : (u + v) % 4 = 1 ∨ (u + v) % 4 = 3 := by
      by_contra hc
      push_neg at hc
      apply hne
      show 2 * (p : ℂ) * ((u + v : ℤ) : ℂ) * sgn4 (u + v) * _ * _ = 0
      rw [show sgn4 (u + v) = 0 from by unfold sgn4; rw [if_neg hc.1, if_neg hc.2]]
      ring
    exact ⟨((u + v - 1) / 2, (u - v - 1) / 2), by
      simp only [foldMap, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  rw [← h1, ← h2, ← tsum_mul_left]
  exact tsum_congr fun q => dualPOdd_comp_bothOdd p hpk y q

/-- The swap fold. -/
private lemma gOddVP_comp_swap (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) :
    gOddVP p y ((Equiv.prodComm ℤ ℤ) q) = gEvenP p y q := by
  obtain ⟨u, v⟩ := q
  show gOddVP p y (v, u) = gEvenP p y (u, v)
  have hswap : gLadderP p y (v, u) = gLadderP p y (u, v) := by
    unfold gLadderP
    rw [show v + u = u + v from by ring, envF_swap,
      show v ^ 2 + u ^ 2 = u ^ 2 + v ^ 2 from by ring]
  have hzero : ∀ a b : ℤ, (a + b) % 2 = 0 → gLadderP p y (a, b) = 0 := by
    intro a b h
    show 2 * (p : ℂ) * ((a + b : ℤ) : ℂ) * sgn4 (a + b) * _ * _ = 0
    rw [show sgn4 (a + b) = 0 from by unfold sgn4; rw [if_neg (by omega), if_neg (by omega)]]
    ring
  simp only [gOddVP, gEvenP]
  by_cases hu : u % 2 = 0
  · rw [if_pos hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, hzero u v (by omega)]
    · rw [if_neg hv]
  · rw [if_neg hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, hswap]
    · rw [if_neg hv, hzero v u (by omega)]

private lemma tsum_gLadderP_eq_two_gEvenP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, gLadderP p y q = 2 * ∑' q : ℤ × ℤ, gEvenP p y q := by
  have hpt : ∀ q : ℤ × ℤ, gLadderP p y q = gEvenP p y q + gOddVP p y q := by
    intro q
    simp only [gEvenP, gOddVP]
    split_ifs <;> ring
  have hswap : ∑' q : ℤ × ℤ, gOddVP p y q = ∑' q : ℤ × ℤ, gEvenP p y q := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (gOddVP p y)]
    exact tsum_congr fun q => gOddVP_comp_swap p y q
  rw [tsum_congr hpt, (summable_gEvenP p hy).tsum_add (summable_gOddVP p hy), hswap]
  ring

/-- The `v ↦ −v` fold replaces the weight `u+v` by `u`. -/
private lemma gEvenP_add_negSnd (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) :
    gEvenP p y q + gEvenP p y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) q)
      = 2 * hHalfP p y q := by
  obtain ⟨u, v⟩ := q
  show gEvenP p y (u, v) + gEvenP p y (u, -v) = 2 * hHalfP p y (u, v)
  simp only [gEvenP, hHalfP]
  by_cases hv : v % 2 = 0
  · rw [if_pos hv, if_pos (show (-v) % 2 = 0 by omega), if_pos hv]
    unfold gLadderP
    show 2 * (p : ℂ) * ((u + v : ℤ) : ℂ) * sgn4 (u + v) *
        ((XP p (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) * ((envF y u v : ℝ) : ℂ) +
        2 * (p : ℂ) * ((u + -v : ℤ) : ℂ) * sgn4 (u + -v) *
          ((XP p (2 * (u ^ 2 + (-v) ^ 2)) : ℤ) : ℂ) * ((envF y u (-v) : ℝ) : ℂ) = _
    rw [show u + -v = u - v from by ring,
      show sgn4 (u - v) = sgn4 (u + v) from by
        unfold sgn4; rw [show (u - v) % 4 = (u + v) % 4 from by omega],
      envF_neg_snd, show 2 * (u ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
    push_cast
    ring
  · rw [if_neg hv, if_neg (show ¬((-v) % 2 = 0) by omega), if_neg hv]
    ring

private lemma tsum_gEvenP_eq_hHalfP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, gEvenP p y q = ∑' q : ℤ × ℤ, hHalfP p y q := by
  have hcomp : Summable (gEvenP p y ∘ ((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ))) :=
    (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).summable_iff).mpr (summable_gEvenP p hy)
  have h2 : (2 : ℂ) * ∑' q : ℤ × ℤ, gEvenP p y q = 2 * ∑' q : ℤ × ℤ, hHalfP p y q := by
    calc (2 : ℂ) * ∑' q : ℤ × ℤ, gEvenP p y q
        = ∑' q : ℤ × ℤ, gEvenP p y q
            + ∑' q : ℤ × ℤ, gEvenP p y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) q) := by
          rw [((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (gEvenP p y)]
          ring
      _ = ∑' q : ℤ × ℤ, (gEvenP p y q
            + gEvenP p y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) q)) :=
          ((summable_gEvenP p hy).tsum_add hcomp).symm
      _ = ∑' q : ℤ × ℤ, (2 : ℂ) * hHalfP p y q :=
          tsum_congr fun q => gEvenP_add_negSnd p y q
      _ = 2 * ∑' q : ℤ × ℤ, hHalfP p y q := tsum_mul_left
  exact mul_left_cancel₀ two_ne_zero h2

/-- The class fold. -/
private lemma tsum_hHalfP_eq_two_hPlusP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, hHalfP p y q = 2 * ∑' q : ℤ × ℤ, hPlusP p y q := by
  have hpt : ∀ q : ℤ × ℤ, hHalfP p y q = hPlusP p y q - hMinusP p y q := by
    rintro ⟨u, v⟩
    simp only [hHalfP, hPlusP, hMinusP, sgn4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hneg : ∑' q : ℤ × ℤ, hMinusP p y q = -∑' q : ℤ × ℤ, hPlusP p y q := by
    have h1 : ∑' q : ℤ × ℤ, hMinusP p y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) q)
        = ∑' q : ℤ × ℤ, hMinusP p y q :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (hMinusP p y)
    have h2 : ∀ q : ℤ × ℤ, hMinusP p y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) q)
        = -hPlusP p y q := by
      rintro ⟨u, v⟩
      show hMinusP p y (-u, -v) = -hPlusP p y (u, v)
      simp only [hMinusP, hPlusP]
      by_cases h : (u + v) % 4 = 1 ∧ v % 2 = 0
      · rw [if_pos (show (-u + -v) % 4 = 3 ∧ (-v) % 2 = 0 by omega), if_pos h,
          envF_neg_both, show 2 * ((-u) ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
        push_cast
        ring
      · rw [if_neg (show ¬((-u + -v) % 4 = 3 ∧ (-v) % 2 = 0) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  rw [tsum_congr hpt, (summable_hPlusP p hy).tsum_sub (summable_hMinusP p hy), hneg]
  ring

/-- The gather onto the cosine-signed target. -/
lemma tsum_hFinalP_eq_four_hPlusP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, hFinalP p y q = 4 * ∑' q : ℤ × ℤ, hPlusP p y q := by
  have hsplit : ∀ q : ℤ × ℤ, hPlusP p y q = aPieceP p y q + bPieceP p y q := by
    rintro ⟨u, v⟩
    simp only [hPlusP, aPieceP, bPieceP]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hfin : ∀ q : ℤ × ℤ, hFinalP p y q = 4 * aPieceP p y q - 4 * bMirrorP p y q := by
    rintro ⟨u, v⟩
    simp only [hFinalP, aPieceP, bMirrorP, cs4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hbm : ∑' q : ℤ × ℤ, bPieceP p y q = -∑' q : ℤ × ℤ, bMirrorP p y q := by
    have h1 : ∑' q : ℤ × ℤ, bPieceP p y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) q)
        = ∑' q : ℤ × ℤ, bPieceP p y q :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (bPieceP p y)
    have h2 : ∀ q : ℤ × ℤ, bPieceP p y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) q)
        = -bMirrorP p y q := by
      rintro ⟨u, v⟩
      show bPieceP p y (-u, -v) = -bMirrorP p y (u, v)
      simp only [bPieceP, bMirrorP]
      by_cases h : u % 4 = 1 ∧ v % 4 = 2
      · rw [if_pos (show (-u) % 4 = 3 ∧ (-v) % 4 = 2 by omega), if_pos h, envF_neg_both,
          show 2 * ((-u) ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
        push_cast
        ring
      · rw [if_neg (show ¬((-u) % 4 = 3 ∧ (-v) % 4 = 2) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  calc ∑' q : ℤ × ℤ, hFinalP p y q
      = ∑' q : ℤ × ℤ, ((4 : ℂ) * aPieceP p y q - 4 * bMirrorP p y q) := tsum_congr hfin
    _ = (∑' q : ℤ × ℤ, (4 : ℂ) * aPieceP p y q) - ∑' q : ℤ × ℤ, (4 : ℂ) * bMirrorP p y q :=
        ((summable_aPieceP p hy).mul_left 4).tsum_sub ((summable_bMirrorP p hy).mul_left 4)
    _ = 4 * (∑' q : ℤ × ℤ, aPieceP p y q) - 4 * ∑' q : ℤ × ℤ, bMirrorP p y q := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = 4 * ((∑' q : ℤ × ℤ, aPieceP p y q) + ∑' q : ℤ × ℤ, bPieceP p y q) := by
        rw [hbm]; ring
    _ = 4 * ∑' q : ℤ × ℤ, (aPieceP p y q + bPieceP p y q) := by
        rw [(summable_aPieceP p hy).tsum_add (summable_bPieceP p hy)]
    _ = 4 * ∑' q : ℤ × ℤ, hPlusP p y q := by
        rw [tsum_congr hsplit]

/-- The complete dual chain: the collapsed dual family equals the gathered target. -/
private lemma tsum_dualP_eq_hFinalP (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hpk : p = 2 * k + 1) {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, dualP p y q
      = ((-1 : ℂ)) ^ k * ∑' q : ℤ × ℤ, hFinalP p y q := by
  have hsplit : ∀ q : ℤ × ℤ, dualP p y q = dualPEven p y q + dualPOdd p y q := by
    intro q
    simp only [dualPEven, dualPOdd]
    split_ifs <;> ring
  rw [tsum_congr hsplit, (summable_dualPEven p hy).tsum_add (summable_dualPOdd p hy),
    tsum_dualPEven_eq_zero p y, zero_add, tsum_dualPOdd_eq_gLadderP p hpk y,
    tsum_gLadderP_eq_two_gEvenP p hy, tsum_gEvenP_eq_hHalfP p hy,
    tsum_hHalfP_eq_two_hPlusP p hy, tsum_hFinalP_eq_four_hPlusP p hy]
  ring

/-! ## 8. The grid landing and the primal reassembly -/

lemma summable_hFinalP (p : ℕ) [Fact p.Prime] {y : ℝ} (hy : 0 < y) :
    Summable (hFinalP p y) := by
  have h := summable_piece p hy (8 * p) (by positivity) le_rfl
    (fun q : ℤ × ℤ => q.1 % 4 = 1)
    (fun q => cs4 q.2 * ((XP p (2 * (q.1 ^ 2 + q.2 ^ 2)) : ℤ) : ℂ))
    (fun q => norm_cs_XP_le p _ _)
  refine h.congr fun q => ?_
  unfold hFinalP
  split_ifs <;> push_cast <;> ring

lemma hFinalP_support (p : ℕ) [Fact p.Prime] (y : ℝ) :
    ∀ q ∉ Set.range gridEmb, hFinalP p y q = 0 := by
  rintro ⟨u, v⟩ hq
  have hcond : ¬(u % 4 = 1 ∧ v % 2 = 0) := by
    intro ⟨hu, hv⟩
    exact hq ⟨((u - 1) / 4, v / 2), by
      simp only [gridEmb, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  by_cases hu : u % 4 = 1
  · have hv : ¬(v % 2 = 0) := fun hv => hcond ⟨hu, hv⟩
    show (if u % 4 = 1 then _ else 0) = 0
    rw [if_pos hu, show cs4 v = 0 from by
      unfold cs4; rw [if_neg (by omega), if_neg (by omega)]]
    ring
  · show (if u % 4 = 1 then _ else 0) = 0
    rw [if_neg hu]

private lemma tsum_gridEmb_eq_hFinalP (p : ℕ) [Fact p.Prime] (y : ℝ) :
    ∑' q : ℤ × ℤ, hFinalP p y (gridEmb q) = ∑' q : ℤ × ℤ, hFinalP p y q := by
  refine gridEmb_injective.tsum_eq ?_
  rw [Function.support_subset_iff]
  intro q hne
  by_contra hc
  exact hne (hFinalP_support p y q hc)

/-- The residue equivalence: `(Fin p × Fin 2p) × ℤ² ≃ ℤ²` by the division algorithm. -/
private def resEquivP (p : ℕ) (hp : 0 < p) :
    (Fin p × Fin (2 * p)) × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := ((p : ℤ) * x.2.1 + ((x.1.1 : ℕ) : ℤ), (2 * p : ℤ) * x.2.2 + ((x.1.2 : ℕ) : ℤ))
  invFun q := ((⟨(q.1 % p).toNat, by
      have h1 := Int.emod_nonneg q.1 (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne')
      have h2 := Int.emod_lt_of_pos q.1 (show (0 : ℤ) < p by exact_mod_cast hp)
      omega⟩,
    ⟨(q.2 % (2 * p)).toNat, by
      have hp2 : (0 : ℤ) < 2 * p := by exact_mod_cast Nat.succ_le_of_lt (by omega)
      have h1 := Int.emod_nonneg q.2 hp2.ne'
      have h2 := Int.emod_lt_of_pos q.2 hp2
      omega⟩),
    (q.1 / p, q.2 / (2 * p)))
  left_inv := by
    rintro ⟨⟨e, d⟩, ⟨n', m'⟩⟩
    have he := e.isLt
    have hd := d.isLt
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp
    have hp2 : (0 : ℤ) < 2 * p := by omega
    have hkey1 : ((p : ℤ) * n' + ((e : ℕ) : ℤ)) % p = ((e : ℕ) : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega)
        (by exact_mod_cast he)]
    have hkey2 : ((2 * p : ℤ) * m' + ((d : ℕ) : ℤ)) % (2 * p) = ((d : ℕ) : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega)
        (by exact_mod_cast hd)]
    have hdiv1 : ((p : ℤ) * n' + ((e : ℕ) : ℤ)) / p = n' := by
      rw [add_comm, Int.add_mul_ediv_left _ _ hp0.ne',
        Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast he), zero_add]
    have hdiv2 : ((2 * p : ℤ) * m' + ((d : ℕ) : ℤ)) / (2 * p) = m' := by
      rw [add_comm, Int.add_mul_ediv_left _ _ hp2.ne',
        Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hd), zero_add]
    simp only [Prod.mk.injEq]
    refine ⟨⟨Fin.ext ?_, Fin.ext ?_⟩, ?_, ?_⟩
    · show (((p : ℤ) * n' + ((e : ℕ) : ℤ)) % p).toNat = (e : ℕ)
      rw [hkey1]
      exact Int.toNat_natCast _
    · show (((2 * p : ℤ) * m' + ((d : ℕ) : ℤ)) % (2 * p)).toNat = (d : ℕ)
      rw [hkey2]
      exact Int.toNat_natCast _
    · exact hdiv1
    · exact hdiv2
  right_inv := by
    rintro ⟨k, l⟩
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp
    have hp2 : (0 : ℤ) < 2 * p := by omega
    simp only [Prod.mk.injEq]
    constructor
    · have h1 := Int.emod_nonneg k hp0.ne'
      have h2 := Int.ediv_add_emod k (p : ℤ)
      rw [Int.toNat_of_nonneg h1]
      omega
    · have h1 := Int.emod_nonneg l hp2.ne'
      have h2 := Int.ediv_add_emod l ((2 * p : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg h1]
      push_cast at h2 ⊢
      omega

/-- The `oddKernel` summand at scale `32p²y`, coerced whole. -/
private def oddT (p : ℕ) (y : ℝ) (e : ℕ) (n : ℤ) : ℂ :=
  ((((n : ℝ) + (4 * (e : ℝ) + 1) / (4 * p)) *
      rexp (-π * ((n : ℝ) + (4 * (e : ℝ) + 1) / (4 * p)) ^ 2 * (32 * p ^ 2 * y)) : ℝ) : ℂ)

/-- The `evenKernel` summand at scale `32p²y`, coerced whole. -/
private def evenT (p : ℕ) (y : ℝ) (d : ℕ) (m : ℤ) : ℂ :=
  ((rexp (-π * ((m : ℝ) + (d : ℝ) / (2 * p)) ^ 2 * (32 * p ^ 2 * y)) : ℝ) : ℂ)

/-- The kernel product at scale `32p²y`, as a lattice double sum. -/
private def primalT (p : ℕ) (y : ℝ) (e d : ℕ) (q : ℤ × ℤ) : ℂ :=
  oddT p y e q.1 * evenT p y d q.2

private lemma hasSum_oddT (p : ℕ) (hp : 0 < p) {y : ℝ} (hy : 0 < y) (e : ℕ) :
    HasSum (oddT p y e)
      ((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
          (32 * p ^ 2 * y) : ℝ) : ℂ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact Complex.hasSum_ofReal.mpr
    (HurwitzZeta.hasSum_int_oddKernel ((4 * (e : ℝ) + 1) / (4 * p))
      (show (0 : ℝ) < 32 * p ^ 2 * y by positivity))

private lemma hasSum_evenT (p : ℕ) (hp : 0 < p) {y : ℝ} (hy : 0 < y) (d : ℕ) :
    HasSum (evenT p y d)
      ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (32 * p ^ 2 * y) : ℝ) : ℂ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact Complex.hasSum_ofReal.mpr
    (HurwitzZeta.hasSum_int_evenKernel ((d : ℝ) / (2 * p))
      (show (0 : ℝ) < 32 * p ^ 2 * y by positivity))

private lemma summable_primalT (p : ℕ) (hp : 0 < p) {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    Summable (primalT p y e d) :=
  summable_norm_iff.mp
    ((summable_norm_iff.mpr (hasSum_oddT p hp hy e).summable).mul_norm
      (summable_norm_iff.mpr (hasSum_evenT p hp hy d).summable))

private lemma oddK_evenK_product (p : ℕ) (hp : 0 < p) {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    ((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
        (32 * p ^ 2 * y) : ℝ) : ℂ) *
        ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (32 * p ^ 2 * y) : ℝ) : ℂ)
      = ∑' q : ℤ × ℤ, primalT p y e d q :=
  (hasSum_oddT p hp hy e).mul_eq (hasSum_evenT p hp hy d)
    (summable_primalT p hp hy e d).hasSum

private lemma cs4_grid (p : ℕ) (m' : ℤ) (d : ℕ) :
    cs4 (2 * ((2 * p : ℤ) * m' + (d : ℤ))) = (((-1 : ℤ) ^ d : ℤ) : ℂ) := by
  have hK : 2 * ((2 * p : ℤ) * m' + (d : ℤ)) = 4 * ((p : ℤ) * m') + 2 * (d : ℤ) := by
    ring
  rw [hK]
  generalize (p : ℤ) * m' = K
  rcases Nat.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [show cs4 (4 * K + 2 * (d : ℤ)) = 1 from by
      unfold cs4; rw [if_pos (by omega)]]
    rw [ht, show ((-1 : ℤ) ^ (t + t) : ℤ) = 1 from by
      rw [show t + t = 2 * t from by ring, pow_mul]; norm_num]
    norm_num
  · rw [show cs4 (4 * K + 2 * (d : ℤ)) = -1 from by
      unfold cs4; rw [if_neg (by omega), if_pos (by omega)]]
    rw [ht, show ((-1 : ℤ) ^ (2 * t + 1) : ℤ) = -1 from by
      rw [pow_add, pow_mul]; norm_num]
    norm_num

private lemma XP_grid (p : ℕ) [Fact p.Prime] (n' m' : ℤ) (e d : ℕ) :
    XP p (2 * ((4 * ((p : ℤ) * n' + (e : ℤ)) + 1) ^ 2 + (2 * ((2 * p : ℤ) * m' + (d : ℤ))) ^ 2))
      = XP p 2 * XP p ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by
  have hu : (4 * ((p : ℤ) * n' + (e : ℤ)) + 1) ≡ 4 * (e : ℤ) + 1 [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-4 * n', by ring⟩
  have hv : (2 * ((2 * p : ℤ) * m' + (d : ℤ))) ≡ 2 * (d : ℤ) [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-4 * m', by ring⟩
  have hX : (4 * ((p : ℤ) * n' + (e : ℤ)) + 1) ^ 2 + (2 * ((2 * p : ℤ) * m' + (d : ℤ))) ^ 2
      ≡ (4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 [ZMOD (p : ℤ)] := by
    have h := (hu.pow 2).add (hv.pow 2)
    have harg : (2 * (d : ℤ)) ^ 2 = 4 * (d : ℤ) ^ 2 := by ring
    rwa [harg] at h
  calc XP p (2 * ((4 * ((p : ℤ) * n' + (e : ℤ)) + 1) ^ 2 +
        (2 * ((2 * p : ℤ) * m' + (d : ℤ))) ^ 2))
      = XP p 2 * XP p ((4 * ((p : ℤ) * n' + (e : ℤ)) + 1) ^ 2 +
          (2 * ((2 * p : ℤ) * m' + (d : ℤ))) ^ 2) := XP_mul p _ _
    _ = XP p 2 * XP p ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by
        rw [XP_congr p hX]

private lemma envF_grid (p : ℕ) (hp : 0 < p) (y : ℝ) (n' m' : ℤ) (e d : ℕ) :
    envF y (4 * ((p : ℤ) * n' + (e : ℤ)) + 1) (2 * ((2 * p : ℤ) * m' + (d : ℤ)))
      = rexp (-π * ((n' : ℝ) + (4 * (e : ℝ) + 1) / (4 * p)) ^ 2 * (32 * p ^ 2 * y)) *
        rexp (-π * ((m' : ℝ) + (d : ℝ) / (2 * p)) ^ 2 * (32 * p ^ 2 * y)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := hp'.ne'
  unfold envF
  rw [← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The pointwise landing: the gathered target at a grid point is `32p²·χ_p(2)` times
the weighted primal kernel summand. -/
private lemma hFinalP_land (p : ℕ) [Fact p.Prime] (hp : 0 < p) (y : ℝ)
    (e : Fin p) (d : Fin (2 * p)) (q : ℤ × ℤ) :
    hFinalP p y (gridEmb (resEquivP p hp ((e, d), q)))
      = 32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ) * ((wP p (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
          primalT p y (e : ℕ) (d : ℕ) q := by
  obtain ⟨n', m'⟩ := q
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hres : resEquivP p hp ((e, d), (n', m'))
      = ((p : ℤ) * n' + ((e : ℕ) : ℤ), (2 * p : ℤ) * m' + ((d : ℕ) : ℤ)) := rfl
  have hgrid : gridEmb ((p : ℤ) * n' + ((e : ℕ) : ℤ), (2 * p : ℤ) * m' + ((d : ℕ) : ℤ))
      = (4 * ((p : ℤ) * n' + ((e : ℕ) : ℤ)) + 1,
         2 * ((2 * p : ℤ) * m' + ((d : ℕ) : ℤ))) := rfl
  have hpne : (p : ℝ) ≠ 0 := hp'.ne'
  rw [hres, hgrid]
  unfold hFinalP
  rw [if_pos (show (4 * ((p : ℤ) * n' + ((e : ℕ) : ℤ)) + 1) % 4 = 1 from by
    generalize (p : ℤ) * n' + ((e : ℕ) : ℤ) = K
    omega)]
  show 8 * (p : ℂ) * ((4 * ((p : ℤ) * n' + ((e : ℕ) : ℤ)) + 1 : ℤ) : ℂ) *
      cs4 (2 * ((2 * p : ℤ) * m' + ((d : ℕ) : ℤ))) * _ * _ = _
  rw [cs4_grid p m' (d : ℕ), XP_grid p n' m' (e : ℕ) (d : ℕ),
    envF_grid p hp y n' m' (e : ℕ) (d : ℕ)]
  unfold wP primalT oddT evenT
  have hpcne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexpand : ((4 * ((p : ℤ) * n' + ((e : ℕ) : ℤ)) + 1 : ℤ) : ℂ)
      = 4 * (p : ℂ) * (((n' : ℝ) + (4 * ((e : ℕ) : ℝ) + 1) / (4 * p) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [hexpand]
  push_cast
  ring

/-- Fin-indexed grid sums are range-indexed grid sums. -/
private lemma fin_grid_to_range (p : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ e : Fin p, ∑ d : Fin (2 * p), F (e : ℕ) (d : ℕ)
      = ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), F e d := by
  calc ∑ e : Fin p, ∑ d : Fin (2 * p), F (e : ℕ) (d : ℕ)
      = ∑ e : Fin p, ∑ d ∈ Finset.range (2 * p), F (e : ℕ) d :=
        Finset.sum_congr rfl fun e _ =>
          Fin.sum_univ_eq_sum_range (fun d => F (e : ℕ) d) (2 * p)
    _ = ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), F e d :=
        Fin.sum_univ_eq_sum_range (fun e => ∑ d ∈ Finset.range (2 * p), F e d) p

/-- The primal side: the gathered target equals `32p²·χ_p(2)` times the grid-weighted
`oddKernel`–`evenKernel` products at scale `32p²y`. -/
lemma primal_side_eq (p : ℕ) [Fact p.Prime] (hp : 0 < p) {y : ℝ} (hy : 0 < y) :
    ∑' q : ℤ × ℤ, hFinalP p y q
      = 32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ) *
          ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
            ((wP p e d : ℤ) : ℂ) *
              (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                  (32 * p ^ 2 * y) : ℝ) : ℂ) *
               ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                  (32 * p ^ 2 * y) : ℝ) : ℂ)) := by
  rw [← tsum_gridEmb_eq_hFinalP p y]
  rw [← (resEquivP p hp).tsum_eq (fun q => hFinalP p y (gridEmb q))]
  have hsum : Summable fun x : (Fin p × Fin (2 * p)) × (ℤ × ℤ) =>
      hFinalP p y (gridEmb (resEquivP p hp x)) := by
    rw [show (fun x : (Fin p × Fin (2 * p)) × (ℤ × ℤ) =>
        hFinalP p y (gridEmb (resEquivP p hp x)))
        = ((hFinalP p y ∘ gridEmb) ∘ resEquivP p hp) from rfl]
    rw [(resEquivP p hp).summable_iff]
    exact (gridEmb_injective.summable_iff (hFinalP_support p y)).mpr
      (summable_hFinalP p hy)
  rw [hsum.tsum_prod' hsum.prod_factor, tsum_fintype]
  rw [Fintype.sum_prod_type]
  have hout : ∀ e : Fin p, ∀ d : Fin (2 * p),
      ∑' q : ℤ × ℤ, hFinalP p y (gridEmb (resEquivP p hp ((e, d), q)))
        = 32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ) * (((wP p (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
            (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ) *
             ((evenKernel ((((d : ℕ) : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ))) := by
    intro e d
    rw [tsum_congr fun q => hFinalP_land p hp y e d q]
    rw [tsum_mul_left, oddK_evenK_product p hp hy (e : ℕ) (d : ℕ)]
    ring
  rw [Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => hout e d]
  have hpull : ∑ e : Fin p, ∑ d : Fin (2 * p),
      (32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ)) * (((wP p (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
        (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ) *
         ((evenKernel ((((d : ℕ) : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ)))
      = (32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ)) * ∑ e : Fin p, ∑ d : Fin (2 * p),
          ((wP p (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
            (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ) *
             ((evenKernel ((((d : ℕ) : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hpull]
  congr 1
  exact fin_grid_to_range p (fun e d =>
    ((wP p e d : ℤ) : ℂ) *
      (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
          (32 * p ^ 2 * y) : ℝ) : ℂ) *
       ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
          (32 * p ^ 2 * y) : ℝ) : ℂ)))

/-! ## 9. The family duplication identity -/

set_option maxHeartbeats 1000000 in
/-- **THE FAMILY DUPLICATION IDENTITY.**  At every prime `p ≡ 1 (mod 4)`, the `2p²`
weighted `sinKernel`–`cosKernel` products at scale `y` equal `32p²·χ_p(2)` times the
`2p²` weighted `oddKernel`–`evenKernel` products at scale `32p²y`.  The phases
collapse through the family eigen-identity, the lattice folds exactly as at level one,
and the fold deposits the **family sign `χ_p(2)`** — the root number dial of the
congruent-number family, with the modulus a parameter. -/
theorem theFamilyDuplicationIdentity (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {y : ℝ} (hy : 0 < y) :
    ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
        (wP p e d : ℝ) *
          (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle) y *
           cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) y)
      = ((-1 : ℝ)) ^ ((p - 1) / 2) * (32 * (p : ℝ) ^ 2 * ((XP p 2 : ℤ) : ℝ)) *
          ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
            (wP p e d : ℝ) *
              (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                  (32 * p ^ 2 * y) *
               evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (32 * p ^ 2 * y)) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨k, hpk⟩ : ∃ k : ℕ, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  have hk2 : (p - 1) / 2 = k := by omega
  have hC : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
        ((wP p e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
      = ((-1 : ℂ)) ^ k * (32 * (p : ℂ) ^ 2 * ((XP p 2 : ℤ) : ℂ)) *
          ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
            ((wP p e d : ℤ) : ℂ) *
              (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                  (32 * p ^ 2 * y) : ℝ) : ℂ) *
               ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                  (32 * p ^ 2 * y) : ℝ) : ℂ)) := by
    rw [dual_side_eq p hp2 hy, tsum_dualP_eq_hFinalP p hpk hy, primal_side_eq p hp0 hy]
    ring
  rw [hk2]
  exact_mod_cast hC
