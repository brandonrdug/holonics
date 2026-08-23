import ElementaryHolonics.Millennium.FamilyThetaFE
import ElementaryHolonics.Millennium.FiveWitness
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# FamilyWitness: the analytic datum at every split prime

**The welding deed of the family campaign.**  The twisted coefficient stream
`c^p_m = χ_p(m)·c_m` inherits every Euler law from the Gaussian-integer structure at
one; quadratic reciprocity (`p ≡ 1 mod 4`) turns the family twist law
`a_q(E_p) = (p|q)·a_q(E₁)` into the identification `c^p_q = a_q(E_p)` at every good
prime; and the Mellin machinery returns the L-function of the sign-`χ_p(2)` family
theta as the Dirichlet series of that stream.

* **`theTraceTwistLawAtEveryModulus`** — `a_q(E_n) = (n|q)·a_q(E₁)` for `q ∤ 2n`:
  one substitution inside the character sum, no modularity input, `n` arbitrary.
* **`theWitnessAtEverySplitPrime : LDatum p`** — every field kernel-checked, at
  every prime `p ≡ 1 (mod 4)` at once.  **The posed Birch–Swinnerton-Dyer
  conjecture is well-posed with a kernel-checked witness across the family.**
* **`theCentralValueVanishesOnTheFiveModEightBranch`** — `L_p(1) = 0` for every
  prime `p ≡ 5 (mod 8)`.
* **`theAnalyticRankIsPositiveOnTheFiveModEightBranch`** — the analytic rank of the
  family witness is nonzero on the whole `p ≡ 5 (mod 8)` branch: the analytic side
  of the conjecture's rank clause predicts, family-wise, that every such `p` is a
  congruent number.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyWitness

open Real Complex
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.FamilyDuplication
open Soma.Holonics.Millennium.FamilyThetaFE
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.HeckeEuler
open Soma.Holonics.Millennium.GaussCoefficient

/-! ## 1. The family twist law -/

/-- **THE TRACE TWIST LAW AT EVERY MODULUS**: for every twist `n` and every odd prime
`q ∤ n`, the trace at `n` is the quadratic character of `n` times the trace at one —
the substitution `x ↦ nx` inside the character sum, with the modulus a parameter and
no modularity input. -/
theorem theTraceTwistLawAtEveryModulus (n : ℕ) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqn : ¬ q ∣ n) :
    traceOfFrobenius n q
      = quadraticChar (ZMod q) ((n : ℕ) : ZMod q) * traceOfFrobenius 1 q := by
  have hn0 : ((n : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqn
  rw [Soma.Holonics.Millennium.FiveTwist.trace_eq_neg_charSum n hq2,
    Soma.Holonics.Millennium.FiveTwist.trace_eq_neg_charSum 1 hq2]
  have hsub : ∑ x : ZMod q, quadraticChar (ZMod q) (x ^ 3 - ((n : ℕ) : ZMod q) ^ 2 * x)
      = quadraticChar (ZMod q) ((n : ℕ) : ZMod q) *
        ∑ u : ZMod q, quadraticChar (ZMod q) (u ^ 3 - ((1 : ℕ) : ZMod q) ^ 2 * u) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ ((n : ℕ) : ZMod q) hn0)
      (fun x => quadraticChar (ZMod q) (x ^ 3 - ((n : ℕ) : ZMod q) ^ 2 * x))]
    refine Finset.sum_congr rfl fun u _ => ?_
    show quadraticChar (ZMod q) ((((n : ℕ) : ZMod q) * u) ^ 3
        - ((n : ℕ) : ZMod q) ^ 2 * (((n : ℕ) : ZMod q) * u)) = _
    have hfac : (((n : ℕ) : ZMod q) * u) ^ 3
        - ((n : ℕ) : ZMod q) ^ 2 * (((n : ℕ) : ZMod q) * u)
        = ((n : ℕ) : ZMod q) ^ 2 * (((n : ℕ) : ZMod q) * (u ^ 3 - ((1 : ℕ) : ZMod q) ^ 2 * u)) := by
      push_cast
      ring
    rw [hfac, map_mul, quadraticChar_sq_one' hn0, one_mul, map_mul]
  rw [hsub]
  ring

/-! ## 2. The family coefficient stream -/

/-- The Dirichlet coefficients at the split prime `p`: the mod-`p` character times the
stream at one. -/
def pCoeff (p : ℕ) [Fact p.Prime] (m : ℕ) : ℤ := XP p (m : ℤ) * heckeCoeff m

lemma pCoeff_zero (p : ℕ) [Fact p.Prime] : pCoeff p 0 = 0 := by
  unfold pCoeff
  rw [heckeCoeff_zero, mul_zero]

lemma pCoeff_one (p : ℕ) [Fact p.Prime] : pCoeff p 1 = 1 := by
  unfold pCoeff
  rw [heckeCoeff_one]
  have h1 : XP p ((1 : ℕ) : ℤ) = 1 := by
    unfold XP
    norm_num
  rw [h1]
  ring

lemma pCoeff_abs_le (p : ℕ) [Fact p.Prime] (m : ℕ) :
    |pCoeff p m| ≤ 9 * (m : ℤ) ^ 2 := by
  unfold pCoeff
  rw [abs_mul]
  have h1 := XP_abs_le p ((m : ℕ) : ℤ)
  have h2 := heckeCoeff_abs_le m
  have h3 := abs_nonneg (heckeCoeff m)
  nlinarith

private lemma XP_natCast_mul (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    XP p ((a * b : ℕ) : ℤ) = XP p (a : ℤ) * XP p (b : ℤ) := by
  rw [show ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) from by push_cast; ring, XP_mul]

lemma pCoeff_mul (p : ℕ) [Fact p.Prime] {a b : ℕ} (hab : Nat.Coprime a b) :
    pCoeff p (a * b) = pCoeff p a * pCoeff p b := by
  unfold pCoeff
  rw [XP_natCast_mul, heckeCoeff_mul hab]
  ring

private lemma XP_sq_of_not_dvd (p : ℕ) [Fact p.Prime] {q : ℕ} (h : ¬ p ∣ q) :
    XP p (q : ℤ) * XP p (q : ℤ) = 1 := by
  have hq0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h
  unfold XP
  rw [show ((q : ℤ) : ZMod p) = ((q : ℕ) : ZMod p) from by push_cast; rfl]
  have := quadraticChar_sq_one hq0
  rw [pow_two] at this
  exact this

/-- The Euler recursion transports to the twist at every good prime. -/
lemma pCoeff_prime_pow (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hqp : q ≠ p) (k : ℕ) :
    pCoeff p (q ^ (k + 2))
      = pCoeff p q * pCoeff p (q ^ (k + 1)) - (q : ℤ) * pCoeff p (q ^ k) := by
  have hrec := heckeCoeff_prime_pow_recursion (p := q) hq2 k
  have hnd : ¬ p ∣ q := by
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  have hpowchi : ∀ j : ℕ, XP p ((q ^ j : ℕ) : ℤ) = XP p ((q : ℕ) : ℤ) ^ j := by
    intro j
    induction j with
    | zero =>
        simp only [pow_zero]
        unfold XP
        norm_num
    | succ n ih =>
        rw [pow_succ, XP_natCast_mul, ih, pow_succ]
  unfold pCoeff
  rw [hpowchi (k + 2), hpowchi (k + 1), hpowchi k]
  have hsq := XP_sq_of_not_dvd p hnd
  have hstep : XP p ((q : ℕ) : ℤ) ^ (k + 2) = XP p ((q : ℕ) : ℤ) ^ k := by
    rw [pow_add, pow_two, hsq, mul_one]
  rw [hstep]
  have hstep1 : XP p ((q : ℕ) : ℤ) * XP p ((q : ℕ) : ℤ) ^ (k + 1)
      = XP p ((q : ℕ) : ℤ) ^ k := by
    rw [pow_succ]
    calc XP p ((q : ℕ) : ℤ) * (XP p ((q : ℕ) : ℤ) ^ k * XP p ((q : ℕ) : ℤ))
        = XP p ((q : ℕ) : ℤ) ^ k * (XP p ((q : ℕ) : ℤ) * XP p ((q : ℕ) : ℤ)) := by ring
      _ = XP p ((q : ℕ) : ℤ) ^ k := by rw [hsq, mul_one]
  linear_combination (heckeCoeff q * heckeCoeff (q ^ (k + 1))) * hstep1
    + XP p ((q : ℕ) : ℤ) ^ k * hrec
    - (2 * heckeCoeff q * heckeCoeff (q ^ (k + 1)) * XP p ((q : ℕ) : ℤ) ^ k) * hsq

/-- The bad-prime clause: two dies on the even shells, `p` dies on the character. -/
lemma pCoeff_bad (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ 2 * p) (k : ℕ) :
    pCoeff p (q ^ (k + 1)) = pCoeff p q ^ (k + 1) := by
  have hq2p : q = 2 ∨ q = p := by
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h)
  rcases hq2p with rfl | hqp'
  · unfold pCoeff
    rw [heckeCoeff_even (by simp [Nat.pow_mod]), heckeCoeff_even (by norm_num),
      mul_zero, mul_zero, zero_pow (by omega : k + 1 ≠ 0)]
  · rw [hqp']
    unfold pCoeff
    have hz : ∀ j : ℕ, 1 ≤ j → XP p ((p ^ j : ℕ) : ℤ) = 0 := by
      intro j hj
      unfold XP
      rw [show (((p ^ j : ℕ) : ℤ) : ZMod p) = (((p ^ j : ℕ) : ℕ) : ZMod p) from by
        push_cast; rfl]
      rw [show (((p ^ j : ℕ) : ℕ) : ZMod p) = 0 from by
        rw [ZMod.natCast_eq_zero_iff]
        exact dvd_pow_self p (by omega)]
      exact MulChar.map_zero _
    rw [hz (k + 1) (by omega),
      show XP p (((p : ℕ) : ℕ) : ℤ) = 0 from by
        have := hz 1 le_rfl
        rwa [pow_one] at this,
      zero_mul, zero_mul, zero_pow (by omega : k + 1 ≠ 0)]

/-! ## 3. The coefficient identification at the good primes -/

/-- **The coefficient identification at every good prime**: the twisted stream is the
point-count stream of the `p`-curve, by Gauss's theorem at one, the family twist law,
and quadratic reciprocity (`p ≡ 1 mod 4`). -/
theorem pCoeff_prime (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p) :
    pCoeff p q = traceOfFrobenius p q := by
  have hqnd : ¬ q ∣ p := by
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h)
  have htwist := theTraceTwistLawAtEveryModulus p (q := q) hq2 hqnd
  have hone : (heckeCoeff q : ℤ) = traceOfFrobenius 1 q :=
    theCoefficientsAgreeAtEveryOddPrime (p := q) hq2
  have hrec : legendreSym q (p : ℤ) = legendreSym p (q : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four hp1 hq2
  have hXleg : XP p ((q : ℕ) : ℤ) = legendreSym p (q : ℤ) := rfl
  have hlegq : legendreSym q (p : ℤ) = quadraticChar (ZMod q) ((p : ℕ) : ZMod q) := by
    show quadraticChar (ZMod q) (((p : ℤ) : ZMod q)) = _
    norm_num
  unfold pCoeff
  rw [hone, hXleg, ← hrec, hlegq, htwist]

/-! ## 4. The L-function at the split prime -/

/-- The L-function of the `p`-curve: the completed function with its archimedean
factor removed.  Entire, because `1/Γ` is entire. -/
def pL (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) (s : ℂ) : ℂ :=
  ((Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi)) ^ (-s) * (Complex.Gamma s)⁻¹ *
    lambdaP p hp1 s

private lemma sqrt_conductor (p : ℕ) (hp0 : 0 < p) :
    Real.sqrt (32 * (p : ℝ) ^ 2) = 4 * p * Real.sqrt 2 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [show (32 : ℝ) * (p : ℝ) ^ 2 = (4 * p) ^ 2 * 2 from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private lemma base_ne_zero (p : ℕ) [Fact p.Prime] :
    ((Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi)) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply div_ne_zero
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    refine (Real.sqrt_pos.mpr ?_).ne'
    positivity
  · simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by norm_num, by simp only [Complex.ofReal_eq_zero]; exact Real.pi_ne_zero⟩

/-- **The L-function is entire at every split prime.** -/
theorem theLFunctionIsEntireAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) : Differentiable ℂ (pL p hp1) := by
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact fun s => (differentiableAt_id.neg.const_cpow (Or.inl (base_ne_zero p)))
    · exact Complex.differentiable_one_div_Gamma
  · exact theCompletedLFunctionIsEntireAtEverySplitPrime p hp1

/-- **The product chart agrees with the completed function** away from the `Γ`
poles. -/
theorem theCompletedProductFormulaHoldsAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    completed (32 * p ^ 2) (pL p hp1) s = lambdaP p hp1 s := by
  unfold completed pL
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (by exact_mod_cast hs)
  have hb : ((Real.sqrt ((32 * p ^ 2 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ≠ 0 := by
    have := base_ne_zero p
    push_cast at this ⊢
    exact this
  have hpow : ((Real.sqrt ((32 * p ^ 2 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]
    exact Complex.exp_ne_zero _
  have hcast : ((Real.sqrt ((32 * p ^ 2 : ℕ) : ℝ) : ℂ) / (2 * Real.pi))
      = ((Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi)) := by
    push_cast
    rfl
  rw [hcast] at hpow hb ⊢
  rw [Complex.cpow_neg]
  field_simp

/-! ## 5. The Dirichlet series agreement -/

/-- The exponential rate of the family theta: `2π/√(32p²) = π√2/(4p)`. -/
def alP (p : ℕ) : ℝ := π * Real.sqrt 2 / (4 * p)

lemma alP_pos (p : ℕ) (hp0 : 0 < p) : 0 < alP p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have h1 := Real.pi_pos
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold alP
  positivity

private def latticeNorm (q : ℤ × ℤ) : ℕ := (q.1 ^ 2 + q.2 ^ 2).toNat

private lemma latticeNorm_eq_iff {q : ℤ × ℤ} {m : ℕ} :
    latticeNorm q = m ↔ q.1 ^ 2 + q.2 ^ 2 = (m : ℤ) := by
  unfold latticeNorm
  have h1 : (0 : ℤ) ≤ q.1 ^ 2 + q.2 ^ 2 := by positivity
  omega

private lemma norm_shell_bound {m : ℕ} {a b : ℤ} (h : a ^ 2 + b ^ 2 = (m : ℤ)) :
    -(m : ℤ) ≤ a ∧ a ≤ (m : ℤ) ∧ -(m : ℤ) ≤ b ∧ b ≤ (m : ℤ) := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + m), sq_nonneg (a - m),
      sq_nonneg (b + m), sq_nonneg (b - m)]

/-- The twisted class-sum term family, at scale `y`. -/
private def clsTermP (p : ℕ) [Fact p.Prime] (y : ℝ) (q : ℤ × ℤ) : ℂ :=
  if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
    ((q.1 : ℤ) : ℂ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℂ) *
      ((rexp (-2 * π * y * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) : ℝ) : ℂ)
  else 0

/-- The fiber sum: the character is constant on the shell, so the weights collect
into `pCoeff p m`. -/
private lemma fiber_hasSumP (p : ℕ) [Fact p.Prime] (y : ℝ) (m : ℕ) :
    HasSum (fun c : {q : ℤ × ℤ // latticeNorm q = m} => clsTermP p y (c : ℤ × ℤ))
      (((pCoeff p m : ℤ) : ℂ) * ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ)) := by
  classical
  refine (hasSum_subtype_iff_indicator
    (s := {q : ℤ × ℤ | latticeNorm q = m}) (f := clsTermP p y)).mpr ?_
  have hvanish : ∀ q : ℤ × ℤ,
      q ∉ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))) →
      Set.indicator {r : ℤ × ℤ | latticeNorm r = m} (clsTermP p y) q = 0 := by
    rintro ⟨a, b⟩ hq
    by_cases hmem : latticeNorm (a, b) = m
    · exfalso
      apply hq
      have hb := norm_shell_bound (latticeNorm_eq_iff.mp hmem)
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hb.1, hb.2.1⟩, ⟨hb.2.2.1, hb.2.2.2⟩⟩
    · exact Set.indicator_of_notMem (s := {r : ℤ × ℤ | latticeNorm r = m}) hmem
        (clsTermP p y)
  have hval : ∑ q ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))),
      Set.indicator {r : ℤ × ℤ | latticeNorm r = m} (clsTermP p y) q
      = ((pCoeff p m : ℤ) : ℂ) * ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ) := by
    have hterm : ∀ q ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
        (Finset.Icc (-(m : ℤ)) (m : ℤ))),
        Set.indicator {r : ℤ × ℤ | latticeNorm r = m} (clsTermP p y) q
        = (if q.1 ^ 2 + q.2 ^ 2 = (m : ℤ) ∧ (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
            then ((q.1 : ℤ) : ℂ) else 0) * ((XP p ((m : ℕ) : ℤ) : ℤ) : ℂ) *
            ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ) := by
      rintro ⟨a, b⟩ -
      rw [Set.indicator_apply]
      by_cases hnorm : latticeNorm (a, b) = m
      · rw [if_pos (show (a, b) ∈ {r : ℤ × ℤ | latticeNorm r = m} from hnorm)]
        have hnorm' := latticeNorm_eq_iff.mp hnorm
        simp only [clsTermP]
        by_cases hclass : ((a + b) % 4 = 1 ∧ b % 2 = 0)
        · rw [if_pos hclass, if_pos ⟨hnorm', hclass.1, hclass.2⟩]
          have hchi : XP p (a ^ 2 + b ^ 2) = XP p ((m : ℕ) : ℤ) := by
            rw [hnorm']
          have henv : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) = (m : ℝ) := by
            exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hnorm'
          rw [hchi, henv]
        · rw [if_neg hclass, if_neg (by tauto)]
          ring
      · have hnorm' : ¬(a ^ 2 + b ^ 2 = (m : ℤ)) := fun hc =>
          hnorm (latticeNorm_eq_iff.mpr hc)
        rw [if_neg (show (a, b) ∉ {r : ℤ × ℤ | latticeNorm r = m} from hnorm),
          if_neg (by tauto)]
        ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hcoeff : ∑ q ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
        (Finset.Icc (-(m : ℤ)) (m : ℤ))),
        (if q.1 ^ 2 + q.2 ^ 2 = (m : ℤ) ∧ (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0
          then ((q.1 : ℤ) : ℂ) else 0) = ((heckeCoeff m : ℤ) : ℂ) := by
      rw [heckeCoeff, heckeShell, Finset.sum_filter]
      push_cast
      rfl
    rw [hcoeff]
    unfold pCoeff
    push_cast
    ring
  rw [← hval]
  exact hasSum_sum_of_ne_finset_zero hvanish

set_option maxHeartbeats 1000000 in
/-- **The family theta is its Dirichlet series**, with the twisted computable integer
coefficients, at every split prime. -/
theorem theFamilyThetaIsItsDirichletSeries (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    {x : ℝ} (hx : 0 < x) :
    HasSum (fun m : ℕ => ((pCoeff p m : ℤ) : ℂ) *
      ((rexp (-2 * π * (Real.sqrt 2 * x / (8 * p)) * (m : ℝ)) : ℝ) : ℂ))
      ((thetaP p x : ℝ) : ℂ) := by
  have hcls : HasSum (clsTermP p (Real.sqrt 2 * x / (8 * p)))
      ((thetaP p x : ℝ) : ℂ) :=
    theFamilyThetaIsTheTwistedClassSum p hp1 hx
  have hσ : HasSum (fun q : Σ m : ℕ, {r : ℤ × ℤ // latticeNorm r = m} =>
      clsTermP p (Real.sqrt 2 * x / (8 * p)) ((Equiv.sigmaFiberEquiv latticeNorm) q))
      ((thetaP p x : ℝ) : ℂ) :=
    ((Equiv.sigmaFiberEquiv latticeNorm).hasSum_iff).mpr hcls
  exact hσ.sigma fun m => fiber_hasSumP p (Real.sqrt 2 * x / (8 * p)) m

/-- The theta's Dirichlet expansion in the exponential form: the rate is `alP p`. -/
private lemma thetaP_hasSum_exp (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    HasSum (fun m : ℕ => ((pCoeff p m : ℤ) : ℂ) * rexp (-(alP p * m) * t))
      ((thetaP p t : ℝ) : ℂ) := by
  have h := theFamilyThetaIsItsDirichletSeries p hp1 (Set.mem_Ioi.mp ht)
  have hfun : (fun m : ℕ => ((pCoeff p m : ℤ) : ℂ) *
      ((rexp (-2 * π * (Real.sqrt 2 * t / (8 * p)) * (m : ℝ)) : ℝ) : ℂ))
      = fun m : ℕ => ((pCoeff p m : ℤ) : ℂ) * rexp (-(alP p * m) * t) := by
    funext m
    congr 2
    unfold alP
    push_cast
    ring
  rwa [hfun] at h

/-- The summability input on the half-plane. -/
private lemma dirichlet_summableP (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 3 < s.re) :
    Summable fun m : ℕ => ‖((pCoeff p m : ℤ) : ℂ)‖ / (alP p * m) ^ s.re := by
  have hp : p.Prime := Fact.out
  have hC := alP_pos p hp.pos
  set σ : ℝ := s.re with hσ
  set C : ℝ := alP p with hC_def
  have hmaj : Summable fun m : ℕ => (9 / C ^ σ) * ((m : ℝ) ^ ((2 : ℝ) - σ)) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show ((pCoeff p 0 : ℤ) : ℂ) = 0 from by rw [pCoeff_zero]; norm_num]
    simp only [norm_zero, Nat.cast_zero, zero_div]
    positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm : ‖((pCoeff p m : ℤ) : ℂ)‖ ≤ 9 * (m : ℝ) ^ 2 := by
    rw [show ((pCoeff p m : ℤ) : ℂ) = (((pCoeff p m : ℤ) : ℝ) : ℂ) from by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    have h1 := pCoeff_abs_le p m
    have h2 : |((pCoeff p m : ℤ) : ℝ)| ≤ ((9 * (m : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hpow : (C * m) ^ σ = C ^ σ * (m : ℝ) ^ σ :=
    Real.mul_rpow hC.le hm0.le
  have hexp : (m : ℝ) ^ ((2 : ℝ) - σ) = (m : ℝ) ^ 2 / (m : ℝ) ^ σ := by
    rw [Real.rpow_sub hm0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [hpow, hexp, show 9 / C ^ σ * ((m : ℝ) ^ 2 / (m : ℝ) ^ σ)
      = 9 * (m : ℝ) ^ 2 / (C ^ σ * (m : ℝ) ^ σ) from div_mul_div_comm 9 (C ^ σ) _ _]
  gcongr

set_option maxHeartbeats 1000000 in
/-- **The L-function agrees with the Dirichlet series of its twisted coefficients**
on the half-plane `re s > 3`, at every split prime. -/
theorem theLFunctionAgreesWithItsDirichletSeriesAtEverySplitPrime
    (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) {s : ℂ} (hs : 3 < s.re) :
    pL p hp1 s = LSeries (fun m => ((pCoeff p m : ℤ) : ℂ)) s := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : 0 < s.re := by linarith
  have hC := alP_pos p hp.pos
  set C : ℝ := alP p with hC_def
  have hmel : HasSum (fun m : ℕ => Complex.Gamma s * ((pCoeff p m : ℤ) : ℂ) /
      ((C * m : ℝ) : ℂ) ^ s)
      (mellin (Complex.ofReal ∘ thetaP p) s) := by
    refine hasSum_mellin (fun m => ?_) hs0 (fun t ht => thetaP_hasSum_exp p hp1 ht)
      (dirichlet_summableP p hs)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      rw [pCoeff_zero]
      norm_num
    · right
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
  have hΛ : mellin (Complex.ofReal ∘ thetaP p) s = lambdaP p hp1 s :=
    (theCompletedLFunctionHasMellinAtEverySplitPrime p hp1 s).2
  rw [hΛ] at hmel
  have hG : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have htsum : lambdaP p hp1 s = Complex.Gamma s *
      ∑' m : ℕ, ((pCoeff p m : ℤ) : ℂ) / ((C * m : ℝ) : ℂ) ^ s := by
    rw [← tsum_mul_left, ← hmel.tsum_eq]
    exact tsum_congr fun m => by ring
  have hterm : ∀ m : ℕ, ((pCoeff p m : ℤ) : ℂ) / ((C * m : ℝ) : ℂ) ^ s
      = ((((C : ℝ)) : ℂ) ^ s)⁻¹ *
          LSeries.term (fun m => ((pCoeff p m : ℤ) : ℂ)) s m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [LSeries.term_zero, show ((pCoeff p 0 : ℤ) : ℂ) = 0 from by
        rw [pCoeff_zero]; norm_num]
      norm_num
    · rw [LSeries.term_of_ne_zero (by omega : m ≠ 0)]
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hsplit : ((C * m : ℝ) : ℂ) ^ s
          = ((C : ℝ) : ℂ) ^ s * ((m : ℝ) : ℂ) ^ s := by
        rw [Complex.ofReal_mul]
        exact Complex.mul_cpow_ofReal_nonneg hC.le hm0.le s
      rw [hsplit]
      have hCs : ((C : ℝ) : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hC.ne')]
        exact Complex.exp_ne_zero _
      have hms : ((m : ℝ) : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne')]
        exact Complex.exp_ne_zero _
      rw [show (((m : ℝ) : ℂ)) = ((m : ℕ) : ℂ) from by push_cast; rfl] at hsplit hms ⊢
      field_simp
  have hfinal : lambdaP p hp1 s = Complex.Gamma s *
      (((((C : ℝ)) : ℂ) ^ s)⁻¹ *
        LSeries (fun m => ((pCoeff p m : ℤ) : ℂ)) s) := by
    rw [htsum, tsum_congr hterm, tsum_mul_left]
    rfl
  have hb0 : (0 : ℝ) < Real.sqrt (32 * p ^ 2) / (2 * π) := by
    have h1 := Real.pi_pos
    have h2 : (0 : ℝ) < Real.sqrt (32 * p ^ 2) := by
      refine Real.sqrt_pos.mpr ?_
      positivity
    positivity
  have hbase : ((Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi))
      = (((Real.sqrt (32 * p ^ 2) / (2 * π) : ℝ)) : ℂ) := by
    push_cast
    rfl
  have hcancel : (Real.sqrt (32 * p ^ 2) / (2 * π) : ℝ) * C = 1 := by
    rw [show Real.sqrt (32 * (p : ℝ) ^ 2) = 4 * p * Real.sqrt 2 from
      sqrt_conductor p hp.pos, hC_def]
    unfold alP
    have h1 := Real.pi_pos
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linear_combination hss
  have hkey : ((Real.sqrt (32 * p ^ 2) : ℂ) / (2 * Real.pi)) ^ (-s) *
      ((((C : ℝ)) : ℂ) ^ s)⁻¹ = 1 := by
    rw [hbase, Complex.cpow_neg, ← mul_inv,
      ← Complex.mul_cpow_ofReal_nonneg hb0.le hC.le, ← Complex.ofReal_mul, hcancel]
    simp
  have hGinv : (Complex.Gamma s)⁻¹ * Complex.Gamma s = 1 := inv_mul_cancel₀ hG
  unfold pL
  rw [hfinal]
  linear_combination (LSeries (fun m => ((pCoeff p m : ℤ) : ℂ)) s *
      ((Complex.Gamma s)⁻¹ * Complex.Gamma s)) * hkey
    + LSeries (fun m => ((pCoeff p m : ℤ) : ℂ)) s * hGinv

/-! ## 6. The witness at every split prime -/

private lemma XP_two_pm (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) :
    XP p 2 = 1 ∨ XP p 2 = -1 := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have := Int.le_of_dvd (by norm_num) h
    omega
  rcases (quadraticChar_isQuadratic (ZMod p)) (((2 : ℤ) : ZMod p)) with h | h | h
  · exact absurd (quadraticChar_eq_zero_iff.mp h) h20
  · exact Or.inl h
  · exact Or.inr h

set_option maxHeartbeats 1000000 in
/-- **THE WITNESS AT EVERY SPLIT PRIME**: the analytic datum of the congruent-number
curve at every prime `p ≡ 1 (mod 4)` at once.  Every field is kernel-checked: the
coefficients are the twisted computable shell sums, their prime values are the point
counts of the `p`-curve (Gauss, the family twist law, and quadratic reciprocity),
their Euler structure transports from the Gaussian-integer factorization, the
L-function is the Mellin transform of the sign-`χ_p(2)` family theta, and the
functional equation carries the second-supplement sign.  **The posed
Birch–Swinnerton-Dyer conjecture is well-posed with a kernel-checked witness across
the family.** -/
noncomputable def theWitnessAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) : LDatum p where
  coeff := fun m => ((pCoeff p m : ℤ) : ℂ)
  coeff_one := by
    rw [pCoeff_one]
    norm_num
  coeff_prime := fun q hq hqd => by
    haveI : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      intro h
      exact hqd ⟨p, by rw [h]⟩
    have hqp : q ≠ p := by
      intro h
      exact hqd ⟨2, by rw [h]; ring⟩
    have h := pCoeff_prime p hp1 q hq2 hqp
    exact_mod_cast h
  coeff_mul := fun a b hab => by
    have h := pCoeff_mul p hab
    exact_mod_cast h
  coeff_prime_pow := fun q k hq hqd => by
    haveI : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      intro h
      exact hqd ⟨p, by rw [h]⟩
    have hqp : q ≠ p := by
      intro h
      exact hqd ⟨2, by rw [h]; ring⟩
    have h := pCoeff_prime_pow p (q := q) hq2 hqp k
    exact_mod_cast h
  coeff_bad := fun q k hq hqd => by
    have hp : p.Prime := Fact.out
    have hp2 : p ≠ 2 := by
      have hp5 : 5 ≤ p := by have := hp.two_le; omega
      omega
    have h := pCoeff_bad p hp2 hq hqd k
    exact_mod_cast h
  L := pL p hp1
  analytic := theLFunctionIsEntireAtEverySplitPrime p hp1
  agrees := fun s hs =>
    theLFunctionAgreesWithItsDirichletSeriesAtEverySplitPrime p hp1 hs
  conductor := 32 * p ^ 2
  conductor_pos := by
    have hp : p.Prime := Fact.out
    have := hp.pos
    positivity
  sign := XP p 2
  sign_pm := XP_two_pm p hp1
  Lambda := lambdaP p hp1
  Lambda_analytic := theCompletedLFunctionIsEntireAtEverySplitPrime p hp1
  Lambda_eq := fun s hs =>
    (theCompletedProductFormulaHoldsAtEverySplitPrime p hp1 s hs).symm
  functional_equation := fun s =>
    theCompletedFunctionalEquationAtEverySplitPrime p hp1 s

/-- **The pose is inhabited at every split prime.** -/
theorem theWitnessExistsAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) : Nonempty (LDatum p) :=
  ⟨theWitnessAtEverySplitPrime p hp1⟩

/-! ## 7. The central vanishing and the analytic rank on the five-mod-eight branch -/

/-- **The central value of the L-function vanishes at every prime `p ≡ 5 (mod 8)`.** -/
theorem theCentralValueVanishesOnTheFiveModEightBranch (p : ℕ) [Fact p.Prime]
    (hp8 : p % 8 = 5) :
    pL p (by omega) 1 = 0 := by
  unfold pL
  rw [theOddHandForcesTheCentralVanishingOnTheFiveModEightFamily p hp8]
  ring

/-- **THE ANALYTIC RANK IS POSITIVE ON THE `p ≡ 5 (mod 8)` BRANCH**: the analytic
rank of the family witness is nonzero at every prime `p ≡ 5 (mod 8)` — the analytic
side of the conjecture's rank clause predicts, family-wise, that every such prime is
a congruent number. -/
theorem theAnalyticRankIsPositiveOnTheFiveModEightBranch (p : ℕ) [Fact p.Prime]
    (hp8 : p % 8 = 5) :
    analyticRank (theWitnessAtEverySplitPrime p (by omega)) ≠ 0 := by
  have hp1 : p % 4 = 1 := by omega
  unfold analyticRank
  show analyticOrderAt (pL p (by omega)) 1 ≠ 0
  intro h0
  rw [analyticOrderAt_eq_zero] at h0
  rcases h0 with h | h
  · exact h ((theLFunctionIsEntireAtEverySplitPrime p (by omega)).analyticAt 1)
  · exact h (theCentralValueVanishesOnTheFiveModEightBranch p hp8)

end Soma.Holonics.Millennium.FamilyWitness

