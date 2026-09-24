import ElementaryHolonics.Millennium.FivePositivity
import ElementaryHolonics.Millennium.FiveTwist
import ElementaryHolonics.Millennium.HeckeWitness
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# FiveWitness: the analytic datum at five, and the rank-one coincidence

**The welding deed of the rank-one campaign.**  The twisted coefficient stream
`c⁵_m = χ₅(m)·c_m` inherits every Euler law from the Gaussian-integer structure at one;
quadratic reciprocity (`5 ≡ 1 mod 4`) turns the twist law `a_p(E₅) = (5|p)·a_p(E₁)`
into the identification `c⁵_p = a_p(E₅)` at every good prime; and the Mellin machinery
returns the L-function of the sign-`−1` theta as the Dirichlet series of that stream.

* **`theWitnessAtFive : LDatum 5`** — every field kernel-checked;
* **`theAnalyticRankAtFiveIsOne`** — `analyticOrderAt L₅ 1 = 1`, from `Λ₅(1) = 0` and
  `Λ₅′(1) ≠ 0` through `analyticOrderAt_deriv_add_one`;
* **`theRankOneCoincidenceAtFive`** — analytic rank exactly one, algebraic rank at
  least one: both sides of the coincidence formal, the upper descent bound the named
  successor.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveWitness

open Real Complex
open Soma.Holonics.Millennium.FiveTheta
open Soma.Holonics.Millennium.FiveDerivative
open Soma.Holonics.Millennium.FivePositivity
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.GaussCoefficient
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.HeckeWitness

/-! ## 1. The twisted coefficient stream -/

/-- The Dirichlet coefficients at five: the mod-five character times the stream at one. -/
def fiveCoeff (m : ℕ) : ℤ := chi5 (m : ℤ) * heckeCoeff m

lemma fiveCoeff_one : fiveCoeff 1 = 1 := by
  unfold fiveCoeff
  rw [heckeCoeff_one]
  decide

lemma fiveCoeff_abs_le (m : ℕ) : |fiveCoeff m| ≤ 9 * (m : ℤ) ^ 2 := by
  unfold fiveCoeff
  rw [abs_mul]
  have h1 := chi5_abs_le (m : ℤ)
  have h2 := heckeCoeff_abs_le m
  have h3 := abs_nonneg (heckeCoeff m)
  nlinarith

private lemma chi5_natCast_mul (a b : ℕ) :
    chi5 ((a * b : ℕ) : ℤ) = chi5 (a : ℤ) * chi5 (b : ℤ) := by
  rw [show ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) from by push_cast; ring, chi5_mul]

lemma fiveCoeff_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    fiveCoeff (a * b) = fiveCoeff a * fiveCoeff b := by
  unfold fiveCoeff
  rw [chi5_natCast_mul, Soma.Holonics.Millennium.HeckeEuler.heckeCoeff_mul hab]
  ring

private lemma chi5_sq_of_ne (m : ℤ) (h : m % 5 ≠ 0) : chi5 m * chi5 m = 1 := by
  have h5 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases h5 with h1 | h1 | h1 | h1 <;> simp [chi5, h1]

/-- The Euler recursion transports to the twist at every good prime. -/
lemma fiveCoeff_prime_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) (k : ℕ) :
    fiveCoeff (p ^ (k + 2))
      = fiveCoeff p * fiveCoeff (p ^ (k + 1)) - (p : ℤ) * fiveCoeff (p ^ k) := by
  have hrec := Soma.Holonics.Millennium.HeckeEuler.heckeCoeff_prime_pow_recursion
    (p := p) hp2 k
  have hchi_ne : (p : ℤ) % 5 ≠ 0 := by
    intro h
    have h5 : (5 : ℤ) ∣ (p : ℤ) := Int.dvd_of_emod_eq_zero h
    have h5' : (5 : ℕ) ∣ p := by exact_mod_cast h5
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) Fact.out).mp h5').symm
  have hpowchi : ∀ j : ℕ, chi5 ((p ^ j : ℕ) : ℤ) = chi5 ((p : ℕ) : ℤ) ^ j := by
    intro j
    induction j with
    | zero => simp; decide
    | succ n ih =>
        rw [pow_succ, chi5_natCast_mul, ih, pow_succ]
  unfold fiveCoeff
  rw [hpowchi (k + 2), hpowchi (k + 1), hpowchi k]
  have hsq := chi5_sq_of_ne (p : ℤ) hchi_ne
  have hstep : chi5 ((p : ℕ) : ℤ) ^ (k + 2) = chi5 ((p : ℕ) : ℤ) ^ k := by
    rw [show k + 2 = k + 2 from rfl, pow_add, pow_two, hsq, mul_one]
  rw [hstep]
  have hstep1 : chi5 ((p : ℕ) : ℤ) * chi5 ((p : ℕ) : ℤ) ^ (k + 1)
      = chi5 ((p : ℕ) : ℤ) ^ k := by
    rw [pow_succ]
    calc chi5 ((p : ℕ) : ℤ) * (chi5 ((p : ℕ) : ℤ) ^ k * chi5 ((p : ℕ) : ℤ))
        = chi5 ((p : ℕ) : ℤ) ^ k * (chi5 ((p : ℕ) : ℤ) * chi5 ((p : ℕ) : ℤ)) := by ring
      _ = chi5 ((p : ℕ) : ℤ) ^ k := by rw [hsq, mul_one]
  linear_combination (heckeCoeff p * heckeCoeff (p ^ (k + 1))) * hstep1
    + chi5 ((p : ℕ) : ℤ) ^ k * hrec
    - (2 * heckeCoeff p * heckeCoeff (p ^ (k + 1)) * chi5 ((p : ℕ) : ℤ) ^ k) * hsq

/-- The bad-prime clause at five: two dies on the even shells, five dies on the
character. -/
lemma fiveCoeff_bad {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 2 * 5) (k : ℕ) :
    fiveCoeff (p ^ (k + 1)) = fiveCoeff p ^ (k + 1) := by
  have hp25 : p = 2 ∨ p = 5 := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  rcases hp25 with rfl | rfl
  · unfold fiveCoeff
    rw [heckeCoeff_even (by simp [Nat.pow_mod]), heckeCoeff_even (by norm_num),
      mul_zero, mul_zero, zero_pow (by omega : k + 1 ≠ 0)]
  · unfold fiveCoeff
    have hz : ∀ j : ℕ, 1 ≤ j → chi5 ((5 ^ j : ℕ) : ℤ) = 0 := by
      intro j hj
      have h5 : ((5 ^ j : ℕ) : ℤ) % 5 = 0 := by
        have hdd : (5 : ℤ) ∣ ((5 ^ j : ℕ) : ℤ) := by
          have hnat : (5 : ℕ) ∣ 5 ^ j := dvd_pow_self 5 (by omega)
          exact_mod_cast hnat
        omega
      unfold chi5
      rw [if_pos h5]
    rw [hz (k + 1) (by omega),
      show chi5 (((5 : ℕ) : ℕ) : ℤ) = 0 from by decide,
      zero_mul, zero_mul, zero_pow (by omega : k + 1 ≠ 0)]

/-! ## 2. The coefficient identification at the good primes -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The mod-five character of an odd prime `q ≠ 5` is the Legendre symbol `(q|5)`. -/
private lemma chi5_eq_legendre (q : ℕ) [Fact q.Prime] (hq5 : q ≠ 5) :
    chi5 ((q : ℕ) : ℤ) = legendreSym 5 (q : ℤ) := by
  have hq0 : q % 5 ≠ 0 := by
    intro h
    exact hq5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) Fact.out).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
  have hleg : legendreSym 5 (q : ℤ) = quadraticChar (ZMod 5) (((q : ℤ) : ZMod 5)) := rfl
  have hzq : ((q : ℤ) : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := by
    push_cast
    rw [ZMod.natCast_mod]
  have hq' : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  rcases hq' with h | h | h | h <;>
  · rw [hleg, hzq, h]
    rw [show chi5 ((q : ℕ) : ℤ) = chi5 (((q % 5 : ℕ) : ℕ) : ℤ) from
      chi5_congr (by push_cast; omega), h]
    decide

/-- **The coefficient identification at every good prime**: the twisted stream is the
point-count stream of the five-curve, by Gauss's theorem at one, the twist law, and
quadratic reciprocity (`5 ≡ 1 mod 4`). -/
theorem fiveCoeff_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    fiveCoeff p = traceOfFrobenius 5 p := by
  have htwist := Soma.Holonics.Millennium.FiveTwist.theTraceTwistLaw (p := p) hp2 hp5
  have hone : (heckeCoeff p : ℤ) = traceOfFrobenius 1 p :=
    theCoefficientsAgreeAtEveryOddPrime (p := p) hp2
  have hrec : legendreSym p (5 : ℤ) = legendreSym 5 (p : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2
  have hlegp : legendreSym p (5 : ℤ) = quadraticChar (ZMod p) (5 : ZMod p) := by
    show quadraticChar (ZMod p) (((5 : ℤ) : ZMod p)) = quadraticChar (ZMod p) (5 : ZMod p)
    norm_num
  unfold fiveCoeff
  rw [hone, chi5_eq_legendre p hp5, ← hrec, hlegp, htwist]

/-! ## 3. The L-function at five -/

/-- The L-function of the five-curve: the completed function with its archimedean
factor removed.  Entire, because `1/Γ` is entire. -/
def fiveL (s : ℂ) : ℂ :=
  ((Real.sqrt 800 : ℂ) / (2 * Real.pi)) ^ (-s) * (Complex.Gamma s)⁻¹ * lambda5 s

private lemma base800_ne_zero : ((Real.sqrt 800 : ℂ) / (2 * Real.pi)) ≠ 0 := by
  apply div_ne_zero
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 800)).ne'
  · simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by norm_num, by simp only [Complex.ofReal_eq_zero]; exact Real.pi_ne_zero⟩

/-- **The L-function at five is entire.** -/
theorem theLFunctionAtFiveIsEntire : Differentiable ℂ fiveL := by
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact fun s => (differentiableAt_id.neg.const_cpow (Or.inl base800_ne_zero))
    · exact Complex.differentiable_one_div_Gamma
  · exact theCompletedLFunctionAtFiveIsEntire

/-- **The product chart agrees with the completed function** away from the `Γ` poles. -/
theorem theCompletedProductFormulaHoldsAtFive (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    completed 800 fiveL s = lambda5 s := by
  unfold completed fiveL
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (by exact_mod_cast hs)
  have hb : ((Real.sqrt ((800 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ≠ 0 := by
    push_cast
    exact base800_ne_zero
  have hpow : ((Real.sqrt ((800 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]
    exact Complex.exp_ne_zero _
  rw [Complex.cpow_neg]
  field_simp
  norm_num

/-! ## 4. The Dirichlet series agreement at five -/

private lemma sqrt2_pos'' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt800_eq : Real.sqrt 800 = 20 * Real.sqrt 2 := by
  rw [show (800 : ℝ) = 20 ^ 2 * 2 from by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)]

private lemma scale800_pos : (0 : ℝ) < π / (10 * Real.sqrt 2) := by
  have h1 := Real.pi_pos
  have h2 := sqrt2_pos''
  positivity

/-! The fibering of the twisted class sum along the norm shells. -/

private def latticeNorm5 (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + p.2 ^ 2).toNat

private lemma latticeNorm5_eq_iff {p : ℤ × ℤ} {m : ℕ} :
    latticeNorm5 p = m ↔ p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) := by
  unfold latticeNorm5
  have h1 : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  omega

private lemma norm_shell_bound5 {m : ℕ} {a b : ℤ} (h : a ^ 2 + b ^ 2 = (m : ℤ)) :
    -(m : ℤ) ≤ a ∧ a ≤ (m : ℤ) ∧ -(m : ℤ) ≤ b ∧ b ≤ (m : ℤ) := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + m), sq_nonneg (a - m),
      sq_nonneg (b + m), sq_nonneg (b - m)]

/-- The twisted class-sum term family, at scale `y`. -/
private def clsTerm (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0 then
    ((p.1 : ℤ) : ℂ) * ((chi5 (p.1 ^ 2 + p.2 ^ 2) : ℤ) : ℂ) *
      ((rexp (-2 * π * y * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ)
  else 0

/-- The fiber sum at five: the character is constant on the shell, so the weights
collect into `fiveCoeff m`. -/
private lemma fiber_hasSum5 (y : ℝ) (m : ℕ) :
    HasSum (fun c : {p : ℤ × ℤ // latticeNorm5 p = m} => clsTerm y (c : ℤ × ℤ))
      (((fiveCoeff m : ℤ) : ℂ) * ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ)) := by
  classical
  refine (hasSum_subtype_iff_indicator
    (s := {q : ℤ × ℤ | latticeNorm5 q = m}) (f := clsTerm y)).mpr ?_
  have hvanish : ∀ p : ℤ × ℤ,
      p ∉ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))) →
      Set.indicator {q : ℤ × ℤ | latticeNorm5 q = m} (clsTerm y) p = 0 := by
    rintro ⟨a, b⟩ hp
    by_cases hmem : latticeNorm5 (a, b) = m
    · exfalso
      apply hp
      have hb := norm_shell_bound5 (latticeNorm5_eq_iff.mp hmem)
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hb.1, hb.2.1⟩, ⟨hb.2.2.1, hb.2.2.2⟩⟩
    · exact Set.indicator_of_notMem (s := {q : ℤ × ℤ | latticeNorm5 q = m}) hmem (clsTerm y)
  have hval : ∑ p ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))),
      Set.indicator {q : ℤ × ℤ | latticeNorm5 q = m} (clsTerm y) p
      = ((fiveCoeff m : ℤ) : ℂ) * ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ) := by
    have hterm : ∀ p ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))),
        Set.indicator {q : ℤ × ℤ | latticeNorm5 q = m} (clsTerm y) p
        = (if p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0
            then ((p.1 : ℤ) : ℂ) else 0) * ((chi5 ((m : ℕ) : ℤ) : ℤ) : ℂ) *
            ((rexp (-2 * π * y * (m : ℝ)) : ℝ) : ℂ) := by
      rintro ⟨a, b⟩ -
      rw [Set.indicator_apply]
      by_cases hnorm : latticeNorm5 (a, b) = m
      · rw [if_pos (show (a, b) ∈ {q : ℤ × ℤ | latticeNorm5 q = m} from hnorm)]
        have hnorm' := latticeNorm5_eq_iff.mp hnorm
        simp only [clsTerm]
        by_cases hclass : ((a + b) % 4 = 1 ∧ b % 2 = 0)
        · rw [if_pos hclass, if_pos ⟨hnorm', hclass.1, hclass.2⟩]
          have hchi : chi5 (a ^ 2 + b ^ 2) = chi5 ((m : ℕ) : ℤ) := by
            rw [hnorm']
          have henv : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) = (m : ℝ) := by
            exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hnorm'
          rw [hchi, henv]
        · rw [if_neg hclass, if_neg (by tauto)]
          ring
      · have hnorm' : ¬(a ^ 2 + b ^ 2 = (m : ℤ)) := fun hc =>
          hnorm (latticeNorm5_eq_iff.mpr hc)
        rw [if_neg (show (a, b) ∉ {q : ℤ × ℤ | latticeNorm5 q = m} from hnorm),
          if_neg (by tauto)]
        ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hcoeff : ∑ p ∈ ((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ (Finset.Icc (-(m : ℤ)) (m : ℤ))),
        (if p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0
          then ((p.1 : ℤ) : ℂ) else 0) = ((heckeCoeff m : ℤ) : ℂ) := by
      rw [heckeCoeff, heckeShell, Finset.sum_filter]
      push_cast
      rfl
    rw [hcoeff]
    unfold fiveCoeff
    push_cast
    ring
  rw [← hval]
  exact hasSum_sum_of_ne_finset_zero hvanish

set_option maxHeartbeats 1000000 in
/-- **The theta at five is its Dirichlet series**, with the twisted computable integer
coefficients. -/
theorem theFiveThetaIsItsDirichletSeries {x : ℝ} (hx : 0 < x) :
    HasSum (fun m : ℕ => ((fiveCoeff m : ℤ) : ℂ) *
      ((rexp (-2 * π * (Real.sqrt 2 * x / 40) * (m : ℝ)) : ℝ) : ℂ))
      ((theta5 x : ℝ) : ℂ) := by
  have hcls : HasSum (clsTerm (Real.sqrt 2 * x / 40)) ((theta5 x : ℝ) : ℂ) :=
    theFiveThetaIsTheTwistedClassSum hx
  have hσ : HasSum (fun q : Σ m : ℕ, {p : ℤ × ℤ // latticeNorm5 p = m} =>
      clsTerm (Real.sqrt 2 * x / 40) ((Equiv.sigmaFiberEquiv latticeNorm5) q))
      ((theta5 x : ℝ) : ℂ) :=
    ((Equiv.sigmaFiberEquiv latticeNorm5).hasSum_iff).mpr hcls
  exact hσ.sigma fun m => fiber_hasSum5 (Real.sqrt 2 * x / 40) m

/-- The theta's Dirichlet expansion in the exponential form `hasSum_mellin` reads:
the rate is `al = π√2/20 = 2π/√800`. -/
private lemma theta5_hasSum_exp {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    HasSum (fun m : ℕ => ((fiveCoeff m : ℤ) : ℂ) *
      rexp (-(Soma.Holonics.Millennium.FivePositivity.al * m) * t))
      ((theta5 t : ℝ) : ℂ) := by
  have h := theFiveThetaIsItsDirichletSeries (Set.mem_Ioi.mp ht)
  have hfun : (fun m : ℕ => ((fiveCoeff m : ℤ) : ℂ) *
      ((rexp (-2 * π * (Real.sqrt 2 * t / 40) * (m : ℝ)) : ℝ) : ℂ))
      = fun m : ℕ => ((fiveCoeff m : ℤ) : ℂ) *
          rexp (-(Soma.Holonics.Millennium.FivePositivity.al * m) * t) := by
    funext m
    congr 2
    unfold Soma.Holonics.Millennium.FivePositivity.al
    push_cast
    ring
  rwa [hfun] at h

/-- The summability input on the half-plane. -/
private lemma dirichlet_summable5 {s : ℂ} (hs : 3 < s.re) :
    Summable fun m : ℕ => ‖((fiveCoeff m : ℤ) : ℂ)‖ /
      (Soma.Holonics.Millennium.FivePositivity.al * m) ^ s.re := by
  have hC := Soma.Holonics.Millennium.FivePositivity.al_pos
  set σ : ℝ := s.re with hσ
  set C : ℝ := Soma.Holonics.Millennium.FivePositivity.al with hC_def
  have hmaj : Summable fun m : ℕ => (9 / C ^ σ) * ((m : ℝ) ^ ((2 : ℝ) - σ)) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show ((fiveCoeff 0 : ℤ) : ℂ) = 0 from by
      unfold fiveCoeff
      rw [heckeCoeff_zero]
      norm_num]
    simp only [norm_zero, Nat.cast_zero, zero_div]
    positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm : ‖((fiveCoeff m : ℤ) : ℂ)‖ ≤ 9 * (m : ℝ) ^ 2 := by
    rw [show ((fiveCoeff m : ℤ) : ℂ) = (((fiveCoeff m : ℤ) : ℝ) : ℂ) from by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    have h1 := fiveCoeff_abs_le m
    have h2 : |((fiveCoeff m : ℤ) : ℝ)| ≤ ((9 * (m : ℤ) ^ 2 : ℤ) : ℝ) := by
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

/-- **The L-function at five agrees with the Dirichlet series of its twisted
coefficients** on the half-plane `re s > 3`. -/
theorem theLFunctionAtFiveAgreesWithItsDirichletSeries {s : ℂ} (hs : 3 < s.re) :
    fiveL s = LSeries (fun m => ((fiveCoeff m : ℤ) : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith
  have hC := Soma.Holonics.Millennium.FivePositivity.al_pos
  set C : ℝ := Soma.Holonics.Millennium.FivePositivity.al with hC_def
  have hmel : HasSum (fun m : ℕ => Complex.Gamma s * ((fiveCoeff m : ℤ) : ℂ) /
      ((C * m : ℝ) : ℂ) ^ s)
      (mellin (Complex.ofReal ∘ theta5) s) := by
    refine hasSum_mellin (fun m => ?_) hs0 (fun t ht => theta5_hasSum_exp ht)
      (dirichlet_summable5 hs)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      unfold fiveCoeff
      rw [heckeCoeff_zero]
      norm_num
    · right
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
  have hΛ : mellin (Complex.ofReal ∘ theta5) s = lambda5 s :=
    (theCompletedLFunctionAtFiveHasMellin s).2
  rw [hΛ] at hmel
  have hG : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have htsum : lambda5 s = Complex.Gamma s *
      ∑' m : ℕ, ((fiveCoeff m : ℤ) : ℂ) / ((C * m : ℝ) : ℂ) ^ s := by
    rw [← tsum_mul_left, ← hmel.tsum_eq]
    exact tsum_congr fun m => by ring
  have hterm : ∀ m : ℕ, ((fiveCoeff m : ℤ) : ℂ) / ((C * m : ℝ) : ℂ) ^ s
      = ((((C : ℝ)) : ℂ) ^ s)⁻¹ *
          LSeries.term (fun m => ((fiveCoeff m : ℤ) : ℂ)) s m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [LSeries.term_zero, show ((fiveCoeff 0 : ℤ) : ℂ) = 0 from by
        unfold fiveCoeff; rw [heckeCoeff_zero]; norm_num]
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
  have hfinal : lambda5 s = Complex.Gamma s *
      (((((C : ℝ)) : ℂ) ^ s)⁻¹ *
        LSeries (fun m => ((fiveCoeff m : ℤ) : ℂ)) s) := by
    rw [htsum, tsum_congr hterm, tsum_mul_left]
    rfl
  have hb0 : (0 : ℝ) < Real.sqrt 800 / (2 * π) := by
    have h1 := Real.pi_pos
    have h2 : (0 : ℝ) < Real.sqrt 800 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hbase : ((Real.sqrt 800 : ℂ) / (2 * Real.pi))
      = (((Real.sqrt 800 / (2 * π) : ℝ)) : ℂ) := by
    push_cast
    rfl
  have hcancel : (Real.sqrt 800 / (2 * π) : ℝ) * C = 1 := by
    rw [sqrt800_eq, hC_def]
    unfold Soma.Holonics.Millennium.FivePositivity.al
    have h1 := Real.pi_pos
    have h2 := sqrt2_pos''
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linear_combination hss
  have hkey : ((Real.sqrt 800 : ℂ) / (2 * Real.pi)) ^ (-s) *
      ((((C : ℝ)) : ℂ) ^ s)⁻¹ = 1 := by
    rw [hbase, Complex.cpow_neg, ← mul_inv,
      ← Complex.mul_cpow_ofReal_nonneg hb0.le hC.le, ← Complex.ofReal_mul, hcancel]
    simp
  have hGinv : (Complex.Gamma s)⁻¹ * Complex.Gamma s = 1 := inv_mul_cancel₀ hG
  unfold fiveL
  rw [hfinal]
  linear_combination (LSeries (fun m => ((fiveCoeff m : ℤ) : ℂ)) s *
      ((Complex.Gamma s)⁻¹ * Complex.Gamma s)) * hkey
    + LSeries (fun m => ((fiveCoeff m : ℤ) : ℂ)) s * hGinv

/-! ## 5. The witness at five -/

/-- **THE WITNESS AT FIVE**: the analytic datum of the congruent-number curve at five.
Every field is kernel-checked: the coefficients are the twisted computable shell sums,
their prime values are the point counts of the five-curve (Gauss, the twist law, and
quadratic reciprocity), their Euler structure transports from the Gaussian-integer
factorization, the L-function is the Mellin transform of the sign-`−1` theta, and the
functional equation carries the sign `−1`. -/
noncomputable def theWitnessAtFive : LDatum 5 where
  coeff := fun m => ((fiveCoeff m : ℤ) : ℂ)
  coeff_one := by
    rw [fiveCoeff_one]
    norm_num
  coeff_prime := fun p hp hpd => by
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      exact hpd ⟨5, by rw [h]⟩
    have hp5 : p ≠ 5 := by
      intro h
      exact hpd ⟨2, by rw [h]⟩
    have h := fiveCoeff_prime p hp2 hp5
    exact_mod_cast h
  coeff_mul := fun a b hab => by
    have h := fiveCoeff_mul hab
    exact_mod_cast h
  coeff_prime_pow := fun p k hp hpd => by
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      exact hpd ⟨5, by rw [h]⟩
    have hp5 : p ≠ 5 := by
      intro h
      exact hpd ⟨2, by rw [h]⟩
    have h := fiveCoeff_prime_pow (p := p) hp2 hp5 k
    exact_mod_cast h
  coeff_bad := fun p k hp hpd => by
    have h := fiveCoeff_bad hp hpd k
    exact_mod_cast h
  L := fiveL
  analytic := theLFunctionAtFiveIsEntire
  agrees := fun s hs => theLFunctionAtFiveAgreesWithItsDirichletSeries hs
  conductor := 800
  conductor_pos := by norm_num
  sign := -1
  sign_pm := Or.inr rfl
  Lambda := lambda5
  Lambda_analytic := theCompletedLFunctionAtFiveIsEntire
  Lambda_eq := fun s hs => (theCompletedProductFormulaHoldsAtFive s hs).symm
  functional_equation := fun s => by
    rw [theCompletedLFunctionalEquationAtFive s]
    push_cast
    ring

/-- **The pose is inhabited at five.** -/
theorem theWitnessAtFiveExists : Nonempty (LDatum 5) := ⟨theWitnessAtFive⟩

/-! ## 6. The analytic rank at five is exactly one -/

private lemma fiveL_at_one : fiveL 1 = 0 := by
  unfold fiveL
  rw [theOddHandForcesTheCentralVanishingAtFive]
  ring

private def uFactor (s : ℂ) : ℂ :=
  ((Real.sqrt 800 : ℂ) / (2 * Real.pi)) ^ (-s) * (Complex.Gamma s)⁻¹

private lemma uFactor_differentiable : Differentiable ℂ uFactor := by
  apply Differentiable.mul
  · exact fun s => (differentiableAt_id.neg.const_cpow (Or.inl base800_ne_zero))
  · exact Complex.differentiable_one_div_Gamma

private lemma uFactor_one_ne_zero : uFactor 1 ≠ 0 := by
  unfold uFactor
  rw [Complex.Gamma_one, inv_one, mul_one]
  rw [Complex.cpow_neg]
  apply inv_ne_zero
  rw [Complex.cpow_one]
  exact base800_ne_zero

private lemma deriv_fiveL_one : deriv fiveL 1 = uFactor 1 * deriv lambda5 1 := by
  have hfl : fiveL = fun s => uFactor s * lambda5 s := by
    funext s
    unfold fiveL uFactor
    ring
  rw [hfl]
  rw [deriv_fun_mul (uFactor_differentiable 1)
    (theCompletedLFunctionAtFiveIsEntire 1)]
  rw [theOddHandForcesTheCentralVanishingAtFive]
  ring

private lemma deriv_fiveL_one_ne_zero : deriv fiveL 1 ≠ 0 := by
  rw [deriv_fiveL_one]
  exact mul_ne_zero uFactor_one_ne_zero theDerivativeDoesNotVanishAtFive

/-- **The analytic rank at five is exactly one**: the L-function vanishes at the
center and its derivative does not — through the derivative-order law, the vanishing
order is one.  Kernel-checked, no Gross–Zagier input. -/
theorem theAnalyticRankAtFiveIsOne : analyticRank theWitnessAtFive = 1 := by
  unfold analyticRank
  show analyticOrderAt fiveL 1 = 1
  have hA : AnalyticAt ℂ fiveL 1 := theLFunctionAtFiveIsEntire.analyticAt 1
  have hkey := hA.analyticOrderAt_deriv_add_one
  have hsub : (fun z => fiveL z - fiveL 1) = fiveL := by
    funext z
    rw [fiveL_at_one, sub_zero]
  rw [hsub] at hkey
  have hd0 : analyticOrderAt (deriv fiveL) 1 = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    exact deriv_fiveL_one_ne_zero
  rw [hd0] at hkey
  rw [← hkey]
  simp

/-! ## 7. The rank-one coincidence -/

/-- **THE RANK-ONE COINCIDENCE AT FIVE.**  The witness's analytic rank is exactly one
— the odd hand kills the central value, the folded first moment is strictly positive —
and the curve's algebraic rank is at least one, carried by the point `(−4, 6)` whose
descent face separates it from every torsion class.  Both sides kernel-checked; the
descent upper bound `¬AlgebraicRankAtLeast 5 2` is the named successor deed, its
material already staged in the completed image-eight descent. -/
theorem theRankOneCoincidenceAtFive :
    analyticRank theWitnessAtFive = 1 ∧ AlgebraicRankAtLeast 5 1 :=
  ⟨theAnalyticRankAtFiveIsOne, theAlgebraicRankAtFiveIsAtLeastOne⟩

end Soma.Holonics.Millennium.FiveWitness
