import Mathlib
import HolonicsResearch.Landmarks.RegularComplexZeros
import HolonicsResearch.Landmarks.IharaEulerProduct

/-!
# The prime cycle theorem at the half: a tempered complex's prime cycles of length `n` number `qⁿ/n` up to the square root

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§5; the sequel to
`research/records/2026-11-18_A_REGULAR_COMPLEXS_OWN_HALF_IS_ONE_CHAIN_OF_FIVE_READINGS_A_KEPT_POSITIVE_FORM_EXISTS_WHERE_THE_MODES_ARE_SEMISIMPLE_ON_THE_LOCUS_AND_THE_SECOND_LAW_STARTS_FROM_ANY_DENSITY.md`).

[proved-standard; formal-checked] `Landmarks/IharaEulerProduct` counts the prime cycles of a finite
complex of contacts (`primeCycles a b n`, the necklaces of the dart matrix: closed walks of `n`
darts with no backtracking, wrap included, taken up to rotation and primitive), and reads them
from the traces of the dart operator `B`: `tr Bⁿ = Σ_(d∣n) d · N_d` (`trace_hashimoto_pow`) and
`Σ_(d∣n) μ(n/d) tr B^d = n · N_n` over `ℤ` (`primeCycles_moebius`).  `Landmarks/RegularComplexZeros`
bounds the real trace `W_l = walkCount a b l` of a complex with `q + 1` darts at every cell whose
modes other than the count are tempered (`walkCount_bound`).  This module joins the two: the prime
cycles of a tempered complex obey the graph's prime number theorem with its error at the half.
Write `c = |E| − |V|` (a real number), `N_n = primeCycles a b n`, `μ` the Möbius function.

What is proved.

* **The bridge** (`walkCount_eq_natCast`, `trace_int_cast`, `primeCycles_moebius_real`): the integer
  trace read in `ℝ` is `walkCount`, so `Σ_(d∣n) μ(n/d) W_d = n N_n` in `ℝ`.
* **P1, the Möbius error** (`moebius_error`, `moebius_error_of_one_le`): under the tempered
  hypotheses, for `n ≥ 1`,
  `|n N_n − Σ_(d∣n) μ(n/d) q^d| ≤ Σ_(d∣n) (1 + 2|c| + 2(|V| − 1)(√q)^d)`; each length's own
  remainder is `|W_d − q^d| ≤ 1 + 2|c| + 2(|V| − 1)(√q)^d` (`walkCount_sub_pow_le`).
* **P2, the square-root form** (`prime_cycle_theorem`, `prime_cycle_theorem_div` and their
  `_of_one_le` forms): `|n N_n − qⁿ| ≤ n((2|V| − 1)(√q)ⁿ + 1 + 2|c|)`, hence
  `|N_n − qⁿ/n| ≤ (2|V| − 1)(√q)ⁿ + 1 + 2|c|`.  A proper divisor `d` of `n` has `2d ≤ n`
  (`two_mul_le_of_proper_divisor`), so `q^d ≤ (√q)ⁿ`, and `n` has at most `n` divisors.
* **P3, the uniform form** (`prime_cycle_theorem_uniform`, `prime_cycle_theorem_uniform_div`): for
  `q ≥ 2`, `|n N_n − qⁿ| ≤ 8|E|(√q)ⁿ` with a constant free of `n`, so
  `|N_n − qⁿ/n| ≤ 8|E|(√q)ⁿ/n`.  The geometric sums are bounded by four times their last term
  once the ratio is at least `4/3` (`geom_sum_le_four_mul`), which `√q` is from `q = 2` on.
* **P4, the reading without tempering** (`mul_primeCycles_le_trace`, `mul_primeCycles_le_walkCount`,
  `primeCycles_le_walkCount_div`): on every finite complex, `n N_n ≤ tr Bⁿ`, since every term of
  `Σ_(d∣n) d N_d` is a count; so `N_n ≤ W_n/n`.  With tempering this gives the one-sided
  `n N_n ≤ qⁿ + 1 + 2|c| + 2(|V| − 1)(√q)ⁿ` (`mul_primeCycles_le_tempered`), sharper than P2's
  upper side.

The reading: the prime cycles of length `n` number `qⁿ/n` up to the square root, the graph's prime
number theorem, and its error is the half's own count: the modes other than the count contribute
`(√q)^d` each, and nothing else in the error grows faster.

## What this does not state

* No converse from the count of prime cycles to tempering is proved here, though
  `Landmarks/RegularComplexHalf`'s chain (`half_tfae`, `tempered_of_rem_le`) gives it for the
  closed-walk count.
* That `walkCount` counts closed walks without backtracking: it is the trace of `Bⁿ` read in `ℝ`;
  `IharaEulerProduct.card_closedWalk_eq_trace` holds the count in `ℚ`.
* Anything about complexes that are not tempered beyond P4, or about the integers' own prime
  number theorem: a regular complex is a finite specimen of the half.

Limits: the constants are the plain ones the proofs give (P2's grows like `n` times the square
root, P3's `8|E|` is not optimized, and P3 asks `q ≥ 2`); the sign `(−1)^d` of the bipartite part
is bounded by `2`, not kept.

The computational object is the helical pair interaction read as a census of returns: a prime cycle
is a closed strand through pair contacts with no immediate reversal, and its count is read from the
dart operator's traces.  Of the winding guide's six general objects this touches the pair (the darts
and their non-reversing contacts) and the cell holonomy (the modes of the cell operator, through
`walkCount_bound`); the helix, faces and placement, the tube and the tower thread stay attached.

Consumers: the atlas row `trace.prime-cycle-theorem-half` (beside `trace.prime-cycle-half-rank`,
whose Möbius line and bound it joins), and the third record of November 18 on the half.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Finset

namespace Holonics.Landmarks.PrimeCycleHalf

open Holonics.Landmarks.RegularComplexZeros
open Holonics.Landmarks.IharaEulerProduct
open Holonics.Compression.Landmark.NecklaceIntegrality

/-! ## Exponents, divisors and the Möbius weights -/

section Exponents

/-- [proved-standard; formal-checked] `(√q)^d ≤ (√q)ⁿ` for `1 ≤ d ≤ n`, the case `q = 0` included. -/
theorem sqrt_pow_le_sqrt_pow (q : ℕ) {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    Real.sqrt q ^ d ≤ Real.sqrt q ^ n := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [zero_pow (by omega : d ≠ 0), zero_pow (by omega : n ≠ 0)]
  · exact pow_le_pow_right₀ (Real.one_le_sqrt.mpr (by exact_mod_cast hq)) hdn

/-- [proved-standard; formal-checked] `q^d ≤ (√q)ⁿ` once `1 ≤ d` and `2d ≤ n`. -/
theorem pow_le_sqrt_pow (q : ℕ) {d n : ℕ} (hd : 1 ≤ d) (h2 : 2 * d ≤ n) :
    (q : ℝ) ^ d ≤ Real.sqrt q ^ n := by
  have h : (q : ℝ) ^ d = Real.sqrt q ^ (2 * d) := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [h]
  exact sqrt_pow_le_sqrt_pow q (by omega) h2

/-- [proved-standard; formal-checked] A proper divisor is at most half: `d ∣ n`, `d ≠ n`, `n ≠ 0`
give `2d ≤ n`. -/
theorem two_mul_le_of_proper_divisor {d n : ℕ} (hd : d ∈ n.divisors) (hne : d ≠ n) :
    2 * d ≤ n := by
  obtain ⟨hdvd, hn⟩ := Nat.mem_divisors.mp hd
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hn
    · simp at hne
    · omega
  calc 2 * d = d * 2 := by ring
    _ ≤ d * k := Nat.mul_le_mul_left d hk

/-- [proved-standard; formal-checked] The Möbius weights read in `ℝ` are at most one in size. -/
theorem abs_moebius_cast_le_one (k : ℕ) :
    |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- [proved-standard; formal-checked] The divisor `n` itself carries weight `μ 1 = 1`:
`Σ_(d∣n) μ(n/d) x^d = xⁿ + Σ_(d∣n, d≠n) μ(n/d) x^d`. -/
theorem moebius_sum_split (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * x ^ d
      = x ^ n + ∑ d ∈ n.divisors.erase n,
          ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * x ^ d := by
  rw [← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn.ne'), Nat.div_self hn,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]

/-- [proved-standard; formal-checked] The proper part of a Möbius sum of nonnegative powers is at
most the plain sum of those powers. -/
theorem abs_moebius_proper_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |∑ d ∈ n.divisors.erase n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * x ^ d|
      ≤ ∑ d ∈ n.divisors.erase n, x ^ d := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hx d)]
  calc _ ≤ 1 * x ^ d := mul_le_mul_of_nonneg_right (abs_moebius_cast_le_one _) (pow_nonneg hx d)
    _ = x ^ d := one_mul _

/-- [proved-standard; formal-checked] A geometric sum whose ratio is at least `4/3` is at most four
times its last term: `Σ_(j ≤ m) x^j ≤ 4 x^m`. -/
theorem geom_sum_le_four_mul {x : ℝ} (hx : 4 / 3 ≤ x) (m : ℕ) :
    ∑ j ∈ range (m + 1), x ^ j ≤ 4 * x ^ m := by
  have hx1 : 0 < x - 1 := by linarith
  have hxm : 0 ≤ x ^ m := pow_nonneg (by linarith) m
  have h : (∑ j ∈ range (m + 1), x ^ j) * (x - 1) ≤ (4 * x ^ m) * (x - 1) := by
    rw [geom_sum_mul, pow_succ]
    nlinarith [mul_nonneg hxm (by linarith : (0 : ℝ) ≤ 3 * x - 4)]
  exact le_of_mul_le_mul_right h hx1

/-- [proved-standard; formal-checked] The divisors of `n` sit in `0, …, n`. -/
theorem sum_divisors_pow_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ d ∈ n.divisors, x ^ d ≤ ∑ j ∈ range (n + 1), x ^ j :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun _d hd => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd)))
    (fun j _ _ => pow_nonneg hx j)

/-- [proved-standard; formal-checked] The proper divisors of `n` sit in `0, …, n/2`. -/
theorem sum_proper_divisors_pow_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ d ∈ n.divisors.erase n, x ^ d ≤ ∑ j ∈ range (n / 2 + 1), x ^ j :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun d hd => by
      obtain ⟨hne, hdD⟩ := Finset.mem_erase.mp hd
      have := two_mul_le_of_proper_divisor hdD hne
      exact Finset.mem_range.mpr (by omega))
    (fun j _ _ => pow_nonneg hx j)

end Exponents

/-! ## The bridge and the reading without tempering -/

section Count

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [proved-derived; formal-checked] The real trace is the dart matrix's natural trace. -/
theorem walkCount_eq_natCast (l : ℕ) :
    walkCount a b l = (((dartMatrix a b) ^ l).trace : ℝ) :=
  trace_hashimoto_pow_eq_natCast a b ℝ l

/-- [proved-derived; formal-checked] **The bridge**: the integer trace of `B^d` read in `ℝ` is
`walkCount`. -/
theorem trace_int_cast (d : ℕ) :
    (((IharaBass.hashimoto ℤ a b) ^ d).trace : ℝ) = walkCount a b d := by
  rw [trace_hashimoto_pow_eq_natCast a b ℤ d, walkCount_eq_natCast, Int.cast_natCast]

/-- [proved-derived; formal-checked] **The Möbius form in `ℝ`**:
`Σ_(d∣n) μ(n/d) W_d = n · N_n`. -/
theorem primeCycles_moebius_real (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * walkCount a b d
      = (n : ℝ) * (primeCycles a b n : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (primeCycles_moebius a b n hn)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, trace_int_cast] at h
  exact h

/-- [proved-derived; formal-checked] **P4, no tempering**: the prime cycles of length `n`, each
counted `n` times, are among the closed walks of length `n`: `n N_n ≤ tr Bⁿ`. -/
theorem mul_primeCycles_le_trace (n : ℕ) (hn : 0 < n) :
    n * primeCycles a b n ≤ ((dartMatrix a b) ^ n).trace := by
  rw [trace_pow_eq_sum_necklace (dartMatrix a b) n hn]
  exact Finset.single_le_sum (f := fun d => d * necklaceCount (dartMatrix a b) d)
    (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn.ne')

/-- [proved-derived; formal-checked] P4 in `ℝ`: `n N_n ≤ W_n`. -/
theorem mul_primeCycles_le_walkCount (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * primeCycles a b n ≤ walkCount a b n := by
  rw [walkCount_eq_natCast]
  exact_mod_cast mul_primeCycles_le_trace a b n hn

/-- [proved-derived; formal-checked] P4 divided: `N_n ≤ W_n / n`. -/
theorem primeCycles_le_walkCount_div (n : ℕ) (hn : 0 < n) :
    (primeCycles a b n : ℝ) ≤ walkCount a b n / n := by
  rw [le_div_iff₀ (by exact_mod_cast hn), mul_comm]
  exact mul_primeCycles_le_walkCount a b n hn

end Count

/-! ## The prime cycle theorem at the half -/

section Tempered

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [proved-derived; formal-checked] One length's remainder: under the tempered hypotheses,
`|W_l − q^l| ≤ 1 + 2|c| + 2(|V| − 1)(√q)^l`. -/
theorem walkCount_sub_pow_le {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (l : ℕ) :
    |walkCount a b l - (q : ℝ) ^ l| ≤
      1 + 2 * |(Fintype.card E : ℝ) - Fintype.card V|
        + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ l := by
  have h := walkCount_bound a b hreg hVE h0 htemp l
  generalize (Fintype.card E : ℝ) - Fintype.card V = c at h ⊢
  have hsign : |(1 : ℝ) + (-1) ^ l| ≤ 2 := by
    calc |(1 : ℝ) + (-1) ^ l| ≤ |(1 : ℝ)| + |(-1 : ℝ) ^ l| := abs_add_le _ _
      _ = 2 := by rw [abs_pow, abs_neg, abs_one, one_pow]; norm_num
  have hcs : |c * (1 + (-1) ^ l)| ≤ 2 * |c| := by
    rw [abs_mul]
    calc |c| * |(1 : ℝ) + (-1) ^ l| ≤ |c| * 2 := mul_le_mul_of_nonneg_left hsign (abs_nonneg c)
      _ = 2 * |c| := by ring
  have hsplit : walkCount a b l - (q : ℝ) ^ l =
      (walkCount a b l - ((q : ℝ) ^ l + 1) - c * (1 + (-1) ^ l)) + 1 + c * (1 + (-1) ^ l) := by
    ring
  have e1 := abs_add_le (walkCount a b l - ((q : ℝ) ^ l + 1) - c * (1 + (-1) ^ l) + 1)
    (c * (1 + (-1) ^ l))
  have e2 := abs_add_le (walkCount a b l - ((q : ℝ) ^ l + 1) - c * (1 + (-1) ^ l)) 1
  rw [abs_one] at e2
  rw [hsplit]
  linarith

/-- [proved-derived; formal-checked] **P1, the Möbius error**: for `n ≥ 1`,
`|n N_n − Σ_(d∣n) μ(n/d) q^d| ≤ Σ_(d∣n) (1 + 2|c| + 2(|V| − 1)(√q)^d)`. -/
theorem moebius_error {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * primeCycles a b n
        - ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d| ≤
      ∑ d ∈ n.divisors, (1 + 2 * |(Fintype.card E : ℝ) - Fintype.card V|
        + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ d) := by
  rw [← primeCycles_moebius_real a b n hn, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [← mul_sub, abs_mul]
  calc _ ≤ 1 * |walkCount a b d - (q : ℝ) ^ d| :=
        mul_le_mul_of_nonneg_right (abs_moebius_cast_le_one _) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact walkCount_sub_pow_le a b hreg hVE h0 htemp d

/-- [proved-derived; formal-checked] P1 with the count of contacts read from the complex
(`1 ≤ q` gives `|V| ≤ |E|`). -/
theorem moebius_error_of_one_le {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * primeCycles a b n
        - ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d| ≤
      ∑ d ∈ n.divisors, (1 + 2 * |(Fintype.card E : ℝ) - Fintype.card V|
        + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ d) :=
  moebius_error a b hreg (card_le_card_of_regular a b hreg hq) h0 htemp n hn

/-- [proved-derived; formal-checked] **P2, the prime cycle theorem at the half**: for `n ≥ 1`,
`|n N_n − qⁿ| ≤ n((2|V| − 1)(√q)ⁿ + 1 + 2|c|)`. -/
theorem prime_cycle_theorem {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * primeCycles a b n - (q : ℝ) ^ n| ≤
      n * ((2 * (Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n + 1
        + 2 * |(Fintype.card E : ℝ) - Fintype.card V|) := by
  have h1 := moebius_error a b hreg hVE h0 htemp n hn
  have hsplit := moebius_sum_split (q : ℝ) n hn
  have h2 := abs_moebius_proper_le (Nat.cast_nonneg q : (0 : ℝ) ≤ q) n
  have hV : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hcard : ((n.divisors.card : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hcardP : (((n.divisors.erase n).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_erase_le).trans (Nat.card_divisors_le_self n)
  have hsq : 0 ≤ Real.sqrt q ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  generalize (Fintype.card E : ℝ) - Fintype.card V = c at h1 ⊢
  -- the whole Möbius error, each `(√q)^d` raised to `(√q)ⁿ`
  have h1' : ∑ d ∈ n.divisors, (1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ d)
      ≤ n * (1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n) := by
    have hpos : 0 ≤ 1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n := by
      have := abs_nonneg c
      have : 0 ≤ ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n := mul_nonneg (by linarith) hsq
      linarith
    calc _ ≤ ∑ _d ∈ n.divisors,
          (1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hle := sqrt_pow_le_sqrt_pow q (Nat.pos_of_mem_divisors hd) (Nat.divisor_le hd)
          have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 2 * ((Fintype.card V : ℝ) - 1))
          linarith
      _ = (n.divisors.card : ℝ) *
          (1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hpos
  -- the proper divisors, each `q^d ≤ (√q)ⁿ`
  have h2' : ∑ d ∈ n.divisors.erase n, (q : ℝ) ^ d ≤ n * Real.sqrt q ^ n := by
    calc _ ≤ ∑ _d ∈ n.divisors.erase n, Real.sqrt q ^ n := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hne, hdD⟩ := Finset.mem_erase.mp hd
          exact pow_le_sqrt_pow q (Nat.pos_of_mem_divisors hdD)
            (two_mul_le_of_proper_divisor hdD hne)
      _ = ((n.divisors.erase n).card : ℝ) * Real.sqrt q ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardP hsq
  have key : (n : ℝ) * primeCycles a b n - (q : ℝ) ^ n =
      ((n : ℝ) * primeCycles a b n
        - ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d)
      + ∑ d ∈ n.divisors.erase n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d := by
    rw [hsplit]
    ring
  rw [key]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ n * (1 + 2 * |c| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n)
        + n * Real.sqrt q ^ n := add_le_add (h1.trans h1') (h2.trans h2')
    _ = _ := by ring

/-- [proved-derived; formal-checked] P2 divided by `n`:
`|N_n − qⁿ/n| ≤ (2|V| − 1)(√q)ⁿ + 1 + 2|c|`. -/
theorem prime_cycle_theorem_div {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(primeCycles a b n : ℝ) - (q : ℝ) ^ n / n| ≤
      (2 * (Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n + 1
        + 2 * |(Fintype.card E : ℝ) - Fintype.card V| := by
  have h := prime_cycle_theorem a b hreg hVE h0 htemp n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (n : ℝ) * primeCycles a b n - (q : ℝ) ^ n
      = n * ((primeCycles a b n : ℝ) - (q : ℝ) ^ n / n) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hn'] at h
  exact le_of_mul_le_mul_left h hn'

/-- [proved-derived; formal-checked] P2 with the count of contacts read from the complex. -/
theorem prime_cycle_theorem_of_one_le {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * primeCycles a b n - (q : ℝ) ^ n| ≤
      n * ((2 * (Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n + 1
        + 2 * |(Fintype.card E : ℝ) - Fintype.card V|) :=
  prime_cycle_theorem a b hreg (card_le_card_of_regular a b hreg hq) h0 htemp n hn

/-- [proved-derived; formal-checked] P2 divided, with the count of contacts read from the
complex. -/
theorem prime_cycle_theorem_div_of_one_le {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 1 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(primeCycles a b n : ℝ) - (q : ℝ) ^ n / n| ≤
      (2 * (Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n + 1
        + 2 * |(Fintype.card E : ℝ) - Fintype.card V| :=
  prime_cycle_theorem_div a b hreg (card_le_card_of_regular a b hreg hq) h0 htemp n hn

/-- [proved-derived; formal-checked] **P3, the uniform form**: for `q ≥ 2` and `n ≥ 1`,
`|n N_n − qⁿ| ≤ 8|E|(√q)ⁿ`, with a constant free of `n`. -/
theorem prime_cycle_theorem_uniform {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 2 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * primeCycles a b n - (q : ℝ) ^ n| ≤
      8 * (Fintype.card E : ℝ) * Real.sqrt q ^ n := by
  have hVE := card_le_card_of_regular a b hreg (by omega)
  have h1 := moebius_error a b hreg hVE h0 htemp n hn
  have hsplit := moebius_sum_split (q : ℝ) n hn
  have h2 := abs_moebius_proper_le (Nat.cast_nonneg q : (0 : ℝ) ≤ q) n
  have hV : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hVE' : (Fintype.card V : ℝ) ≤ Fintype.card E := by exact_mod_cast hVE
  have hcard : ((n.divisors.card : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hc : |(Fintype.card E : ℝ) - Fintype.card V| = Fintype.card E - Fintype.card V :=
    abs_of_nonneg (by linarith)
  rw [hc] at h1
  -- the ratio `√q` is at least `4/3`
  have hx : (4 / 3 : ℝ) ≤ Real.sqrt q := (Real.le_sqrt' (by norm_num)).mpr (by nlinarith)
  have hx1 : (1 : ℝ) ≤ Real.sqrt q := by linarith
  have hgx := geom_sum_le_four_mul hx n
  -- `n ≤ 4 (√q)ⁿ`
  have hn4 : (n : ℝ) ≤ 4 * Real.sqrt q ^ n := by
    have hs1 : ∑ _j ∈ range (n + 1), (1 : ℝ) ≤ ∑ j ∈ range (n + 1), Real.sqrt q ^ j :=
      Finset.sum_le_sum fun _ _ => one_le_pow₀ hx1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs1
    push_cast at hs1
    linarith
  -- the Möbius error is at most `4(1 + 2c)(√q)ⁿ + 8(|V| − 1)(√q)ⁿ`
  have h1' : ∑ d ∈ n.divisors, (1 + 2 * ((Fintype.card E : ℝ) - Fintype.card V)
        + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ d)
      ≤ 4 * (1 + 2 * ((Fintype.card E : ℝ) - Fintype.card V)) * Real.sqrt q ^ n
        + 8 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hs := (sum_divisors_pow_le (Real.sqrt_nonneg (q : ℝ)) n).trans hgx
    have hA : 0 ≤ 1 + 2 * ((Fintype.card E : ℝ) - Fintype.card V) := by linarith
    have hB : 0 ≤ 2 * ((Fintype.card V : ℝ) - 1) := by linarith
    have e1 := mul_le_mul_of_nonneg_right (hcard.trans hn4) hA
    have e2 := mul_le_mul_of_nonneg_left hs hB
    nlinarith
  -- the proper divisors give at most `4 q^(n/2) ≤ 4 (√q)ⁿ`
  have h2' : ∑ d ∈ n.divisors.erase n, (q : ℝ) ^ d ≤ 4 * Real.sqrt q ^ n := by
    have hgq := geom_sum_le_four_mul (by linarith : (4 / 3 : ℝ) ≤ q) (n / 2)
    have hhalf : (q : ℝ) ^ (n / 2) ≤ Real.sqrt q ^ n := by
      rw [show (q : ℝ) ^ (n / 2) = Real.sqrt q ^ (2 * (n / 2)) by
        rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]]
      exact pow_le_pow_right₀ hx1 (by omega)
    calc _ ≤ _ := sum_proper_divisors_pow_le (Nat.cast_nonneg q) n
      _ ≤ _ := hgq
      _ ≤ _ := by linarith
  have key : (n : ℝ) * primeCycles a b n - (q : ℝ) ^ n =
      ((n : ℝ) * primeCycles a b n
        - ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d)
      + ∑ d ∈ n.divisors.erase n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (q : ℝ) ^ d := by
    rw [hsplit]
    ring
  rw [key]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 4 * (1 + 2 * ((Fintype.card E : ℝ) - Fintype.card V)) * Real.sqrt q ^ n
        + 8 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n + 4 * Real.sqrt q ^ n :=
        add_le_add (h1.trans h1') (h2.trans h2')
    _ = _ := by ring

/-- [proved-derived; formal-checked] P3 divided by `n`: `|N_n − qⁿ/n| ≤ 8|E|(√q)ⁿ/n`. -/
theorem prime_cycle_theorem_uniform_div {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hq : 2 ≤ q) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    |(primeCycles a b n : ℝ) - (q : ℝ) ^ n / n| ≤
      8 * (Fintype.card E : ℝ) * Real.sqrt q ^ n / n := by
  have h := prime_cycle_theorem_uniform a b hreg hq h0 htemp n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (n : ℝ) * primeCycles a b n - (q : ℝ) ^ n
      = n * ((primeCycles a b n : ℝ) - (q : ℝ) ^ n / n) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hn'] at h
  rw [le_div_iff₀ hn', mul_comm]
  exact h

/-- [proved-derived; formal-checked] P4 with tempering, the one-sided count:
`n N_n ≤ qⁿ + 1 + 2|c| + 2(|V| − 1)(√q)ⁿ`. -/
theorem mul_primeCycles_le_tempered {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (eigen a b i) ^ 2 ≤ 4 * (q : ℝ)) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * primeCycles a b n ≤
      (q : ℝ) ^ n + 1 + 2 * |(Fintype.card E : ℝ) - Fintype.card V|
        + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n := by
  have h4 := mul_primeCycles_le_walkCount a b n hn
  have hw := walkCount_sub_pow_le a b hreg hVE h0 htemp n
  have := le_abs_self (walkCount a b n - (q : ℝ) ^ n)
  linarith

end Tempered

/-! ## Audit -/

section Audit

#print axioms sqrt_pow_le_sqrt_pow
#print axioms pow_le_sqrt_pow
#print axioms two_mul_le_of_proper_divisor
#print axioms abs_moebius_cast_le_one
#print axioms moebius_sum_split
#print axioms abs_moebius_proper_le
#print axioms geom_sum_le_four_mul
#print axioms sum_divisors_pow_le
#print axioms sum_proper_divisors_pow_le
#print axioms walkCount_eq_natCast
#print axioms trace_int_cast
#print axioms primeCycles_moebius_real
#print axioms mul_primeCycles_le_trace
#print axioms mul_primeCycles_le_walkCount
#print axioms primeCycles_le_walkCount_div
#print axioms walkCount_sub_pow_le
#print axioms moebius_error
#print axioms moebius_error_of_one_le
#print axioms prime_cycle_theorem
#print axioms prime_cycle_theorem_div
#print axioms prime_cycle_theorem_of_one_le
#print axioms prime_cycle_theorem_div_of_one_le
#print axioms prime_cycle_theorem_uniform
#print axioms prime_cycle_theorem_uniform_div
#print axioms mul_primeCycles_le_tempered

end Audit

end Holonics.Landmarks.PrimeCycleHalf
