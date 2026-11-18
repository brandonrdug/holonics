import Mathlib
import Holonics.Foundation.ReceiverAtlas
import Holonics.Aeon.Production.Zeta

/-!
# The count of Markov parameters that separates two sources

[definition] Source: `Foundation/ReceiverAtlas`, section (a) of the separating atlases, where the
declared-port statement of realization theory at its classical bound stood as the unproved `Prop`
`MarkovTwoNSuffices` (issue #410, from #21). A source is a linear system `x' = A x + B u`,
`y = C x` read through its declared ports, and its `k`-th Markov parameter is the response
`C Aᵏ B` at time `k` (`Atlas.SeparatingAtlas.markov`).

[proved-derived; formal-checked] What is proved.

1. **A common annihilator bounds the separating time** (`responses_agree_of_common_annihilator`).
   If one monic polynomial `g` annihilates both generators, `g(A) = 0` and `g(A') = 0`, and the
   two responses agree at every time below `deg g`, they agree at every time. The generators may
   have different dimensions. The reason is one division: `Xᵏ = q·g + r` with `deg r < deg g`, so
   `C Aᵏ B = Σ_(i < deg g) r_i · C Aⁱ B` with the same coefficients `r_i` on both sides
   (`pow_eq_aeval_modByMonic`, `response_expand`).
2. **Dimensions `n` and `n'` are separated by the first `n + n'` parameters**
   (`markov_agree_add`): the product of the two characteristic polynomials is monic of degree
   `n + n'` and annihilates both generators (Cayley–Hamilton on each factor).
3. **`MarkovTwoNSuffices` holds** over every field and at every dimension (`markovTwoNSuffices`):
   it is item 2 at `n' = n`.
4. **The sharper count by minimal polynomials** (`markov_agree_minpoly`): the first
   `deg μ_A + deg μ_A'` parameters suffice, which is at most `n + n'`.
5. **The existing truncation is the same lemma** (`markov_truncation_of_common_annihilator`): a
   shared characteristic polynomial is a common annihilator of degree `n`, which is
   `ReceiverAtlas.markov_truncation`'s bound.
6. **Ruler, the bound is reached at `n = 1`** (`one_parameter_does_not_separate`,
   `two_n_is_least_at_one`): over `ℚ` the one-dimensional sources `(c, a, b) = (1, 1, 1)` and
   `(1, 2, 1)` agree at time `0` and differ at time `1`.
7. **The count `2n` is the least at every dimension `n ≥ 1`** (`two_n_is_least`). The cyclic
   step on `n = m + 1` states, excited at the last state and read at the first, responds only at
   the times `k ≡ m` modulo `n` (`cyclicSource_markov`, through `Zeta.mapMatrix_pow_apply`). With
   gain `1` and weight `1` against gain `2` and weight `2^(−m)` the two responses agree at every
   time below `2n − 1` (both read `1` at `k = m` and nothing else) and differ at `k = 2n − 1`
   (`1` against `2ⁿ`). So `2n` cannot be lowered without the shared characteristic polynomial.

Limits. The statement is about the responses only: that two sources indistinguishable at their
ports have similar minimal realizations (the Kalman decomposition) is not stated here, and the
proof does not use it, nor the rank of the block Hankel matrix. The least-count ruler is over
`ℚ`; over a field of two elements the gain `2` is not available and no ruler is given there.

Computational object: the helical pair interaction, read as a pair of sources compared through
their declared ports. Of the winding guide's six objects it touches the faces and placement (a
response is a face of the generator's powers at a port) and the tower thread (the remainder of
`Xᵏ` modulo the common annihilator is the restriction that every later time factors through);
helix, pair, cell holonomy and tube stay attached and are not used.

Consumers: `Foundation/ReceiverAtlas` (the declared-port atlas, R7), `Foundation/HankelKey`
(finite Hankel rank reads the same recurrence from the responses' side).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.MarkovSeparation

open Matrix Polynomial
open Holonics.Foundation.CausalChord
open Holonics.Foundation.Atlas Holonics.Foundation.Atlas.SeparatingAtlas

section General

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] **A power is the remainder's evaluation.** If the monic `g`
annihilates `A`, every power `Aᵏ` is the evaluation at `A` of the remainder of `Xᵏ` modulo `g`. -/
theorem pow_eq_aeval_modByMonic {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K)
    {g : K[X]} (hA : aeval A g = 0) (k : ℕ) :
    A ^ k = aeval A (((X : K[X]) ^ k) %ₘ g) := by
  have key : aeval A ((((X : K[X]) ^ k) %ₘ g) + g * (((X : K[X]) ^ k) /ₘ g))
      = aeval A ((X : K[X]) ^ k) := by
    rw [Polynomial.modByMonic_add_div ((X : K[X]) ^ k) g]
  rw [map_add, map_mul, hA, zero_mul, add_zero] at key
  rw [key]
  simp

/-- [proved-derived; formal-checked] **A response through a polynomial of the generator is the
polynomial's combination of the responses below its degree bound.** -/
theorem response_expand {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix κ ι K)
    (A : Matrix ι ι K) (B : Matrix ι μ K) (r : K[X]) {d : ℕ} (hr : r.natDegree < d) :
    C * aeval A r * B = ∑ i ∈ Finset.range d, r.coeff i • (C * A ^ i * B) := by
  rw [Polynomial.aeval_eq_sum_range' hr, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- [proved-derived; formal-checked] **A common annihilator bounds the separating time.** Two
sources, of any two dimensions, whose generators are annihilated by one monic polynomial `g` and
whose responses agree at every time below `deg g` have the same response at every time. -/
theorem responses_agree_of_common_annihilator {ι ι' κ μ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {A : Matrix ι ι K} {A' : Matrix ι' ι' K}
    (C : Matrix κ ι K) (B : Matrix ι μ K) (C' : Matrix κ ι' K) (B' : Matrix ι' μ K)
    {g : K[X]} (hg : g.Monic) (hA : aeval A g = 0) (hA' : aeval A' g = 0)
    (h : ∀ k, k < g.natDegree → C * A ^ k * B = C' * A' ^ k * B') :
    ∀ k, C * A ^ k * B = C' * A' ^ k * B' := by
  intro k
  rcases eq_or_ne g 1 with h1 | h1
  · -- the annihilator is `1`: both matrix rings are trivial and every response is zero
    have hz : (1 : Matrix ι ι K) = 0 := by simpa [h1] using hA
    have hz' : (1 : Matrix ι' ι' K) = 0 := by simpa [h1] using hA'
    have hAk : A ^ k = 0 := by rw [← mul_one (A ^ k), hz, mul_zero]
    have hAk' : A' ^ k = 0 := by rw [← mul_one (A' ^ k), hz', mul_zero]
    rw [hAk, hAk']
    simp
  · have hdeg : ((((X : K[X]) ^ k) %ₘ g)).natDegree < g.natDegree :=
      Polynomial.natDegree_modByMonic_lt _ hg h1
    rw [pow_eq_aeval_modByMonic A hA k, pow_eq_aeval_modByMonic A' hA' k,
      response_expand C A B _ hdeg, response_expand C' A' B' _ hdeg]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]

end General

section Markov

variable {K : Type} [Field K] {n n' m p : ℕ}

/-- [proved-derived; formal-checked] **Dimensions `n` and `n'` are separated by the first
`n + n'` Markov parameters.** The product of the two characteristic polynomials is the common
annihilator. -/
theorem markov_agree_add (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K) (C' : Matrix (Fin p) (Fin n') K)
    (A' : Matrix (Fin n') (Fin n') K) (B' : Matrix (Fin n') (Fin m) K)
    (h : ∀ k, k < n + n' → markov C A B k = markov C' A' B' k) :
    ∀ k, markov C A B k = markov C' A' B' k := by
  have hg : (A.charpoly * A'.charpoly).Monic := A.charpoly_monic.mul A'.charpoly_monic
  have hdeg : (A.charpoly * A'.charpoly).natDegree = n + n' := by
    rw [A.charpoly_monic.natDegree_mul A'.charpoly_monic, A.charpoly_natDegree_eq_dim,
      A'.charpoly_natDegree_eq_dim, Fintype.card_fin, Fintype.card_fin]
  have hA : aeval A (A.charpoly * A'.charpoly) = 0 := by
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hA' : aeval A' (A.charpoly * A'.charpoly) = 0 := by
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero]
  simp only [markov] at h ⊢
  exact responses_agree_of_common_annihilator C B C' B' hg hA hA' (fun k hk => h k (hdeg ▸ hk))

/-- [proved-derived; formal-checked] **The count by minimal polynomials.** The first
`deg μ_A + deg μ_A'` Markov parameters separate two sources, with `μ` the minimal polynomial. -/
theorem markov_agree_minpoly (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K) (C' : Matrix (Fin p) (Fin n') K)
    (A' : Matrix (Fin n') (Fin n') K) (B' : Matrix (Fin n') (Fin m) K)
    (h : ∀ k, k < (minpoly K A).natDegree + (minpoly K A').natDegree →
      markov C A B k = markov C' A' B' k) :
    ∀ k, markov C A B k = markov C' A' B' k := by
  have hm : (minpoly K A).Monic := minpoly.monic (Matrix.isIntegral A)
  have hm' : (minpoly K A').Monic := minpoly.monic (Matrix.isIntegral A')
  have hdeg : (minpoly K A * minpoly K A').natDegree
      = (minpoly K A).natDegree + (minpoly K A').natDegree := hm.natDegree_mul hm'
  have hA : aeval A (minpoly K A * minpoly K A') = 0 := by
    rw [map_mul, minpoly.aeval, zero_mul]
  have hA' : aeval A' (minpoly K A * minpoly K A') = 0 := by
    rw [map_mul, minpoly.aeval, mul_zero]
  simp only [markov] at h ⊢
  exact responses_agree_of_common_annihilator C B C' B' (hm.mul hm') hA hA'
    (fun k hk => h k (hdeg ▸ hk))

/-- [proved-derived; formal-checked] **The truncation under a shared characteristic polynomial**
(`ReceiverAtlas.markov_truncation`) is the common-annihilator lemma at `g = χ_A = χ_A'`, of
degree `n`. -/
theorem markov_truncation_of_common_annihilator {A A' : Matrix (Fin n) (Fin n) K}
    (hchar : A.charpoly = A'.charpoly) (C : Matrix (Fin p) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K)
    (h : ∀ k, k < n → markov C A B k = markov C A' B k) :
    ∀ k, markov C A B k = markov C A' B k := by
  have hdeg : A.charpoly.natDegree = n := by
    rw [A.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hA' : aeval A' A.charpoly = 0 := by rw [hchar]; exact Matrix.aeval_self_charpoly A'
  simp only [markov] at h ⊢
  exact responses_agree_of_common_annihilator C B C B A.charpoly_monic
    (Matrix.aeval_self_charpoly A) hA' (fun k hk => h k (hdeg ▸ hk))

/-- [proved-derived; formal-checked] **The first `2n` Markov parameters separate two sources of
dimension `n`**, over every field: the statement `ReceiverAtlas.MarkovTwoNSuffices` held as a
`Prop`. -/
theorem markovTwoNSuffices (K : Type) [Field K] (n : ℕ) : MarkovTwoNSuffices K n := by
  intro m p L L' h k
  exact markov_agree_add L.readout L.state L.excitation L'.readout L'.state L'.excitation
    (fun k hk => h k (by omega)) k

end Markov

section Ruler

/-- [definition] The one-dimensional source over `ℚ` with generator `a` and unit ports. -/
def scalarSource (a : ℚ) : Linearization ℚ 1 1 1 where
  state := !![a]
  excitation := !![1]
  readout := !![1]

/-- [proved-derived; formal-checked] The scalar source's response at time `k` is `aᵏ`. -/
theorem scalarSource_markov (a : ℚ) (k : ℕ) :
    linearizationMarkov (scalarSource a) k = !![a ^ k] := by
  have hpow : (!![a] : Matrix (Fin 1) (Fin 1) ℚ) ^ k = !![a ^ k] := by
    induction k with
    | zero => ext i j; fin_cases i; fin_cases j; simp
    | succ k ih => rw [pow_succ, ih]; ext i j; fin_cases i; fin_cases j; simp [pow_succ]
  simp only [linearizationMarkov, markov, scalarSource]
  rw [hpow]
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- [counterexample; formal-checked] **One parameter does not separate dimension one.** The
sources `(1, 1, 1)` and `(1, 2, 1)` agree at every time below `1` and differ at time `1`. -/
theorem one_parameter_does_not_separate :
    (∀ k, k < 1 → linearizationMarkov (scalarSource 1) k = linearizationMarkov (scalarSource 2) k)
      ∧ linearizationMarkov (scalarSource 1) 1 ≠ linearizationMarkov (scalarSource 2) 1 := by
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain rfl : k = 0 := by omega
    rw [scalarSource_markov, scalarSource_markov]
    simp
  · rw [scalarSource_markov, scalarSource_markov]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

/-- [counterexample; formal-checked] **At dimension one the count `2n` is the least.** The
statement with `2n − 1 = n` parameters in place of `2n` fails over `ℚ`, while
`markovTwoNSuffices` holds: without a shared characteristic polynomial the bound `n` of
`ReceiverAtlas.markov_truncation` is not available. -/
theorem two_n_is_least_at_one :
    ¬ ∀ (L L' : Linearization ℚ 1 1 1),
        (∀ k, k < 2 * 1 - 1 → linearizationMarkov L k = linearizationMarkov L' k) →
          ∀ k, linearizationMarkov L k = linearizationMarkov L' k := by
  intro h
  exact one_parameter_does_not_separate.2
    (h (scalarSource 1) (scalarSource 2) (fun k hk => one_parameter_does_not_separate.1 k hk) 1)

end Ruler

section Tight

open Holonics.Aeon.Production.Zeta (mapMatrix mapMatrix_pow_apply)

/-- [definition] The cyclic step on `m + 1` states. -/
def step (m : ℕ) : Fin (m + 1) → Fin (m + 1) := fun i => i + 1

/-- [proved-derived; formal-checked] `k` cyclic steps from state `0` reach state
`k mod (m + 1)`. -/
theorem step_iterate_val (m k : ℕ) : ((step m)^[k] 0).val = k % (m + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', step, Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod,
      Nat.mod_add_mod]

/-- [proved-derived; formal-checked] The cyclic step reaches the last state from `0` at the
times `k ≡ m` modulo `m + 1`. -/
theorem step_reaches_last_iff (m k : ℕ) : (step m)^[k] 0 = Fin.last m ↔ k % (m + 1) = m := by
  rw [Fin.ext_iff, step_iterate_val, Fin.val_last]

/-- [definition] The cyclic source of dimension `m + 1` over `ℚ`: the cyclic step with gain `g`,
excited at the last state and read at state `0` with weight `c`. -/
def cyclicSource (m : ℕ) (g c : ℚ) : Linearization ℚ (m + 1) 1 1 where
  state := g • mapMatrix (step m)
  excitation := Matrix.of fun i _ => if i = Fin.last m then 1 else 0
  readout := Matrix.of fun _ j => if j = 0 then c else 0

/-- [proved-derived; formal-checked] The cyclic source responds `c·gᵏ` at the times `k ≡ m`
modulo `m + 1` and nothing at the others. -/
theorem cyclicSource_markov (m : ℕ) (g c : ℚ) (k : ℕ) :
    linearizationMarkov (cyclicSource m g c) k 0 0
      = if k % (m + 1) = m then c * g ^ k else 0 := by
  simp only [linearizationMarkov, markov, cyclicSource]
  rw [_root_.smul_pow, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, mapMatrix_pow_apply,
    smul_eq_mul]
  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single 0]
  · simp [step_reaches_last_iff]
  · intro x _ hx
    simp [hx]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- [counterexample; formal-checked] **The count `2n` is the least at every dimension `n ≥ 1`.**
Over `ℚ`, the cyclic sources of dimension `n = m + 1` with gains `1` and `2`, the second read
with weight `2^(−m)`, agree at every time below `2n − 1` and differ at time `2n − 1`. -/
theorem two_n_is_least (m : ℕ) :
    ¬ ∀ (L L' : Linearization ℚ (m + 1) 1 1),
        (∀ k, k < 2 * (m + 1) - 1 → linearizationMarkov L k = linearizationMarkov L' k) →
          ∀ k, linearizationMarkov L k = linearizationMarkov L' k := by
  intro h
  have hagree : ∀ k, k < 2 * (m + 1) - 1 →
      linearizationMarkov (cyclicSource m 1 1) k
        = linearizationMarkov (cyclicSource m 2 ((2 ^ m)⁻¹)) k := by
    intro k hk
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [cyclicSource_markov, cyclicSource_markov]
    by_cases hkm : k % (m + 1) = m
    · have hk' : k = m := by
        rcases Nat.lt_or_ge k (m + 1) with hlt | hge
        · rwa [Nat.mod_eq_of_lt hlt] at hkm
        · exfalso
          have h1 : k % (m + 1) = k - (m + 1) := by
            rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
          omega
      subst hk'
      rw [if_pos hkm, if_pos hkm, one_pow, mul_one, inv_mul_cancel₀ (by positivity)]
    · rw [if_neg hkm, if_neg hkm]
  have hdiff := congrFun (congrFun (h _ _ hagree (2 * m + 1)) 0) 0
  rw [cyclicSource_markov, cyclicSource_markov] at hdiff
  have hmod : (2 * m + 1) % (m + 1) = m := by
    rw [show 2 * m + 1 = m + (m + 1) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (Nat.lt_succ_self m)]
  rw [if_pos hmod, if_pos hmod] at hdiff
  have h2 : ((2 : ℚ) ^ m)⁻¹ * 2 ^ (2 * m + 1) = 2 ^ (m + 1) := by
    rw [show 2 * m + 1 = m + (m + 1) by ring, pow_add]
    field_simp
  rw [h2, one_pow, mul_one] at hdiff
  have h3 : (1 : ℚ) < 2 ^ (m + 1) := one_lt_pow₀ (by norm_num) (by omega)
  linarith

end Tight

end Holonics.Foundation.MarkovSeparation
