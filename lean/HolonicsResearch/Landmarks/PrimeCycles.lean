import Holonics.Compression.Landmark.PrimitiveCycle
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Primes as primitive cycles: one cycle machine carries the return-map zeta and the Euler product

[definition] Rebuild step 3 (#145), the null-cone record §5. A **cycle machine** has one site per
primitive cycle `i`, of length `ℓ_i`, carrying the material `exp(−s·ℓ_i)` at the complex clock
`s`: `M = diag(exp(−s ℓ_i))` (`cycleMachine`). Its transfer determinant is the Euler product over
its sites, `det(1 − M) = ∏_i (1 − exp(−s ℓ_i))` (`cycleMachine_det`), and its closed-word faces
are `tr(Mᵏ) = Σ_i exp(−s ℓ_i)ᵏ` (`cycleMachine_trace_pow`).

[proved-derived; formal-checked] Two instances of that one construction.

1. **A finite return map** (`Compression/Landmark/PrimitiveCycle`). Take its primitive cycles
   (`primitiveCycles f d`) with their integer lengths `d`. The cycle machine's transfer determinant
   is the return map's transfer determinant `det(1 − T·M_f)` at `T = e^{−s}`, which
   `PrimitiveCycle.transfer_determinant_euler_product` writes as `∏_d (1 − T^d)^(p_d)`
   (`returnMap_cycleMachine_det`).
2. **The primes below `N`** (Mathlib's `riemannZeta_eulerProduct`). Take one site per prime `p < N`
   with length `log p`. Then `exp(−s log p) = p^(−s)`, the cycle machine's transfer determinant is
   the truncated Euler product `∏_(p<N) (1 − p^(−s))` (`primeMachine_det`), and its inverse tends to
   `ζ(s)` for `Re s > 1` (`primeMachine_tendsto_zeta`). Its closed-word faces are the prime-power
   weights `Σ_(p<N) p^(−ks)` (`primeMachine_trace_pow`).

[interpretation; formal-checked] **The analogy, with its exact form** (`counting_forms`). The machine
counts closed aeons of `n` epochs as `N_n = Σ_(d∣n) d·p_d` (`PrimitiveCycle.periodic_count`); the
integers weigh `log n = Σ_(d∣n) Λ(d)` with `Λ(p^k) = log p` (Mathlib's `vonMangoldt_sum`,
`vonMangoldt_apply_pow`). The primitive length `d` of a cycle plays the part of `log p`, the length
of the prime's orbit.

[counterexample; formal-checked] **`ζ` is not the zeta of a finite return map.**
- A finite return map on `α` has at most `#α` primitive cycles (`primitive_cycles_le_card`), while
  the primes below `N` outgrow every bound (`primes_outgrow_every_return_map`).
- The prime lengths are not the integer lengths of any return map: `0 < log 2 < 1`
  (`log_two_not_a_cycle_length`).

The identification holds only through the cycle machine's truncations and their limit.

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Landmarks.PrimeCycles

open Finset Filter Topology
open Holonics.Compression.Landmark.PrimitiveCycle
open Holonics.Aeon.Production.Zeta

/-! ## 1. The cycle machine -/

section CycleMachine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The cycle machine**: one site per primitive cycle of length `ℓ i`, carrying
`exp(−s·ℓ i)` at the complex clock `s`. -/
def cycleMachine (ℓ : ι → ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => Complex.exp (-s * (ℓ i : ℂ))

/-- [proved-derived; formal-checked] **The transfer determinant of the cycle machine is the Euler
product over its sites.** -/
theorem cycleMachine_det (ℓ : ι → ℝ) (s : ℂ) :
    (1 - cycleMachine ℓ s).det = ∏ i, (1 - Complex.exp (-s * (ℓ i : ℂ))) := by
  rw [cycleMachine, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal]

/-- [proved-derived; formal-checked] **The closed-word faces of the cycle machine.** -/
theorem cycleMachine_trace_pow (ℓ : ι → ℝ) (s : ℂ) (k : ℕ) :
    ((cycleMachine ℓ s) ^ k).trace = ∑ i, Complex.exp (-s * (ℓ i : ℂ)) ^ k := by
  rw [cycleMachine, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

end CycleMachine

/-! ## 2. The return-map instance -/

section ReturnMap

variable {α : Type*} [Fintype α] [DecidableEq α] (f : α → α)

/-- [definition] The primitive cycles of a finite return map, with their lengths. -/
def cycles : Finset (Σ _ : ℕ, Cycle α) :=
  (Icc 1 (Fintype.card α)).sigma fun d => primitiveCycles f d

/-- [proved-derived; formal-checked] **The cycle machine of a return map is its transfer
determinant**: with one site per primitive cycle of length `d`, `det(1 − M)` is
`det(1 − T·M_f)` at `T = e^{−s}`, i.e. `∏_d (1 − T^d)^(p_d)`. -/
theorem returnMap_cycleMachine_det (s : ℂ) :
    (1 - cycleMachine (ι := cycles f) (fun c => ((c : Σ _ : ℕ, Cycle α).1 : ℝ)) s).det =
      Polynomial.aeval (Complex.exp (-s)) (mapMatrix f).charpolyRev := by
  rw [cycleMachine_det, transfer_determinant_euler_product, map_prod,
    Finset.prod_coe_sort (cycles f) (fun c => 1 - Complex.exp (-s * ((c.1 : ℕ) : ℝ))), cycles,
    Finset.prod_sigma]
  refine Finset.prod_congr rfl fun d _ => ?_
  dsimp only
  rw [Finset.prod_const, primitiveCount, map_pow, map_sub, map_one, map_pow,
    Polynomial.aeval_X]
  congr 1
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [mul_comm]

/-- [proved-derived; formal-checked] **A finite return map has at most `#α` primitive cycles**: the
`d · p_d` occurrences of the length-`d` cycles are disjoint. -/
theorem primitive_cycles_le_card :
    ∑ d ∈ Icc 1 (Fintype.card α), primitiveCount f d ≤ Fintype.card α := by
  have hle : ∑ d ∈ Icc 1 (Fintype.card α), primitiveCount f d ≤
      ∑ d ∈ Icc 1 (Fintype.card α), d * primitiveCount f d :=
    Finset.sum_le_sum fun d hd => Nat.le_mul_of_pos_left _ (by simp at hd; omega)
  refine hle.trans ?_
  rw [← Finset.sum_congr rfl fun d hd => card_minimalPeriod_eq f d (by simp at hd; omega)]
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro d _ d' _ hdd'
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact hdd' (h1.symm.trans h2)

end ReturnMap

/-! ## 3. The prime instance -/

/-- [definition] **The prime machine below `N`**: the cycle machine with one site per prime
`p < N`, of length `log p`. -/
def primeMachine (s : ℂ) (N : ℕ) : Matrix (Nat.primesBelow N) (Nat.primesBelow N) ℂ :=
  cycleMachine (fun p : Nat.primesBelow N => Real.log (p : ℕ)) s

/-- [proved-derived; formal-checked] **A prime site carries `p^(−s)`**: `exp(−s log p) = p^(−s)`. -/
theorem exp_neg_log_eq_cpow {p : ℕ} (hp : 0 < p) (s : ℂ) :
    Complex.exp (-s * ((Real.log p : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp', Complex.ofReal_log (by positivity), Complex.ofReal_natCast,
    mul_comm]

/-- [proved-derived; formal-checked] **The prime machine's transfer determinant is the truncated
Euler product** `∏_(p<N) (1 − p^(−s))`. -/
theorem primeMachine_det (s : ℂ) (N : ℕ) :
    (1 - primeMachine s N).det = ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-s)) := by
  rw [primeMachine, cycleMachine_det]
  rw [← Finset.prod_coe_sort (Nat.primesBelow N) (fun p => 1 - (p : ℂ) ^ (-s))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : 0 < (p : ℕ) := (Nat.prime_of_mem_primesBelow p.2).pos
  rw [exp_neg_log_eq_cpow hp]

/-- [proved-derived; formal-checked] **The prime machine's closed-word faces are the prime-power
weights** `Σ_(p<N) p^(−ks)`. -/
theorem primeMachine_trace_pow (s : ℂ) (N k : ℕ) :
    ((primeMachine s N) ^ k).trace = ∑ p ∈ Nat.primesBelow N, ((p : ℂ) ^ (-s)) ^ k := by
  rw [primeMachine, cycleMachine_trace_pow]
  rw [← Finset.sum_coe_sort (Nat.primesBelow N) (fun p => ((p : ℂ) ^ (-s)) ^ k)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : 0 < (p : ℕ) := (Nat.prime_of_mem_primesBelow p.2).pos
  rw [exp_neg_log_eq_cpow hp]

/-- [proved-derived; formal-checked] **The inverse transfer determinants of the prime machines tend
to `ζ(s)`** for `Re s > 1` (Mathlib's `riemannZeta_eulerProduct`). -/
theorem primeMachine_tendsto_zeta {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ((1 - primeMachine s N).det)⁻¹) atTop (𝓝 (riemannZeta s)) := by
  have h := riemannZeta_eulerProduct hs
  refine h.congr fun N => ?_
  rw [primeMachine_det, Finset.prod_inv_distrib]

/-! ## 4. The analogy and its refusals -/

/-- [interpretation; formal-checked] **The counting forms.** A finite return map counts its closed
aeons of `n` epochs by its primitive cycles weighted by their lengths, `N_n = Σ_(d∣n) d·p_d`; the
integers weigh `log n = Σ_(d∣n) Λ(d)`, where `Λ(p^k) = log p` is the length of the prime's
orbit. -/
theorem counting_forms {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter fun x => f^[n] x = x).card = ∑ d ∈ n.divisors, d * primitiveCount f d ∧
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d = Real.log n ∧
      ∀ p k : ℕ, p.Prime → k ≠ 0 → ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p :=
  ⟨periodic_count f n hn, ArithmeticFunction.vonMangoldt_sum, fun _ _ hp hk => by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]⟩

/-- [counterexample; formal-checked] **The primes outgrow every finite return map**: for every
finite return map there is a truncation with more prime sites than the map has primitive
cycles. -/
theorem primes_outgrow_every_return_map {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) :
    ∃ N, ∑ d ∈ Icc 1 (Fintype.card α), primitiveCount f d < (Nat.primesBelow N).card := by
  refine ⟨Nat.nth Nat.Prime (Fintype.card α + 1), ?_⟩
  refine lt_of_le_of_lt (primitive_cycles_le_card f) ?_
  rw [Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting'_nth_eq]
  omega

/-- [counterexample; formal-checked] **`log 2` is not the length of a cycle**: `0 < log 2 < 1`, so
no return map (whose cycle lengths are positive integers) has the prime `2`'s orbit. -/
theorem log_two_not_a_cycle_length : 0 < Real.log 2 ∧ Real.log 2 < 1 ∧ ∀ d : ℕ, Real.log 2 ≠ d := by
  have h0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  refine ⟨h0, h1, fun d hd => ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd'
  · simp at hd; linarith
  · have : (1 : ℝ) ≤ d := by exact_mod_cast hd'
    linarith

section Audit
#print axioms cycleMachine_det
#print axioms cycleMachine_trace_pow
#print axioms returnMap_cycleMachine_det
#print axioms primitive_cycles_le_card
#print axioms exp_neg_log_eq_cpow
#print axioms primeMachine_det
#print axioms primeMachine_trace_pow
#print axioms primeMachine_tendsto_zeta
#print axioms counting_forms
#print axioms primes_outgrow_every_return_map
#print axioms log_two_not_a_cycle_length
end Audit

end Holonics.Landmarks.PrimeCycles
