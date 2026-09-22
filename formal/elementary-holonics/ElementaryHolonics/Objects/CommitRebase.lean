import ElementaryHolonics.Transport.AccumulatedReceiverDefect

/-!
# Commit and rebase: a published centre with a recorded residual

[definition] Objects 8 and 10 of `docs/ELEMENTARY_OBJECTS.md`: the law the native enclosure
commit implements (worker E). An enclosure ball `B(x̂, r)` is committed by publishing a (dyadic)
centre `c` and recording a residual `ρ ≥ ‖x̂ − c‖`. Later steps read the point `c`; the residual is
a ledger entry, not a radius carried into every read. **Radius propagation** instead carries the
ball into every later read.

[proved-derived; formal-checked] What is proved.

1. **One step.** A step with Lipschitz constant `K` from `c` differs from the step from `x̂` by at
   most `K ρ` (`rebase_step_residual`); witness `x̂ = 1/3`, `c = 5/16`, `ρ = 1/48`, `F = 2x`
   attains it (`dyadic_rebase_witness`).
2. **`n` commits.** If each commit publishes within `r_i` of the step it commits, and every step
   is `K`-Lipschitz, the committed trajectory stays within `Σ_(i<n) K^(n−1−i) r_i` of the exact
   one (`commit_chain_residual`), composing `Transport/AccumulatedReceiverDefect.distance_le_budget`
   (the telephone chain) and evaluating its expansion at constant `K`
   (`expansion_const`).
3. **Radius propagation.** The propagated radius `R_(i+1) = K R_i + r_i` is the same number,
   `R_n = Σ_(i<n) K^(n−1−i) r_i` (`propagatedRadius_eq`). The difference between the two laws is
   where that number goes — into every later read (propagation) or into a ledger no read consumes
   (rebase) — which is a statement about the implementation, not a theorem proved here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Soma.Holonics.Objects.CommitRebase

open Soma.Holonics.Transport.AccumulatedReceiverDefect

/-- [proved-derived; formal-checked] **One rebased step.** -/
theorem rebase_step_residual {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (F : X → Y) {K : ℝ} (hK : 0 ≤ K) (lip : ∀ x y, ‖F x - F y‖ ≤ K * ‖x - y‖)
    {xh c : X} {ρ : ℝ} (hρ : ‖xh - c‖ ≤ ρ) : ‖F c - F xh‖ ≤ K * ρ := by
  calc ‖F c - F xh‖ ≤ K * ‖c - xh‖ := lip c xh
    _ = K * ‖xh - c‖ := by rw [norm_sub_rev]
    _ ≤ K * ρ := mul_le_mul_of_nonneg_left hρ hK

/-- [proved-derived; formal-checked] Witness: `x̂ = 1/3`, dyadic centre `5/16`, residual `1/48`,
step `x ↦ 2x`: the step from the centre is off by exactly `2 · 1/48`. -/
theorem dyadic_rebase_witness :
    ‖((1 : ℝ) / 3) - 5 / 16‖ ≤ 1 / 48 ∧ ‖(2 * (5 / 16 : ℝ)) - 2 * (1 / 3)‖ = 2 * (1 / 48) := by
  constructor <;> norm_num [Real.norm_eq_abs, abs_of_pos, abs_of_neg]

/-- [proved-derived; formal-checked] The telephone-chain expansion at a constant rate `K` and zero
initial defect is `Σ_(i<n) r_i K^(n−1−i)`. -/
theorem expansion_const (K : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    expansion (fun _ => K) r 0 n = ∑ i ∈ Finset.range n, r i * K ^ (n - 1 - i) := by
  simp only [expansion, zero_mul, zero_add, Finset.prod_const, Nat.card_Ico, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 2
  have := Finset.mem_range.mp hi
  omega

/-- [proved-derived; formal-checked] **`n` commits.** Exact trajectory `x_(i+1) = F_i x_i`,
committed trajectory `y` with `y₀ = x₀` and each commit within `r_i` of the step it commits
(`‖F_i y_i − y_(i+1)‖ ≤ r_i`), all steps `K`-Lipschitz: `‖x_n − y_n‖ ≤ Σ_(i<n) K^(n−1−i) r_i`. -/
theorem commit_chain_residual {X : Type*} [NormedAddCommGroup X] (F : ℕ → X → X)
    (x y : ℕ → X) {K : ℝ} (hK : 0 ≤ K) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (h0 : x 0 = y 0) (hx : ∀ i, x (i + 1) = F i (x i))
    (lip : ∀ i a b, ‖F i a - F i b‖ ≤ K * ‖a - b‖)
    (commit : ∀ i, ‖F i (y i) - y (i + 1)‖ ≤ r i) (n : ℕ) :
    ‖x n - y n‖ ≤ ∑ i ∈ Finset.range n, r i * K ^ (n - 1 - i) := by
  rw [← expansion_const]
  exact distance_le_budget F (fun i _ => y (i + 1)) x y (fun _ => K) r 0
    (by rw [h0, sub_self, norm_zero]) hx (fun _ => rfl) (fun _ => hK) hr lip commit n

/-- [definition] The radius carried by propagation: `R₀ = 0`, `R_(i+1) = K R_i + r_i`. -/
def propagatedRadius (K : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => K * propagatedRadius K r i + r i

/-- [proved-derived; formal-checked] The propagated radius equals the rebase ledger bound. -/
theorem propagatedRadius_eq (K : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    propagatedRadius K r n = ∑ i ∈ Finset.range n, r i * K ^ (n - 1 - i) := by
  induction n with
  | zero => simp [propagatedRadius]
  | succ n ih =>
      rw [propagatedRadius, ih, Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        have := Finset.mem_range.mp hi
        rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ]
        ring
      · simp

section Audit
#print axioms rebase_step_residual
#print axioms dyadic_rebase_witness
#print axioms expansion_const
#print axioms commit_chain_residual
#print axioms propagatedRadius_eq
end Audit

end Soma.Holonics.Objects.CommitRebase
