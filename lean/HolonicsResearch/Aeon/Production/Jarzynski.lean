import Mathlib

/-!
# A driven aeon: the mean of `exp(−β W)` is fixed by the two bounding constitutions

`Holonics/Aeon/Production/PathReversal` owns the production of a **stationary** aeon: one chain
`P`, one law `π`, `σₙ = D(P_γ ‖ P_(Rγ)) ≥ 0`, additive over epochs, zero exactly under detailed
balance. `Aeon/Production/Kolmogorov` owns the converse of the cycle criterion. Here the aeon is
**driven**: the constitution's energies change along the clock, tick by tick, so no one law is
stationary and the path law is not the reversal's. The notation follows `PathReversal`: an aeon of
`n` epochs is a path `γ : Fin (n+1) → S`, its reversal is `γ ∘ Fin.rev`, and `pathProb`, `revProb`
are the driven `pathLaw` and the law of the reversed protocol. This file imports Mathlib alone.

[definition] **The setting.** States `S` (finite, inhabited). A protocol of energies
`E : ℕ → S → ℝ`, an inverse temperature `β`, Boltzmann weights `w t x = exp(−β E t x)`
(`weight`), their sum `Z t` (`partition`) and the free energy `F t = −(1/β) log Z t`
(`freeEnergy`). Kernels `K : ℕ → S → S → ℝ` with nonnegative entries, unit rows and the weight of
their own tick stationary, `Σ_x w t x · K t x y = w t y` (`Driven`). One tick `t → t+1` is a
**work step** (the energies move from `E t` to `E (t+1)` at a held state, the work
`E (t+1) x − E t x`) followed by a **heat step** (the state moves by `K (t+1)`):

```text
pathProb γ = w 0 (γ₀)/Z 0 · ∏_(t<n) K (t+1) (γ_t, γ_(t+1))
work γ     = Σ_(t<n) (E (t+1) (γ_t) − E t (γ_t))
revProb γ' = w n (γ'₀)/Z n · ∏_(s<n) K (n−s) (γ'_s, γ'_(s+1))        (heat step first)
```

The reversed protocol runs the same kernels in the opposite order, and in each of its ticks the
heat step comes **before** the work step: started from `w n / Z n`, its tick `s` moves the state by
`K (n−s)` at the energies `E (n−s)` and then lowers the energies to `E (n−s−1)`. That order is
forced by the forward convention, and `n = 1` shows it: forward `x₀ → x₁` by `K 1` after the
energies reached `E 1`, so the reverse must use `K 1` while the energies are still `E 1`.

[proved-standard; formal-checked] What is proved (Jarzynski 1997, Crooks 1999; finite chains).

0. **The driven path law is a law** (`pathProb_nonneg`, `sum_pathProb`), and so is the reversed
   protocol's (`revProb_nonneg`, `sum_revProb`), from nonnegative entries and unit rows alone.
1. **Jarzynski's equality** (`jarzynski`): `Σ_γ pathProb γ · exp(−β · work γ) = Z n / Z 0`, for
   every protocol, every length and every kernel that keeps its tick's weight stationary. Detailed
   balance is not used, and the driving's speed does not enter. The proof is the marginal at the
   last occurrence (`jarzynski_marginal`): the work-weighted law of `γ_n` is `w n / Z 0`, the
   weight of the current constitution over the first one's sum. In free-energy form
   (`jarzynski_freeEnergy`): `Σ_γ pathProb γ · exp(−β (work γ − ΔF)) = 1`.
2. **The second law in the mean** (`second_law`): for `β > 0`,
   `F n − F 0 ≤ Σ_γ pathProb γ · work γ`. Equality holds only when the work is the free-energy
   difference on every path of positive weight (`work_eq_of_second_law_eq`).
3. **No driving** (`work_eq_zero_of_static`, `partition_static`, `jarzynski_static`): with
   `E t = E 0` the work vanishes on every path and the equality reads `1 = 1`.
4. **Crooks' relation** (`crooks`): under detailed balance at each tick,
   `w t x · K t x y = w t y · K t y x`, for every path
   `pathProb γ · exp(−β · work γ) · Z 0 = revProb (γ ∘ Fin.rev) · Z n`, and where the reversed
   weight is not zero `pathProb γ / revProb (γ ∘ Fin.rev) = exp(β (work γ − ΔF))`
   (`crooks_ratio`). A path of positive forward weight has positive reversed weight
   (`revProb_pos_of_pathProb_pos`).
5. **Dissipated work is the production of the driven aeon** (`dissipated_work_eq_relativeEntropy`):
   `Σ_γ pathProb γ · log(pathProb γ / revProb (γ ∘ Fin.rev)) = β (Σ_γ pathProb γ · work γ − ΔF)`.
   The left side is the relative entropy of the forward path law against the reversed protocol's
   law of the reversed path, the driven form of `PathReversal.production`; with no driving and one
   kernel (`E t = E 0`, `K t = P`) it is that production at the law `π = w 0 / Z 0`.

[interpretation] The reading on the objects. A work step changes the constitution at a held state
and a heat step is the state's motion against the constitution of its tick; the weights
`exp(−β W)` are the ratio of consecutive constitutions read at the place the aeon holds. The
equality says that this ratio, carried along any aeon, has a mean fixed by the two bounding
constitutions: a count over paths decides `Z n / Z 0`, and the route between them does not enter.

**What this does not state.** No continuous time, no infinite state space and no Hamiltonian
dynamics: the chain is finite and the clock is discrete. The kernels are given with their
stationarity as a hypothesis; nothing constructs them from a constitution (Glauber or Metropolis
rates are not built). `second_law` is the inequality in the mean only: a single aeon can have
`work γ < ΔF`, and no bound on that probability is proved here. Crooks' relation is stated per
path; the ratio of the two laws of the work as distributions on `ℝ` is not derived from it. The
join to `PathReversal.production` at `E t = E 0`, `K t = P` is described above and not formalized,
since this file imports Mathlib alone. The words work, heat and free energy are the canonical
chart's; nothing here derives that chart.

No `axiom`, no `sorry`.
-/

open Finset

noncomputable section

namespace Holonics.Aeon.Production.Jarzynski

/-! ## 1. Weights, work, and the snoc forms that need no sum over states -/

section Pointwise

variable {S : Type*}

/-- [definition] The Boltzmann weight of state `x` under the energies of tick `t`. -/
def weight (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) : ℝ := Real.exp (-β * E t x)

/-- [definition] The work along an aeon: at each tick the energies change at the held state. -/
def work (E : ℕ → S → ℝ) (n : ℕ) (γ : Fin (n + 1) → S) : ℝ :=
  ∑ t : Fin n, (E ((t : ℕ) + 1) (γ t.castSucc) - E (t : ℕ) (γ t.castSucc))

/-- [definition] Detailed balance of each tick's kernel against that tick's weight. -/
def DetailedBalance (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) : Prop :=
  ∀ t x y, weight β E t x * K t x y = weight β E t y * K t y x

theorem weight_pos (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) : 0 < weight β E t x :=
  Real.exp_pos _

/-- [proved-derived; formal-checked] A work step multiplies the weight at the held state by
`exp(−β · work)`: the ratio of consecutive constitutions read at one place. -/
theorem weight_succ (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) :
    weight β E t x * Real.exp (-β * (E (t + 1) x - E t x)) = weight β E (t + 1) x := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

theorem work_snoc (E : ℕ → S → ℝ) {n : ℕ} (γ : Fin (n + 1) → S) (y : S) :
    work E (n + 1) (Fin.snoc γ y) =
      work E n γ + (E (n + 1) (γ (Fin.last n)) - E n (γ (Fin.last n))) := by
  unfold work
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last]

/-- [proved-derived; formal-checked] **No driving, no work.** -/
theorem work_eq_zero_of_static {E : ℕ → S → ℝ} (hE : ∀ t, E t = E 0) {n : ℕ}
    (γ : Fin (n + 1) → S) : work E n γ = 0 := by
  unfold work
  refine sum_eq_zero fun t _ => ?_
  rw [hE ((t : ℕ) + 1), hE (t : ℕ), sub_self]

end Pointwise

/-! ## 2. The driven path law -/

variable {S : Type*} [Fintype S]

/-- [definition] The sum of the weights of tick `t`. -/
def partition (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) : ℝ := ∑ x, weight β E t x

/-- [definition] The free energy of tick `t`: `F t = −(1/β) log Z t`. -/
def freeEnergy (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) : ℝ := -(1 / β) * Real.log (partition β E t)

/-- [definition] The law of a driven aeon: the first constitution's weight at `γ₀`, then at tick
`t` the kernel of the energies just reached. -/
def pathProb (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (n : ℕ) (γ : Fin (n + 1) → S) : ℝ :=
  weight β E 0 (γ 0) / partition β E 0 *
    ∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)

/-- [definition] The law of the reversed protocol: started from the last constitution's weight,
the same kernels in the opposite order, each heat step before its work step. The index
`(s.rev : ℕ) + 1` is `n − s` (`rev_index`). -/
def revProb (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (n : ℕ) (γ : Fin (n + 1) → S) : ℝ :=
  weight β E n (γ 0) / partition β E n *
    ∏ s : Fin n, K ((s.rev : ℕ) + 1) (γ s.castSucc) (γ s.succ)

/-- [definition] A driven chain: nonnegative kernels with unit rows, each keeping the weight of
its own tick stationary. -/
structure Driven (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) : Prop where
  nonneg : ∀ t x y, 0 ≤ K t x y
  row : ∀ t x, ∑ y, K t x y = 1
  stationary : ∀ t y, ∑ x, weight β E t x * K t x y = weight β E t y

variable {β : ℝ} {E : ℕ → S → ℝ} {K : ℕ → S → S → ℝ}

theorem rev_index {n : ℕ} (s : Fin n) : ((s.rev : ℕ) + 1) = n - (s : ℕ) := by
  rw [Fin.val_rev]
  have := s.isLt
  omega

theorem partition_pos [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) : 0 < partition β E t :=
  sum_pos (fun x _ => weight_pos β E t x) univ_nonempty

theorem partition_static {E : ℕ → S → ℝ} (hE : ∀ t, E t = E 0) (β : ℝ) (n : ℕ) :
    partition β E n = partition β E 0 := by
  unfold partition weight
  rw [hE n]

/-- [proved-derived; formal-checked] Detailed balance with unit rows keeps each tick's weight
stationary. -/
theorem Driven.of_detailedBalance (hK : ∀ t x y, 0 ≤ K t x y) (hrow : ∀ t x, ∑ y, K t x y = 1)
    (hdb : DetailedBalance β E K) : Driven β E K where
  nonneg := hK
  row := hrow
  stationary := fun t y => by
    simp_rw [hdb t _ y, ← mul_sum, hrow t y, mul_one]

/-- [proved-derived; formal-checked] `exp(−β ΔF) = Z n / Z 0`. -/
theorem exp_neg_freeEnergy_diff [Nonempty S] (hβ : β ≠ 0) (E : ℕ → S → ℝ) (n : ℕ) :
    Real.exp (-β * (freeEnergy β E n - freeEnergy β E 0)) =
      partition β E n / partition β E 0 := by
  have h : -β * (freeEnergy β E n - freeEnergy β E 0) =
      Real.log (partition β E n) - Real.log (partition β E 0) := by
    unfold freeEnergy
    field_simp
    ring
  rw [h, Real.exp_sub, Real.exp_log (partition_pos β E n), Real.exp_log (partition_pos β E 0)]

/-! ## 3. Aeons of `n + 1` epochs are aeons of `n` epochs and one more occurrence -/

theorem sum_snoc {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 2) → S) → M) :
    ∑ γ', F γ' = ∑ γ : Fin (n + 1) → S, ∑ y, F (Fin.snoc γ y) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => S)) (fun p => F (Fin.snoc p.2 p.1)) F
    (fun _ => rfl), Fintype.sum_prod_type, sum_comm]

theorem sum_fin_one {M : Type*} [AddCommMonoid M] (F : (Fin 1 → S) → M) :
    ∑ γ, F γ = ∑ x, F (fun _ => x) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ fun γ => by
    congr 1; funext i; rw [Subsingleton.elim i default]; rfl

theorem pathProb_snoc (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) {n : ℕ}
    (γ : Fin (n + 1) → S) (y : S) :
    pathProb β E K (n + 1) (Fin.snoc γ y) =
      pathProb β E K n γ * K (n + 1) (γ (Fin.last n)) y := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc γ y : Fin (n + 2) → S) 0 = γ 0 := by
    simp
  simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last]
  ring

/-- [proved-derived; formal-checked] Peeling the last tick of the reversed protocol leaves the
reversed protocol of the shifted energies and kernels, then the kernel `K 1`. -/
theorem revProb_snoc (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) {n : ℕ}
    (γ : Fin (n + 1) → S) (y : S) :
    revProb β E K (n + 1) (Fin.snoc γ y) =
      revProb β (fun t => E (t + 1)) (fun t => K (t + 1)) n γ * K 1 (γ (Fin.last n)) y := by
  unfold revProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc γ y : Fin (n + 2) → S) 0 = γ 0 := by
    simp
  simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last,
    Fin.rev_castSucc, Fin.val_succ, Fin.rev_last, Fin.val_zero, zero_add]
  rw [← mul_assoc]
  rfl

/-! ## 4. Both laws are laws -/

theorem pathProb_nonneg [Nonempty S] (h : Driven β E K) {n : ℕ} (γ : Fin (n + 1) → S) :
    0 ≤ pathProb β E K n γ :=
  mul_nonneg (div_nonneg (weight_pos β E 0 _).le (partition_pos β E 0).le)
    (prod_nonneg fun _ _ => h.nonneg _ _ _)

theorem revProb_nonneg [Nonempty S] (hK : ∀ t x y, 0 ≤ K t x y) {n : ℕ} (γ : Fin (n + 1) → S) :
    0 ≤ revProb β E K n γ :=
  mul_nonneg (div_nonneg (weight_pos β E n _).le (partition_pos β E n).le)
    (prod_nonneg fun _ _ => hK _ _ _)

/-- [proved-derived; formal-checked] **The driven path law has total mass one**, from unit rows. -/
theorem sum_pathProb [Nonempty S] (hrow : ∀ t x, ∑ y, K t x y = 1) (n : ℕ) :
    ∑ γ, pathProb β E K n γ = 1 := by
  induction n with
  | zero =>
    rw [sum_fin_one]
    simp only [pathProb, univ_eq_empty, prod_empty, mul_one]
    rw [← sum_div]
    exact div_self (partition_pos β E 0).ne'
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [pathProb_snoc, ← mul_sum, hrow, mul_one]
    exact ih

/-- [proved-derived; formal-checked] **The reversed protocol's law has total mass one**, from unit
rows. -/
theorem sum_revProb [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) {K : ℕ → S → S → ℝ}
    (hrow : ∀ t x, ∑ y, K t x y = 1) (n : ℕ) :
    ∑ γ, revProb β E K n γ = 1 := by
  induction n generalizing E K with
  | zero =>
    rw [sum_fin_one]
    simp only [revProb, univ_eq_empty, prod_empty, mul_one]
    rw [← sum_div]
    exact div_self (partition_pos β E 0).ne'
  | succ n ih =>
    rw [sum_snoc]
    simp_rw [revProb_snoc, ← mul_sum, hrow, mul_one]
    exact ih (fun t => E (t + 1)) (fun t x => hrow (t + 1) x)

/-! ## 5. Jarzynski's equality -/

/-- [proved-standard; formal-checked] **The work-weighted law of the last occurrence is the
current constitution's weight over the first one's sum.** -/
theorem jarzynski_marginal [Nonempty S] (h : Driven β E K) (n : ℕ) (g : S → ℝ) :
    ∑ γ : Fin (n + 1) → S,
        pathProb β E K n γ * Real.exp (-β * work E n γ) * g (γ (Fin.last n)) =
      ∑ x, weight β E n x / partition β E 0 * g x := by
  induction n generalizing g with
  | zero =>
    rw [sum_fin_one]
    simp [pathProb, work]
  | succ n ih =>
    rw [sum_snoc]
    have hstep : ∀ γ : Fin (n + 1) → S,
        ∑ y, pathProb β E K (n + 1) (Fin.snoc γ y) *
            Real.exp (-β * work E (n + 1) (Fin.snoc γ y)) *
            g ((Fin.snoc γ y : Fin (n + 2) → S) (Fin.last (n + 1))) =
          pathProb β E K n γ * Real.exp (-β * work E n γ) *
            (fun x => Real.exp (-β * (E (n + 1) x - E n x)) * ∑ y, K (n + 1) x y * g y)
              (γ (Fin.last n)) := by
      intro γ
      simp only [pathProb_snoc, work_snoc, Fin.snoc_last, mul_add, Real.exp_add, mul_sum]
      exact sum_congr rfl fun y _ => by ring
    simp_rw [hstep]
    rw [ih (fun x => Real.exp (-β * (E (n + 1) x - E n x)) * ∑ y, K (n + 1) x y * g y)]
    have hx : ∀ x, weight β E n x / partition β E 0 *
          (Real.exp (-β * (E (n + 1) x - E n x)) * ∑ y, K (n + 1) x y * g y) =
        ∑ y, weight β E (n + 1) x * K (n + 1) x y * (g y / partition β E 0) := by
      intro x
      rw [← weight_succ β E n x, mul_sum, mul_sum]
      exact sum_congr rfl fun y _ => by ring
    simp_rw [hx]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_mul, h.stationary (n + 1) y]
    ring

/-- [proved-standard; formal-checked] **Jarzynski's equality** for a driven finite chain:
the mean of `exp(−β · work)` over the driven aeons is `Z n / Z 0`. -/
theorem jarzynski [Nonempty S] (h : Driven β E K) (n : ℕ) :
    ∑ γ, pathProb β E K n γ * Real.exp (-β * work E n γ) =
      partition β E n / partition β E 0 := by
  have hm := jarzynski_marginal h n (fun _ => 1)
  simp only [mul_one] at hm
  rw [hm, ← sum_div]
  rfl

/-- [proved-standard; formal-checked] Jarzynski's equality in free-energy form:
`Σ_γ pathProb γ · exp(−β (work γ − ΔF)) = 1`. -/
theorem jarzynski_freeEnergy [Nonempty S] (h : Driven β E K) (hβ : β ≠ 0) (n : ℕ) :
    ∑ γ, pathProb β E K n γ *
        Real.exp (-β * (work E n γ - (freeEnergy β E n - freeEnergy β E 0))) = 1 := by
  have hZ0 := (partition_pos β E 0).ne'
  have hZn := (partition_pos β E n).ne'
  have hterm : ∀ γ : Fin (n + 1) → S, pathProb β E K n γ *
        Real.exp (-β * (work E n γ - (freeEnergy β E n - freeEnergy β E 0))) =
      pathProb β E K n γ * Real.exp (-β * work E n γ) *
        (partition β E 0 / partition β E n) := by
    intro γ
    have hsplit : -β * (work E n γ - (freeEnergy β E n - freeEnergy β E 0)) =
        -β * work E n γ - -β * (freeEnergy β E n - freeEnergy β E 0) := by ring
    rw [hsplit, Real.exp_sub, exp_neg_freeEnergy_diff hβ E n]
    field_simp
  simp_rw [hterm]
  rw [← sum_mul, jarzynski h n]
  field_simp

/-- [proved-derived; formal-checked] With no driving the equality reads `1 = 1`. -/
theorem jarzynski_static [Nonempty S] (h : Driven β E K) (hE : ∀ t, E t = E 0) (n : ℕ) :
    ∑ γ, pathProb β E K n γ * Real.exp (-β * work E n γ) = 1 := by
  rw [jarzynski h n, partition_static hE β n]
  exact div_self (partition_pos β E 0).ne'

/-! ## 6. The second law in the mean -/

/-- [proved-standard; formal-checked] **The second law in the mean**: the mean work of a driven
aeon is at least the free-energy difference of its two bounding constitutions. -/
theorem second_law [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (n : ℕ) :
    freeEnergy β E n - freeEnergy β E 0 ≤ ∑ γ, pathProb β E K n γ * work E n γ := by
  set ΔF := freeEnergy β E n - freeEnergy β E 0 with hΔF
  have h1 := jarzynski_freeEnergy h hβ.ne' n
  rw [← hΔF] at h1
  have h2 : ∑ γ, pathProb β E K n γ * (1 + -β * (work E n γ - ΔF)) ≤
      ∑ γ, pathProb β E K n γ * Real.exp (-β * (work E n γ - ΔF)) :=
    sum_le_sum fun γ _ => mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (-β * (work E n γ - ΔF))]) (pathProb_nonneg h γ)
  have h3 : ∑ γ, pathProb β E K n γ * (1 + -β * (work E n γ - ΔF)) =
      (1 + β * ΔF) - β * ∑ γ, pathProb β E K n γ * work E n γ := by
    have hterm : ∀ γ : Fin (n + 1) → S, pathProb β E K n γ * (1 + -β * (work E n γ - ΔF)) =
        (1 + β * ΔF) * pathProb β E K n γ - β * (pathProb β E K n γ * work E n γ) := by
      intro γ; ring
    simp_rw [hterm]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_pathProb h.row n, mul_one]
  rw [h3, h1] at h2
  have h4 : β * ΔF ≤ β * ∑ γ, pathProb β E K n γ * work E n γ := by linarith
  exact le_of_mul_le_mul_left h4 hβ

/-- [proved-standard; formal-checked] **Equality in the second law is rigid**: if the mean work
equals the free-energy difference, the work equals it on every aeon of positive weight. -/
theorem work_eq_of_second_law_eq [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (n : ℕ)
    (heq : ∑ γ, pathProb β E K n γ * work E n γ = freeEnergy β E n - freeEnergy β E 0)
    (γ : Fin (n + 1) → S) (hγ : 0 < pathProb β E K n γ) :
    work E n γ = freeEnergy β E n - freeEnergy β E 0 := by
  set ΔF := freeEnergy β E n - freeEnergy β E 0 with hΔF
  have h1 := jarzynski_freeEnergy h hβ.ne' n
  rw [← hΔF] at h1
  have hnn : ∀ γ' ∈ (univ : Finset (Fin (n + 1) → S)),
      0 ≤ pathProb β E K n γ' *
        (Real.exp (-β * (work E n γ' - ΔF)) - 1 - -β * (work E n γ' - ΔF)) :=
    fun γ' _ => mul_nonneg (pathProb_nonneg h γ')
      (by linarith [Real.add_one_le_exp (-β * (work E n γ' - ΔF))])
  have hsum : ∑ γ', pathProb β E K n γ' *
      (Real.exp (-β * (work E n γ' - ΔF)) - 1 - -β * (work E n γ' - ΔF)) = 0 := by
    have hterm : ∀ γ' : Fin (n + 1) → S, pathProb β E K n γ' *
          (Real.exp (-β * (work E n γ' - ΔF)) - 1 - -β * (work E n γ' - ΔF)) =
        pathProb β E K n γ' * Real.exp (-β * (work E n γ' - ΔF)) -
          (1 + β * ΔF) * pathProb β E K n γ' + β * (pathProb β E K n γ' * work E n γ') := by
      intro γ'; ring
    simp_rw [hterm]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_pathProb h.row n, h1, heq]
    ring
  have hzero := (sum_eq_zero_iff_of_nonneg hnn).mp hsum γ (mem_univ γ)
  have hu : Real.exp (-β * (work E n γ - ΔF)) - 1 - -β * (work E n γ - ΔF) = 0 := by
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact absurd h0 hγ.ne'
    · exact h0
  have hu0 : -β * (work E n γ - ΔF) = 0 := by
    by_contra hne
    have := Real.add_one_lt_exp hne
    linarith
  have hw : work E n γ - ΔF = 0 := by
    rcases mul_eq_zero.mp hu0 with h0 | h0
    · exact absurd (neg_eq_zero.mp h0) hβ.ne'
    · exact h0
  linarith

/-! ## 7. Crooks' relation -/

/-- [proved-derived; formal-checked] The reversed protocol's law at the reversed aeon, written on
the forward aeon: the last constitution's weight at `γ_n`, and each kernel run backwards. -/
theorem revProb_reversal (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) {n : ℕ}
    (γ : Fin (n + 1) → S) :
    revProb β E K n (γ ∘ Fin.rev) =
      weight β E n (γ (Fin.last n)) / partition β E n *
        ∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc) := by
  unfold revProb
  simp only [Function.comp_apply, Fin.rev_zero, Fin.rev_castSucc, Fin.rev_succ]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun t : Fin n => K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc))

/-- [proved-standard; formal-checked] **Crooks' relation, per aeon.** Under detailed balance at
each tick, the forward weight of an aeon times `exp(−β · work)` times `Z 0` is the reversed
protocol's weight of the reversed aeon times `Z n`. -/
theorem crooks [Nonempty S] (hdb : DetailedBalance β E K) (n : ℕ) (γ : Fin (n + 1) → S) :
    pathProb β E K n γ * Real.exp (-β * work E n γ) * partition β E 0 =
      revProb β E K n (γ ∘ Fin.rev) * partition β E n := by
  have hZ0 := (partition_pos β E 0).ne'
  have hZn := (partition_pos β E n).ne'
  have hD : 0 < ∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc) :=
    prod_pos fun _ _ => weight_pos β E _ _
  -- the work steps carry the weights of tick `t` to those of tick `t + 1` at the held states
  have hW : Real.exp (-β * work E n γ) * ∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc) =
      ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.castSucc) := by
    unfold work
    rw [mul_sum, Real.exp_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun t _ => by rw [mul_comm]; exact weight_succ β E t _
  -- detailed balance turns each heat step around
  have hAU : (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)) *
        ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.castSucc) =
      (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc)) *
        ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.succ) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun t _ => by
      rw [mul_comm, hdb ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ), mul_comm]
  -- the weights along the aeon, split at its first and at its last occurrence
  have hT : weight β E 0 (γ 0) * ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.succ) =
      (∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc)) * weight β E n (γ (Fin.last n)) := by
    have h1 := Fin.prod_univ_succ (fun i : Fin (n + 1) => weight β E (i : ℕ) (γ i))
    have h2 := Fin.prod_univ_castSucc (fun i : Fin (n + 1) => weight β E (i : ℕ) (γ i))
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h1 h2
    rw [← h1, h2]
  rw [revProb_reversal]
  unfold pathProb
  have e1 : weight β E 0 (γ 0) / partition β E 0 *
        (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)) *
        Real.exp (-β * work E n γ) * partition β E 0 =
      weight β E 0 (γ 0) * (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)) *
        Real.exp (-β * work E n γ) := by
    field_simp
  have e2 : weight β E n (γ (Fin.last n)) / partition β E n *
        (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc)) * partition β E n =
      weight β E n (γ (Fin.last n)) *
        ∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc) := by
    field_simp
  rw [e1, e2]
  apply mul_right_cancel₀ hD.ne'
  calc weight β E 0 (γ 0) * (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)) *
          Real.exp (-β * work E n γ) * ∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc)
      = weight β E 0 (γ 0) * ((∏ t : Fin n, K ((t : ℕ) + 1) (γ t.castSucc) (γ t.succ)) *
          (Real.exp (-β * work E n γ) * ∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc))) := by
        ring
    _ = weight β E 0 (γ 0) * ((∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc)) *
          ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.succ)) := by
        rw [hW, hAU]
    _ = (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc)) *
          (weight β E 0 (γ 0) * ∏ t : Fin n, weight β E ((t : ℕ) + 1) (γ t.succ)) := by
        ring
    _ = weight β E n (γ (Fin.last n)) *
          (∏ t : Fin n, K ((t : ℕ) + 1) (γ t.succ) (γ t.castSucc)) *
          ∏ t : Fin n, weight β E (t : ℕ) (γ t.castSucc) := by
        rw [hT]; ring

/-- [proved-derived; formal-checked] An aeon of positive forward weight has positive weight under
the reversed protocol. -/
theorem revProb_pos_of_pathProb_pos [Nonempty S] (hdb : DetailedBalance β E K) {n : ℕ}
    {γ : Fin (n + 1) → S} (hγ : 0 < pathProb β E K n γ) :
    0 < revProb β E K n (γ ∘ Fin.rev) := by
  have hc := crooks hdb n γ
  have hpos : 0 < pathProb β E K n γ * Real.exp (-β * work E n γ) * partition β E 0 :=
    mul_pos (mul_pos hγ (Real.exp_pos _)) (partition_pos β E 0)
  rw [hc] at hpos
  exact (pos_iff_pos_of_mul_pos hpos).mpr (partition_pos β E n)

/-- [proved-standard; formal-checked] **Crooks' ratio**: `P_F(γ) / P_R(Rγ) = exp(β (W − ΔF))`. -/
theorem crooks_ratio [Nonempty S] (hdb : DetailedBalance β E K) (hβ : β ≠ 0) (n : ℕ)
    (γ : Fin (n + 1) → S) (hrev : revProb β E K n (γ ∘ Fin.rev) ≠ 0) :
    pathProb β E K n γ / revProb β E K n (γ ∘ Fin.rev) =
      Real.exp (β * (work E n γ - (freeEnergy β E n - freeEnergy β E 0))) := by
  have hZ0 := (partition_pos β E 0).ne'
  have hc := crooks hdb n γ
  have hsplit : β * (work E n γ - (freeEnergy β E n - freeEnergy β E 0)) =
      β * work E n γ + -β * (freeEnergy β E n - freeEnergy β E 0) := by ring
  have ha : Real.exp (-β * work E n γ) * Real.exp (β * work E n γ) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  rw [hsplit, Real.exp_add, exp_neg_freeEnergy_diff hβ E n, div_eq_iff hrev]
  calc pathProb β E K n γ
      = pathProb β E K n γ * (Real.exp (-β * work E n γ) * Real.exp (β * work E n γ)) := by
        rw [ha, mul_one]
    _ = Real.exp (β * work E n γ) *
          (pathProb β E K n γ * Real.exp (-β * work E n γ) * partition β E 0) /
            partition β E 0 := by
        rw [eq_div_iff hZ0]; ring
    _ = Real.exp (β * work E n γ) *
          (revProb β E K n (γ ∘ Fin.rev) * partition β E n) / partition β E 0 := by
        rw [hc]
    _ = Real.exp (β * work E n γ) * (partition β E n / partition β E 0) *
          revProb β E K n (γ ∘ Fin.rev) := by
        ring

/-- [proved-standard; formal-checked] **Dissipated work is the production of the driven aeon**:
the relative entropy of the forward path law against the reversed protocol's law of the reversed
aeon is `β (⟨W⟩ − ΔF)`. -/
theorem dissipated_work_eq_relativeEntropy [Nonempty S] (hrow : ∀ t x, ∑ y, K t x y = 1)
    (hdb : DetailedBalance β E K) (hβ : β ≠ 0) (n : ℕ) :
    ∑ γ, pathProb β E K n γ *
        Real.log (pathProb β E K n γ / revProb β E K n (γ ∘ Fin.rev)) =
      β * (∑ γ, pathProb β E K n γ * work E n γ -
        (freeEnergy β E n - freeEnergy β E 0)) := by
  set ΔF := freeEnergy β E n - freeEnergy β E 0 with hΔF
  have hrhs : β * (∑ γ, pathProb β E K n γ * work E n γ - ΔF) =
      ∑ γ, pathProb β E K n γ * (β * (work E n γ - ΔF)) := by
    have hterm : ∀ γ : Fin (n + 1) → S, pathProb β E K n γ * (β * (work E n γ - ΔF)) =
        β * (pathProb β E K n γ * work E n γ) - β * ΔF * pathProb β E K n γ := by
      intro γ; ring
    simp_rw [hterm]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_pathProb hrow n]
    ring
  rw [hrhs]
  refine sum_congr rfl fun γ _ => ?_
  by_cases hγ : pathProb β E K n γ = 0
  · rw [hγ, zero_mul, zero_mul]
  · have hrev : revProb β E K n (γ ∘ Fin.rev) ≠ 0 := by
      intro h0
      have hc := crooks hdb n γ
      rw [h0, zero_mul] at hc
      rcases mul_eq_zero.mp hc with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact hγ h2
        · exact (Real.exp_pos _).ne' h2
      · exact (partition_pos β E 0).ne' h1
    rw [crooks_ratio hdb hβ n γ hrev, Real.log_exp]

/-- [proved-derived; formal-checked] Summing Crooks' relation over the aeons gives Jarzynski's
equality again, by the reversed protocol's total mass: a second proof under detailed balance. -/
theorem jarzynski_of_crooks [Nonempty S] (hrow : ∀ t x, ∑ y, K t x y = 1)
    (hdb : DetailedBalance β E K) (n : ℕ) :
    ∑ γ, pathProb β E K n γ * Real.exp (-β * work E n γ) =
      partition β E n / partition β E 0 := by
  have hZ0 := (partition_pos β E 0).ne'
  rw [eq_div_iff hZ0, sum_mul]
  simp_rw [crooks hdb n]
  rw [← sum_mul]
  have hsum : ∑ γ : Fin (n + 1) → S, revProb β E K n (γ ∘ Fin.rev) = 1 := by
    rw [← sum_revProb β E hrow n]
    exact Fintype.sum_equiv
      { toFun := fun γ : Fin (n + 1) → S => γ ∘ Fin.rev
        invFun := fun γ => γ ∘ Fin.rev
        left_inv := fun γ => by funext i; simp
        right_inv := fun γ => by funext i; simp } _ _ fun _ => rfl
  rw [hsum, one_mul]

section Audit

#print axioms sum_pathProb
#print axioms sum_revProb
#print axioms jarzynski_marginal
#print axioms jarzynski
#print axioms jarzynski_freeEnergy
#print axioms jarzynski_static
#print axioms second_law
#print axioms work_eq_of_second_law_eq
#print axioms work_eq_zero_of_static
#print axioms revProb_reversal
#print axioms crooks
#print axioms crooks_ratio
#print axioms revProb_pos_of_pathProb_pos
#print axioms dissipated_work_eq_relativeEntropy
#print axioms jarzynski_of_crooks
#print axioms Driven.of_detailedBalance

end Audit

end Holonics.Aeon.Production.Jarzynski
