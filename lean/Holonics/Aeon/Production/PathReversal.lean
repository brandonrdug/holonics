import Holonics.Foundation.ReceiverCodeCost
import Holonics.Aeon.Production.Kac
import Holonics.Aeon.Clock.Epoch
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Production is the relative entropy of an aeon against its reversal

[definition] Aeon record A5, A6 and A9, Lean obligation 4 (second half). A finite Markov chain `P`
with law `π` at the first occurrence moves along an **aeon of `n` epochs**, a path
`γ : Fin (n+1) → S`. The chain and its law are **exact rationals**; the path law
`P_γ = π(γ₀) ∏ P(γᵢ, γᵢ₊₁)` (`pathLaw`), the reversed law (`revLaw`) and the one-epoch flow
`J(x,y) = π x P(x,y)` (`flow`) are exact, over any ordered field. Only the logarithm is real: the
**production** of the aeon is the relative entropy of the path law against the reversed one, read
in the real chart inside the logarithm,

```text
σₙ = D(P_γ ‖ P_(Rγ)) = Σ_γ P_γ log (P_γ / P_(Rγ))                (production)
σ  = Σ_(x,y) J(x,y) log (J(x,y)/J(y,x))                         (epochProduction)
```

The path is an aeon of the groupoid: the complete transition complex on the states carries it as
the chained word of its steps (`pathAeon`), the affinities `log(P(x,y)/P(y,x))` are a clock on it
(`affinityClock`), and a section's arrivals are a cut clock whose reading is the section's coarse
ticks (`arrivalClock`, the returns of `Kac`).

[proved-derived; formal-checked] What is proved, for `π > 0`, `P ≥ 0` with symmetric support
(`P x y > 0 ⇒ P y x > 0`).

1. **Production is nonnegative for every aeon**, with no stationarity: the path law and its
   reversal carry one total mass (`sum_pathLaw_reversal`), and Gibbs' inequality for finite
   nonnegative weights (`relativeEntropy_nonneg`) gives `σₙ ≥ 0`
   (`production_nonneg_of_support`).
2. **Production is additive over epochs** for a stochastic chain whose law is stationary
   (`Kac.Stationary`): `σₙ = n σ` (`production_eq_mul`), from the exact recursion
   `σₙ₊₁ = σₙ + σ` (`production_succ`), the law of the last occurrence (`last_marginal`) and the
   snoc form of the reversed law (`revLaw_snoc`).
3. **The epoch production is the existing edge code production.**
   `σ = (ln 2/2) Σ_(x,y) edgeCodeProduction(J(x,y), J(y,x))`
   (`epochProduction_eq_edgeCode`, over `Foundation/ReceiverCodeCost.edgeCodeProduction`), hence
   `σ ≥ 0`, and `σ = 0` exactly under detailed balance `J(x,y) = J(y,x)`
   (`epochProduction_eq_zero_iff`).
4. **The arrow of an aeon:** `σₙ = 0 ⇔ detailed balance` for every `n ≥ 1`
   (`production_eq_zero_iff`).
5. **State plus heat.** For a positive aeon, `log(P_γ/P_(Rγ))` splits into the boundary term
   `log π(γ₀) − log π(γₙ)` (state time, read by the two bounding occurrences) plus the reading of
   the affinity clock along the path aeon (`pathLogRatio_split`, `pathLogRatio_eq_reading`). On a
   cycle the boundary term vanishes and the reading is the cycle affinity, which does not depend on
   `π` (`cycle_logRatio_eq_affinity`). Under detailed balance the affinity is exact,
   `log π y − log π x` (`detailedBalance_affinity_exact`), so every cycle affinity vanishes
   (`detailedBalance_cycle_affinity_zero`): reversibility is a closed, exact clock. The reversed
   path reads the affinity clock as the reversed aeon does, with the opposite sign
   (`reading_pathAeon_reversal`).
6. **Placement and reversibility (A9).** `P` is self-adjoint in `ℓ²(π)` exactly under detailed
   balance (`selfAdjoint_iff_detailedBalance`, over any field), and then every complex eigenvalue
   is real (`detailedBalance_eigenvalue_real`).
7. **Kac's coarse ticks are readings.** The arrivals of a path at a section `A` are the reading of
   the section's arrival clock along the path aeon (`arrivalClock_reading`).

[counterexample; formal-checked] **Detailed balance is load-bearing.** The biased rotation of
three states (`2/3` forward, `1/3` back) is stationary for the uniform law, stochastic, with
symmetric support, and not reversible: `σ = (1/3) log 2 > 0` (`rotation_production_pos`), every
cycle `0 → 1 → 2 → 0` reads affinity `3 log 2` (`rotation_cycle_affinity`), and it has the
non-real eigenvalue `−1/2 + i√3/6` (`rotation_nonreal_eigenvalue`).

[open] Owed in #62: the converse of Kolmogorov's criterion (every cycle affinity zero ⇒ detailed
balance). Scope: finite state spaces; the positivity and support hypotheses are stated where used.
The continuous-time and port-Hamiltonian forms of production (`⟨Jv, DJv⟩/T`) are not treated here.
No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Aeon.Production.PathReversal

open scoped BigOperators
open Finset
open Holonics.Foundation.ReceiverCodeCost

variable {S : Type*} [Fintype S]

/-! ## 1. Exact path laws, over any ordered field -/

section Laws

variable {K : Type*} [Field K]

/-- [definition] The one-epoch flow `J(x,y) = π x · P(x,y)`: the law of an aeon of one epoch. -/
def flow (π : S → K) (P : S → S → K) (x y : S) : K := π x * P x y

/-- [definition] **Detailed balance**: every edge carries equal flow both ways. -/
def DetailedBalance (π : S → K) (P : S → S → K) : Prop := ∀ x y, flow π P x y = flow π P y x

/-- [definition] The law of an aeon of `n` epochs: `π(γ₀) ∏ P(γᵢ, γᵢ₊₁)`. -/
def pathLaw (π : S → K) (P : S → S → K) (n : ℕ) (γ : Fin (n + 1) → S) : K :=
  π (γ 0) * ∏ i : Fin n, P (γ i.castSucc) (γ i.succ)

/-- [definition] The **reversal** `Rγ = γ ∘ rev`: the same occurrences, run backwards. -/
def reversal {n : ℕ} (γ : Fin (n + 1) → S) : Fin (n + 1) → S := γ ∘ Fin.rev

/-- [definition] The reversed law, written out: `π(γₙ) ∏ P(γᵢ₊₁, γᵢ)`. -/
def revLaw (π : S → K) (P : S → S → K) (n : ℕ) (γ : Fin (n + 1) → S) : K :=
  π (γ (Fin.last n)) * ∏ i : Fin n, P (γ i.succ) (γ i.castSucc)

omit [Fintype S] in
/-- [proved-derived; formal-checked] The law of the reversed aeon is the reversed law. -/
theorem pathLaw_reversal (π : S → K) (P : S → S → K) {n : ℕ} (γ : Fin (n + 1) → S) :
    pathLaw π P n (reversal γ) = revLaw π P n γ := by
  unfold pathLaw revLaw reversal
  simp only [Function.comp_apply, Fin.rev_zero, Fin.rev_castSucc, Fin.rev_succ]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun j => P (γ j.succ) (γ j.castSucc))

omit [Fintype S] in
theorem reversal_reversal {n : ℕ} (γ : Fin (n + 1) → S) : reversal (reversal γ) = γ := by
  funext i; simp [reversal]

/-- [definition] Reversal as a bijection of aeons. -/
def reversalEquiv (n : ℕ) : (Fin (n + 1) → S) ≃ (Fin (n + 1) → S) where
  toFun := reversal
  invFun := reversal
  left_inv := reversal_reversal
  right_inv := reversal_reversal

/-- [proved-derived; formal-checked] The path law and its reversal carry one total mass. -/
theorem sum_pathLaw_reversal (π : S → K) (P : S → S → K) (n : ℕ) :
    ∑ γ, pathLaw π P n (reversal γ) = ∑ γ, pathLaw π P n γ :=
  Fintype.sum_equiv (reversalEquiv n) _ _ fun _ => rfl

/-! ## 4. The last occurrence and the snoc form -/


variable (π : S → K) (P : S → S → K)

omit [Fintype S] in
theorem pathLaw_snoc {n : ℕ} (γ : Fin (n + 1) → S) (y : S) :
    pathLaw π P (n + 1) (Fin.snoc γ y) = pathLaw π P n γ * P (γ (Fin.last n)) y := by
  unfold pathLaw
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc γ y : Fin (n + 2) → S) 0 = γ 0 := by
    simp
  simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

omit [Fintype S] in
theorem revLaw_snoc {n : ℕ} (γ : Fin (n + 1) → S) (y : S) :
    revLaw π P (n + 1) (Fin.snoc γ y) * π (γ (Fin.last n)) =
      revLaw π P n γ * (π y * P y (γ (Fin.last n))) := by
  unfold revLaw
  rw [Fin.prod_univ_castSucc]
  have hl : (Fin.snoc γ y : Fin (n + 2) → S) (Fin.last (n + 1)) = y := Fin.snoc_last _ _
  simp only [hl, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last]
  ring

/-- [proved-derived; formal-checked] Aeons of `n + 1` epochs are aeons of `n` epochs followed by
one more occurrence. -/
theorem sum_snoc {M : Type*} [AddCommMonoid M] {n : ℕ} (F : (Fin (n + 2) → S) → M) :
    ∑ γ', F γ' = ∑ γ : Fin (n + 1) → S, ∑ y, F (Fin.snoc γ y) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => S)) (fun p => F (Fin.snoc p.2 p.1)) F
    (fun _ => rfl), Fintype.sum_prod_type, sum_comm]

theorem sum_fin_one {M : Type*} [AddCommMonoid M] (F : (Fin 1 → S) → M) :
    ∑ γ, F γ = ∑ x, F (fun _ => x) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ fun γ => by
    congr 1; funext i; rw [Subsingleton.elim i default]; rfl

/-- [proved-derived; formal-checked] **The last occurrence of an aeon from a stationary law has
the stationary law.** -/
theorem last_marginal {π : S → K} {P : S → S → K} (hπ : Kac.Stationary P π) (n : ℕ) (g : S → K) :
    ∑ γ : Fin (n + 1) → S, pathLaw π P n γ * g (γ (Fin.last n)) = ∑ x, π x * g x := by
  induction n generalizing g with
  | zero =>
    rw [sum_fin_one]
    simp [pathLaw]
  | succ n ih =>
    rw [sum_snoc]
    have hstep : ∀ γ : Fin (n + 1) → S, ∑ y, pathLaw π P (n + 1) (Fin.snoc γ y) *
        g ((Fin.snoc γ y : Fin (n + 2) → S) (Fin.last (n + 1))) =
        pathLaw π P n γ * (fun x => ∑ y, P x y * g y) (γ (Fin.last n)) := by
      intro γ
      simp only [pathLaw_snoc, Fin.snoc_last, mul_sum]
      exact sum_congr rfl fun y _ => by ring
    simp_rw [hstep]
    rw [ih (fun x => ∑ y, P x y * g y)]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← hπ y, sum_mul]
    exact sum_congr rfl fun x _ => by ring

/-- [proved-derived; formal-checked] **`P` is self-adjoint in `ℓ²(π)` exactly under detailed
balance:** `⟨f, P g⟩_π = ⟨P f, g⟩_π` for all `f`, `g`, over any ordered field. -/
theorem selfAdjoint_iff_detailedBalance [DecidableEq S] {π : S → K} {P : S → S → K} :
    (∀ f g : S → K, ∑ x, π x * f x * ∑ y, P x y * g y =
        ∑ x, π x * (∑ y, P x y * f y) * g x) ↔ DetailedBalance π P := by
  constructor
  · intro h x y
    have := h (Pi.single x 1) (Pi.single y 1)
    simp only [mul_sum, sum_mul] at this
    simp [Pi.single_apply] at this
    unfold flow
    linear_combination this
  · intro hdb f g
    have lhs : ∑ x, π x * f x * ∑ y, P x y * g y = ∑ x, ∑ y, flow π P x y * f x * g y := by
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]; exact sum_congr rfl fun y _ => by simp only [flow]; ring
    have rhs : ∑ x, π x * (∑ y, P x y * f y) * g x = ∑ x, ∑ y, flow π P x y * f y * g x := by
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum, sum_mul]; exact sum_congr rfl fun y _ => by simp only [flow]; ring
    rw [lhs, rhs, sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => by rw [hdb]

/-! ### Positivity -/

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [definition] The hypotheses under which the path law and its reversal share support. -/
structure Admissible (π : S → K) (P : S → S → K) : Prop where
  pos : ∀ x, 0 < π x
  nonneg : ∀ x y, 0 ≤ P x y
  support : ∀ x y, 0 < P x y → 0 < P y x



variable {π : S → K} {P : S → S → K}

omit [Fintype S] in
theorem pathLaw_nonneg (hA : Admissible π P) {n : ℕ} (γ : Fin (n + 1) → S) :
    0 ≤ pathLaw π P n γ :=
  mul_nonneg (hA.pos _).le (prod_nonneg fun _ _ => hA.nonneg _ _)

omit [Fintype S] in
theorem revLaw_nonneg (hA : Admissible π P) {n : ℕ} (γ : Fin (n + 1) → S) :
    0 ≤ revLaw π P n γ :=
  mul_nonneg (hA.pos _).le (prod_nonneg fun _ _ => hA.nonneg _ _)

omit [Fintype S] in
/-- [proved-derived; formal-checked] A positive aeon has positive steps. -/
theorem steps_pos_of_pathLaw_pos (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) (i : Fin n) : 0 < P (γ i.castSucc) (γ i.succ) := by
  have hprod : ∏ j : Fin n, P (γ j.castSucc) (γ j.succ) ≠ 0 := by
    intro h; rw [pathLaw, h, mul_zero] at hγ; exact lt_irrefl 0 hγ
  exact lt_of_le_of_ne (hA.nonneg _ _) ((prod_ne_zero_iff.mp hprod i (mem_univ i))).symm

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Support symmetry transfers to paths:** a positive aeon has
a positive reversal. -/
theorem revLaw_pos_of_pathLaw_pos (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) : 0 < revLaw π P n γ :=
  mul_pos (hA.pos _) (prod_pos fun i _ => hA.support _ _ (steps_pos_of_pathLaw_pos hA hγ i))

omit [Fintype S] in
theorem flow_nonneg (hA : Admissible π P) (x y : S) : 0 ≤ flow π P x y :=
  mul_nonneg (hA.pos x).le (hA.nonneg x y)

omit [Fintype S] in
theorem flow_support (hA : Admissible π P) {x y : S} (h : 0 < flow π P x y) :
    0 < flow π P y x :=
  mul_pos (hA.pos y) (hA.support x y (pos_of_mul_pos_right h (hA.pos x).le))

omit [Fintype S] in
theorem flow_zero_of_zero (hA : Admissible π P) {x y : S} (h : flow π P x y = 0) :
    flow π P y x = 0 := by
  by_contra hne
  have := flow_support hA (lt_of_le_of_ne (flow_nonneg hA y x) (Ne.symm hne))
  exact this.ne' h

end Laws

/-- [proved-derived; formal-checked] Telescoping along an aeon:
`Σᵢ (f(i+1) − f(i)) = f(n) − f(0)`. -/
theorem sum_fin_telescope {M : Type*} [AddCommGroup M] {n : ℕ} (f : Fin (n + 1) → M) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc] at h ⊢
    rw [h, Fin.succ_last]
    simp only [Fin.castSucc_zero]
    abel

/-! ## 2. The exact chain read in the real chart -/

section Cast

variable (π : S → ℚ) (P : S → S → ℚ)

/-- [definition] The exact law read in `ℝ`. -/
abbrev lawR : S → ℝ := fun x => (π x : ℝ)

/-- [definition] The exact chain read in `ℝ`. -/
abbrev chainR : S → S → ℝ := fun x y => (P x y : ℝ)

omit [Fintype S] in
theorem flow_cast (x y : S) : ((flow π P x y : ℚ) : ℝ) = flow (lawR π) (chainR P) x y := by
  simp [flow]

omit [Fintype S] in
theorem pathLaw_cast {n : ℕ} (γ : Fin (n + 1) → S) :
    ((pathLaw π P n γ : ℚ) : ℝ) = pathLaw (lawR π) (chainR P) n γ := by
  simp [pathLaw]

omit [Fintype S] in
theorem revLaw_cast {n : ℕ} (γ : Fin (n + 1) → S) :
    ((revLaw π P n γ : ℚ) : ℝ) = revLaw (lawR π) (chainR P) n γ := by
  simp [revLaw]

variable {π P}

omit [Fintype S] in
theorem Admissible.cast (h : Admissible π P) : Admissible (lawR π) (chainR P) where
  pos x := by exact_mod_cast h.pos x
  nonneg x y := by exact_mod_cast h.nonneg x y
  support x y hxy := by exact_mod_cast h.support x y (by exact_mod_cast hxy)

omit [Fintype S] in
theorem detailedBalance_cast_iff : DetailedBalance (lawR π) (chainR P) ↔ DetailedBalance π P := by
  refine forall₂_congr fun x y => ?_
  rw [← flow_cast, ← flow_cast]
  exact Rat.cast_inj

theorem stationary_cast (h : Kac.Stationary P π) : Kac.Stationary (chainR P) (lawR π) := by
  intro y
  have := congrArg (fun q : ℚ => (q : ℝ)) (h y)
  simpa using this

theorem rows_cast (h : ∀ x, ∑ y, P x y = 1) : ∀ x, ∑ y, chainR P x y = 1 := by
  intro x
  have := congrArg (fun q : ℚ => (q : ℝ)) (h x)
  simpa using this

end Cast

/-! ## 3. Production in the real chart -/

namespace RealChart

/-- [definition] Production of real weights: `D(P_γ ‖ P_(Rγ))`. -/
def production (π : S → ℝ) (P : S → S → ℝ) (n : ℕ) : ℝ :=
  ∑ γ, pathLaw π P n γ * Real.log (pathLaw π P n γ / pathLaw π P n (reversal γ))

/-- [definition] Epoch production of real weights. -/
def epochProduction (π : S → ℝ) (P : S → S → ℝ) : ℝ :=
  ∑ x, ∑ y, flow π P x y * Real.log (flow π P x y / flow π P y x)

/-! ### Gibbs' inequality for finite nonnegative weights -/

/-- [proved-derived; formal-checked] `p log(p/q) ≥ p − q` for `p ≥ 0`, `q ≥ 0`, `p > 0 ⇒ q > 0`. -/
theorem mul_log_div_ge_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hac : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  rcases hp.eq_or_lt with h0 | hpos
  · subst h0; simpa using hq
  · have hqpos := hac hpos
    have hlog := Real.log_le_sub_one_of_pos (div_pos hqpos hpos)
    have hinv : Real.log (p / q) = -Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv]
    have : p * Real.log (q / p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left hlog hpos.le
    have hcancel : p * (q / p - 1) = q - p := by field_simp
    linarith

/-- [proved-derived; formal-checked] **Gibbs' inequality.** For finite nonnegative weights of
equal total mass with `p ≪ q`, `D(p‖q) = Σ p log(p/q) ≥ 0`. -/
theorem relativeEntropy_nonneg {ι : Type*} [Fintype ι] {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hac : ∀ i, 0 < p i → 0 < q i) (hmass : ∑ i, p i = ∑ i, q i) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have h := sum_le_sum fun i (_ : i ∈ univ) => mul_log_div_ge_sub (hp i) (hq i) (hac i)
  rw [sum_sub_distrib, hmass, sub_self] at h
  exact h

section Positivity

variable {π : S → ℝ} {P : S → S → ℝ}

/-- [proved-derived; formal-checked] **Production is nonnegative for every aeon**, with no
stationarity: Gibbs' inequality against the reversal, which has the same total mass. -/
theorem production_nonneg_of_support (hA : Admissible π P) (n : ℕ) : 0 ≤ production π P n := by
  unfold production
  refine relativeEntropy_nonneg (fun γ => pathLaw_nonneg hA γ) (fun γ => pathLaw_nonneg hA _)
    (fun γ hγ => ?_) (sum_pathLaw_reversal π P n).symm
  rw [pathLaw_reversal]; exact revLaw_pos_of_pathLaw_pos hA hγ

end Positivity

/-! ### Additivity over epochs -/

section Additive

variable {π : S → ℝ} {P : S → S → ℝ}

theorem production_eq_revLaw (n : ℕ) :
    production π P n =
      ∑ γ, pathLaw π P n γ * Real.log (pathLaw π P n γ / revLaw π P n γ) := by
  unfold production
  simp_rw [pathLaw_reversal]

theorem production_zero : production π P 0 = 0 := by
  rw [production_eq_revLaw]
  refine sum_eq_zero fun γ _ => ?_
  have h : revLaw π P 0 γ = pathLaw π P 0 γ := by
    simp [revLaw, pathLaw, Fin.last]
  rw [h]
  rcases eq_or_ne (pathLaw π P 0 γ) 0 with h0 | h0
  · simp [h0]
  · simp [div_self h0]

/-- [proved-derived; formal-checked] **One more epoch adds one epoch of production:**
`σₙ₊₁ = σₙ + σ` for a stationary stochastic admissible chain. -/
theorem production_succ (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    production π P (n + 1) = production π P n + epochProduction π P := by
  rw [production_eq_revLaw, production_eq_revLaw, sum_snoc]
  set E : S → S → ℝ := fun x y => Real.log (flow π P x y / flow π P y x) with hE
  set L : (Fin (n + 1) → S) → ℝ := fun γ => Real.log (pathLaw π P n γ / revLaw π P n γ) with hL
  have hterm : ∀ (γ : Fin (n + 1) → S) (y : S),
      pathLaw π P (n + 1) (Fin.snoc γ y) *
          Real.log (pathLaw π P (n + 1) (Fin.snoc γ y) / revLaw π P (n + 1) (Fin.snoc γ y)) =
        pathLaw π P n γ * P (γ (Fin.last n)) y * (L γ + E (γ (Fin.last n)) y) := by
    intro γ y
    set x := γ (Fin.last n)
    rw [pathLaw_snoc]
    rcases eq_or_lt_of_le (mul_nonneg (pathLaw_nonneg hA γ) (hA.nonneg x y)) with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    · have hγ : 0 < pathLaw π P n γ := pos_of_mul_pos_left hpos (hA.nonneg x y)
      have hxy : 0 < P x y := pos_of_mul_pos_right hpos (pathLaw_nonneg hA γ)
      have hyx : 0 < P y x := hA.support x y hxy
      have hrev : 0 < revLaw π P n γ := revLaw_pos_of_pathLaw_pos hA hγ
      have hπx := hA.pos x
      have hπy := hA.pos y
      have hsnoc : revLaw π P (n + 1) (Fin.snoc γ y) =
          revLaw π P n γ * (π y * P y x) / π x := by
        rw [eq_div_iff hπx.ne', revLaw_snoc]
      have hratio : pathLaw π P n γ * P x y / revLaw π P (n + 1) (Fin.snoc γ y) =
          (pathLaw π P n γ / revLaw π P n γ) * (flow π P x y / flow π P y x) := by
        rw [hsnoc]; simp only [flow]; field_simp
      rw [hratio, Real.log_mul (div_pos hγ hrev).ne'
        (div_pos (show 0 < flow π P x y from mul_pos hπx hxy)
          (show 0 < flow π P y x from mul_pos hπy hyx)).ne']
  simp_rw [hterm]
  have hsplit : ∀ γ : Fin (n + 1) → S,
      ∑ y, pathLaw π P n γ * P (γ (Fin.last n)) y * (L γ + E (γ (Fin.last n)) y) =
        pathLaw π P n γ * L γ +
          pathLaw π P n γ * (fun x => ∑ y, P x y * E x y) (γ (Fin.last n)) := by
    intro γ
    simp only [mul_add, sum_add_distrib]
    congr 1
    · rw [← sum_mul, ← mul_sum, hrow, mul_one]
    · rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  simp_rw [hsplit]
  rw [sum_add_distrib, last_marginal hπ n (fun x => ∑ y, P x y * E x y)]
  congr 1
  unfold epochProduction
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by simp only [flow, hE]; ring

/-- [proved-derived; formal-checked] **Production is additive over epochs:** `σₙ = n σ`. -/
theorem production_eq_mul (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    production π P n = n * epochProduction π P := by
  induction n with
  | zero => simp [production_zero]
  | succ n ih => rw [production_succ hA hπ hrow, ih]; push_cast; ring

end Additive

/-! ### The epoch production is the edge code production -/

section EdgeCode

variable {π : S → ℝ} {P : S → S → ℝ}

/-- [proved-derived; formal-checked] **The edge code production vanishes exactly on balanced
positive flows.** -/
theorem edgeCodeProduction_eq_zero_iff {f b : ℝ} (hf : 0 < f) (hb : 0 < b) :
    edgeCodeProduction f b = 0 ↔ f = b := by
  unfold edgeCodeProduction
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [div_eq_zero_iff, or_iff_left hlog2, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact Real.log_injOn_pos (Set.mem_Ioi.mpr hf) (Set.mem_Ioi.mpr hb) h
  · intro h; exact Or.inl h

omit [Fintype S] in
theorem edgeCode_nonneg (hA : Admissible π P) (x y : S) :
    0 ≤ edgeCodeProduction (flow π P x y) (flow π P y x) := by
  rcases (flow_nonneg hA x y).eq_or_lt with h0 | hpos
  · rw [← h0, flow_zero_of_zero hA h0.symm]; simp [edgeCodeProduction]
  · exact edgeCodeProduction_nonnegative hpos (flow_support hA hpos)

omit [Fintype S] in
theorem log_flow_div (hA : Admissible π P) (x y : S) :
    Real.log (flow π P x y / flow π P y x) =
      Real.log (flow π P x y) - Real.log (flow π P y x) := by
  rcases (flow_nonneg hA x y).eq_or_lt with h0 | hpos
  · rw [← h0, flow_zero_of_zero hA h0.symm]; simp
  · exact Real.log_div hpos.ne' (flow_support hA hpos).ne'

/-- [proved-derived; formal-checked] **The epoch production is the edge code production**
summed over ordered edges: `σ = (ln 2/2) Σ edgeCodeProduction(J(x,y), J(y,x))`. -/
theorem epochProduction_eq_edgeCode (hA : Admissible π P) :
    epochProduction π P =
      Real.log 2 / 2 * ∑ x, ∑ y, edgeCodeProduction (flow π P x y) (flow π P y x) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  set J := flow π P
  set D : S → S → ℝ := fun x y => Real.log (J x y) - Real.log (J y x)
  have hsym : ∑ x, ∑ y, J x y * D x y = ∑ x, ∑ y, (-(J y x * D x y)) := by
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    simp only [D]; ring
  have hmain : epochProduction π P = (1 / 2) * ∑ x, ∑ y, (J x y - J y x) * D x y := by
    unfold epochProduction
    simp_rw [log_flow_div hA]
    have h2 : ∑ x, ∑ y, (J x y - J y x) * D x y =
        ∑ x, ∑ y, J x y * D x y + ∑ x, ∑ y, (-(J y x * D x y)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun y _ => by ring
    rw [h2, ← hsym]
    ring
  rw [hmain, mul_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [edgeCodeProduction, D]
  field_simp

/-- [proved-derived; formal-checked] `σ ≥ 0`. -/
theorem epochProduction_nonneg (hA : Admissible π P) : 0 ≤ epochProduction π P := by
  rw [epochProduction_eq_edgeCode hA]
  exact mul_nonneg (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num))
    (sum_nonneg fun x _ => sum_nonneg fun y _ => edgeCode_nonneg hA x y)

/-- [proved-derived; formal-checked] **`σ = 0` exactly under detailed balance.** -/
theorem epochProduction_eq_zero_iff (hA : Admissible π P) :
    epochProduction π P = 0 ↔ DetailedBalance π P := by
  rw [epochProduction_eq_edgeCode hA, mul_eq_zero,
    or_iff_right (div_ne_zero (Real.log_pos (by norm_num)).ne' (by norm_num))]
  rw [sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => edgeCode_nonneg hA x y]
  simp_rw [sum_eq_zero_iff_of_nonneg fun y _ => edgeCode_nonneg hA _ y]
  constructor
  · intro h x y
    rcases (flow_nonneg hA x y).eq_or_lt with h0 | hpos
    · rw [← h0, flow_zero_of_zero hA h0.symm]
    · exact (edgeCodeProduction_eq_zero_iff hpos (flow_support hA hpos)).mp
        (h x (mem_univ x) y (mem_univ y))
  · intro h x _ y _
    rw [h x y]; simp [edgeCodeProduction]

/-- [proved-derived; formal-checked] **Production of aeons.** For a stationary stochastic
admissible chain: `σₙ ≥ 0`, and for `n ≥ 1`, `σₙ = 0` exactly under detailed balance. -/
theorem production_eq_zero_iff (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) {n : ℕ} (hn : 0 < n) :
    production π P n = 0 ↔ DetailedBalance π P := by
  rw [production_eq_mul hA hπ hrow, mul_eq_zero,
    or_iff_right (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), epochProduction_eq_zero_iff hA]

end EdgeCode

/-! ### State plus heat, and reversibility as an exact clock -/

section StateHeat

variable {π : S → ℝ} {P : S → S → ℝ}

/-- [definition] The affinity of a real chain's step. -/
def affinity (P : S → S → ℝ) (x y : S) : ℝ := Real.log (P x y / P y x)

omit [Fintype S] in
/-- [proved-derived; formal-checked] **State plus heat.** For a positive aeon,
`log(P_γ/P_(Rγ)) = (log π(γ₀) − log π(γₙ)) + Σᵢ affinity(γᵢ, γᵢ₊₁)`: the first term is read by the
two bounding occurrences alone. -/
theorem pathLogRatio_split (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) :
    Real.log (pathLaw π P n γ / revLaw π P n γ) =
      (Real.log (π (γ 0)) - Real.log (π (γ (Fin.last n)))) +
        ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) := by
  have hstep := steps_pos_of_pathLaw_pos hA hγ
  have hback : ∀ i : Fin n, 0 < P (γ i.succ) (γ i.castSucc) := fun i =>
    hA.support _ _ (hstep i)
  unfold pathLaw revLaw
  rw [Real.log_div (mul_pos (hA.pos _) (prod_pos fun i _ => hstep i)).ne'
      (mul_pos (hA.pos _) (prod_pos fun i _ => hback i)).ne',
    Real.log_mul (hA.pos _).ne' (prod_pos fun i _ => hstep i).ne',
    Real.log_mul (hA.pos _).ne' (prod_pos fun i _ => hback i).ne',
    Real.log_prod (fun i _ => (hstep i).ne'), Real.log_prod (fun i _ => (hback i).ne')]
  unfold affinity
  rw [add_sub_add_comm, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun i _ => (Real.log_div (hstep i).ne' (hback i).ne').symm

omit [Fintype S] in
/-- [proved-derived; formal-checked] **A cycle reads its affinity.** On a positive aeon that
returns to its first occurrence, the path log-ratio is the cycle affinity, which does not
depend on the law `π`. -/
theorem cycle_logRatio_eq_affinity (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) (hcycle : γ 0 = γ (Fin.last n)) :
    Real.log (pathLaw π P n γ / revLaw π P n γ) =
      ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) := by
  rw [pathLogRatio_split hA hγ, hcycle, sub_self, zero_add]

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Under detailed balance the affinity is exact:**
`affinity(x,y) = log π y − log π x` on every positive step. -/
theorem detailedBalance_affinity_exact (hA : Admissible π P) (hdb : DetailedBalance π P)
    {x y : S} (hxy : 0 < P x y) : affinity P x y = Real.log (π y) - Real.log (π x) := by
  have hyx := hA.support x y hxy
  have h := hdb x y
  unfold flow at h
  unfold affinity
  have : P x y / P y x = π y / π x := by
    rw [div_eq_div_iff hyx.ne' (hA.pos x).ne']; linarith
  rw [this, Real.log_div (hA.pos y).ne' (hA.pos x).ne']

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Reversibility is an exact clock:** under detailed balance
every positive cycle reads zero affinity (Kolmogorov's criterion, the forward direction). -/
theorem detailedBalance_cycle_affinity_zero (hA : Admissible π P) (hdb : DetailedBalance π P)
    {n : ℕ} {γ : Fin (n + 1) → S} (hγ : 0 < pathLaw π P n γ) (hcycle : γ 0 = γ (Fin.last n)) :
    ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) = 0 := by
  have hstep := steps_pos_of_pathLaw_pos hA hγ
  simp_rw [fun i => detailedBalance_affinity_exact hA hdb (hstep i)]
  rw [sum_fin_telescope (fun i => Real.log (π (γ i))), hcycle, sub_self]

end StateHeat

section Spectrum

variable {π : S → ℝ} {P : S → S → ℝ}

/-- [proved-derived; formal-checked] **Detailed balance places the spectrum on the real line.**
Every complex eigenvalue of a chain in detailed balance with a positive law is real. -/
theorem detailedBalance_eigenvalue_real (hpos : ∀ x, 0 < π x) (hdb : DetailedBalance π P)
    {v : S → ℂ} (hv : v ≠ 0) {μ : ℂ} (heig : ∀ x, ∑ y, (P x y : ℂ) * v y = μ * v x) :
    μ.im = 0 := by
  set H : ℂ := ∑ x, (π x : ℂ) * (starRingEnd ℂ) (v x) * ∑ y, (P x y : ℂ) * v y with hH
  set N : ℝ := ∑ x, π x * Complex.normSq (v x) with hN
  have hHN : H = μ * N := by
    rw [hH, hN]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [heig x, Complex.normSq_eq_conj_mul_self]
    ring
  have hconj : (starRingEnd ℂ) H = H := by
    rw [hH, map_sum]
    have : ∀ x, (starRingEnd ℂ) ((π x : ℂ) * (starRingEnd ℂ) (v x) * ∑ y, (P x y : ℂ) * v y) =
        ∑ y, ((flow π P x y : ℝ) : ℂ) * v x * (starRingEnd ℂ) (v y) := by
      intro x
      simp only [map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      simp only [flow]; push_cast; ring
    simp_rw [this]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hdb x y]; simp only [flow]; push_cast; ring
  have hNpos : 0 < N := by
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    have hle : π x * Complex.normSq (v x) ≤ N :=
      single_le_sum (f := fun x => π x * Complex.normSq (v x))
        (fun x _ => mul_nonneg (hpos x).le (Complex.normSq_nonneg _)) (mem_univ x)
    exact lt_of_lt_of_le (mul_pos (hpos x) (Complex.normSq_pos.mpr hx)) hle
  rw [hHN, map_mul, Complex.conj_ofReal] at hconj
  have hμ : (starRingEnd ℂ) μ = μ :=
    mul_right_cancel₀ (by exact_mod_cast hNpos.ne' : (N : ℂ) ≠ 0) hconj
  exact Complex.conj_eq_iff_im.mp hμ

end Spectrum

end RealChart

/-! ## 4. Production of the exact chain -/

section Exact

variable {π : S → ℚ} {P : S → S → ℚ}

/-- [definition] **Production** of aeons of `n` epochs of the exact chain, `D(P_γ ‖ P_(Rγ))`: the
exact path laws, read in `ℝ` only inside the logarithm. -/
def production (π : S → ℚ) (P : S → S → ℚ) (n : ℕ) : ℝ :=
  ∑ γ, ((pathLaw π P n γ : ℚ) : ℝ) *
    Real.log (((pathLaw π P n γ : ℚ) : ℝ) / ((pathLaw π P n (reversal γ) : ℚ) : ℝ))

/-- [definition] **Epoch production** `σ = Σ J(x,y) log (J(x,y)/J(y,x))` of the exact flows. -/
def epochProduction (π : S → ℚ) (P : S → S → ℚ) : ℝ :=
  ∑ x, ∑ y, ((flow π P x y : ℚ) : ℝ) *
    Real.log (((flow π P x y : ℚ) : ℝ) / ((flow π P y x : ℚ) : ℝ))

/-- [definition] The **affinity** of a step: `log (P(x,y)/P(y,x))`, the heat read by the medium. -/
def affinity (P : S → S → ℚ) (x y : S) : ℝ := Real.log (((P x y : ℚ) : ℝ) / ((P y x : ℚ) : ℝ))

theorem production_eq_real (π : S → ℚ) (P : S → S → ℚ) (n : ℕ) :
    production π P n = RealChart.production (lawR π) (chainR P) n := by
  simp only [production, RealChart.production, pathLaw_cast]

theorem epochProduction_eq_real (π : S → ℚ) (P : S → S → ℚ) :
    epochProduction π P = RealChart.epochProduction (lawR π) (chainR P) := by
  simp only [epochProduction, RealChart.epochProduction, flow_cast]

omit [Fintype S] in
theorem affinity_eq_real (P : S → S → ℚ) (x y : S) :
    affinity P x y = RealChart.affinity (chainR P) x y := rfl

/-- [proved-derived; formal-checked] **Production is nonnegative for every aeon**, with no
stationarity: Gibbs' inequality against the reversal, which has the same total mass. -/
theorem production_nonneg_of_support (hA : Admissible π P) (n : ℕ) : 0 ≤ production π P n := by
  rw [production_eq_real]; exact RealChart.production_nonneg_of_support hA.cast n

/-- [proved-derived; formal-checked] **One more epoch adds one epoch of production:**
`σₙ₊₁ = σₙ + σ` for a stationary stochastic admissible chain. -/
theorem production_succ (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    production π P (n + 1) = production π P n + epochProduction π P := by
  rw [production_eq_real, production_eq_real, epochProduction_eq_real]
  exact RealChart.production_succ hA.cast (stationary_cast hπ) (rows_cast hrow) n

/-- [proved-derived; formal-checked] **Production is additive over epochs:** `σₙ = n σ`. -/
theorem production_eq_mul (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    production π P n = n * epochProduction π P := by
  rw [production_eq_real, epochProduction_eq_real]
  exact RealChart.production_eq_mul hA.cast (stationary_cast hπ) (rows_cast hrow) n

/-- [proved-derived; formal-checked] **The epoch production is the edge code production**
summed over ordered edges: `σ = (ln 2/2) Σ edgeCodeProduction(J(x,y), J(y,x))`. -/
theorem epochProduction_eq_edgeCode (hA : Admissible π P) :
    epochProduction π P =
      Real.log 2 / 2 * ∑ x, ∑ y,
        edgeCodeProduction ((flow π P x y : ℚ) : ℝ) ((flow π P y x : ℚ) : ℝ) := by
  rw [epochProduction_eq_real, RealChart.epochProduction_eq_edgeCode hA.cast]
  simp only [flow_cast]

/-- [proved-derived; formal-checked] `σ ≥ 0`. -/
theorem epochProduction_nonneg (hA : Admissible π P) : 0 ≤ epochProduction π P := by
  rw [epochProduction_eq_real]; exact RealChart.epochProduction_nonneg hA.cast

/-- [proved-derived; formal-checked] **`σ = 0` exactly under detailed balance.** -/
theorem epochProduction_eq_zero_iff (hA : Admissible π P) :
    epochProduction π P = 0 ↔ DetailedBalance π P := by
  rw [epochProduction_eq_real, RealChart.epochProduction_eq_zero_iff hA.cast,
    detailedBalance_cast_iff]

/-- [proved-derived; formal-checked] **Production of aeons.** For a stationary stochastic
admissible chain and `n ≥ 1`, `σₙ = 0` exactly under detailed balance. -/
theorem production_eq_zero_iff (hA : Admissible π P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) {n : ℕ} (hn : 0 < n) :
    production π P n = 0 ↔ DetailedBalance π P := by
  rw [production_eq_real, RealChart.production_eq_zero_iff hA.cast (stationary_cast hπ)
    (rows_cast hrow) hn, detailedBalance_cast_iff]

omit [Fintype S] in
/-- [proved-derived; formal-checked] **State plus heat.** For a positive aeon,
`log(P_γ/P_(Rγ)) = (log π(γ₀) − log π(γₙ)) + Σᵢ affinity(γᵢ, γᵢ₊₁)`: the first term is read by the
two bounding occurrences alone. -/
theorem pathLogRatio_split (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) :
    Real.log (((pathLaw π P n γ : ℚ) : ℝ) / ((revLaw π P n γ : ℚ) : ℝ)) =
      (Real.log (π (γ 0)) - Real.log (π (γ (Fin.last n)))) +
        ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) := by
  rw [pathLaw_cast, revLaw_cast]
  exact RealChart.pathLogRatio_split hA.cast (by rw [← pathLaw_cast]; exact_mod_cast hγ)

omit [Fintype S] in
/-- [proved-derived; formal-checked] **A cycle reads its affinity.** On a positive aeon that
returns to its first occurrence, the path log-ratio is the cycle affinity, which does not depend
on the law `π`. -/
theorem cycle_logRatio_eq_affinity (hA : Admissible π P) {n : ℕ} {γ : Fin (n + 1) → S}
    (hγ : 0 < pathLaw π P n γ) (hcycle : γ 0 = γ (Fin.last n)) :
    Real.log (((pathLaw π P n γ : ℚ) : ℝ) / ((revLaw π P n γ : ℚ) : ℝ)) =
      ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) := by
  rw [pathLogRatio_split hA hγ, hcycle, sub_self, zero_add]

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Under detailed balance the affinity is exact:**
`affinity(x,y) = log π y − log π x` on every positive step. -/
theorem detailedBalance_affinity_exact (hA : Admissible π P) (hdb : DetailedBalance π P)
    {x y : S} (hxy : 0 < P x y) : affinity P x y = Real.log (π y) - Real.log (π x) :=
  RealChart.detailedBalance_affinity_exact hA.cast (detailedBalance_cast_iff.mpr hdb)
    (by exact_mod_cast hxy)

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Reversibility is an exact clock:** under detailed balance
every positive cycle reads zero affinity (Kolmogorov's criterion, the forward direction). -/
theorem detailedBalance_cycle_affinity_zero (hA : Admissible π P) (hdb : DetailedBalance π P)
    {n : ℕ} {γ : Fin (n + 1) → S} (hγ : 0 < pathLaw π P n γ) (hcycle : γ 0 = γ (Fin.last n)) :
    ∑ i : Fin n, affinity P (γ i.castSucc) (γ i.succ) = 0 :=
  RealChart.detailedBalance_cycle_affinity_zero hA.cast (detailedBalance_cast_iff.mpr hdb)
    (by rw [← pathLaw_cast]; exact_mod_cast hγ) hcycle

/-- [proved-derived; formal-checked] **Detailed balance places the spectrum on the real line.**
Every complex eigenvalue of an exact chain in detailed balance with a positive law is real. -/
theorem detailedBalance_eigenvalue_real (hpos : ∀ x, 0 < π x) (hdb : DetailedBalance π P)
    {v : S → ℂ} (hv : v ≠ 0) {μ : ℂ} (heig : ∀ x, ∑ y, ((P x y : ℚ) : ℂ) * v y = μ * v x) :
    μ.im = 0 :=
  RealChart.detailedBalance_eigenvalue_real (π := lawR π) (P := chainR P)
    (fun x => by exact_mod_cast hpos x) (detailedBalance_cast_iff.mpr hdb) hv
    (fun x => by simpa [Complex.ofReal_ratCast] using heig x)

end Exact

/-! ## 5. The path is an aeon of the groupoid -/

section PathAeon

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Epoch

/-- [definition] **The transition complex** of the states: an oriented edge for every transition
`x → y`, and no two-cell. -/
def transitionComplex (S : Type*) : ParametricComplex S (S × S) Empty where
  src e := e.1
  tgt e := e.2
  base f := f.elim
  boundary f := f.elim

/-- [definition] The word of a path: each transition traversed along its orientation. -/
def pathWord {n : ℕ} (γ : Fin (n + 1) → S) : List ((S × S) × Bool) :=
  List.ofFn fun i : Fin n => ((γ i.castSucc, γ i.succ), true)

omit [Fintype S] in
theorem pathWord_chained : ∀ {n : ℕ} (γ : Fin (n + 1) → S),
    (transitionComplex S).Chained (γ 0) (pathWord γ) (γ (Fin.last n))
  | 0, γ => by simp [pathWord]
  | n + 1, γ => by
    rw [pathWord, List.ofFn_succ]
    refine ⟨rfl, ?_⟩
    have h := pathWord_chained (fun i : Fin (n + 1) => γ i.succ)
    simp only [pathWord, Fin.succ_castSucc, Fin.succ_last] at h
    exact h

/-- [definition] **The path aeon**: a path of `n` epochs as an aeon of the transition complex, from
its first to its last occurrence. -/
def pathAeon {n : ℕ} (γ : Fin (n + 1) → S) :
    Aeon (transitionComplex S) (γ 0) (γ (Fin.last n)) :=
  ⟨pathWord γ, pathWord_chained γ⟩

omit [Fintype S] in
/-- A form on transitions reads a path word as the sum over its steps. -/
theorem wordReading_pathWord {A : Type*} [AddCommGroup A] (ω : S × S → A) {n : ℕ}
    (γ : Fin (n + 1) → S) :
    wordReading ω (pathWord γ) = ∑ i : Fin n, ω (γ i.castSucc, γ i.succ) := by
  induction n with
  | zero => simp [pathWord]
  | succ n ih =>
    rw [pathWord, List.ofFn_succ, wordReading_cons, Fin.sum_univ_succ]
    have := ih (fun i : Fin (n + 1) => γ i.succ)
    simp only [pathWord, Fin.succ_castSucc] at this
    simp only [stepReading, if_true, Fin.castSucc_zero]
    rw [this]

omit [Fintype S] in
/-- Every form on the transition complex is closed: it has no two-cell. -/
theorem transition_isClosed {A : Type*} [AddCommGroup A] (ω : S × S → A) :
    IsClosed (transitionComplex S) ω := fun f => f.elim

/-- [definition] **The affinity clock** of an exact chain on the transition complex. -/
def affinityClock (P : S → S → ℚ) : Clock (transitionComplex S) ℝ :=
  ⟨fun e => affinity P e.1 e.2, transition_isClosed _⟩

omit [Fintype S] in
/-- [proved-derived; formal-checked] **The heat of a path is a clock reading**: for a positive aeon
the path log-ratio is its state term plus the affinity clock's reading of the path aeon. -/
theorem pathLogRatio_eq_reading {π : S → ℚ} {P : S → S → ℚ} (hA : Admissible π P) {n : ℕ}
    {γ : Fin (n + 1) → S} (hγ : 0 < pathLaw π P n γ) :
    Real.log (((pathLaw π P n γ : ℚ) : ℝ) / ((revLaw π P n γ : ℚ) : ℝ)) =
      (Real.log (π (γ 0)) - Real.log (π (γ (Fin.last n)))) +
        reading (affinityClock P) (pathAeon γ) := by
  rw [pathLogRatio_split hA hγ]
  congr 1
  exact (wordReading_pathWord (fun e => affinity P e.1 e.2) γ).symm

omit [Fintype S] in
/-- [proved-derived; formal-checked] **The reversed path reads the affinity clock as the reversed
aeon does**: along a positive path of a chain with symmetric support, the affinity clock reads the
reversed path `Rγ` as `−` its reading of `γ`, which is the groupoid's reversal law
`reading (Rγ) = −reading γ`. -/
theorem reading_pathAeon_reversal {π : S → ℚ} {P : S → S → ℚ} (hA : Admissible π P) {n : ℕ}
    {γ : Fin (n + 1) → S} (hγ : 0 < pathLaw π P n γ) :
    wordReading (affinityClock P).form (pathWord (reversal γ)) =
      reading (affinityClock P) (pathAeon γ).reverse := by
  have hstep := steps_pos_of_pathLaw_pos hA hγ
  rw [reading_reverse]
  simp only [reading, pathAeon, wordReading_pathWord, affinityClock]
  have hswap : ∀ i : Fin n, affinity P (γ i.succ) (γ i.castSucc) =
      -affinity P (γ i.castSucc) (γ i.succ) := by
    intro i
    have h1 : (0 : ℝ) < P (γ i.castSucc) (γ i.succ) := by exact_mod_cast hstep i
    have h2 : (0 : ℝ) < P (γ i.succ) (γ i.castSucc) := by
      exact_mod_cast hA.support _ _ (hstep i)
    unfold affinity
    rw [← Real.log_inv, inv_div]
  rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [reversal, Function.comp_apply, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ]
  rw [hswap, Fin.rev_rev]

/-- [definition] **The arrival clock of a section** `A`: the cut reading `1` on each transition
into `A`. -/
def arrivalClock [DecidableEq S] (A : Finset S) : CutClock (transitionComplex S) where
  clock := ⟨fun e => if e.2 ∈ A then 1 else 0, transition_isClosed _⟩
  isCut e := by by_cases h : e.2 ∈ A <;> simp [h]

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Kac's coarse ticks are readings**: the arrival clock of a
section reads a path aeon as the number of its steps that land in the section, the returns whose
first-step equations `Kac` solves. -/
theorem arrivalClock_reading [DecidableEq S] (A : Finset S) {n : ℕ} (γ : Fin (n + 1) → S) :
    reading (arrivalClock A).clock (pathAeon γ) =
      ((Finset.univ.filter fun i : Fin n => γ i.succ ∈ A).card : ℤ) := by
  simp only [reading, pathAeon, arrivalClock]
  rw [wordReading_pathWord]
  simp [Finset.sum_boole]

end PathAeon

/-! ## 6. Detailed balance is load-bearing: the biased rotation -/

namespace Rotation

/-- [definition] The biased rotation of three states: forward with `2/3`, back with `1/3`. -/
def P : Fin 3 → Fin 3 → ℚ := fun x y => !![0, 2 / 3, 1 / 3; 1 / 3, 0, 2 / 3; 2 / 3, 1 / 3, 0] x y

/-- [definition] The uniform law. -/
def π : Fin 3 → ℚ := fun _ => 1 / 3

theorem admissible : Admissible π P where
  pos := fun x => by simp [π]
  nonneg := fun x y => by fin_cases x <;> fin_cases y <;> norm_num [P]
  support := fun x y h => by revert h; fin_cases x <;> fin_cases y <;> norm_num [P]

theorem stationary : Kac.Stationary P π := by
  intro y; fin_cases y <;> simp [π, P, Fin.sum_univ_three] <;> norm_num

theorem rows : ∀ x, ∑ y, P x y = 1 := by
  intro x; fin_cases x <;> simp [P, Fin.sum_univ_three] <;> norm_num

/-- [counterexample; formal-checked] **A stationary chain with positive production.** The biased
rotation has `σ = (1/3) log 2 > 0`, so it is not in detailed balance, and its aeons of `n` epochs
produce `σₙ = (n/3) log 2`. -/
theorem rotation_production_pos :
    epochProduction π P = Real.log 2 / 3 ∧ 0 < epochProduction π P ∧ ¬ DetailedBalance π P ∧
      ∀ n, production π P n = n * (Real.log 2 / 3) := by
  have hσ : epochProduction π P = Real.log 2 / 3 := by
    have h12 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    unfold epochProduction flow
    simp [Fin.sum_univ_three, π, P]
    norm_num [h12]
    ring
  have hpos : 0 < epochProduction π P := by
    rw [hσ]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨hσ, hpos, fun hdb => ?_, fun n => ?_⟩
  · rw [(epochProduction_eq_zero_iff admissible).mpr hdb] at hpos
    exact lt_irrefl 0 hpos
  · rw [production_eq_mul admissible stationary rows, hσ]

/-- [counterexample; formal-checked] **The cycle `0 → 1 → 2 → 0` reads affinity `3 log 2`.** -/
theorem rotation_cycle_affinity :
    affinity P 0 1 + affinity P 1 2 + affinity P 2 0 = 3 * Real.log 2 := by
  have h12 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  simp [affinity, P]
  ring

/-- [definition] The primitive cube root of unity `ω = −1/2 + i√3/2`. -/
def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

/-- [counterexample; formal-checked] **Production permits complex spectrum.** The biased rotation
has the eigenvalue `2/3 ω + 1/3 ω̄ = −1/2 + i√3/6`, whose imaginary part is not zero, with
eigenvector `(1, ω, ω̄)`. -/
theorem rotation_nonreal_eigenvalue :
    let v : Fin 3 → ℂ := ![1, ω, (starRingEnd ℂ) ω]
    let μ : ℂ := ⟨-1 / 2, Real.sqrt 3 / 6⟩
    (∀ x, ∑ y, ((P x y : ℚ) : ℂ) * v y = μ * v x) ∧ μ.im ≠ 0 := by
  intro v μ
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases x <;>
      simp [v, μ, ω, P, Fin.sum_univ_three, Complex.ext_iff] <;>
      constructor <;> nlinarith [hs]
  · simp only [μ, ne_eq]
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    change ¬ Real.sqrt 3 / 6 = 0
    positivity

end Rotation

section Audit

#print axioms production_nonneg_of_support
#print axioms production_succ
#print axioms production_eq_mul
#print axioms epochProduction_eq_edgeCode
#print axioms epochProduction_eq_zero_iff
#print axioms production_eq_zero_iff
#print axioms pathLogRatio_split
#print axioms pathLogRatio_eq_reading
#print axioms reading_pathAeon_reversal
#print axioms arrivalClock_reading
#print axioms detailedBalance_cycle_affinity_zero
#print axioms selfAdjoint_iff_detailedBalance
#print axioms detailedBalance_eigenvalue_real
#print axioms Rotation.rotation_production_pos
#print axioms Rotation.rotation_cycle_affinity
#print axioms Rotation.rotation_nonreal_eigenvalue

end Audit

end Holonics.Aeon.Production.PathReversal
