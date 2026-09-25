import Holonics.Foundation.SituatedInformationRate
import Holonics.Geometry.CrossRatio
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Kac's lemma and Abramov's formula for finite Markov chains

[definition] Aeon record A4 and the across-grains law, Lean obligation 4 (first half). A finite
Markov chain `P` on states `S` is a motion whose every step is one **fine epoch**. A **section**
`Σ' = A` (a nonempty finite set of states) is a coarser receiver: its ticks are the returns of the
motion to `A`, and one **coarse epoch** runs from a crossing of `A` to the next.

* `avoid P A g y = Σ_(z ∉ A) P y z · g z` is one fine epoch of the motion that has not yet crossed
  the section.
* `survival P A n y = (avoid P A)^[n] 1 y` is the mass, started at `y`, that has not crossed `A`
  at fine epochs `1, …, n`: the probability `P_y(τ_A > n)` of the first-return time `τ_A ≥ 1`.
  Its partial sums are the truncated mean first return `E_y[min(τ_A, N)]`, and the mean first
  return is their limit `Σ_n P_y(τ_A > n)` (the tail-sum formula).
* `FirstReturnEquations P A f m`: `m y = f y + avoid P A m y`, the first-step equations of the
  observable `f` accumulated over one coarse epoch. `f = 1` gives the mean first return.

[proved-derived; formal-checked] What is proved.

1. **Kac's ledger, exact at every truncation, over any commutative ring.** For a stationary
   measure `π`, `Σ_(y∈A) π y · E_y[min(τ_A, N)] = Σ_y π y − Σ_y π y · P_y(τ_A > N)`
   (`kac_ledger`). Only stationarity is used.
2. **Kac's lemma for observables** (`kac_observable`): if `m` solves the first-step equations of
   `f`, then `Σ_(y∈A) π y · m y = Σ_y π y · f y`. With `f = 1` (`kac`): the mean first return
   from `π` restricted to `A` is the undivided pair `(π(S) : π(A))`, a ratio of section measures,
   and `π(S)/π(A)` when `π(A) ≠ 0` (`kac_grain_ratio`); for one state `x`, `π x · m x = 1`
   (`kac_single_state`).
3. **Existence under irreducibility, over `ℚ`.** For a stochastic irreducible chain and a
   nonempty section the first-step equations of every observable have exactly one solution
   (`firstReturn_existsUnique`), by a maximum principle (`avoid_fixed_eq_zero`). The mean first
   return is at least one (`one_le_meanReturn`).
4. **Kac's lemma as a series** (`kac_hasSum`): for a stochastic irreducible chain with stationary
   law `π` of total mass one, `Σ_n P_x(τ_x > n) = 1/π x`, a `HasSum` in `ℝ` of exact rationals
   (`meanReturn_hasSum` identifies the solution of the equations with the series).
5. **Abramov's formula for the induced chain.** One coarse epoch's **word** (the path until the
   return to `A`, stopped at `N` fine epochs) has an exact rational law (`wordLaw`, of total mass one
   for a stochastic chain: `wordLaw_mass`). Its entropy obeys the chain rule along the excursion,
   `H_(N+1) = h + avoid H_N` with `h y = −Σ_z P y z log P y z` (`wordEntropy_succ`), so
   `H_N = Σ_(n<N) avoidⁿ h` (`wordEntropy_eq_sum`): the truncation of the first-step solution of
   `h`. Kac's ledger for an observable (`kac_ledger_observable`) then gives **Abramov's ledger**,
   exact at every truncation: `Σ_(y∈A) π y H_N(y) = Σ_y π y h(y) − Σ_y π y (avoidᴺ h)(y)`
   (`abramov_ledger`). For a stochastic irreducible chain, a nonnegative stationary law and a
   section of nonzero stationary mass the tail vanishes and the entropy of the coarse epoch's word
   from the section's normalized law is `Σ π h / π(A)` (`abramov`): with `Σ π = 1`,
   `h(T_A) = h(T)/μ(A)`.

[counterexample; formal-checked] **Irreducibility is load-bearing** (`reducible_kac_fails`): the
identity chain on two states with the stationary law `(1/2, 1/2)` returns to `0` after exactly one
epoch, so `π 0 · E_0[τ_0] = 1/2 ≠ 1`; the ledger's residue stays `1/2` at every truncation, and
the first-step equations have no solution.

[open] Owed in #62: the identification of the induced shift's Kolmogorov–Sinai entropy with the
per-word entropy `Σ_(y∈A) π_A(y) H(W_y)` (the entropy rate of the Markov chain of words, whose
conditional word law depends only on the returning state), and Abramov's formula
`h(T_A) = h(T)/μ(A)` for a general ergodic measure-preserving map. What is proved is the finite
Markov form: the exact ledger at every truncation and its limit.

Scope: finite state spaces. No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Aeon.Production.Kac

open scoped BigOperators
open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## 1. The avoidance kernel and the ledger, over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- [definition] **Stationarity**: `Σ_x π x · P x y = π y`. -/
def Stationary (P : S → S → R) (π : S → R) : Prop := ∀ y, ∑ x, π x * P x y = π y

/-- [definition] One fine epoch of the motion that has not crossed the section `A`. -/
def avoid (P : S → S → R) (A : Finset S) (g : S → R) : S → R :=
  fun y => ∑ z ∈ Aᶜ, P y z * g z

/-- [definition] `P_y(τ_A > n)`: the mass from `y` not crossing `A` at fine epochs `1, …, n`. -/
def survival (P : S → S → R) (A : Finset S) (n : ℕ) : S → R := (avoid P A)^[n] (fun _ => 1)

/-- [definition] The truncated mean first return `E_y[min(τ_A, N)] = Σ_(n<N) P_y(τ_A > n)`. -/
def truncatedReturn (P : S → S → R) (A : Finset S) (N : ℕ) (y : S) : R :=
  ∑ n ∈ range N, survival P A n y

/-- [definition] **First-step equations** of an observable `f` accumulated over one coarse epoch:
`m y = f y + Σ_(z ∉ A) P y z · m z`. With `f = 1`, `m` is the mean first return to `A`. -/
def FirstReturnEquations (P : S → S → R) (A : Finset S) (f m : S → R) : Prop :=
  ∀ y, m y = f y + avoid P A m y

theorem avoid_add (P : S → S → R) (A : Finset S) (g h : S → R) :
    avoid P A (g + h) = avoid P A g + avoid P A h := by
  funext y; simp [avoid, mul_add, sum_add_distrib]

theorem avoid_smul (P : S → S → R) (A : Finset S) (c : R) (g : S → R) :
    avoid P A (c • g) = c • avoid P A g := by
  funext y; simp [avoid, mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem avoid_iterate_add (P : S → S → R) (A : Finset S) (n : ℕ) (g h : S → R) :
    (avoid P A)^[n] (g + h) = (avoid P A)^[n] g + (avoid P A)^[n] h := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, avoid_add]

theorem avoid_iterate_smul (P : S → S → R) (A : Finset S) (n : ℕ) (c : R) (g : S → R) :
    (avoid P A)^[n] (c • g) = c • (avoid P A)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, avoid_smul]

/-- [proved-derived; formal-checked] **One avoiding epoch from a stationary measure** lands on
the complement of the section with the stationary weights. -/
theorem stationary_avoid_sum {P : S → S → R} {π : S → R} (hπ : Stationary P π) (A : Finset S)
    (g : S → R) : ∑ y, π y * avoid P A g y = ∑ z ∈ Aᶜ, π z * g z := by
  simp only [avoid, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← hπ z, sum_mul]
  exact sum_congr rfl fun y _ => by ring

/-- [proved-derived; formal-checked] **Kac's ledger, exact at every truncation.**
`Σ_(y∈A) π y · E_y[min(τ_A, N)] = Σ π − Σ_y π y · P_y(τ_A > N)`: the mass that has crossed is the
mass that entered minus the mass still avoiding. -/
theorem kac_ledger {P : S → S → R} {π : S → R} (hπ : Stationary P π) (A : Finset S) (N : ℕ) :
    ∑ y ∈ A, π y * truncatedReturn P A N y =
      ∑ y, π y - ∑ y, π y * survival P A N y := by
  induction N with
  | zero => simp [truncatedReturn, survival]
  | succ N ih =>
    have hstep : ∑ y, π y * survival P A (N + 1) y = ∑ z ∈ Aᶜ, π z * survival P A N z := by
      simp only [survival, Function.iterate_succ_apply']
      exact stationary_avoid_sum hπ A _
    have hsplit := sum_add_sum_compl A (fun y => π y * survival P A N y)
    simp only [truncatedReturn, sum_range_succ, mul_add, sum_add_distrib] at ih ⊢
    rw [ih, hstep]
    linear_combination hsplit

/-- [proved-derived; formal-checked] **Kac's lemma for observables.** A solution of the
first-step equations of `f`, read from the stationary measure on the section, carries the
stationary mean of `f`: `Σ_(y∈A) π y · m y = Σ_y π y · f y`. -/
theorem kac_observable {P : S → S → R} {π : S → R} (hπ : Stationary P π) {A : Finset S}
    {f m : S → R} (hm : FirstReturnEquations P A f m) :
    ∑ y ∈ A, π y * m y = ∑ y, π y * f y := by
  have htotal : ∑ y, π y * m y = ∑ y, π y * f y + ∑ z ∈ Aᶜ, π z * m z := by
    rw [← stationary_avoid_sum hπ A m, ← sum_add_distrib]
    exact sum_congr rfl fun y _ => by rw [hm y, mul_add]
  have hsplit := sum_add_sum_compl A (fun y => π y * m y)
  linear_combination hsplit + htotal

/-- [proved-derived; formal-checked] **Kac's lemma.** `Σ_(y∈A) π y · E_y[τ_A] = Σ_y π y`. -/
theorem kac {P : S → S → R} {π : S → R} (hπ : Stationary P π) {A : Finset S} {m : S → R}
    (hm : FirstReturnEquations P A (fun _ => 1) m) : ∑ y ∈ A, π y * m y = ∑ y, π y := by
  simpa using kac_observable hπ hm

/-- [proved-derived; formal-checked] **Kac's lemma for one state.** `π x · E_x[τ_x] = π(S)`. -/
theorem kac_single_state {P : S → S → R} {π : S → R} (hπ : Stationary P π) {x : S} {m : S → R}
    (hm : FirstReturnEquations P {x} (fun _ => 1) m) : π x * m x = ∑ y, π y := by
  simpa using kac hπ hm

end Ring

/-- [proved-derived; formal-checked] **Across grains the time ratio is a ratio of section
measures.** The mean first return to `A` from `π` restricted to `A`, kept as the undivided pair
`(Σ_(y∈A) π y · m y : π(A))`, is the pair `(π(S) : π(A))`; when the section carries stationary mass,
`π(A) ≠ 0`, it is `π(S)/π(A)` fine epochs per coarse epoch. -/
theorem kac_grain_ratio {K : Type*} [Field K] {P : S → S → K} {π : S → K} (hπ : Stationary P π)
    {A : Finset S} {m : S → K} (hm : FirstReturnEquations P A (fun _ => 1) m) :
    (⟨∑ y ∈ A, π y * m y, ∑ y ∈ A, π y⟩ : RatioPresentation K) = ⟨∑ y, π y, ∑ y ∈ A, π y⟩ ∧
      (∑ y ∈ A, π y ≠ 0 →
        (∑ y ∈ A, π y * m y) / ∑ y ∈ A, π y = (∑ y, π y) / ∑ y ∈ A, π y) := by
  rw [kac hπ hm]
  exact ⟨rfl, fun _ => rfl⟩

/-! ## 2. Existence under irreducibility, over `ℚ` -/

section Existence

/-- [definition] A stochastic kernel: nonnegative rows of total mass one. -/
def Stochastic (P : S → S → ℚ) : Prop := (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- [definition] **Irreducibility**: every state reaches every state by positive steps. -/
def Irreducible (P : S → S → ℚ) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun a b => 0 < P a b) x y

/-- [proved-derived; formal-checked] A state at the maximum of an avoiding fixed field steps only
to maximal states off the section. -/
theorem max_step {P : S → S → ℚ} (hP : Stochastic P) {A : Finset S} {v : S → ℚ}
    (hv : ∀ y, v y = avoid P A v y) {M : ℚ} (hMpos : 0 < M) (hMmax : ∀ y, v y ≤ M) {b : S}
    (hb : v b = M) {z : S} (hz : 0 < P b z) : z ∉ A ∧ v z = M := by
  set u : S → ℚ := fun w => if w ∈ A then 0 else v w with hu
  have hvb : v b = ∑ w, P b w * u w := by
    rw [hv b, avoid, ← sum_add_sum_compl A (fun w => P b w * u w)]
    have hA : ∑ w ∈ A, P b w * u w = 0 := sum_eq_zero fun w hw => by simp [hu, hw]
    rw [hA, zero_add]
    exact sum_congr rfl fun w hw => by simp [hu, mem_compl.mp hw]
  have hule : ∀ w, u w ≤ M := fun w => by
    by_cases hw : w ∈ A
    · simp [hu, hw, hMpos.le]
    · simp [hu, hw, hMmax w]
  have hzero : ∑ w, P b w * (M - u w) = 0 := by
    have : ∑ w, P b w * (M - u w) = M * ∑ w, P b w - ∑ w, P b w * u w := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun w _ => by ring
    rw [this, hP.2 b, mul_one, ← hvb, hb, sub_self]
  have hterm := (sum_eq_zero_iff_of_nonneg (fun w _ => mul_nonneg (hP.1 b w)
    (sub_nonneg.mpr (hule w)))).mp hzero z (mem_univ z)
  have huz : u z = M := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hz.ne'
    · linarith
  by_cases hzA : z ∈ A
  · simp [hu, hzA] at huz; exact absurd huz.symm hMpos.ne'
  · exact ⟨hzA, by simpa [hu, hzA] using huz⟩

/-- [proved-derived; formal-checked] **Maximum principle.** For a stochastic irreducible chain and
a nonempty section, a field fixed by the avoiding epoch is nowhere positive. -/
theorem avoid_fixed_nonpos {P : S → S → ℚ} (hP : Stochastic P) (hirr : Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {v : S → ℚ} (hv : ∀ y, v y = avoid P A v y) (y : S) :
    v y ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨b, -, hbmax⟩ := exists_max_image univ v ⟨y, mem_univ y⟩
  set M := v b
  have hMpos : 0 < M := lt_of_lt_of_le hpos (hbmax y (mem_univ y))
  have hMmax : ∀ w, v w ≤ M := fun w => hbmax w (mem_univ w)
  obtain ⟨z, hz⟩ : ∃ z, 0 < P b z := by
    by_contra hnone
    push Not at hnone
    have h1 := hP.2 b
    have h0 : ∑ w, P b w = 0 := sum_eq_zero fun w _ => le_antisymm (hnone w) (hP.1 b w)
    rw [h0] at h1; exact zero_ne_one h1
  obtain ⟨hzA, hzM⟩ := max_step hP hv hMpos hMmax rfl hz
  obtain ⟨x₀, hx₀⟩ := hA
  have reach : ∀ w, Relation.ReflTransGen (fun a b => 0 < P a b) z w → w ∉ A ∧ v w = M := by
    intro w hw
    induction hw with
    | refl => exact ⟨hzA, hzM⟩
    | tail _ hstep ih => exact max_step hP hv hMpos hMmax ih.2 hstep
  exact (reach x₀ (hirr z x₀)).1 hx₀

/-- [proved-derived; formal-checked] **An avoiding fixed field vanishes.** -/
theorem avoid_fixed_eq_zero {P : S → S → ℚ} (hP : Stochastic P) (hirr : Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {v : S → ℚ} (hv : ∀ y, v y = avoid P A v y) : v = 0 := by
  have hneg : ∀ y, (-v) y = avoid P A (-v) y := fun y => by
    have := avoid_smul P A (-1) v
    simp only [neg_one_smul] at this
    rw [this, Pi.neg_apply, Pi.neg_apply, hv y]
  funext y
  exact le_antisymm (avoid_fixed_nonpos hP hirr hA hv y)
    (by simpa using avoid_fixed_nonpos hP hirr hA hneg y)

/-- [definition] `m ↦ m − avoid m` as a linear map. -/
def returnOperator (P : S → S → ℚ) (A : Finset S) : (S → ℚ) →ₗ[ℚ] (S → ℚ) where
  toFun m := m - avoid P A m
  map_add' g h := by rw [avoid_add]; abel
  map_smul' c g := by rw [avoid_smul]; simp [smul_sub]

/-- [proved-derived; formal-checked] **The first-step equations have exactly one solution** for
every observable, when the chain is stochastic and irreducible and the section nonempty. -/
theorem firstReturn_existsUnique {P : S → S → ℚ} (hP : Stochastic P) (hirr : Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (f : S → ℚ) : ∃! m, FirstReturnEquations P A f m := by
  have hinj : Function.Injective (returnOperator P A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply avoid_fixed_eq_zero hP hirr hA
    intro y
    have := congrFun hv y
    simp only [returnOperator, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
      Pi.zero_apply] at this
    linarith
  obtain ⟨m, hm⟩ := LinearMap.injective_iff_surjective.mp hinj f
  have hsol : FirstReturnEquations P A f m := fun y => by
    have := congrFun hm y
    simp only [returnOperator, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply] at this
    linarith
  refine ⟨m, hsol, fun m' hm' => hinj ?_⟩
  rw [hm]
  funext y
  simp only [returnOperator, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  linarith [hm' y]

/-- [proved-derived; formal-checked] The avoiding epoch preserves nonnegativity. -/
theorem avoid_nonneg {P : S → S → ℚ} (hP : Stochastic P) (A : Finset S) {g : S → ℚ}
    (hg : ∀ y, 0 ≤ g y) (y : S) : 0 ≤ avoid P A g y :=
  sum_nonneg fun z _ => mul_nonneg (hP.1 y z) (hg z)

theorem avoid_iterate_nonneg {P : S → S → ℚ} (hP : Stochastic P) (A : Finset S) (n : ℕ)
    {g : S → ℚ} (hg : ∀ y, 0 ≤ g y) (y : S) : 0 ≤ (avoid P A)^[n] g y := by
  induction n generalizing y with
  | zero => exact hg y
  | succ n ih => rw [Function.iterate_succ_apply']; exact avoid_nonneg hP A ih y

theorem avoid_iterate_mono {P : S → S → ℚ} (hP : Stochastic P) (A : Finset S) (n : ℕ)
    {g h : S → ℚ} (hgh : ∀ y, g y ≤ h y) (y : S) : (avoid P A)^[n] g y ≤ (avoid P A)^[n] h y := by
  have hdiff : (avoid P A)^[n] h = (avoid P A)^[n] g + (avoid P A)^[n] (h - g) := by
    rw [← avoid_iterate_add]; congr 1; abel
  rw [hdiff, Pi.add_apply]
  linarith [avoid_iterate_nonneg hP A n (g := h - g) (fun y => sub_nonneg.mpr (hgh y)) y]

/-- [proved-derived; formal-checked] **The mean first return is at least one epoch.** -/
theorem one_le_meanReturn {P : S → S → ℚ} (hP : Stochastic P) {A : Finset S} {m : S → ℚ}
    (hm : FirstReturnEquations P A (fun _ => 1) m) (y : S) : 1 ≤ m y := by
  obtain ⟨b, -, hbmin⟩ := exists_min_image univ m ⟨y, mem_univ y⟩
  have hmin : ∀ w, m b ≤ m w := fun w => hbmin w (mem_univ w)
  have hnonneg : 0 ≤ m b := by
    by_contra hneg
    push Not at hneg
    have hmass : ∑ z ∈ Aᶜ, P b z ≤ 1 := by
      rw [← hP.2 b, ← sum_add_sum_compl A (P b)]
      linarith [sum_nonneg fun z (_ : z ∈ A) => hP.1 b z]
    have hlow : m b * ∑ z ∈ Aᶜ, P b z ≤ avoid P A m b := by
      rw [avoid, mul_sum]
      exact sum_le_sum fun z _ => by nlinarith [hP.1 b z, hmin z]
    have hmass' : m b ≤ m b * ∑ z ∈ Aᶜ, P b z := by
      nlinarith [sum_nonneg fun z (_ : z ∈ Aᶜ) => hP.1 b z]
    have := hm b
    linarith
  have := hm y
  linarith [avoid_nonneg hP A (g := m) (fun w => le_trans hnonneg (hmin w)) y]

/-- [proved-derived; formal-checked] **The solution is the truncated return plus the mass still
avoiding:** `m = Σ_(n<N) P(τ_A > n) + avoid^[N] m`. -/
theorem meanReturn_split {P : S → S → ℚ} {A : Finset S} {m : S → ℚ}
    (hm : FirstReturnEquations P A (fun _ => 1) m) (N : ℕ) (y : S) :
    m y = truncatedReturn P A N y + (avoid P A)^[N] m y := by
  have hfix : m = (fun _ => 1) + avoid P A m := funext hm
  induction N generalizing y with
  | zero => simp [truncatedReturn]
  | succ N ih =>
    have hnext : (avoid P A)^[N] m = survival P A N + (avoid P A)^[N + 1] m := by
      conv_lhs => rw [hfix]
      rw [avoid_iterate_add, Function.iterate_succ_apply]
      rfl
    rw [ih y, hnext, Pi.add_apply, truncatedReturn, truncatedReturn, sum_range_succ]
    ring

/-- [proved-derived; formal-checked] **The solution of the first-step equations is the mean first
return**, `Σ_n P_y(τ_A > n)`, as a convergent series of exact rationals. -/
theorem meanReturn_hasSum {P : S → S → ℚ} (hP : Stochastic P) {A : Finset S} {m : S → ℚ}
    (hm : FirstReturnEquations P A (fun _ => 1) m) (y : S) :
    HasSum (fun n => ((survival P A n y : ℚ) : ℝ)) (m y : ℝ) := by
  have hsurv : ∀ n w, 0 ≤ survival P A n w := fun n w =>
    avoid_iterate_nonneg hP A n (fun _ => zero_le_one) w
  have hm0 : ∀ w, 0 ≤ m w := fun w => le_trans zero_le_one (one_le_meanReturn hP hm w)
  have hrest : ∀ N w, 0 ≤ (avoid P A)^[N] m w := fun N w => avoid_iterate_nonneg hP A N hm0 w
  obtain ⟨b, -, hbmax⟩ := exists_max_image univ m ⟨y, mem_univ y⟩
  set c := m b
  have hbound : ∀ N w, (avoid P A)^[N] m w ≤ c * survival P A N w := by
    intro N w
    have hmono := avoid_iterate_mono hP A N (g := m) (h := c • fun _ => 1)
      (fun w => by simpa using hbmax w (mem_univ w)) w
    rwa [avoid_iterate_smul] at hmono
  have hsummable : Summable (fun n => ((survival P A n y : ℚ) : ℝ)) := by
    refine summable_of_sum_range_le (c := (m y : ℝ)) (fun n => by exact_mod_cast hsurv n y)
      fun N => ?_
    have := meanReturn_split hm N y
    have h2 : truncatedReturn P A N y ≤ m y := by linarith [hrest N y]
    have h3 : ((truncatedReturn P A N y : ℚ) : ℝ) ≤ (m y : ℝ) := by exact_mod_cast h2
    simpa [truncatedReturn] using h3
  have htail : Tendsto (fun N => (((avoid P A)^[N] m y : ℚ) : ℝ)) atTop (𝓝 0) := by
    have hzero := hsummable.tendsto_atTop_zero.const_mul (c : ℝ)
    rw [mul_zero] at hzero
    refine squeeze_zero (fun N => by exact_mod_cast hrest N y) (fun N => ?_) hzero
    exact_mod_cast hbound N y
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by exact_mod_cast hsurv n y)]
  have hconst : Tendsto (fun _ : ℕ => (m y : ℝ)) atTop (𝓝 (m y : ℝ)) := tendsto_const_nhds
  have := hconst.sub htail
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  have hs := meanReturn_split hm N y
  have : ((m y : ℚ) : ℝ) - (((avoid P A)^[N] m y : ℚ) : ℝ) =
      ((truncatedReturn P A N y : ℚ) : ℝ) := by
    rw [← Rat.cast_sub]; congr 1; linarith
  rw [this, truncatedReturn]
  push_cast
  rfl

/-- [proved-derived; formal-checked] **Kac's lemma.** For a stochastic irreducible chain with a
stationary law of total mass one, the mean return time to a state is the reciprocal of its
stationary mass: `Σ_n P_x(τ_x > n) = 1/π x`, and `π x > 0`. -/
theorem kac_hasSum {P : S → S → ℚ} (hP : Stochastic P) (hirr : Irreducible P) {π : S → ℚ}
    (hπ : Stationary P π) (hmass : ∑ y, π y = 1) (x : S) :
    0 < π x ∧ HasSum (fun n => ((survival P {x} n x : ℚ) : ℝ)) (1 / (π x : ℝ)) := by
  obtain ⟨m, hm, -⟩ := firstReturn_existsUnique hP hirr (singleton_nonempty x) (fun _ => 1)
  have hkac : π x * m x = 1 := by rw [kac_single_state hπ hm, hmass]
  have hm1 := one_le_meanReturn hP hm x
  have hπpos : 0 < π x := by
    have : 0 < π x * m x := by rw [hkac]; exact one_pos
    exact pos_of_mul_pos_left this (by linarith)
  refine ⟨hπpos, ?_⟩
  have hmx : (m x : ℝ) = 1 / (π x : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hπpos.ne'), mul_comm]; exact_mod_cast hkac
  rw [← hmx]
  exact meanReturn_hasSum hP hm x

end Existence

/-! ## 3. Abramov's formula: the entropy of the coarse epoch's word -/

section Abramov

open Holonics.Foundation.SituatedInformationRate
open Real (negMulLog negMulLog_zero negMulLog_one negMulLog_mul negMulLog_nonneg)

/-- [definition] **The word of one coarse epoch, stopped at `N` fine epochs**: the law of the path
`x₁ … x_k`, `k = min(τ_A, N)`, from `y`. At horizon `N + 1` the first step to `z` is taken with
`P y z`; the word ends on reaching the section, and otherwise continues from `z` at horizon `N`.
Exact rationals. -/
def wordLaw (P : S → S → ℚ) (A : Finset S) : ℕ → S → List S → ℚ
  | 0, _, w => if w = [] then 1 else 0
  | _ + 1, _, [] => 0
  | N + 1, y, z :: w => P y z * (if z ∈ A then (if w = [] then 1 else 0) else wordLaw P A N z w)

/-- [definition] The words of at most `N` letters. -/
def words : ℕ → Finset (List S)
  | 0 => {[]}
  | N + 1 => insert [] ((univ ×ˢ words N).image fun zw => zw.1 :: zw.2)

theorem nil_mem_words : ∀ N, ([] : List S) ∈ words N
  | 0 => by simp [words]
  | _ + 1 => by simp [words]

theorem nil_not_mem_image (N : ℕ) :
    ([] : List S) ∉ (univ ×ˢ (words N : Finset (List S))).image fun zw => zw.1 :: zw.2 := by
  simp

/-- Summing over the words of `N + 1` letters: the empty word, then the first letter and the rest. -/
theorem sum_words_succ {M : Type*} [AddCommMonoid M] (N : ℕ) (f : List S → M) :
    ∑ w ∈ words (N + 1), f w = f [] + ∑ z, ∑ w ∈ words N, f (z :: w) := by
  rw [words, sum_insert (nil_not_mem_image N), sum_image, sum_product]
  intro a _ b _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

/-- [proved-derived; formal-checked] The word of a stochastic chain is a law: its total mass is
one at every horizon. -/
theorem wordLaw_mass {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) :
    ∀ N y, ∑ w ∈ words N, wordLaw P A N y w = 1
  | 0, y => by simp [words, wordLaw]
  | N + 1, y => by
    rw [sum_words_succ]
    simp only [wordLaw, zero_add, ← mul_sum]
    have hz : ∀ z, (∑ w ∈ words N,
        (if z ∈ A then (if w = [] then (1 : ℚ) else 0) else wordLaw P A N z w)) = 1 := by
      intro z
      split_ifs with hz
      · rw [sum_ite_eq' (words N) [] (fun _ => (1 : ℚ)), if_pos (nil_mem_words N)]
      · exact wordLaw_mass hrow A N z
    simp only [hz, mul_one]
    exact hrow y

/-- [definition] **The entropy of one fine epoch** from `y`: `h y = −Σ_z P y z log P y z`, of the
exact rational law, the logarithm being the only real quantity. -/
def epochEntropy (P : S → S → ℚ) (y : S) : ℝ := ∑ z, negMulLog (P y z : ℝ)

/-- [definition] **The entropy of the coarse epoch's word**, stopped at `N` fine epochs. -/
def wordEntropy (P : S → S → ℚ) (A : Finset S) (N : ℕ) (y : S) : ℝ :=
  ∑ w ∈ words N, negMulLog (wordLaw P A N y w : ℝ)

/-- [definition] The chain read over `ℝ`, for the observables that carry a logarithm. -/
def realKernel (P : S → S → ℚ) : S → S → ℝ := fun x y => (P x y : ℝ)

/-- [proved-derived; formal-checked] **The chain rule of entropy along the excursion.** The word of
`N + 1` fine epochs carries the entropy of its first step plus, where that step avoids the section,
the entropy of the rest: `H_(N+1) = h + avoid H_N`. -/
theorem wordEntropy_succ {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N : ℕ)
    (y : S) :
    wordEntropy P A (N + 1) y =
      epochEntropy P y + avoid (realKernel P) A (wordEntropy P A N) y := by
  have hstop : ∑ w ∈ (words N : Finset (List S)),
      negMulLog (((if w = [] then 1 else 0 : ℚ)) : ℝ) = 0 := by
    refine sum_eq_zero fun w _ => ?_
    split_ifs <;> simp
  have hstopMass : ∑ w ∈ (words N : Finset (List S)), (((if w = [] then 1 else 0 : ℚ)) : ℝ) = 1 := by
    rw [← Rat.cast_sum, sum_ite_eq', if_pos (nil_mem_words N), Rat.cast_one]
  have hmass : ∀ z, ∑ w ∈ words N, ((wordLaw P A N z w : ℚ) : ℝ) = 1 := fun z => by
    rw [← Rat.cast_sum, wordLaw_mass hrow A N z, Rat.cast_one]
  unfold wordEntropy
  rw [sum_words_succ (S := S) N (fun w => negMulLog (wordLaw P A (N + 1) y w : ℝ))]
  simp only [wordLaw, Rat.cast_zero, negMulLog_zero, zero_add, Rat.cast_mul, negMulLog_mul,
    sum_add_distrib, ← sum_mul, ← mul_sum]
  unfold epochEntropy avoid realKernel
  rw [← sum_add_sum_compl A, ← sum_add_sum_compl A (fun z => ((P y z : ℚ) : ℝ) * _)]
  have hA : ∀ z ∈ A, (∑ w ∈ words N, (((if z ∈ A then (if w = [] then 1 else 0) else
      wordLaw P A N z w : ℚ)) : ℝ)) * negMulLog (P y z : ℝ) +
        (P y z : ℝ) * ∑ w ∈ words N, negMulLog (((if z ∈ A then (if w = [] then 1 else 0) else
          wordLaw P A N z w : ℚ)) : ℝ) = negMulLog (P y z : ℝ) := by
    intro z hz
    simp only [if_pos hz, hstopMass, hstop]
    ring
  have hAc : ∀ z ∈ Aᶜ, (∑ w ∈ words N, (((if z ∈ A then (if w = [] then 1 else 0) else
      wordLaw P A N z w : ℚ)) : ℝ)) * negMulLog (P y z : ℝ) +
        (P y z : ℝ) * ∑ w ∈ words N, negMulLog (((if z ∈ A then (if w = [] then 1 else 0) else
          wordLaw P A N z w : ℚ)) : ℝ) =
        negMulLog (P y z : ℝ) + (P y z : ℝ) * ∑ w ∈ words N, negMulLog (wordLaw P A N z w : ℝ) := by
    intro z hz
    simp only [if_neg (mem_compl.mp hz), hmass, one_mul]
  rw [add_add_add_comm, ← sum_add_distrib, ← sum_add_distrib, sum_congr rfl hA, sum_congr rfl hAc,
    sum_add_distrib, ← sum_add_sum_compl A (fun z => negMulLog (P y z : ℝ))]
  ring

/-- [proved-derived; formal-checked] **The stopped word's entropy is the accumulated fine
entropy**: `H_N = Σ_(n<N) avoidⁿ h`, the truncation of the first-step solution. -/
theorem wordEntropy_eq_sum {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) :
    ∀ N, wordEntropy P A N =
      ∑ n ∈ range N, (avoid (realKernel P) A)^[n] (epochEntropy P)
  | 0 => by
    funext y
    simp [wordEntropy, words, wordLaw]
  | N + 1 => by
    funext y
    have hlin : ∀ (s : Finset ℕ) (g : ℕ → S → ℝ),
        avoid (realKernel P) A (∑ n ∈ s, g n) = ∑ n ∈ s, avoid (realKernel P) A (g n) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => funext x; simp [avoid]
      | insert a s ha ih => rw [sum_insert ha, avoid_add, ih, sum_insert ha]
    rw [wordEntropy_succ hrow, wordEntropy_eq_sum hrow A N, sum_range_succ', hlin]
    simp only [Pi.add_apply, Finset.sum_apply, Function.iterate_succ_apply',
      Function.iterate_zero_apply]
    ring

/-- [proved-derived; formal-checked] **Kac's ledger for an observable, exact at every truncation.**
`Σ_(y∈A) π y Σ_(n<N) (avoidⁿ f) y = Σ_y π y f y − Σ_y π y (avoidᴺ f) y`. -/
theorem kac_ledger_observable {R : Type*} [CommRing R] {P : S → S → R} {π : S → R}
    (hπ : Stationary P π) (A : Finset S) (f : S → R) (N : ℕ) :
    ∑ y ∈ A, π y * ∑ n ∈ range N, (avoid P A)^[n] f y =
      ∑ y, π y * f y - ∑ y, π y * (avoid P A)^[N] f y := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : ∑ y, π y * (avoid P A)^[N + 1] f y = ∑ z ∈ Aᶜ, π z * (avoid P A)^[N] f z := by
      rw [Function.iterate_succ_apply']
      exact stationary_avoid_sum hπ A _
    have hsplit := sum_add_sum_compl A (fun y => π y * (avoid P A)^[N] f y)
    simp only [sum_range_succ, mul_add, sum_add_distrib] at ih ⊢
    rw [ih, hstep]
    linear_combination hsplit

/-- [definition] The stationary weights restricted to the section, over `ℝ`. -/
def sectionWeight (π : S → ℚ) (A : Finset S) : S → ℝ := fun y => if y ∈ A then (π y : ℝ) else 0

/-- [proved-derived; formal-checked] **Abramov's ledger, exact at every truncation.** Read from the
stationary law on the section, the entropy of the coarse epoch's word stopped at `N` fine epochs is
the fine entropy of `π` minus the entropy still avoiding the section:
`Σ_(y∈A) π y H_N(y) = Σ_y π y h(y) − Σ_y π y (avoidᴺ h)(y)`. Only stationarity and stochastic rows
are used. -/
theorem abramov_ledger {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) {π : S → ℚ}
    (hπ : Stationary P π) (A : Finset S) (N : ℕ) :
    totalInformation (sectionWeight π A) (wordEntropy P A N) =
      totalInformation (fun y => (π y : ℝ)) (epochEntropy P) -
        ∑ y, (π y : ℝ) * (avoid (realKernel P) A)^[N] (epochEntropy P) y := by
  have hπR : Stationary (realKernel P) (fun y => (π y : ℝ)) := fun y => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hπ y)
    simpa [realKernel] using this
  have hinfo : totalInformation (sectionWeight π A) (wordEntropy P A N) =
      ∑ y ∈ A, (π y : ℝ) * wordEntropy P A N y := by
    simp only [totalInformation, sectionWeight, ite_mul, zero_mul]
    rw [← sum_filter]; congr 1; ext y; simp
  rw [hinfo, wordEntropy_eq_sum hrow A N]
  simp only [Finset.sum_apply]
  exact kac_ledger_observable hπR A _ N

/-- The real kernel carries the rational avoiding epoch. -/
theorem avoid_realKernel_cast (P : S → S → ℚ) (A : Finset S) (g : S → ℚ) :
    avoid (realKernel P) A (fun y => (g y : ℝ)) = fun y => ((avoid P A g y : ℚ) : ℝ) := by
  funext y; simp [avoid, realKernel]

theorem avoid_realKernel_iterate_cast (P : S → S → ℚ) (A : Finset S) (g : S → ℚ) (n : ℕ) :
    (avoid (realKernel P) A)^[n] (fun y => (g y : ℝ)) =
      fun y => (((avoid P A)^[n] g y : ℚ) : ℝ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, avoid_realKernel_cast,
      Function.iterate_succ_apply']

/-- The avoiding epoch of a nonnegative kernel is monotone. -/
theorem avoid_realKernel_iterate_mono {P : S → S → ℚ} (hP : ∀ x y, 0 ≤ P x y) (A : Finset S)
    (n : ℕ) {g h : S → ℝ} (hgh : ∀ y, g y ≤ h y) (y : S) :
    (avoid (realKernel P) A)^[n] g y ≤ (avoid (realKernel P) A)^[n] h y := by
  induction n generalizing y with
  | zero => exact hgh y
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ih z)
      (by simp only [realKernel]; exact_mod_cast hP y z)

omit [DecidableEq S] in
/-- [proved-derived; formal-checked] One fine epoch of a stochastic row carries nonnegative
entropy. -/
theorem epochEntropy_nonneg {P : S → S → ℚ} (hP : Stochastic P) (y : S) :
    0 ≤ epochEntropy P y := by
  refine sum_nonneg fun z _ => negMulLog_nonneg (by exact_mod_cast hP.1 y z) ?_
  have : P y z ≤ 1 := by
    rw [← hP.2 y]
    exact single_le_sum (fun w _ => hP.1 y w) (mem_univ z)
  exact_mod_cast this

/-- [proved-derived; formal-checked] **Abramov's formula for the induced chain.** For a
stochastic, irreducible chain with a nonnegative stationary law `π` and a section of nonzero
stationary mass `π(A) ≠ 0`, the entropy of one coarse epoch's word read from the section's
normalized stationary law `π|_A / π(A)` is `Σ_y π y h(y) / π(A)`: with `Σ π = 1`, the fine entropy
rate `h` divided by the section's measure, `h(T_A) = h(T)/μ(A)`. The word is stopped at `N` fine
epochs and the formula holds in the limit `N → ∞` of the exact ledger (`abramov_ledger`), the
tail vanishing because the chain crosses the section (`meanReturn_hasSum`). -/
theorem abramov {P : S → S → ℚ} (hP : Stochastic P) (hirr : Irreducible P) {π : S → ℚ}
    (hπ : Stationary P π) (hπpos : ∀ y, 0 ≤ π y) {A : Finset S}
    (hA : totalMass (sectionWeight π A) ≠ 0) :
    Filter.Tendsto (fun N => informationRate (sectionWeight π A) (wordEntropy P A N))
      Filter.atTop
      (𝓝 (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) /
        totalMass (sectionWeight π A))) := by
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hA (by simp [totalMass, sectionWeight])
  obtain ⟨m, hm, -⟩ := firstReturn_existsUnique hP hirr hAne (fun _ => 1)
  -- the survival mass tends to zero
  have hsurv : ∀ y, Filter.Tendsto (fun N => ((survival P A N y : ℚ) : ℝ)) Filter.atTop (𝓝 0) :=
    fun y => (meanReturn_hasSum hP hm y).summable.tendsto_atTop_zero
  obtain ⟨b, -, hbmax⟩ := exists_max_image univ (epochEntropy P) ⟨hAne.choose, mem_univ _⟩
  set c := epochEntropy P b
  have hbound : ∀ N y, (avoid (realKernel P) A)^[N] (epochEntropy P) y ≤
      c * ((survival P A N y : ℚ) : ℝ) := by
    intro N y
    have hmono := avoid_realKernel_iterate_mono hP.1 A N (g := epochEntropy P)
      (h := fun y => c * (((fun _ => (1 : ℚ)) y : ℚ) : ℝ)) (fun w => by simpa using hbmax w (mem_univ w)) y
    have hsmul : (avoid (realKernel P) A)^[N] (fun y => c * (((fun _ => (1 : ℚ)) y : ℚ) : ℝ)) =
        c • (avoid (realKernel P) A)^[N] (fun y => (((fun _ => (1 : ℚ)) y : ℚ) : ℝ)) := by
      rw [← avoid_iterate_smul]; rfl
    rw [hsmul, avoid_realKernel_iterate_cast] at hmono
    simpa [survival] using hmono
  have hlow : ∀ N y, 0 ≤ (avoid (realKernel P) A)^[N] (epochEntropy P) y := by
    intro N y
    have := avoid_realKernel_iterate_mono hP.1 A N (g := fun _ => (0 : ℝ))
      (h := epochEntropy P) (fun w => epochEntropy_nonneg hP w) y
    have h0 : (avoid (realKernel P) A)^[N] (fun _ => (0 : ℝ)) = fun _ => 0 :=
      Function.iterate_fixed (by funext x; simp [avoid]) N
    rwa [h0] at this
  have htail : Filter.Tendsto
      (fun N => ∑ y, (π y : ℝ) * (avoid (realKernel P) A)^[N] (epochEntropy P) y)
      Filter.atTop (𝓝 0) := by
    have hlim : Filter.Tendsto (fun N => ∑ y, (π y : ℝ) * (c * ((survival P A N y : ℚ) : ℝ)))
        Filter.atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset S) fun y _ =>
        ((hsurv y).const_mul c).const_mul (π y : ℝ)
      simpa using this
    refine squeeze_zero (fun N => sum_nonneg fun y _ =>
      mul_nonneg (by exact_mod_cast hπpos y) (hlow N y)) (fun N => sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hbound N y) (by exact_mod_cast hπpos y)) hlim
  have hledger : ∀ N, informationRate (sectionWeight π A) (wordEntropy P A N) =
      (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) -
        ∑ y, (π y : ℝ) * (avoid (realKernel P) A)^[N] (epochEntropy P) y) /
          totalMass (sectionWeight π A) := fun N => by
    rw [informationRate, abramov_ledger hP.2 hπ A N]
  simp_rw [hledger]
  have := (tendsto_const_nhds (x := totalInformation (fun y => (π y : ℝ)) (epochEntropy P))).sub
    htail
  rw [sub_zero] at this
  exact this.div_const _

end Abramov

/-! ## 4. Irreducibility is load-bearing -/

namespace Reducible

/-- [definition] The identity chain on two states: each state stays put. -/
def stay : Fin 2 → Fin 2 → ℚ := fun x y => if x = y then 1 else 0

/-- [definition] The uniform law, stationary for `stay`. -/
def uniform : Fin 2 → ℚ := fun _ => 1 / 2

theorem stay_stationary : Stationary stay uniform := by
  intro y; fin_cases y <;> simp [stay, uniform]

theorem stay_stochastic : Stochastic stay :=
  ⟨fun x y => by unfold stay; split_ifs <;> norm_num,
    fun x => by fin_cases x <;> simp [stay]⟩

theorem stay_not_irreducible : ¬ Irreducible stay := by
  intro h
  have := h 0 1
  have hstuck : ∀ w, Relation.ReflTransGen (fun a b => 0 < stay a b) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      by_contra hne
      simp [stay, Ne.symm hne] at hstep
  exact absurd (hstuck 1 this) (by decide)

theorem stay_survival_zero (n : ℕ) : survival stay {0} (n + 1) 0 = 0 := by
  rw [survival, Function.iterate_succ_apply']
  simp [avoid, stay, Finset.compl_singleton]

theorem stay_survival_one (n : ℕ) : survival stay {0} n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [survival, Function.iterate_succ_apply']
    simp only [avoid, Finset.compl_singleton]
    rw [show (Finset.univ.erase (0 : Fin 2)) = {1} by decide, sum_singleton]
    change stay 1 1 * survival stay {0} n 1 = 1
    rw [ih]; simp [stay]

/-- [counterexample; formal-checked] **Kac fails without irreducibility.** The identity chain with
the stationary law `(1/2, 1/2)` returns to `0` after one epoch at every truncation, so
`π 0 · E_0[τ_0] = 1/2 ≠ 1`; the ledger keeps a residue `1/2` of mass that never crosses; and the
first-step equations of the mean return have no solution. -/
theorem reducible_kac_fails :
    ¬ Irreducible stay ∧ Stationary stay uniform ∧ ∑ y, uniform y = 1 ∧
      (∀ N, truncatedReturn stay {0} (N + 1) 0 = 1) ∧
      uniform 0 * 1 ≠ 1 ∧
      (∀ N, ∑ y, uniform y * survival stay {0} (N + 1) y = 1 / 2) ∧
      ¬ ∃ m, FirstReturnEquations stay {0} (fun _ => 1) m := by
  refine ⟨stay_not_irreducible, stay_stationary, by norm_num [uniform], ?_, by
    norm_num [uniform], ?_, ?_⟩
  · intro N
    induction N with
    | zero => simp [truncatedReturn, survival]
    | succ N ih => rw [truncatedReturn, sum_range_succ, ← truncatedReturn, ih,
        stay_survival_zero, add_zero]
  · intro N
    rw [Fin.sum_univ_two, stay_survival_zero, stay_survival_one]; norm_num [uniform]
  · rintro ⟨m, hm⟩
    have := hm 1
    simp only [avoid, Finset.compl_singleton] at this
    rw [show (Finset.univ.erase (0 : Fin 2)) = {1} by decide, sum_singleton] at this
    simp [stay] at this

end Reducible

section Audit

#print axioms kac_ledger
#print axioms kac_observable
#print axioms kac_single_state
#print axioms kac_grain_ratio
#print axioms firstReturn_existsUnique
#print axioms meanReturn_hasSum
#print axioms kac_hasSum
#print axioms wordLaw_mass
#print axioms wordEntropy_succ
#print axioms wordEntropy_eq_sum
#print axioms kac_ledger_observable
#print axioms abramov_ledger
#print axioms abramov
#print axioms Reducible.reducible_kac_fails

end Audit

end Holonics.Aeon.Production.Kac
