import Holonics.Aeon.Production.Kac

/-!
# The induced chain on a section and the entropy rate of its words

[definition] Source: the box of #410 "The Kolmogorov–Sinai entropy of the induced shift (general
Abramov) and general ergodic maps (`Aeon/Production/Kac`)", and the `[open]` paragraph of
`Aeon/Production/Kac`: the identification of the induced shift's entropy with the per-word entropy
`Σ_(y∈A) π_A(y) H(W_y)`, the entropy rate of the Markov chain of words whose conditional word law
depends only on the returning state. This module takes the finite Markov side of that box. Aeon
record A4 and the across-grains law; atlas `aeon.abramov-ledger`, `aeon.abramov-induced-chain`,
`aeon.a4-entropy-clock-change`, `aeon.kac-observable`, `aeon.kac-existence`, `aeon.kac-series`,
`aeon.epoch-ticks`, `xent.clock-change`.

A finite chain `P` moves one **fine epoch** a step. A **section** `A` is a coarser receiver: its
epochs run from one crossing of `A` to the next, and epochs count the flux through it. The
**induced chain** moves one **coarse epoch** a step: `P_A(y, y′)` is the mass started at `y` whose
first return to `A` lands at `y′`. The **word** of a coarse epoch is the owner's `wordLaw`, stopped
at `N` fine epochs, and the next coarse epoch starts where the word ends (`endState`).

[proved-standard; formal-checked] What is proved: classical statements, each restated on the
owner's objects. Throughout `P` is a stochastic irreducible chain of rationals and `A` a nonempty
section, as in the owner's `abramov`; items 1 and 6 are the house's own derivation and witness
(`[proved-derived; formal-checked]`).

1. **The first-step solution and its series.** `firstReturnSolution P A f` is the one solution of
   the owner's first-step equations (`firstReturnSolution_spec`, `firstReturnSolution_eq`, through
   `firstReturn_existsUnique`). A solution is its truncated series plus the field still avoiding,
   `m = Σ_(n<N) avoidⁿ f + avoidᴺ m`, over any commutative ring (`firstReturn_split`); a field still
   avoiding is bounded by the survival mass and dies out (`avoid_iterate_abs_le`,
   `avoid_iterate_tendsto_zero`), so for `f ≥ 0` the solution is the series `Σ_n avoidⁿ f`
   (`firstReturnSolution_hasSum`).
2. **The induced chain.** `inducedKernel P A y y′` is the first-step solution of `f = P(·, y′)` for
   `y′ ∈ A`, and `0` off `A`. It is the series of first landings (`inducedKernel_hasSum`), it is
   nonnegative (`inducedKernel_nonneg`), and its rows carry mass one on `A`
   (`inducedKernel_row`): the landing fields add (`firstReturnEquations_sum`) to the solution of
   `Σ_(y′∈A) P(·, y′)`, which the constant `1` also solves. So it is a stochastic kernel
   (`inducedKernel_stochastic`).
3. **Kac's ledger read on the return state.** With `π` stationary, `Σ_(y∈A) π y · m_(y′)(y) = π y′`
   for every state `y′` (`occupation_stationary`: the owner's `kac_observable` with `f = P(·, y′)`
   and `Σ_y π y P(y, y′) = π y′`). On the section it reads `Σ_(y∈A) π y · P_A(y, y′) = π y′`
   (`induced_stationary`); off it, the mean occupation of `y′` in one coarse epoch. The normalized
   law `π_A = π|_A / π(A)` (`sectionLaw`, of mass one: `sectionLaw_mass`, nonnegative for a
   nonnegative `π`: `sectionLaw_nonneg`) is a stationary law of the induced chain
   (`sectionLaw_stationary`).
4. **The chain of words at every truncation.** The words of successive coarse epochs form a chain
   whose next word's law is the word law from the state where the last word ended (`blockLaw`, of
   mass one: `blockLaw_mass`). That state has the truncated return kernel `Q_N` (`endKernel`, rows
   of mass one: `endKernel_mass`), with first-step equations
   `Q_(N+1)(·, y′) = [y′ ∈ A] P(·, y′) + avoid Q_N(·, y′)` and `Q_0(y, y′) = [y = y′]` (`endKernel_succ`,
   `endKernel_zero`). The chain rule along the coarse epochs,
   `H(W₁, …, W_(n+1) | y) = H_N(y) + Σ_(y′) Q_N(y, y′) H(W₁, …, W_n | y′)` (`blockEntropy_succ`; the
   two-word block `H(W₁, W₂ | y) = H_N(y) + Σ Q_N H_N`: `twoWord_chain_rule`), gives the block
   entropy from any law `ν` as `Σ_(k<n) Σ_y (ν Q_Nᵏ)(y) H_N(y)` (`blockEntropy_eq_sum`); from a
   stationary law of `Q_N` it is `n` times the per-word entropy (`blockEntropy_of_stationary`). Only
   stochastic rows are used.
5. **The limit `N → ∞` and Abramov for the word chain.** `H_N(y) → H(W_y)`, the series
   `Σ_n (avoidⁿ h)(y)` of the fine entropy accumulated until the return (`wordEntropyLimit`,
   `wordEntropy_tendsto`); `Q_N → P_A` entrywise (`endKernel_tendsto`), so `ν Q_Nᵏ → ν P_Aᵏ`
   (`stepLaw_iterate_tendsto`). From the section's law the block entropy of `n` words tends to
   `n · Σ_y π_A(y) H(W_y)` (`wordChain_blockEntropy_tendsto`), and the per-word entropy is
   Abramov's ratio `Σ_y π y h(y) / π(A)` (`sectionLaw_wordEntropyLimit`, the limit of the owner's
   `abramov_ledger`, read as the owner's information rate by `sectionLaw_sum_eq`). So the entropy
   rate of the word chain is `Σ π h / π(A)`; with `Σ π = 1`, the fine rate over the section's
   measure, `h(T_A) = h(T)/μ(A)` (`wordChain_abramov`, and per word at every `n ≥ 1`:
   `wordChain_entropyRate`). No sign of `π` is used: the tail of the ledger dies by
   `avoid_iterate_tendsto_zero`, where the owner's `abramov` takes `π ≥ 0`.
6. **Witness.** On three states, `0 → 0, 1` with `1/2` each, `1 → 2`, `2 → 0`, with the section
   `{0, 1}` and the stationary law `(1/2, 1/4, 1/4)`: the induced kernel on the section is
   `[[1/2, 1/2], [1, 0]]` (`loop_inducedKernel`), the section's law `(2/3, 1/3)` is stationary for
   it (`loop_sectionLaw`), and `n` words carry `n · (2/3) log 2` in the limit, the fine rate
   `(1/2) log 2` over the section's measure `3/4` (`loop_wordChain`): the word from `0` is `[0]` or
   `[1]`, and from `1` it is `[2, 0]`.

The block entropy is read from the state where the block starts,
`Σ_y π_A(y) H(W₁, …, W_n | Y₀ = y)`. In the stationary chain of words `Y₀` is the end state of the
word before, so it is the block entropy given the previous word: the form whose per-word value is
the entropy rate of a stationary Markov chain, at every `n`.

What is not claimed. The Kolmogorov–Sinai entropy of the induced shift as a supremum over
partitions (Mathlib has no owner), the generator theorem that would identify it with the entropy
rate of the word chain, Abramov's formula for a general ergodic measure-preserving map, and
countable state spaces. The block entropy of `n` words from the mixture `Σ_y π_A(y) W_y` without the
starting state differs from the conditioned one by the information the words carry about `Y₀` (at
most `log |A|`), and it is not stated. The block law is the path law of the fine chain cut at its
returns through its recursion (the Markov property at a return); no path-space measure or strong
Markov property is built. `H(W_y)` is the series of the accumulated fine entropy, the limit of the
stopped entropies; that it is the entropy of the untruncated word law on the countable set of
finite words is not stated. The limit is taken in `N` at each `n`, as the owner's `abramov` takes
it; the rate of the truncated chain as `n → ∞` before `N → ∞` is not stated.

Computational object: the helical pair interaction read at a section, one coarse epoch a step. Of
the winding guide's six objects it touches the tube (a word is the clocked span between two
crossings of the section, and the induced kernel is the transfer from one section chart to the
next) and the tower thread (the section's coarse clock is a restriction of the fine clock, with
Kac's and Abramov's ratios across the grains); helix, pair, faces and placement and cell holonomy
stay attached.

Consumers: `Aeon/Production/Kac` (the finite Markov side of its `[open]` paragraph), atlas
`aeon.abramov-induced-chain` and `aeon.a4-entropy-clock-change`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.InducedWords

open scoped BigOperators
open Finset Filter Topology
open Holonics.Aeon.Production.Kac
open Holonics.Foundation.SituatedInformationRate
open Real (negMulLog negMulLog_zero negMulLog_one negMulLog_mul)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## 1. The first-step solution and its series -/

section Solution

open Classical in
/-- [definition] **The solution of the first-step equations** of an observable `f`: the field `m`
with `m y = f y + Σ_(z ∉ A) P y z · m z`, chosen when one exists and `0` otherwise. For a
stochastic irreducible chain and a nonempty section it is the one solution
(`firstReturnSolution_spec`, `firstReturnSolution_eq`). -/
def firstReturnSolution (P : S → S → ℚ) (A : Finset S) (f : S → ℚ) : S → ℚ :=
  if h : ∃ m, FirstReturnEquations P A f m then h.choose else 0

/-- [proved-derived; formal-checked] Under irreducibility the chosen field solves the equations. -/
theorem firstReturnSolution_spec {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (f : S → ℚ) :
    FirstReturnEquations P A f (firstReturnSolution P A f) := by
  have h : ∃ m, FirstReturnEquations P A f m := (firstReturn_existsUnique hP hirr hA f).exists
  rw [firstReturnSolution, dif_pos h]
  exact h.choose_spec

/-- [proved-derived; formal-checked] Every solution of the equations is the chosen one. -/
theorem firstReturnSolution_eq {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {f m : S → ℚ} (hm : FirstReturnEquations P A f m) :
    firstReturnSolution P A f = m :=
  (firstReturn_existsUnique hP hirr hA f).unique (firstReturnSolution_spec hP hirr hA f) hm

/-- [proved-derived; formal-checked] The avoiding epoch carries differences. -/
theorem avoid_sub {R : Type*} [CommRing R] (P : S → S → R) (A : Finset S) (g h : S → R) :
    avoid P A (g - h) = avoid P A g - avoid P A h := by
  funext y; simp [avoid, mul_sub, sum_sub_distrib]

/-- [proved-derived; formal-checked] **A solution is its truncated series plus the field still
avoiding**: `m = Σ_(n<N) avoidⁿ f + avoidᴺ m`, over any commutative ring. -/
theorem firstReturn_split {R : Type*} [CommRing R] {P : S → S → R} {A : Finset S} {f m : S → R}
    (hm : FirstReturnEquations P A f m) (N : ℕ) (y : S) :
    m y = ∑ n ∈ range N, (avoid P A)^[n] f y + (avoid P A)^[N] m y := by
  have hfix : m = f + avoid P A m := funext hm
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    have hnext : (avoid P A)^[N] m = (avoid P A)^[N] f + (avoid P A)^[N + 1] m := by
      conv_lhs => rw [hfix]
      rw [avoid_iterate_add, Function.iterate_succ_apply]
    rw [ih y, hnext, Pi.add_apply, sum_range_succ]
    ring

/-- [proved-derived; formal-checked] The avoiding epochs of a constant field carry the survival
mass: `avoidᴺ c = c · P(τ_A > N)`. -/
theorem avoid_iterate_const (P : S → S → ℚ) (A : Finset S) (N : ℕ) (c : ℝ) (y : S) :
    (avoid (realKernel P) A)^[N] (fun _ => c) y = c * ((survival P A N y : ℚ) : ℝ) := by
  have h1 : (fun _ : S => c) = c • (fun y => (((fun _ => (1 : ℚ)) y : ℚ) : ℝ)) := by
    funext y; simp
  rw [h1, avoid_iterate_smul, avoid_realKernel_iterate_cast]
  simp [survival]

/-- [proved-derived; formal-checked] **The field still avoiding is bounded by the survival mass**:
`|avoidᴺ g| ≤ c · P(τ_A > N)` whenever `|g| ≤ c`. -/
theorem avoid_iterate_abs_le {P : S → S → ℚ} (hP : ∀ x y, 0 ≤ P x y) (A : Finset S) (N : ℕ)
    {g : S → ℝ} {c : ℝ} (hc : ∀ x, |g x| ≤ c) (y : S) :
    |(avoid (realKernel P) A)^[N] g y| ≤ c * ((survival P A N y : ℚ) : ℝ) := by
  rw [abs_le]
  constructor
  · have := avoid_realKernel_iterate_mono hP A N (g := fun _ => -c) (h := g)
      (fun x => by linarith [neg_abs_le (g x), hc x]) y
    rw [avoid_iterate_const] at this
    linarith
  · have := avoid_realKernel_iterate_mono hP A N (g := g) (h := fun _ => c)
      (fun x => (le_abs_self _).trans (hc x)) y
    rwa [avoid_iterate_const] at this

/-- [proved-derived; formal-checked] The survival mass is summable over the fine epochs. -/
theorem survival_summable {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (y : S) :
    Summable (fun N => ((survival P A N y : ℚ) : ℝ)) := by
  obtain ⟨m, hm, -⟩ := firstReturn_existsUnique hP hirr hA (fun _ => 1)
  exact (meanReturn_hasSum hP hm y).summable

/-- [proved-derived; formal-checked] **Every field still avoiding the section dies out**:
`avoidᴺ g → 0`, for a stochastic irreducible chain and a nonempty section. -/
theorem avoid_iterate_tendsto_zero {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (g : S → ℝ) (y : S) :
    Tendsto (fun N => (avoid (realKernel P) A)^[N] g y) atTop (𝓝 0) := by
  have hc : ∀ x, |g x| ≤ ∑ z, |g z| := fun x =>
    single_le_sum (f := fun z => |g z|) (fun z _ => abs_nonneg (g z)) (mem_univ x)
  have hlim := (survival_summable hP hirr hA y).tendsto_atTop_zero.const_mul (∑ z, |g z|)
  rw [mul_zero] at hlim
  exact squeeze_zero_norm (fun N => by
    rw [Real.norm_eq_abs]; exact avoid_iterate_abs_le hP.1 A N hc y) hlim

/-- [proved-derived; formal-checked] **The first-step solution of a nonnegative observable is its
series** `Σ_n (avoidⁿ f) y`, a convergent series of rationals. -/
theorem firstReturnSolution_hasSum {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {f : S → ℚ} (hf : ∀ y, 0 ≤ f y) (y : S) :
    HasSum (fun n => (((avoid P A)^[n] f y : ℚ) : ℝ)) (firstReturnSolution P A f y : ℝ) := by
  have hm := firstReturnSolution_spec hP hirr hA f
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by exact_mod_cast avoid_iterate_nonneg hP A n hf y)]
  have htail := avoid_iterate_tendsto_zero hP hirr hA
    (fun x => (firstReturnSolution P A f x : ℝ)) y
  simp only [avoid_realKernel_iterate_cast] at htail
  have := (tendsto_const_nhds (x := (firstReturnSolution P A f y : ℝ))).sub htail
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  have hq : firstReturnSolution P A f y - (avoid P A)^[N] (firstReturnSolution P A f) y =
      ∑ n ∈ range N, (avoid P A)^[n] f y := by
    linarith [firstReturn_split hm N y]
  exact_mod_cast hq

end Solution

/-! ## 2. The induced chain on the section -/

section Induced

/-- [definition] **The induced kernel on the section**: `P_A(y, y′)` is the mass, started at `y`,
whose first return to `A` (at fine epoch `≥ 1`) lands at `y′ ∈ A`; it is the first-step solution of
the observable `f = P(·, y′)`, and `0` for `y′ ∉ A`. -/
def inducedKernel (P : S → S → ℚ) (A : Finset S) : S → S → ℚ :=
  fun y y' => if y' ∈ A then firstReturnSolution P A (fun x => P x y') y else 0

/-- [proved-standard; formal-checked] **The induced kernel is the series of first landings**:
`P_A(y, y′) = Σ_n (avoidⁿ P(·, y′))(y)`, the `n`-th term the mass that avoids `A` for `n` fine
epochs and then steps to `y′`. -/
theorem inducedKernel_hasSum {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {y' : S} (hy' : y' ∈ A) (y : S) :
    HasSum (fun n => (((avoid P A)^[n] (fun x => P x y') y : ℚ) : ℝ)) (inducedKernel P A y y' : ℝ) := by
  simp only [inducedKernel, if_pos hy']
  exact firstReturnSolution_hasSum hP hirr hA (fun x => hP.1 x y') y

/-- [proved-standard; formal-checked] The induced kernel is nonnegative. -/
theorem inducedKernel_nonneg {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (y y' : S) : 0 ≤ inducedKernel P A y y' := by
  by_cases hy' : y' ∈ A
  · have := (inducedKernel_hasSum hP hirr hA hy' y).nonneg fun n => by
      exact_mod_cast avoid_iterate_nonneg hP A n (fun x => hP.1 x y') y
    exact_mod_cast this
  · simp [inducedKernel, hy']

/-- [proved-derived; formal-checked] The first-step equations add: solutions of `f_i` sum to a
solution of `Σ f_i`. -/
theorem firstReturnEquations_sum {R : Type*} [CommRing R] {P : S → S → R} {A : Finset S}
    {ι : Type*} (s : Finset ι) {f m : ι → S → R}
    (h : ∀ i ∈ s, FirstReturnEquations P A (f i) (m i)) :
    FirstReturnEquations P A (fun y => ∑ i ∈ s, f i y) (fun y => ∑ i ∈ s, m i y) := by
  intro y
  have hav : avoid P A (fun y => ∑ i ∈ s, m i y) y = ∑ i ∈ s, avoid P A (m i) y := by
    simp only [avoid, mul_sum]
    exact sum_comm
  rw [hav, ← sum_add_distrib]
  exact sum_congr rfl fun i hi => h i hi y

/-- [proved-standard; formal-checked] **The first return lands on the section with total mass
one**: `Σ_(y′∈A) P_A(y, y′) = 1`. The sum of the landing fields solves the equations of
`Σ_(y′∈A) P(·, y′)`, which the constant `1` also solves. -/
theorem inducedKernel_row {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (y : S) : ∑ y' ∈ A, inducedKernel P A y y' = 1 := by
  have hsum := firstReturnEquations_sum A (f := fun y' x => P x y')
    (m := fun y' => firstReturnSolution P A (fun x => P x y'))
    (fun y' _ => firstReturnSolution_spec hP hirr hA _)
  have hone : FirstReturnEquations P A (fun x => ∑ y' ∈ A, P x y') (fun _ => 1) := by
    intro x
    simp only [avoid, mul_one]
    rw [sum_add_sum_compl, hP.2 x]
  have hy := congrFun ((firstReturn_existsUnique hP hirr hA _).unique hsum hone) y
  rw [← hy]
  exact sum_congr rfl fun y' hy' => by simp [inducedKernel, hy']

/-- [proved-standard; formal-checked] **The induced chain is stochastic**: from every state the first
return to `A` is a law on `A`. -/
theorem inducedKernel_stochastic {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) : Stochastic (inducedKernel P A) := by
  refine ⟨inducedKernel_nonneg hP hirr hA, fun x => ?_⟩
  rw [← sum_add_sum_compl A (inducedKernel P A x), inducedKernel_row hP hirr hA x,
    sum_eq_zero fun y hy => by simp [inducedKernel, mem_compl.mp hy], add_zero]

/-- [proved-standard; formal-checked] **The stationary law is the mean occupation of one coarse
epoch**: `Σ_(y∈A) π y · m_(y′)(y) = π y′` for every state `y′`, with `m_(y′)` the first-step
solution of `P(·, y′)`. On the section it is the landing law; off it, the mean number of visits to
`y′` before the return. -/
theorem occupation_stationary {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {π : S → ℚ} (hπ : Stationary P π) (y' : S) :
    ∑ y ∈ A, π y * firstReturnSolution P A (fun x => P x y') y = π y' := by
  rw [kac_observable hπ (firstReturnSolution_spec hP hirr hA _)]
  exact hπ y'

/-- [proved-standard; formal-checked] **The section's stationary weights are stationary for the
induced chain**: `Σ_(y∈A) π y · P_A(y, y′) = π y′` for `y′ ∈ A`. -/
theorem induced_stationary {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {π : S → ℚ} (hπ : Stationary P π) {y' : S} (hy' : y' ∈ A) :
    ∑ y ∈ A, π y * inducedKernel P A y y' = π y' := by
  simp only [inducedKernel, if_pos hy']
  exact occupation_stationary hP hirr hA hπ y'

/-- [definition] **The section's normalized law** `π_A = π|_A / π(A)`. -/
def sectionLaw (π : S → ℚ) (A : Finset S) : S → ℚ :=
  fun y => (if y ∈ A then π y else 0) / ∑ x ∈ A, π x

/-- [proved-standard; formal-checked] **The section's normalized law is a stationary law of the
induced chain** (Kac's ledger read on the return state). -/
theorem sectionLaw_stationary {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) {π : S → ℚ} (hπ : Stationary P π) :
    Stationary (inducedKernel P A) (sectionLaw π A) := by
  intro y'
  simp only [sectionLaw, div_mul_eq_mul_div, ← sum_div, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter]
  by_cases hy' : y' ∈ A
  · rw [induced_stationary hP hirr hA hπ hy', if_pos hy']
  · rw [if_neg hy', sum_eq_zero fun y _ => by simp [inducedKernel, hy']]

/-- [proved-derived; formal-checked] The section's normalized law has total mass one. -/
theorem sectionLaw_mass {π : S → ℚ} {A : Finset S} (hA : ∑ x ∈ A, π x ≠ 0) :
    ∑ y, sectionLaw π A y = 1 := by
  simp only [sectionLaw, ← sum_div]
  rw [sum_ite_mem, univ_inter, div_self hA]

omit [Fintype S] in
/-- [proved-derived; formal-checked] The section's normalized law of a nonnegative law is
nonnegative. -/
theorem sectionLaw_nonneg {π : S → ℚ} (hπ : ∀ y, 0 ≤ π y) (A : Finset S) (y : S) :
    0 ≤ sectionLaw π A y :=
  div_nonneg (by split_ifs <;> simp [hπ y]) (sum_nonneg fun x _ => hπ x)

end Induced

/-! ## 3. The chain of words at a truncation -/

section Words

/-- [definition] **The state where a word ends**: its last letter, or the starting state for the
empty word. The next coarse epoch starts there. -/
def endState : S → List S → S
  | y, [] => y
  | _, z :: w => endState z w

/-- [definition] **The truncated return kernel** `Q_N(y, y′)`: the mass of the words of one coarse
epoch, stopped at `N` fine epochs, that end at `y′`. -/
def endKernel (P : S → S → ℚ) (A : Finset S) (N : ℕ) (y y' : S) : ℚ :=
  ∑ w ∈ words N, wordLaw P A N y w * if endState y w = y' then 1 else 0

/-- [proved-derived; formal-checked] At horizon zero the word is empty and ends where it starts. -/
theorem endKernel_zero (P : S → S → ℚ) (A : Finset S) (y y' : S) :
    endKernel P A 0 y y' = if y = y' then 1 else 0 := by
  simp [endKernel, words, wordLaw, endState]

/-- [proved-derived; formal-checked] **The truncated return kernel's first-step equations**:
`Q_(N+1)(·, y′) = [y′ ∈ A] P(·, y′) + avoid Q_N(·, y′)`. -/
theorem endKernel_succ (P : S → S → ℚ) (A : Finset S) (N : ℕ) (y y' : S) :
    endKernel P A (N + 1) y y' =
      (if y' ∈ A then P y y' else 0) + avoid P A (fun z => endKernel P A N z y') y := by
  rw [endKernel, sum_words_succ]
  show wordLaw P A (N + 1) y [] * (if y = y' then 1 else 0) +
      ∑ z, ∑ w ∈ words N, wordLaw P A (N + 1) y (z :: w) * (if endState z w = y' then 1 else 0) = _
  simp only [wordLaw, zero_mul, zero_add]
  rw [← sum_add_sum_compl A]
  congr 1
  · rw [← sum_ite_eq' A y' (fun z => P y z)]
    refine sum_congr rfl fun z hz => ?_
    rw [sum_eq_single_of_mem [] (nil_mem_words N) (fun w _ hw => by simp [hz, hw])]
    show P y z * (if z ∈ A then (if ([] : List S) = [] then (1 : ℚ) else 0) else wordLaw P A N z []) *
      (if z = y' then 1 else 0) = _
    by_cases h : z = y'
    · subst h; simp [hz]
    · simp [hz, h]
  · simp only [avoid, endKernel, mul_sum]
    refine sum_congr rfl fun z hz => sum_congr rfl fun w _ => ?_
    rw [if_neg (mem_compl.mp hz), mul_assoc]

/-- [proved-derived; formal-checked] Summing over words by their end state. -/
theorem sum_words_endState (P : S → S → ℚ) (A : Finset S) (N : ℕ) (y : S) (g : S → ℝ) :
    ∑ w ∈ words N, (wordLaw P A N y w : ℝ) * g (endState y w) =
      ∑ y', (endKernel P A N y y' : ℝ) * g y' := by
  simp only [endKernel, Rat.cast_sum, Rat.cast_mul, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_assoc, ← mul_sum]
  congr 1
  simp only [apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul,
    sum_ite_eq, mem_univ, if_true]

/-- [proved-derived; formal-checked] The truncated return kernel of a stochastic chain has rows of
total mass one. -/
theorem endKernel_mass {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N : ℕ)
    (y : S) : ∑ y', endKernel P A N y y' = 1 := by
  simp only [endKernel]
  rw [sum_comm]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  exact wordLaw_mass hrow A N y

/-- [definition] The blocks of `n` words of at most `N` letters each. -/
def blocks (N : ℕ) : ℕ → Finset (List (List S))
  | 0 => {[]}
  | n + 1 => ((words N : Finset (List S)) ×ˢ blocks N n).image fun p => p.1 :: p.2

/-- [proved-derived; formal-checked] Summing over the blocks of `n + 1` words: the first word, then
the rest. -/
theorem sum_blocks_succ {M : Type*} [AddCommMonoid M] (N n : ℕ) (f : List (List S) → M) :
    ∑ ws ∈ blocks N (n + 1), f ws = ∑ w ∈ words N, ∑ ws ∈ blocks N n, f (w :: ws) := by
  rw [blocks, sum_image, sum_product]
  intro a _ b _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

/-- [definition] **The block law of `n` successive words** from `y`, each word stopped at `N` fine
epochs: the first word has the word law from `y`, and the next word's law is the word law from the
state where the first ended, so it depends only on the returning state. Rationals. -/
def blockLaw (P : S → S → ℚ) (A : Finset S) (N : ℕ) : ℕ → S → List (List S) → ℚ
  | 0, _, ws => if ws = [] then 1 else 0
  | _ + 1, _, [] => 0
  | n + 1, y, w :: ws => wordLaw P A N y w * blockLaw P A N n (endState y w) ws

/-- [proved-derived; formal-checked] The block law of a stochastic chain is a law: total mass one. -/
theorem blockLaw_mass {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N : ℕ) :
    ∀ n y, ∑ ws ∈ blocks N n, blockLaw P A N n y ws = 1
  | 0, y => by simp [blocks, blockLaw]
  | n + 1, y => by
    rw [sum_blocks_succ]
    simp only [blockLaw, ← mul_sum, blockLaw_mass hrow A N n, mul_one]
    exact wordLaw_mass hrow A N y

/-- [definition] **The entropy of a block of `n` successive words** from `y`. -/
def blockEntropy (P : S → S → ℚ) (A : Finset S) (N n : ℕ) (y : S) : ℝ :=
  ∑ ws ∈ blocks N n, negMulLog (blockLaw P A N n y ws : ℝ)

/-- [proved-derived; formal-checked] A block of no words carries no entropy. -/
theorem blockEntropy_zero (P : S → S → ℚ) (A : Finset S) (N : ℕ) (y : S) :
    blockEntropy P A N 0 y = 0 := by
  simp [blockEntropy, blocks, blockLaw]

/-- [proved-standard; formal-checked] **The chain rule along the coarse epochs**: a block of `n + 1`
words carries the entropy of its first word plus the block entropy of the rest from the state
where the first word ended, `H(W₁, …, W_(n+1) | y) = H_N(y) + Σ_(y′) Q_N(y, y′) H(W₁, …, W_n | y′)`. -/
theorem blockEntropy_succ {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N n : ℕ)
    (y : S) :
    blockEntropy P A N (n + 1) y =
      wordEntropy P A N y + ∑ y', (endKernel P A N y y' : ℝ) * blockEntropy P A N n y' := by
  have hmass : ∀ x, ∑ ws ∈ blocks N n, (blockLaw P A N n x ws : ℝ) = 1 := fun x => by
    rw [← Rat.cast_sum, blockLaw_mass hrow A N n x, Rat.cast_one]
  rw [blockEntropy, sum_blocks_succ, ← sum_words_endState]
  simp only [blockLaw, Rat.cast_mul, negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum, hmass,
    one_mul]
  rfl

/-- [proved-standard; formal-checked] **The two-word block**:
`H(W₁, W₂ | y) = H_N(y) + Σ_(y′) Q_N(y, y′) H_N(y′)`. -/
theorem twoWord_chain_rule {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N : ℕ)
    (y : S) :
    blockEntropy P A N 2 y =
      wordEntropy P A N y + ∑ y', (endKernel P A N y y' : ℝ) * wordEntropy P A N y' := by
  rw [blockEntropy_succ hrow]
  congr 1
  refine sum_congr rfl fun y' _ => ?_
  rw [blockEntropy_succ hrow]
  simp [blockEntropy_zero]

/-- [definition] **One step of a kernel on a law**: `(ν Q)(y′) = Σ_y ν y · Q y y′`. -/
def stepLaw (Q : S → S → ℝ) (ν : S → ℝ) : S → ℝ := fun y' => ∑ y, ν y * Q y y'

/-- [proved-standard; formal-checked] **The block entropy from a law, at every truncation**: from
`ν`, a block of `n` words carries `Σ_(k<n) Σ_y (ν Q_Nᵏ)(y) H_N(y)`, the word entropy read at the law
of each coarse epoch's starting state. -/
theorem blockEntropy_eq_sum {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S) (N : ℕ) :
    ∀ (n : ℕ) (ν : S → ℝ), ∑ y, ν y * blockEntropy P A N n y =
      ∑ k ∈ range n, ∑ y, (stepLaw (realKernel (endKernel P A N)))^[k] ν y * wordEntropy P A N y
  | 0, ν => by simp [blockEntropy_zero]
  | n + 1, ν => by
    have hstep : ∑ y, ν y * ∑ y', (endKernel P A N y y' : ℝ) * blockEntropy P A N n y' =
        ∑ y', stepLaw (realKernel (endKernel P A N)) ν y' * blockEntropy P A N n y' := by
      simp only [stepLaw, realKernel, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    simp only [blockEntropy_succ hrow, mul_add, sum_add_distrib]
    rw [hstep, blockEntropy_eq_sum hrow A N n, sum_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    ring

/-- [proved-standard; formal-checked] **At every truncation, from a stationary law of the truncated
return kernel, `n` words carry `n` times the per-word entropy** `Σ_y ν y H_N(y)`. -/
theorem blockEntropy_of_stationary {P : S → S → ℚ} (hrow : ∀ x, ∑ y, P x y = 1) (A : Finset S)
    (N : ℕ) {ν : S → ℝ} (hν : Stationary (realKernel (endKernel P A N)) ν) (n : ℕ) :
    ∑ y, ν y * blockEntropy P A N n y = n * ∑ y, ν y * wordEntropy P A N y := by
  have hfix : stepLaw (realKernel (endKernel P A N)) ν = ν := funext hν
  rw [blockEntropy_eq_sum hrow, sum_congr rfl fun k _ => by rw [Function.iterate_fixed hfix k],
    sum_const, card_range, nsmul_eq_mul]

end Words

/-! ## 4. The limit `N → ∞`: the entropy rate of the word chain -/

section Rate

/-- [definition] **The entropy of the coarse epoch's word** `H(W_y)`, read as the series
`Σ_n (avoidⁿ h)(y)` of the fine entropy accumulated until the return. -/
def wordEntropyLimit (P : S → S → ℚ) (A : Finset S) (y : S) : ℝ :=
  ∑' n, (avoid (realKernel P) A)^[n] (epochEntropy P) y

/-- [proved-derived; formal-checked] **The stopped word's entropy tends to the word's entropy**:
`H_N(y) → H(W_y)`. -/
theorem wordEntropy_tendsto {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (y : S) :
    Tendsto (fun N => wordEntropy P A N y) atTop (𝓝 (wordEntropyLimit P A y)) := by
  have hc : ∀ x, |epochEntropy P x| ≤ ∑ z, |epochEntropy P z| := fun x =>
    single_le_sum (f := fun z => |epochEntropy P z|) (fun z _ => abs_nonneg _) (mem_univ x)
  have hs : Summable (fun n => (avoid (realKernel P) A)^[n] (epochEntropy P) y) :=
    Summable.of_norm_bounded ((survival_summable hP hirr hA y).mul_left (∑ z, |epochEntropy P z|))
      fun n => by rw [Real.norm_eq_abs]; exact avoid_iterate_abs_le hP.1 A n hc y
  refine hs.hasSum.tendsto_sum_nat.congr fun N => ?_
  rw [wordEntropy_eq_sum hP.2 A N, Finset.sum_apply]

/-- [proved-derived; formal-checked] **The truncated return kernel tends to the induced kernel**:
`Q_N(y, y′) → P_A(y, y′)`, with `Q_N(·, y′) − m = avoidᴺ (δ_(y′) − m)` for the first-step solution
`m` of `[y′ ∈ A] P(·, y′)`. -/
theorem endKernel_tendsto {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {A : Finset S} (hA : A.Nonempty) (y y' : S) :
    Tendsto (fun N => (endKernel P A N y y' : ℝ)) atTop (𝓝 (inducedKernel P A y y' : ℝ)) := by
  have hm := firstReturnSolution_spec hP hirr hA (fun x => if y' ∈ A then P x y' else 0)
  set m := firstReturnSolution P A (fun x => if y' ∈ A then P x y' else 0) with hmdef
  have hQ : ∀ x, inducedKernel P A x y' = m x := by
    intro x
    by_cases hy' : y' ∈ A
    · simp only [inducedKernel, if_pos hy', hmdef]
    · have hzero : FirstReturnEquations P A (fun x => if y' ∈ A then P x y' else 0) 0 := by
        intro x; simp [avoid, hy']
      rw [hmdef, firstReturnSolution_eq hP hirr hA hzero]
      simp [inducedKernel, hy']
  have hdiff : ∀ N, (fun x => endKernel P A N x y') - m =
      (avoid P A)^[N] ((fun x => if x = y' then 1 else 0) - m) := by
    intro N
    induction N with
    | zero => funext x; simp [endKernel_zero]
    | succ N ih =>
      rw [Function.iterate_succ_apply', ← ih, avoid_sub]
      funext x
      simp only [Pi.sub_apply]
      linear_combination endKernel_succ P A N x y' - hm x
  have htail := avoid_iterate_tendsto_zero hP hirr hA
    (fun x => ((((fun x => if x = y' then (1 : ℚ) else 0) - m) x : ℚ) : ℝ)) y
  simp only [avoid_realKernel_iterate_cast] at htail
  have := (tendsto_const_nhds (x := (m y : ℝ))).add htail
  rw [add_zero, ← hQ y] at this
  refine this.congr fun N => ?_
  have h := congrFun (hdiff N) y
  simp only [Pi.sub_apply] at h
  rw [← h, hQ y]
  push_cast
  ring

omit [DecidableEq S] in
/-- [proved-derived; formal-checked] **The laws of the starting states converge**: when each
`Q_N(y, y′) → Q(y, y′)`, the `k`-th step of any law converges, `ν Q_Nᵏ → ν Qᵏ`. -/
theorem stepLaw_iterate_tendsto {Q : ℕ → S → S → ℝ} {Q' : S → S → ℝ}
    (hQ : ∀ y y', Tendsto (fun N => Q N y y') atTop (𝓝 (Q' y y'))) (ν : S → ℝ) (k : ℕ) (y' : S) :
    Tendsto (fun N => (stepLaw (Q N))^[k] ν y') atTop (𝓝 ((stepLaw Q')^[k] ν y')) := by
  induction k generalizing y' with
  | zero => exact tendsto_const_nhds
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact tendsto_finsetSum _ fun y _ => (ih y).mul (hQ y y')

/-- [proved-derived; formal-checked] The section's normalized law reads an observable as the
owner's information rate of the section's weights. -/
theorem sectionLaw_sum_eq (π : S → ℚ) (A : Finset S) (g : S → ℝ) :
    ∑ y, (sectionLaw π A y : ℝ) * g y = informationRate (sectionWeight π A) g := by
  have hmass : totalMass (sectionWeight π A) = ((∑ x ∈ A, π x : ℚ) : ℝ) := by
    simp only [totalMass, sectionWeight]
    rw [sum_ite_mem, univ_inter, Rat.cast_sum]
  rw [informationRate, hmass, totalInformation, sum_div]
  refine sum_congr rfl fun y _ => ?_
  simp only [sectionLaw, sectionWeight]
  split_ifs <;> push_cast <;> ring

/-- [proved-standard; formal-checked] **The per-word entropy is Abramov's ratio**:
`Σ_(y∈A) π_A(y) H(W_y) = Σ_y π y h(y) / π(A)`, the limit of the owner's ledger. -/
theorem sectionLaw_wordEntropyLimit {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {π : S → ℚ} (hπ : Stationary P π) {A : Finset S} (hA : ∑ x ∈ A, π x ≠ 0) :
    ∑ y, (sectionLaw π A y : ℝ) * wordEntropyLimit P A y =
      totalInformation (fun y => (π y : ℝ)) (epochEntropy P) / totalMass (sectionWeight π A) := by
  have hAne : A.Nonempty := nonempty_of_sum_ne_zero hA
  have h1 : Tendsto (fun N => ∑ y, (sectionLaw π A y : ℝ) * wordEntropy P A N y) atTop
      (𝓝 (∑ y, (sectionLaw π A y : ℝ) * wordEntropyLimit P A y)) :=
    tendsto_finsetSum _ fun y _ => (wordEntropy_tendsto hP hirr hAne y).const_mul _
  have htail : Tendsto
      (fun N => ∑ y, (π y : ℝ) * (avoid (realKernel P) A)^[N] (epochEntropy P) y) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ fun y _ =>
      (avoid_iterate_tendsto_zero hP hirr hAne (epochEntropy P) y).const_mul (π y : ℝ)
  have h2 : Tendsto (fun N => ∑ y, (sectionLaw π A y : ℝ) * wordEntropy P A N y) atTop
      (𝓝 (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) /
        totalMass (sectionWeight π A))) := by
    have hrate : ∀ N, ∑ y, (sectionLaw π A y : ℝ) * wordEntropy P A N y =
        (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) -
          ∑ y, (π y : ℝ) * (avoid (realKernel P) A)^[N] (epochEntropy P) y) /
            totalMass (sectionWeight π A) := fun N => by
      rw [sectionLaw_sum_eq, informationRate, abramov_ledger hP.2 hπ A N]
    simp_rw [hrate]
    simpa using (tendsto_const_nhds.sub htail).div_const (totalMass (sectionWeight π A))
  exact tendsto_nhds_unique h1 h2

/-- [proved-standard; formal-checked] **The block entropy of `n` words from the section's law tends
to `n` times the per-word entropy**: `Σ_y π_A(y) H(W₁, …, W_n | y) → n · Σ_(y∈A) π_A(y) H(W_y)`,
because `π_A` is stationary for the induced chain that the truncated return kernels approach. -/
theorem wordChain_blockEntropy_tendsto {P : S → S → ℚ} (hP : Stochastic P)
    (hirr : Kac.Irreducible P) {π : S → ℚ} (hπ : Stationary P π) {A : Finset S}
    (hA : ∑ x ∈ A, π x ≠ 0) (n : ℕ) :
    Tendsto (fun N => ∑ y, (sectionLaw π A y : ℝ) * blockEntropy P A N n y) atTop
      (𝓝 (n * ∑ y, (sectionLaw π A y : ℝ) * wordEntropyLimit P A y)) := by
  have hAne : A.Nonempty := nonempty_of_sum_ne_zero hA
  have hfix : stepLaw (realKernel (inducedKernel P A)) (fun y => (sectionLaw π A y : ℝ)) =
      fun y => (sectionLaw π A y : ℝ) := by
    funext y'
    have := congrArg (fun q : ℚ => (q : ℝ)) (sectionLaw_stationary hP hirr hAne hπ y')
    simpa [stepLaw, realKernel] using this
  have hlim := tendsto_finsetSum (range n) fun k _ => tendsto_finsetSum univ fun y _ =>
    (stepLaw_iterate_tendsto (Q := fun N => realKernel (endKernel P A N))
      (Q' := realKernel (inducedKernel P A)) (fun y y' => endKernel_tendsto hP hirr hAne y y')
      (fun y => (sectionLaw π A y : ℝ)) k y).mul (wordEntropy_tendsto hP hirr hAne y)
  simp only [Function.iterate_fixed hfix, sum_const, card_range, nsmul_eq_mul] at hlim
  refine hlim.congr fun N => ?_
  rw [blockEntropy_eq_sum hP.2]

/-- [proved-standard; formal-checked] **Abramov for the word chain**: the block entropy of `n` words
from the section's law tends to `n · Σ_y π y h(y) / π(A)`; with `Σ π = 1`, `n · h(T)/μ(A)`. -/
theorem wordChain_abramov {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {π : S → ℚ} (hπ : Stationary P π) {A : Finset S} (hA : ∑ x ∈ A, π x ≠ 0) (n : ℕ) :
    Tendsto (fun N => ∑ y, (sectionLaw π A y : ℝ) * blockEntropy P A N n y) atTop
      (𝓝 (n * (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) /
        totalMass (sectionWeight π A)))) := by
  rw [← sectionLaw_wordEntropyLimit hP hirr hπ hA]
  exact wordChain_blockEntropy_tendsto hP hirr hπ hA n

/-- [proved-standard; formal-checked] **The entropy rate of the word chain, per word**: for `n ≥ 1`
words, `(1/n) Σ_y π_A(y) H(W₁, …, W_n | y) → Σ_y π y h(y) / π(A)`. -/
theorem wordChain_entropyRate {P : S → S → ℚ} (hP : Stochastic P) (hirr : Kac.Irreducible P)
    {π : S → ℚ} (hπ : Stationary P π) {A : Finset S} (hA : ∑ x ∈ A, π x ≠ 0) {n : ℕ}
    (hn : 0 < n) :
    Tendsto (fun N => (∑ y, (sectionLaw π A y : ℝ) * blockEntropy P A N n y) / n) atTop
      (𝓝 (totalInformation (fun y => (π y : ℝ)) (epochEntropy P) /
        totalMass (sectionWeight π A))) := by
  have h := (wordChain_abramov hP hirr hπ hA n).div_const (n : ℝ)
  rwa [mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)] at h

end Rate

/-! ## 5. A witness: three states and a section of two -/

namespace Witness

open Matrix (cons_val_two tail_cons head_cons)

/-- [definition] The chain on three states: `0` steps to `0` or `1` with `1/2` each, `1` steps to
`2`, and `2` steps to `0`. -/
def loop : Fin 3 → Fin 3 → ℚ := ![![1 / 2, 1 / 2, 0], ![0, 0, 1], ![1, 0, 0]]

/-- [definition] The section `{0, 1}`. -/
def sec : Finset (Fin 3) := {0, 1}

/-- [definition] The stationary law `(1/2, 1/4, 1/4)`. -/
def law : Fin 3 → ℚ := ![1 / 2, 1 / 4, 1 / 4]

/-- [proved-derived; formal-checked] The witness is stochastic. -/
theorem loop_stochastic : Stochastic loop := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · fin_cases x <;> fin_cases y <;> norm_num [loop, cons_val_two, tail_cons, head_cons]
  · fin_cases x <;> norm_num [loop, Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

/-- [proved-derived; formal-checked] The witness is irreducible: `0 → 1 → 2 → 0`. -/
theorem loop_irreducible : Kac.Irreducible loop := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < loop a b) 0 1 :=
    .single (by norm_num [loop, cons_val_two, tail_cons, head_cons])
  have h12 : Relation.ReflTransGen (fun a b => 0 < loop a b) 1 2 :=
    .single (by norm_num [loop, cons_val_two, tail_cons, head_cons])
  have h20 : Relation.ReflTransGen (fun a b => 0 < loop a b) 2 0 :=
    .single (by norm_num [loop, cons_val_two, tail_cons, head_cons])
  intro x y
  fin_cases x <;> fin_cases y
  exacts [.refl, h01, h01.trans h12, h12.trans h20, .refl, h12, h20, h20.trans h01, .refl]

/-- [proved-derived; formal-checked] `(1/2, 1/4, 1/4)` is stationary for the witness. -/
theorem law_stationary : Stationary loop law := by
  intro y; fin_cases y <;> norm_num [loop, law, Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

/-- [proved-derived; formal-checked] The complement of the section is `{2}`. -/
theorem sec_compl : secᶜ = {2} := by decide

/-- [proved-derived; formal-checked] The section is nonempty. -/
theorem sec_nonempty : sec.Nonempty := ⟨0, by decide⟩

/-- [proved-derived; formal-checked] **The induced kernel of the witness**: on the section `{0, 1}`
the first return from `0` lands on `0` or `1` with `1/2` each, and from `1` (through `2`) and from
`2` it lands on `0`. -/
theorem loop_inducedKernel :
    inducedKernel loop sec = ![![1 / 2, 1 / 2, 0], ![1, 0, 0], ![1, 0, 0]] := by
  have col0 : FirstReturnEquations loop sec (fun x => loop x 0) ![1 / 2, 1, 1] := by
    intro y; fin_cases y <;> norm_num [avoid, sec_compl, loop, cons_val_two, tail_cons, head_cons]
  have col1 : FirstReturnEquations loop sec (fun x => loop x 1) ![1 / 2, 0, 0] := by
    intro y; fin_cases y <;> norm_num [avoid, sec_compl, loop, cons_val_two, tail_cons, head_cons]
  have e0 := firstReturnSolution_eq loop_stochastic loop_irreducible sec_nonempty col0
  have e1 := firstReturnSolution_eq loop_stochastic loop_irreducible sec_nonempty col1
  have k0 : ∀ y, inducedKernel loop sec y 0 = ![1 / 2, 1, 1] y := fun y => by
    simp only [inducedKernel]; rw [if_pos (by decide), e0]
  have k1 : ∀ y, inducedKernel loop sec y 1 = ![1 / 2, 0, 0] y := fun y => by
    simp only [inducedKernel]; rw [if_pos (by decide), e1]
  have k2 : ∀ y, inducedKernel loop sec y 2 = 0 := fun y => by
    simp only [inducedKernel]; rw [if_neg (by decide)]
  funext y y'
  fin_cases y' <;> fin_cases y <;> simp [k0, k1, k2]

/-- [proved-derived; formal-checked] The section's normalized law of the witness is `(2/3, 1/3)`
on `{0, 1}`, stationary for the induced kernel `[[1/2, 1/2], [1, 0]]`. -/
theorem loop_sectionLaw : sectionLaw law sec = ![2 / 3, 1 / 3, 0] ∧
    Stationary (inducedKernel loop sec) (sectionLaw law sec) := by
  refine ⟨?_, sectionLaw_stationary loop_stochastic loop_irreducible sec_nonempty law_stationary⟩
  funext y
  fin_cases y <;> simp [sectionLaw, sec, law, cons_val_two, tail_cons, head_cons] <;> norm_num

/-- [proved-derived; formal-checked] **The witness's word chain**: from the section's law, `n`
words carry, as the truncation is lifted, `n · (2/3) log 2`: the fine rate `(1/2) log 2` over the
section's measure `3/4`. The words from `0` are `[0]` and `[1]`, and from `1` the word is `[2, 0]`. -/
theorem loop_wordChain (n : ℕ) :
    Tendsto (fun N => ∑ y, (sectionLaw law sec y : ℝ) * blockEntropy loop sec N n y) atTop
      (𝓝 (n * (2 / 3 * Real.log 2))) := by
  have hs : ∑ x ∈ sec, law x = 3 / 4 := by
    rw [sec, sum_pair (by decide)]; norm_num [law]
  have h := wordChain_abramov loop_stochastic loop_irreducible law_stationary
    (by rw [hs]; norm_num) n
  have hinfo : totalInformation (fun y => (law y : ℝ)) (epochEntropy loop) = 1 / 2 * Real.log 2 := by
    simp only [totalInformation, epochEntropy, Fin.sum_univ_three]
    norm_num [loop, law, Real.negMulLog, Real.log_inv, cons_val_two, tail_cons, head_cons]
    rw [one_div, Real.log_inv]
    ring
  have hmass : totalMass (sectionWeight law sec) = 3 / 4 := by
    simp only [totalMass, sectionWeight, Fin.sum_univ_three]
    norm_num [sec, law, cons_val_two, tail_cons, head_cons]
    decide
  rw [hinfo, hmass] at h
  convert h using 2
  ring

end Witness

end Holonics.Aeon.Production.InducedWords
