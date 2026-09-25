import Holonics.Physics.AccumulatedNormalResponse
import Holonics.Objects.Deposition
import Holonics.Holon.Deposition
import Holonics.Holon.MomentStorage
import Holonics.Transport.SourceMoment

/-!
# HNN.Normal: the normal constitution and its deposition, per locus

[definition] Item 4 of the step 4 design (`docs/plans/THE_REBUILD.md`, "The laws stated in Lean
first"). Every learned map of the HNN is one **locus** `U` with its own normal law `W_U H_U = B_U`
and its own statistics; there is no global Gram. A deposit reads, at the ticks of the locus's
diamond window, a weight `w`, a feature `f_t` and a covector `g_t`:

```text
H_U ← H_U + Σ_t w f_t f_tᵀ ,   B_U ← B_U + Σ_t w (W_U f_t + γ_U g_t) f_tᵀ ,   W_U H_U = B_U
x ← x + η_x G_x / h_x                                   factor families (c_a, b_a, F_a, …)
q_r ← q_r + η_q Lᵀ g_σ / h_q                           the standing, through the lock chart
```

Everything is realified and exact: statements are over a general field (so over `ℚ`), with
transposes. The complex chart of the same identities is the owner
`Physics/AccumulatedNormalResponse`, joined in §2 and §3.

[proved-derived; formal-checked] What is proved.

1. **The statistic is the standing of the samples** (`normalStatistic_standing`). The objective
   `J(W) = Σ_t w_t |W f_t − y_t|²` is `tr(W H Wᵀ) − 2 tr(W Bᵀ) + C_data` with
   `(H, B, C_data) = Σ_t w_t (f_t f_tᵀ, y_t f_tᵀ, |y_t|²)` (`objective_eq_statisticObjective`),
   after every further sample word. `normalStanding` is the `Foundation/Standing.StandingLaw`
   whose sources are sample lists and whose `retain` is the statistic: it keeps the statistic,
   never the sample list. Witness: `[(1,1),(1,1)]` and `[(1,1),(−1,−1)]` are distinct lists with
   one statistic (`statistic_forgets_the_samples`).
2. **The prox step** (`normal_prox_step`). With `W H = B`, `H' = H + w f fᵀ`,
   `B' = B + w (W f + γ g) fᵀ` and `H'` invertible, `W' H' = B'` holds exactly when
   `W' = W + w γ g fᵀ H'⁻¹`. The complex chart composes the owner's
   `normalResidual_preserved_of_gain_receipt` with `normalProxyTarget_residual_eq_scaled_covector`
   (`normal_prox_step_complex`). The solved state `W H = B` and the invertible Gram are
   load-bearing (`normal_prox_step_needs_the_solve`, `normal_prox_step_needs_invertible_gram`).
3. **Deposition is per locus** (`deposit_local`). A locus with an empty diamond window keeps its
   map and statistics; a locus whose covectors all vanish keeps its map while its Gram grows; each
   locus reads only its own window; a Gram entry `(i, j)` moves only where some window feature is
   nonzero at both `i` and `j`. The solved state is carried by a deposit (`depositLocus_solves`).
   The complex chart iterates the owner's `normal_law_local` (`deposit_local_complex`). A nonempty
   window with a nonzero covector moves the map (`nonempty_window_moves_the_map`).
4. **Reaction deposits do no deposition work** (`reaction_deposit_storage_unchanged`): a deposit
   that changes only the reaction material leaves the storage `Q`, so the owner's `commit_balance`
   loses its work term and is the word balance; with passive words the owner's
   `committed_energy_bound` at `ε = 0` gives `E_N ≤ E_0`
   (`reaction_deposits_keep_committed_energy`). Both hypotheses are load-bearing: a storage change
   does work (`storage_deposit_does_work`), and an active learned block diverges at fixed storage
   (the owner's `normal_law_divergence_witness`, restated as `active_reaction_diverges`).
5. **Factor carriers stay PSD with no clamp** (`factorCarrier_psd`). `C = c cᵀ`, `K = b bᵀ` and
   `D = F Fᵀ` are unit-weight quadratic moments of their factor columns, so the owner's
   `storageEnergy_quadraticMoment_nonneg` keeps them PSD under every factor update. An additive
   update of `C` itself does not (`additive_carrier_update_leaves_psd`).
6. **The standing moves only through its lock chart** (`standing_deposit`). The sheet classes are
   `σ_ρ(q) = sign(Δ_ρ)` with `sign 0 = +1` and `Δ = L q`; the element operator
   `K(q) = W_s + Σ_ρ σ_ρ(q) A_ρ` reads `q` only through them
   (`elementOperator_eq_of_sheetClass_eq`), and off the fold they are locally constant
   (`sheetClass_locally_constant`), so the word's derivative in `q` is zero there. The declared
   chart carries the class covector to `q` by `Lᵀ`, the step moves the contrast along it, and a class
   changes exactly where the deposit carries `Δ_ρ` across zero. At the fold the class jumps under
   arbitrarily small deposits (`sheet_fold_witness`); a negative step moves the contrast against
   the covector (`standing_step_sign_witness`).

[definition; agent-inferred] **What runs is the carried law** (Decision 22 of the step 4 design).
The laws here are exact, and a map that is an operand of its own covector grows in bits under them.
The deposit is carried on a declared lattice in `HNN/LatticeDeposit`: the entries' bits are bounded
by their magnitudes (`lattice_bits_bounded`), the carried remainders' by the locus's deposit clock
(`remainder_rat_bits_bounded`, `O(L + 2 log₂ m)`), and each deposit releases only the tail below
its clock's precision (`release_bounded_since_founding`). `B` is not carried and `H` is, so the
running map is the prox step at the carried Gram (`normal_prox_step`), and the statistic of §1 is
the exact accumulation every carried value stays within one lattice unit of
(`within_one_unit_since_founding`), not the carried state itself.

[open] Owed in #62 ("Step 4 (#73) owed"): the bits of the solved charts `H⁻¹`, which follow the
Hadamard bound of the carried Grams, and the word-level certificate of the lattice rule.
-/

noncomputable section

namespace Holonics.HNN.Normal

open Matrix
open Holonics
open Holonics.HolonCore
open Holonics.Foundation.Chronology
open Holonics.Foundation.Standing
open Holonics.Transport.SourceMoment

/-! ## 1. The normal statistic is the standing of the samples -/

section Statistic

variable {𝕜 : Type*} [Field 𝕜] {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- [definition] One observed return at a locus: its weight, feature and target. -/
structure Sample (𝕜 σ τ : Type*) where
  weight : 𝕜
  feature : σ → 𝕜
  target : τ → 𝕜

/-- [definition] The locus objective `J(W) = Σ_t w_t |W f_t − y_t|²`. -/
def objective (l : List (Sample 𝕜 σ τ)) (W : Matrix τ σ 𝕜) : 𝕜 :=
  (l.map fun s => s.weight * ((W *ᵥ s.feature - s.target) ⬝ᵥ (W *ᵥ s.feature - s.target))).sum

/-- [definition] The normal statistic `(H, B, C_data)`. -/
abbrev Statistic (𝕜 σ τ : Type*) := Matrix σ σ 𝕜 × Matrix τ σ 𝕜 × 𝕜

/-- [definition] The statistic of one sample: `w (f fᵀ, y fᵀ, |y|²)`. -/
def sampleStatistic (s : Sample 𝕜 σ τ) : Statistic 𝕜 σ τ :=
  (s.weight • vecMulVec s.feature s.feature, s.weight • vecMulVec s.target s.feature,
    s.weight * (s.target ⬝ᵥ s.target))

/-- [definition] The statistic of a sample list. -/
def statistic (l : List (Sample 𝕜 σ τ)) : Statistic 𝕜 σ τ := (l.map sampleStatistic).sum

/-- [definition] The objective read from a statistic: `tr(W H Wᵀ) − 2 tr(W Bᵀ) + C_data`. -/
def statisticObjective (S : Statistic 𝕜 σ τ) (W : Matrix τ σ 𝕜) : 𝕜 :=
  (W * S.1 * Wᵀ).trace - 2 * (W * S.2.1ᵀ).trace + S.2.2

theorem statisticObjective_add (S T : Statistic 𝕜 σ τ) (W : Matrix τ σ 𝕜) :
    statisticObjective (S + T) W = statisticObjective S W + statisticObjective T W := by
  simp only [statisticObjective, Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.transpose_add, Matrix.trace_add]
  ring

theorem statisticObjective_zero (W : Matrix τ σ 𝕜) : statisticObjective 0 W = 0 := by
  simp [statisticObjective]

/-- [proved-derived; formal-checked] One sample's objective is read from its statistic. -/
theorem statisticObjective_sample (s : Sample 𝕜 σ τ) (W : Matrix τ σ 𝕜) :
    statisticObjective (sampleStatistic s) W =
      s.weight * ((W *ᵥ s.feature - s.target) ⬝ᵥ (W *ᵥ s.feature - s.target)) := by
  simp only [statisticObjective, sampleStatistic, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.transpose_smul, transpose_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    trace_vecMulVec, vecMul_transpose, smul_eq_mul, sub_dotProduct, dotProduct_sub,
    dotProduct_comm s.target (W *ᵥ s.feature)]
  ring

/-- [proved-derived; formal-checked] **The objective factors through the statistic.** -/
theorem objective_eq_statisticObjective (l : List (Sample 𝕜 σ τ)) (W : Matrix τ σ 𝕜) :
    objective l W = statisticObjective (statistic l) W := by
  induction l with
  | nil => simp [objective, statistic, statisticObjective_zero]
  | cons s l ih =>
      simp only [objective, statistic, List.map_cons, List.sum_cons] at ih ⊢
      rw [statisticObjective_add, statisticObjective_sample, ih]

/-- [definition] The induced generator on the statistic: add the sample's statistic. -/
def statisticStep (s : Sample 𝕜 σ τ) (S : Statistic 𝕜 σ τ) : Statistic 𝕜 σ τ :=
  S + sampleStatistic s

omit [Fintype σ] in
theorem statistic_append_one (l : List (Sample 𝕜 σ τ)) (s : Sample 𝕜 σ τ) :
    statistic (appendLetter s l) = statisticStep s (statistic l) := by
  simp [appendLetter, statistic, statisticStep]

/-- [definition] **The normal standing of one locus.** Sources are sample lists, generators
append a sample, receivers are maps `W`, the observation is the objective, and the retention is
the statistic `(H, B, C_data)`; the reopening runs the induced generator on the statistic. -/
def normalStanding :
    StandingLaw (Sample 𝕜 σ τ) (Matrix τ σ 𝕜) (List (Sample 𝕜 σ τ)) (Statistic 𝕜 σ τ) 𝕜 where
  transport := appendLetter
  observe W l := objective l W
  retain := statistic
  reopen W word S := statisticObjective (transportWord statisticStep word S) W
  sufficient W word l := by
    rw [objective_eq_statisticObjective,
      generatorEquivarianceExtendsToEveryTransportWord appendLetter statisticStep statistic
        (fun s l => statistic_append_one l s) word l]

/-- [proved-derived; formal-checked] **The objective factors through `(H, B, C_data)` after every
further sample word** (`normalStanding.sufficient`), and two sample lists with one statistic agree
on every objective after every word: the statistic is a lawful standing, and the sample list is not
kept. -/
theorem normalStatistic_standing (l : List (Sample 𝕜 σ τ)) (W : Matrix τ σ 𝕜)
    (word : List (Sample 𝕜 σ τ)) :
    objective l W = statisticObjective (statistic l) W ∧
      objective (transportWord appendLetter word l) W =
        statisticObjective (transportWord statisticStep word (statistic l)) W ∧
      ∀ l' : List (Sample 𝕜 σ τ), statistic l = statistic l' →
        objective (transportWord appendLetter word l) W =
          objective (transportWord appendLetter word l') W :=
  ⟨objective_eq_statisticObjective l W, (normalStanding.sufficient W word l).symm,
    fun _ h => normalStanding.futureAgreement_of_retain_eq h W word⟩

/-- The two witness samples on `ℚ¹`. -/
def plusSample : Sample ℚ (Fin 1) (Fin 1) := ⟨1, ![1], ![1]⟩
def minusSample : Sample ℚ (Fin 1) (Fin 1) := ⟨1, ![-1], ![-1]⟩

/-- [counterexample; formal-checked] **The statistic forgets the samples.** `[(1,1),(1,1)]` and
`[(1,1),(−1,−1)]` are different sample lists with one statistic, so the standing keeps no sample
list. -/
theorem statistic_forgets_the_samples :
    [plusSample, plusSample] ≠ [plusSample, minusSample] ∧
      statistic [plusSample, plusSample] = statistic [plusSample, minusSample] := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrArg (fun l => (l.getD 1 plusSample).feature 0) h
    norm_num [plusSample, minusSample] at this
  · simp only [statistic, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      sampleStatistic, plusSample, minusSample]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
    · ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
    · simp [dotProduct]

end Statistic

/-! ## 2. The prox step of the normal law -/

section Prox

variable {𝕜 : Type*} [Field 𝕜] {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ]

omit [DecidableEq σ] [Fintype τ] in
theorem proxCross_eq (W : Matrix τ σ 𝕜) (w γ : 𝕜) (f : σ → 𝕜) (g : τ → 𝕜) :
    w • vecMulVec (W *ᵥ f + γ • g) f = W * (w • vecMulVec f f) + (w * γ) • vecMulVec g f := by
  ext i j
  simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.add_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mul_smul, mul_vecMulVec]
  ring

omit [Fintype τ] in
/-- [proved-derived; formal-checked] **The prox step.** At a solved locus `W H = B`, after one
return with weight `w`, feature `f` and covector `g`, `H' = H + w f fᵀ` and
`B' = B + w (W f + γ g) fᵀ`; when `H'` is invertible the solve `W' H' = B'` holds exactly when
`W' = W + w γ g fᵀ H'⁻¹`. -/
theorem normal_prox_step {W : Matrix τ σ 𝕜} {H : Matrix σ σ 𝕜} {B : Matrix τ σ 𝕜}
    (hsolve : W * H = B) (w γ : 𝕜) (f : σ → 𝕜) (g : τ → 𝕜)
    (hunit : IsUnit (H + w • vecMulVec f f).det) (W' : Matrix τ σ 𝕜) :
    W' * (H + w • vecMulVec f f) = B + w • vecMulVec (W *ᵥ f + γ • g) f ↔
      W' = W + (w * γ) • vecMulVec g f * (H + w • vecMulVec f f)⁻¹ := by
  have hcross : B + w • vecMulVec (W *ᵥ f + γ • g) f =
      W * (H + w • vecMulVec f f) + (w * γ) • vecMulVec g f := by
    rw [proxCross_eq W w γ f g, ← hsolve, Matrix.mul_add]
    abel
  rw [hcross]
  constructor
  · intro h
    calc W' = W' * (H + w • vecMulVec f f) * (H + w • vecMulVec f f)⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right _ _ hunit).symm
      _ = _ := by
          rw [h, Matrix.add_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hunit]
  · intro h
    rw [h, Matrix.add_mul, Matrix.mul_assoc ((w * γ) • vecMulVec g f),
      Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

/-- [counterexample; formal-checked] **The solved state is load-bearing.** On `ℚ¹` with `H = 1`,
`B = 1` and `W = 0` (so `W H ≠ B`), a zero return (`f = 0`) leaves `H' = 1`, `B' = 1`; the solve
is `W' = 1`, while the prox formula returns `W = 0`. -/
theorem normal_prox_step_needs_the_solve :
    (0 : Matrix (Fin 1) (Fin 1) ℚ) * 1 ≠ 1 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℚ) * (1 + (1 : ℚ) • vecMulVec 0 0) =
        1 + (1 : ℚ) • vecMulVec ((0 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ 0 + (1 : ℚ) • 0) 0 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℚ) ≠
        0 + ((1 : ℚ) * 1) • vecMulVec (0 : Fin 1 → ℚ) 0 * (1 + (1 : ℚ) • vecMulVec 0 0)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congrFun (congrFun h 0) 0; simp at this
  · ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
  · intro h; have := congrFun (congrFun h 0) 0; simp [vecMulVec] at this

/-- [counterexample; formal-checked] **The invertible Gram is load-bearing.** On `ℚ¹` with
`H = 0`, `B = 0`, `W = 0` and a zero return, `H' = 0`: `W' = 1` solves `W' H' = B'` while the prox
formula returns `0`, so the solve does not determine the map. -/
theorem normal_prox_step_needs_invertible_gram :
    (1 : Matrix (Fin 1) (Fin 1) ℚ) * (0 + (1 : ℚ) • vecMulVec 0 0) =
        0 + (1 : ℚ) • vecMulVec ((0 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ 0 + (1 : ℚ) • 0) 0 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℚ) ≠
        0 + ((1 : ℚ) * 1) • vecMulVec (0 : Fin 1 → ℚ) 0 * (0 + (1 : ℚ) • vecMulVec 0 0)⁻¹ := by
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
  · intro h; have := congrFun (congrFun h 0) 0; simp [vecMulVec] at this

open Holonics.Physics.AccumulatedNormalResponse in
/-- [proved-derived; formal-checked] **The complex chart of the prox step**, composing the owner:
at a solved locus `W H = B`, a gain receipt `gainᴴ H' = fᴴ` (`H' = H + f fᴴ`) and the proxy target
`W f + σ g` give `(W + σ g gainᴴ) H' = B + (W f + σ g) fᴴ` exactly
(`normalResidual_preserved_of_gain_receipt`, `normalProxyTarget_residual_eq_scaled_covector`,
`normalProxyCross_eq_updatedCross`). -/
theorem normal_prox_step_complex {Source Target : Type*} [Fintype Source] [Fintype Target]
    (W : Matrix Target Source ℂ) (H : Matrix Source Source ℂ) (B : Matrix Target Source ℂ)
    (hsolve : W * H = B) (f : Column Source) (sigma : ℝ) (g : Column Target)
    (gain : Column Source) (hgain : gain.conjTranspose * updatedGram H f = f.conjTranspose) :
    (W + (sigma • g) * gain.conjTranspose) * updatedGram H f = normalProxyCross B W f sigma g := by
  have h := normalResidual_preserved_of_gain_receipt W H B f (normalProxyTarget W f sigma g) gain 0
    hgain rfl
  have hzero : normalResidual W H B = 0 := by rw [normalResidual, hsolve, sub_self]
  rw [hzero] at h
  unfold normalResidual updatedResponse at h
  rw [normalProxyTarget_residual_eq_scaled_covector, add_zero,
    ← normalProxyCross_eq_updatedCross, sub_eq_zero] at h
  exact h

end Prox

/-! ## 3. Deposition acts per locus, inside its diamond window -/

section Local

variable {𝕜 : Type*} [Field 𝕜] {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ]

/-- [definition] The state of one linear locus: its map `W` and its statistics `(H, B)`. -/
structure LocusState (𝕜 σ τ : Type*) where
  map : Matrix τ σ 𝕜
  gram : Matrix σ σ 𝕜
  cross : Matrix τ σ 𝕜

/-- [definition] A locus's window data: `(w, f_t, g_t)` at each tick of its diamond window. -/
abbrev Window (𝕜 σ τ : Type*) := List (𝕜 × (σ → 𝕜) × (τ → 𝕜))

/-- [definition] The window Gram `Σ_t w f_t f_tᵀ`. -/
def windowGram (data : Window 𝕜 σ τ) : Matrix σ σ 𝕜 :=
  (data.map fun d => d.1 • vecMulVec d.2.1 d.2.1).sum

/-- [definition] The window covector `Σ_t w g_t f_tᵀ`. -/
def windowCovector (data : Window 𝕜 σ τ) : Matrix τ σ 𝕜 :=
  (data.map fun d => d.1 • vecMulVec d.2.2 d.2.1).sum

/-- [definition] **The deposit of one locus** with proxy step `γ`: the statistics sum over the
window only, and the map is the prox solve `W + γ (Σ w g fᵀ) H'⁻¹`. -/
def depositLocus (γ : 𝕜) (θ : LocusState 𝕜 σ τ) (data : Window 𝕜 σ τ) : LocusState 𝕜 σ τ where
  map := θ.map + γ • windowCovector data * (θ.gram + windowGram data)⁻¹
  gram := θ.gram + windowGram data
  cross := θ.cross + (data.map fun d => d.1 • vecMulVec (θ.map *ᵥ d.2.1 + γ • d.2.2) d.2.1).sum

omit [DecidableEq σ] [Fintype τ] in
theorem window_cross_eq (W : Matrix τ σ 𝕜) (γ : 𝕜) (data : Window 𝕜 σ τ) :
    (data.map fun d => d.1 • vecMulVec (W *ᵥ d.2.1 + γ • d.2.2) d.2.1).sum =
      W * windowGram data + γ • windowCovector data := by
  induction data with
  | nil => simp [windowGram, windowCovector]
  | cons d data ih =>
      simp only [windowGram, windowCovector, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, Matrix.mul_add, smul_add]
      have : d.1 • vecMulVec (W *ᵥ d.2.1 + γ • d.2.2) d.2.1 =
          W * (d.1 • vecMulVec d.2.1 d.2.1) + γ • (d.1 • vecMulVec d.2.2 d.2.1) := by
        ext i j
        simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.add_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.mul_smul, mul_vecMulVec]
        ring
      rw [this]; abel

omit [Fintype τ] in
/-- [proved-derived; formal-checked] **A deposit carries the solved state.** If `W H = B` and the
new Gram is invertible, the deposited locus is solved again. -/
theorem depositLocus_solves (γ : 𝕜) (θ : LocusState 𝕜 σ τ) (data : Window 𝕜 σ τ)
    (hsolve : θ.map * θ.gram = θ.cross) (hunit : IsUnit (θ.gram + windowGram data).det) :
    (depositLocus γ θ data).map * (depositLocus γ θ data).gram = (depositLocus γ θ data).cross := by
  simp only [depositLocus]
  rw [window_cross_eq, Matrix.add_mul, Matrix.mul_assoc (γ • windowCovector data),
    Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one, ← hsolve, Matrix.mul_add]
  abel

omit [DecidableEq σ] [Fintype σ] [Fintype τ] in
theorem windowCovector_eq_zero (data : Window 𝕜 σ τ) (h : ∀ d ∈ data, d.2.2 = 0) :
    windowCovector data = 0 := by
  induction data with
  | nil => simp [windowCovector]
  | cons d data ih =>
      simp only [windowCovector, List.map_cons, List.sum_cons] at ih ⊢
      rw [h d (List.mem_cons_self), ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
      simp

omit [DecidableEq σ] [Fintype σ] [Fintype τ] in
theorem windowGram_apply_eq_zero (data : Window 𝕜 σ τ) (i j : σ)
    (h : ∀ d ∈ data, d.2.1 i = 0 ∨ d.2.1 j = 0) : windowGram data i j = 0 := by
  induction data with
  | nil => simp [windowGram]
  | cons d data ih =>
      simp only [windowGram, List.map_cons, List.sum_cons] at ih ⊢
      rw [Matrix.add_apply, ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
      rcases h d List.mem_cons_self with hd | hd <;> simp [vecMulVec, hd]

/-- [proved-derived; formal-checked] **Deposition is per locus.** For a family of loci, each with
its own feature and target widths, the deposit at locus `ℓ`:
* reads only `ℓ`'s own state and window (two families agreeing there deposit identically there);
* leaves `ℓ` unchanged when its diamond window is empty;
* keeps `ℓ`'s map when no covector reached it, although its Gram grows by the window's features;
* moves a Gram entry `(i, j)` only where some window feature is nonzero at both `i` and `j`. -/
theorem deposit_local {Locus : Type*} {σ' τ' : Locus → Type*} [∀ ℓ, Fintype (σ' ℓ)]
    [∀ ℓ, Fintype (τ' ℓ)] [∀ ℓ, DecidableEq (σ' ℓ)] (γ : Locus → 𝕜)
    (Θ Θ' : ∀ ℓ, LocusState 𝕜 (σ' ℓ) (τ' ℓ)) (data data' : ∀ ℓ, Window 𝕜 (σ' ℓ) (τ' ℓ))
    (ℓ : Locus) :
    (Θ ℓ = Θ' ℓ → data ℓ = data' ℓ →
      depositLocus (γ ℓ) (Θ ℓ) (data ℓ) = depositLocus (γ ℓ) (Θ' ℓ) (data' ℓ)) ∧
    (data ℓ = [] → depositLocus (γ ℓ) (Θ ℓ) (data ℓ) = Θ ℓ) ∧
    ((∀ d ∈ data ℓ, d.2.2 = 0) →
      (depositLocus (γ ℓ) (Θ ℓ) (data ℓ)).map = (Θ ℓ).map ∧
        (depositLocus (γ ℓ) (Θ ℓ) (data ℓ)).gram = (Θ ℓ).gram + windowGram (data ℓ)) ∧
    (∀ i j, (∀ d ∈ data ℓ, d.2.1 i = 0 ∨ d.2.1 j = 0) →
      (depositLocus (γ ℓ) (Θ ℓ) (data ℓ)).gram i j = (Θ ℓ).gram i j) := by
  refine ⟨fun h h' => by rw [h, h'], fun h => ?_, fun h => ?_, fun i j h => ?_⟩
  · rw [h]
    cases hθ : Θ ℓ
    simp [depositLocus, windowGram, windowCovector]
  · refine ⟨?_, rfl⟩
    simp [depositLocus, windowCovector_eq_zero _ h]
  · simp [depositLocus, windowGram_apply_eq_zero _ i j h]

/-- [counterexample; formal-checked] **A reached locus moves.** On `ℚ¹` at `W = 0`, `H = 1`, one
window tick with `w = f = g = 1` and `γ = 1` moves the map to `1/2`: an empty window is
load-bearing in `deposit_local`. -/
theorem nonempty_window_moves_the_map :
    (depositLocus (1 : ℚ) ⟨0, 1, 0⟩ [((1 : ℚ), ![1], ![1])]).map 0 0 = 1 / 2 := by
  have hgram : (1 : Matrix (Fin 1) (Fin 1) ℚ) + windowGram [((1 : ℚ), ![1], ![1])] = !![2] := by
    ext i j; fin_cases i; fin_cases j; simp [windowGram, vecMulVec]; norm_num
  have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1 / 2] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j; simp
  simp only [depositLocus, hgram, hinv]
  simp [windowCovector, vecMulVec, Matrix.mul_apply]

open Holonics.Physics.AccumulatedNormalResponse Holonics.Objects.Deposition in
/-- [proved-derived; formal-checked] **The complex chart of entrywise locality**, iterating the
owner's `normal_law_local` over a window: a Gram entry `(i, j)` is unchanged when every window
feature vanishes at `i` or at `j`. -/
theorem deposit_local_complex {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (xs : List (Column ι))
    (i j : ι) (h : ∀ x ∈ xs, x i () = 0 ∨ x j () = 0) :
    (xs.foldl updatedGram H) i j = H i j := by
  induction xs generalizing H with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih (updatedGram H x) (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      exact normal_law_local H x i j (h x List.mem_cons_self)

end Local

/-! ## 4. Reaction deposits do no deposition work -/

section Reaction

/-- [proved-derived; formal-checked] **A reaction deposit leaves the storage and does no work.**
Composing the owner's `commit_balance` at `Q' = Q`: the deposition work `½⟨x⁺, (Q' − Q) x⁺⟩` is
zero, and the committed energy change is exactly the word balance at the learned reaction `L`
(`ε_k = 0`). -/
theorem reaction_deposit_storage_unchanged {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σ μ : Type*}
    [Fintype σ] [Fintype μ] {Q J R L : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J)
    (B : Matrix σ μ 𝕜) (h : 𝕜) (x x' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : x' - x = h • ((J - R + L) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) + B *ᵥ u)) :
    (1 / 2 : 𝕜) * (x' ⬝ᵥ ((Q - Q) *ᵥ x')) = 0 ∧
      storageEnergy Q x' - storageEnergy Q x =
        -(h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (R *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x')))))) +
          h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (L *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))))) +
          h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (B *ᵥ u)) := by
  have hwork : (1 / 2 : 𝕜) * (x' ⬝ᵥ ((Q - Q) *ᵥ x')) = 0 := by simp
  refine ⟨hwork, ?_⟩
  have hb := commit_balance hQ hJ Q B h x x' u hstep
  rw [hwork, add_zero] at hb
  exact hb

/-- [proved-derived; formal-checked] **Passive words with reaction deposits keep the committed
energy.** Composing the owner's `committed_energy_bound` at fixed storage `Q_k = Q` and `ε_k = 0`:
`E(x_n; Q) ≤ E(x_0; Q)`. -/
theorem reaction_deposits_keep_committed_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {σ : Type*} [Fintype σ] (x : ℕ → σ → 𝕜) (Q : Matrix σ σ 𝕜)
    (J R L : ℕ → Matrix σ σ 𝕜) (h : 𝕜) (hh : 0 ≤ h) (hQ : Qᵀ = Q) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e)) (hL : ∀ k e, e ⬝ᵥ (L k *ᵥ e) ≤ 0)
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + L k) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1))))))
    (n : ℕ) : storageEnergy Q (x n) ≤ storageEnergy Q (x 0) := by
  have := committed_energy_bound x (fun _ => Q) J R L (fun _ => 0) h hh (fun _ => hQ) hJ hR hL
    hstep (fun _ y => by simp) (fun _ => by norm_num) n
  simpa using this

/-- [counterexample; formal-checked] **A storage deposit does work.** Moving `Q = 1` to `Q' = 2` on
`ℚ¹` at `x = 1` does work `½` (the owner's `deposition_work`): the reaction-only hypothesis is
load-bearing for `ε_k = 0`. -/
theorem storage_deposit_does_work :
    storageEnergy (!![2] : Matrix (Fin 1) (Fin 1) ℚ) ![1] - storageEnergy 1 ![1] = 1 / 2 := by
  rw [deposition_work]
  simp [dotProduct, mulVec]
  norm_num

/-- [counterexample; formal-checked] **An active learned block diverges at fixed storage.** The
owner's `normal_law_divergence_witness`: with `Q = 1` never changing, the learned block
`diag(1, −1)` drives the committed energy from `1/2` to `9/2` in one commit, so passivity of the
learned reaction is load-bearing in `reaction_deposits_keep_committed_energy`. -/
theorem active_reaction_diverges :
    storageEnergy 1 (divergentState 0) < storageEnergy 1 (divergentState 1) := by
  rw [normal_law_divergence_witness.2.2.2 0, normal_law_divergence_witness.2.2.2 1]
  norm_num

end Reaction

/-! ## 5. Factor carriers stay positive semidefinite -/

section Factor

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {σ κ : Type*} [Fintype σ] [Fintype κ]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype σ] in
/-- [proved-derived; formal-checked] A factor carrier `c cᵀ` is the unit-weight quadratic moment of
the factor's columns. -/
theorem carrier_eq_quadraticMoment (c : Matrix σ κ 𝕜) :
    c * cᵀ = Holonics.Holon.HolonicQuadraticMomentCondensation.quadraticMoment (fun _ => (1 : 𝕜))
      (fun k i => c i k) := by
  ext i j
  simp [Matrix.mul_apply, Holonics.Holon.HolonicQuadraticMomentCondensation.quadraticMoment]

/-- [proved-derived; formal-checked] **Factor carriers stay PSD, with no clamp.** For contact
factors `c`, `b`, `F` and every factor update `x ← x + (η/h) G`, the carriers `C = c cᵀ`,
`K = b bᵀ`, `D = F Fᵀ` stay positive semidefinite, by the owner's
`storageEnergy_quadraticMoment_nonneg`. -/
theorem factorCarrier_psd (c b F Gc Gb GF : Matrix σ κ 𝕜) (η h : 𝕜) (v : σ → 𝕜) :
    0 ≤ v ⬝ᵥ (((c + (η / h) • Gc) * (c + (η / h) • Gc)ᵀ) *ᵥ v) ∧
      0 ≤ v ⬝ᵥ (((b + (η / h) • Gb) * (b + (η / h) • Gb)ᵀ) *ᵥ v) ∧
      0 ≤ v ⬝ᵥ (((F + (η / h) • GF) * (F + (η / h) • GF)ᵀ) *ᵥ v) := by
  have key : ∀ a : Matrix σ κ 𝕜, 0 ≤ v ⬝ᵥ ((a * aᵀ) *ᵥ v) := fun a => by
    have := storageEnergy_quadraticMoment_nonneg (fun _ => (1 : 𝕜)) (fun _ => zero_le_one)
      (fun k i => a i k) v
    rw [← carrier_eq_quadraticMoment, storageEnergy] at this
    linarith
  exact ⟨key _, key _, key _⟩

/-- [counterexample; formal-checked] **An additive carrier update leaves PSD.** Updating `C = 0`
itself by the covector `G = −1` on `ℚ¹` gives `⟨1, C' 1⟩ = −1`. -/
theorem additive_carrier_update_leaves_psd :
    (![1] : Fin 1 → ℚ) ⬝ᵥ (((0 : Matrix (Fin 1) (Fin 1) ℚ) + (1 : ℚ) • (-1)) *ᵥ ![1]) < 0 := by
  simp [dotProduct, mulVec]

end Factor

/-! ## 6. The standing moves only through its lock chart -/

section Standing

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ι ρ n : Type*} [Fintype ι] [Fintype ρ]

/-- [definition] The sheet class `σ_ρ(q) = sign((L q)_ρ)` with the half-open tie rule
`sign 0 = +1`. -/
def sheetClass (L : Matrix ρ ι 𝕜) (q : ι → 𝕜) (r : ρ) : 𝕜 :=
  if 0 ≤ (L *ᵥ q) r then 1 else -1

/-- [definition] The ring's element operator at the sheet classes of the standing:
`K(q) = W_s + Σ_ρ σ_ρ(q) A_ρ`. -/
def elementOperator (Ws : Matrix n n 𝕜) (A : ρ → Matrix n n 𝕜) (L : Matrix ρ ι 𝕜)
    (q : ι → 𝕜) : Matrix n n 𝕜 :=
  Ws + ∑ r, sheetClass L q r • A r

omit [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The element reads the standing only through its classes.** -/
theorem elementOperator_eq_of_sheetClass_eq (Ws : Matrix n n 𝕜) (A : ρ → Matrix n n 𝕜)
    (L : Matrix ρ ι 𝕜) {q q' : ι → 𝕜} (h : ∀ r, sheetClass L q r = sheetClass L q' r) :
    elementOperator Ws A L q = elementOperator Ws A L q' := by
  simp only [elementOperator, h]

/-- [proved-derived; formal-checked] **Off the fold the classes are locally constant.** If no
contrast coordinate is zero, every deposit moving each contrast coordinate by less than
`min_ρ |Δ_ρ|` keeps every class and the element operator: the word's derivative in `q` is zero
there. -/
theorem sheetClass_locally_constant (Ws : Matrix n n 𝕜) (A : ρ → Matrix n n 𝕜)
    (L : Matrix ρ ι 𝕜) (q : ι → 𝕜) (hoff : ∀ r, (L *ᵥ q) r ≠ 0) :
    ∃ ε > 0, ∀ δ : ι → 𝕜, (∀ r, |(L *ᵥ δ) r| < ε) →
      (∀ r, sheetClass L (q + δ) r = sheetClass L q r) ∧
        elementOperator Ws A L (q + δ) = elementOperator Ws A L q := by
  classical
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ r, ε ≤ |(L *ᵥ q) r| := by
    by_cases hρ : Nonempty ρ
    · obtain ⟨r₀, -, hr₀⟩ := Finset.exists_min_image Finset.univ (fun r => |(L *ᵥ q) r|)
        (Finset.univ_nonempty_iff.mpr hρ)
      exact ⟨|(L *ᵥ q) r₀|, abs_pos.mpr (hoff r₀), fun r => hr₀ r (Finset.mem_univ r)⟩
    · exact ⟨1, one_pos, fun r => (hρ ⟨r⟩).elim⟩
  refine ⟨ε, hε, fun δ hδ => ?_⟩
  have hcls : ∀ r, sheetClass L (q + δ) r = sheetClass L q r := by
    intro r
    have hsum : (L *ᵥ (q + δ)) r = (L *ᵥ q) r + (L *ᵥ δ) r := by rw [mulVec_add]; rfl
    have h1 := hle r
    have h2 := hδ r
    unfold sheetClass
    rw [hsum]
    rcases lt_or_gt_of_ne (hoff r) with hneg | hpos
    · rw [abs_of_neg hneg] at h1
      have : (L *ᵥ q) r + (L *ᵥ δ) r < 0 := by linarith [le_abs_self ((L *ᵥ δ) r)]
      rw [if_neg (not_le.mpr this), if_neg (not_le.mpr hneg)]
    · rw [abs_of_pos hpos] at h1
      have : 0 ≤ (L *ᵥ q) r + (L *ᵥ δ) r := by linarith [neg_abs_le ((L *ᵥ δ) r)]
      rw [if_pos this, if_pos hpos.le]
  exact ⟨hcls, elementOperator_eq_of_sheetClass_eq Ws A L hcls⟩

/-- [proved-derived; formal-checked] **The standing's deposit, through the declared lock chart.**
With the class covector `g` on the contrast coordinates and the step `q' = q + (η/h) Lᵀ g`:
* the chart carries `g` to `q` by the transpose of the contrast map, `⟨g, L δ⟩ = ⟨Lᵀ g, δ⟩`;
* the step moves the contrast along the covector, `⟨g, Δ' − Δ⟩ = (η/h) |Lᵀ g|² ≥ 0` for
  `η/h ≥ 0`;
* a sheet class changes exactly where the deposit carries `Δ_ρ` across zero (half-open sheet). -/
theorem standing_deposit (L : Matrix ρ ι 𝕜) (q : ι → 𝕜) (g : ρ → 𝕜) (η h : 𝕜)
    (hstep : 0 ≤ η / h) :
    (∀ δ : ι → 𝕜, g ⬝ᵥ (L *ᵥ δ) = (Lᵀ *ᵥ g) ⬝ᵥ δ) ∧
      g ⬝ᵥ (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g)) - L *ᵥ q) = (η / h) * ((Lᵀ *ᵥ g) ⬝ᵥ (Lᵀ *ᵥ g)) ∧
      0 ≤ g ⬝ᵥ (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g)) - L *ᵥ q) ∧
      ∀ r, (sheetClass L (q + (η / h) • (Lᵀ *ᵥ g)) r ≠ sheetClass L q r ↔
        ((0 ≤ (L *ᵥ q) r ∧ (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g))) r < 0) ∨
          ((L *ᵥ q) r < 0 ∧ 0 ≤ (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g))) r))) := by
  have hT : ∀ δ : ι → 𝕜, g ⬝ᵥ (L *ᵥ δ) = (Lᵀ *ᵥ g) ⬝ᵥ δ := fun δ => by
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have hmove : g ⬝ᵥ (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g)) - L *ᵥ q) =
      (η / h) * ((Lᵀ *ᵥ g) ⬝ᵥ (Lᵀ *ᵥ g)) := by
    rw [mulVec_add, add_sub_cancel_left, mulVec_smul, dotProduct_smul, hT, smul_eq_mul]
  have hsq : 0 ≤ (Lᵀ *ᵥ g) ⬝ᵥ (Lᵀ *ᵥ g) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨hT, hmove, by rw [hmove]; exact mul_nonneg hstep hsq, fun r => ?_⟩
  unfold sheetClass
  set Δ := (L *ᵥ q) r
  set Δ' := (L *ᵥ (q + (η / h) • (Lᵀ *ᵥ g))) r
  by_cases h1 : 0 ≤ Δ <;> by_cases h2 : 0 ≤ Δ'
  · rw [if_pos h1, if_pos h2]
    exact ⟨fun hne => absurd rfl hne, by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith⟩
  · rw [if_pos h1, if_neg h2]
    exact ⟨fun _ => Or.inl ⟨h1, lt_of_not_ge h2⟩, fun _ => by norm_num⟩
  · rw [if_neg h1, if_pos h2]
    exact ⟨fun _ => Or.inr ⟨lt_of_not_ge h1, h2⟩, fun _ => by norm_num⟩
  · rw [if_neg h1, if_neg h2]
    exact ⟨fun hne => absurd rfl hne, by rintro (⟨h, -⟩ | ⟨-, h⟩) <;> contradiction⟩

/-- [counterexample; formal-checked] **The step's sign is load-bearing.** On `ℚ¹` with `L = 1`,
`g = 1` and `η/h = −1`, the deposit moves the contrast against the covector: `⟨g, Δ' − Δ⟩ = −1`. -/
theorem standing_step_sign_witness :
    (![1] : Fin 1 → ℚ) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ
        (0 + (-1 : ℚ) • ((1 : Matrix (Fin 1) (Fin 1) ℚ)ᵀ *ᵥ ![1])) -
      (1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ 0) = -1 := by
  simp [dotProduct]

/-- [counterexample; formal-checked] **At the fold the class jumps.** On `ℚ¹` with `L = 1` and
`q = 0`, the tie rule gives class `+1`, and every deposit `−ε/2` with `ε > 0` flips it to `−1`:
off-fold is load-bearing in `sheetClass_locally_constant`. -/
theorem sheet_fold_witness :
    sheetClass (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 = 1 ∧
      ∀ ε : ℚ, 0 < ε → sheetClass (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 + ![-(ε / 2)]) 0 = -1 := by
  refine ⟨by simp [sheetClass], fun ε hε => ?_⟩
  have : ¬ (0 : ℚ) ≤ -(ε / 2) := by linarith
  simp [sheetClass, this]

end Standing

section Audit

#print axioms normalStatistic_standing
#print axioms statistic_forgets_the_samples
#print axioms normal_prox_step
#print axioms normal_prox_step_needs_the_solve
#print axioms normal_prox_step_needs_invertible_gram
#print axioms normal_prox_step_complex
#print axioms depositLocus_solves
#print axioms deposit_local
#print axioms nonempty_window_moves_the_map
#print axioms deposit_local_complex
#print axioms reaction_deposit_storage_unchanged
#print axioms reaction_deposits_keep_committed_energy
#print axioms storage_deposit_does_work
#print axioms active_reaction_diverges
#print axioms factorCarrier_psd
#print axioms additive_carrier_update_leaves_psd
#print axioms elementOperator_eq_of_sheetClass_eq
#print axioms sheetClass_locally_constant
#print axioms standing_deposit
#print axioms standing_step_sign_witness
#print axioms sheet_fold_witness

end Audit

end Holonics.HNN.Normal
