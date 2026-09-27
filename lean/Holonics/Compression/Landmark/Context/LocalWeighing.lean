import Holonics.Compression.Landmark.Context.Tree

/-!
# Compression.Landmark.Context.LocalWeighing: every face weighed at each landmark, in each digit tree and across epochs

[definition; agent-inferred] Decision 34 of the step 4 design (`docs/plans/THE_REBUILD.md`,
"Weighing is local"), rebuild step 4 (#73). Decisions 30, 32 and 33 located one limit: a mixture
of whole passages telescopes to `½W_T + ½W_X` and can use a face only where it beats the tree over
the whole passage. Decision 28's own law already weighs locally: each landmark weighs its face
against its split by that landmark's evidence. This owner extends that weighing to every face. The
computational object is the helical pair interaction; this owner is the receiving parametron's
landmark tree weighing each face by its own evidence. Of the winding guide's six general objects it
touches three: **faces and placement** (every weighed face is a normalized receiving face, and the
executed faces partition the unit cell as the tree's do), the **tower thread** (the landmark's
routed digits, the digit tree of a dyadic cell, and the epochs of the passage are its restrictions)
and the **pair** (each two-face weighing is a ratio of two likelihoods, stepped by the faces' ratio
at the target). The tube is the passage, one cell per tick; no cell holonomy is claimed (a tree and
a forward chain have no two-cells). One law serves the three local weighings: the **forward
mixture** over faces with a stochastic kernel (the static prior is the identity kernel, the fixed
share its switching kernel).

```text
forward     F_0 = π ;  F_(t+1)(x) = Σ_y F_t(y) f_y(t) T(y, x) ;  q_t = Σ_x F_t(x) f_x(t) / Σ_x F_t(x)
telescope   ∏_(t<n) q_t = Σ_x F_n(x)                                        T stochastic
dominance   −log₂ ∏ q ≤ −log₂ π(σ_0) − Σ_t log₂ T(σ_t, σ_(t+1)) − Σ_t log₂ f_(σ_t)(t)        every σ
executed    weights on f ρ, r_t ≤ ρ ≤ R_t:  the same bound + Σ_t log₂(R_t/r_t)
static      T = 1:  F_n(x) = π_x A_x(n),  ∏ q = Σ_x π_x A_x(n)
two faces   β_0 = π/(1 − π),  β' = β a/b,  λ = β/(1 + β);   π = 1 − 2^(−j):  β_0 = 2^j − 1
share       T = 1 − α (stay), α (switch):  −log₂ ∏ q ≤ −log₂ ∏_t f_(σ_t) + 1 + k(−log₂ α) + (n − k)(−log₂(1 − α))
            β' = S_α(β a/b),  S_α(β) = ((1 − α)β + α)/((1 − α) + αβ);  α = 2^(−j): ((2^j − 1)β + 1)/((2^j − 1) + β)
            |log S_α(y) − log S_α(x)| ≤ |log y − log x|
landmark    E_s = π KT_s + (1 − π) X_s over its routed digits;  e_s = μ_s k_s + (1 − μ_s) x,  μ_s = γ_s/(1 + γ_s),
            γ_s = π KT_s/((1 − π) X_s),  γ' = γ k(b)/x(b)
            W_s = w_d E_s + (1 − w_d) ∏_b W_(s b) = Σ_S prior_w(S) ∏_(leaves) E ;  q_d = λ_d e_d + (1 − λ_d) q_(d+1) ;  β' = β e_d/q_(d+1)
            −log₂ W ≤ −log₂ prior_w(S) + Σ_(leaves ℓ) (−log₂ π_(σ ℓ)) − log₂ ∏_(leaves ℓ) X_(σ ℓ)(ℓ)
digit tree  W_h = Σ_k π_k W_h^(w_k) = Σ_(k, S) π_k prior_(w_k)(S) ∏_(leaves) E ;  Σ_(k, S) π_k prior_(w_k)(S) = 1
            −log₂ W_h ≤ −log₂ π_k − log₂ prior_(w_k)(S) − log₂ ∏_(leaves) E
```

[proved-derived; formal-checked] What is proved.

1. **The forward mixture** (`fwd`, `fwdMix`, `forward_telescope`, `forward_dominance`,
   `forward_weight_step`): for a prior, positive faces and a stochastic kernel, every total forward
   weight is positive, the mixture's product telescopes to the total forward weight, and it
   dominates every face sequence weighed by its prior and kernel, in products and in bits. The
   posterior weights step by the faces' likelihood ratios at the target, then the kernel.
2. **The executed forward mixture** (`fwdExec`, `forward_executed`): weights propagated with charted
   faces `f ρ` (a rational chart, a rebase) and scored with the true faces lose at most
   `Σ_t log₂(R_t/r_t)` against the ideal bound: the chart's drift adds once over the passage. At two
   faces with the chart on one side it is `Tree.sequential_mixture_executed`'s `Σ|log₂ ρ|`.
3. **The static mixture** (`idKernel`, `static_mixture`, `two_face_prior`): under the identity
   kernel each face's forward weight is its prior times its prequential likelihood, the product
   telescopes to `Σ_x π_x A_x(n)` and codes within `−log₂ π_x` of every face. Over two faces with the
   prior `(π, 1 − π)` the ratio opens at `π/(1 − π)` and steps by the faces' ratio; at `½` it is
   Decision 30's `seqMix`; on the dyadic ladder the founding ratio is `2^j − 1`.
4. **The fixed share** (`shareKernel`, `switches`, `stays`, `share_prod`, `fixed_share`,
   `shareMap`, `share_ratio_step`, `share_log_lipschitz`): from `½/½` at the switching rate
   `α ∈ (0, 1)`, the mixture codes within `1 + k(−log₂ α) + (n − k)(−log₂(1 − α))` of every face
   sequence with `k` switches over `n` cells (Herbster–Warmuth); the executed ratio steps by the
   likelihood ratio, then the share map, which on the ladder `α = 2^(−j)` is
   `((2^j − 1)β + 1)/((2^j − 1) + β)`; and the share map never amplifies a drift in `log β`.
5. **The tree over own weights** (`Tree.{ownWeight, ownSplit, ownLik,
   own_mixture_over_trees, ownWeight_kt, ownLik_kt, ownWeight_one, own_kraft_and_dominance}`,
   stated once in `Tree` since Decision 39, every node law's weighting): for any positive
   own weights the tree is the mixture over pruned trees with the stop law's prior, its prior is
   complete, and it codes within the prior's code of every pruned tree. The declared stop law
   (`Tree.stopWeight`, `treeLik`) is its case at the KT own weight.
6. **Node-local mixing** (`ownLik_mul`, `ownLik_mono`, `node_local_dominance`,
   `own_face_normalized`, `node_local_founding`): with each landmark's own weight the static
   mixture of its KT mass and an admitted external face over its routed digits, the tree stays
   normalized (each own face is a normalized face, so the opened path is, under any stop weights)
   and Kraft-complete, and each landmark pays at most `−log₂` of its prior weight. An unfounded
   landmark reads `π/|A| + (1 − π) x`.
7. **The opened-path step over own weights** (`Tree.{ownLam, ownRatio, ownLam_mem,
   ownWeight_off, ownSplit_arrive, own_weight_step₀, own_weight_step, own_ratio_step}`, stated once
   in `Tree` since Decision 39): an arrival that moves
   each opened landmark's own weight by its own face multiplies each opened node's weight by the path
   face over own faces, and the ratio steps by `β' = β e_d/q_(d+1)`: the stop law's step with the own
   face in place of the KT face.
8. **The stop-weight mixture per digit tree** (`stop_mixture_per_tree`): each digit tree's mixture
   of the declared stop-weight laws under a prior is the mixture over (law, pruned tree), its prior
   is complete, and it codes within `−log₂ π_k − log₂ prior_(w_k)(S)` of every law and pruned tree.

[proved-standard] The forward (hidden Markov) recursion and the fixed share are Herbster and
Warmuth (1998) and Vovk's aggregating algorithm; the proofs here are this owner's.

[open] Owed in #62 ("Step 4 (#73) owed"): the executed lattice's per-cell certificates of the three
laws composed over the passage (the own face's rounding and the own ratio's drift at each landmark,
the join tree's rounding over the digit tree's laws, the share step's rebase) into per-cell rules
like `Landmarks::face_rule`; `forward_executed` and `share_log_lipschitz` are their passage-level
parts, and the Rust tests check the executed faces against the ideal weighting.

| Lean | Rust |
|---|---|
| `forward_telescope`, `forward_dominance`, `forward_weight_step`, `forward_executed` | `compression::landmark::context::{JoinTree, FaceJoins}`, `hnn::receiving::Mixture::switching` |
| `static_mixture`, `two_face_prior` | `compression::landmark::context::JoinTree` (a two-face join from `β₀ = 2^j − 1`) |
| `fixed_share`, `share_ratio_step`, `share_log_lipschitz` | `hnn::receiving::Mixture::switching` |
| `Tree.{own_mixture_over_trees, own_kraft_and_dominance, own_weight_step, own_ratio_step}`, `node_local_dominance`, `own_face_normalized`, `node_local_founding` | `compression::landmark::context::{Landmarks::local, LocalLaw}` (retired at `89460425`); the own-weight tree is every node law's (`compression::landmark::context::Capacity`, Decision 39) |
| `stop_mixture_per_tree` | `compression::landmark::context::{StopMixture, FaceJoins}` |

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.LocalWeighing

open Finset
open Holonics.Compression.Landmark.Context.Tree

/-- A positive quantity below another reads fewer bits: `−log₂ b ≤ −log₂ a` for `0 < a ≤ b`. -/
theorem neg_logb_le_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    -Real.logb 2 b ≤ -Real.logb 2 a := by
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) ha hab
  linarith

/-! ## 1. The forward mixture over faces -/

section Forward

variable {ι : Type*} [Fintype ι]

/-- [definition] **The forward weights** of a mixture over the faces `ι`: the prior `F₀` at the
opening, then at each cell the weight of every face multiplied by its face of the target and moved
by the kernel `T`, `F_(t+1)(x) = Σ_y F_t(y) f_y(t) T(y, x)`. -/
def fwd (F0 : ι → ℚ) (f : ι → ℕ → ℚ) (T : ι → ι → ℚ) : ℕ → ι → ℚ
  | 0 => F0
  | t + 1 => fun x => ∑ y, fwd F0 f T t y * f y t * T y x

/-- [definition] **The forward mixture's face** of the target at cell `t`: the faces weighed by the
normalized forward weights, `q_t = Σ_x F_t(x) f_x(t) / Σ_x F_t(x)`. -/
def fwdMix (F0 : ι → ℚ) (f : ι → ℕ → ℚ) (T : ι → ι → ℚ) (t : ℕ) : ℚ :=
  (∑ x, fwd F0 f T t x * f x t) / ∑ x, fwd F0 f T t x

/-- [definition] **A stochastic kernel**: nonnegative entries, every row summing to one. -/
def Stochastic (T : ι → ι → ℚ) : Prop := (∀ y x, 0 ≤ T y x) ∧ ∀ y, ∑ x, T y x = 1

/-- [definition] **A prior over the faces**: nonnegative weights summing to one. -/
def IsPrior (F0 : ι → ℚ) : Prop := (∀ x, 0 ≤ F0 x) ∧ ∑ x, F0 x = 1

theorem fwd_zero (F0 : ι → ℚ) (f : ι → ℕ → ℚ) (T : ι → ι → ℚ) : fwd F0 f T 0 = F0 := rfl

theorem fwd_succ (F0 : ι → ℚ) (f : ι → ℕ → ℚ) (T : ι → ι → ℚ) (t : ℕ) (x : ι) :
    fwd F0 f T (t + 1) x = ∑ y, fwd F0 f T t y * f y t * T y x := rfl

theorem fwd_nonneg {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : ∀ x, 0 ≤ F0 x)
    (hf : ∀ x t, 0 ≤ f x t) (hT : ∀ y x, 0 ≤ T y x) : ∀ t x, 0 ≤ fwd F0 f T t x
  | 0, x => hF x
  | t + 1, x => sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (fwd_nonneg hF hf hT t y) (hf y t)) (hT y x)

theorem fwd_pos {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} [Nonempty ι] (hF : ∀ x, 0 < F0 x)
    (hf : ∀ x t, 0 < f x t) (hT : ∀ y x, 0 < T y x) : ∀ t x, 0 < fwd F0 f T t x
  | 0, x => hF x
  | t + 1, x => sum_pos (fun y _ =>
      mul_pos (mul_pos (fwd_pos hF hf hT t y) (hf y t)) (hT y x)) univ_nonempty

/-- The kernel moves the forward weights without changing their total: a stochastic kernel's rows
sum to one. -/
theorem fwd_sum_succ {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hT : Stochastic T) (t : ℕ) :
    ∑ x, fwd F0 f T (t + 1) x = ∑ y, fwd F0 f T t y * f y t := by
  simp only [fwd_succ]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_sum, hT.2 y, mul_one]

theorem fwd_sum_pos {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : IsPrior F0)
    (hf : ∀ x t, 0 < f x t) (hT : Stochastic T) : ∀ t, 0 < ∑ x, fwd F0 f T t x
  | 0 => by rw [fwd_zero, hF.2]; exact one_pos
  | t + 1 => by
    rw [fwd_sum_succ hT]
    have hprev := fwd_sum_pos hF hf hT t
    obtain ⟨y, _, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ))
      (g := fwd F0 f T t) (by simpa using hprev)
    exact sum_pos' (fun x _ => mul_nonneg
        (fwd_nonneg hF.1 (fun x t => (hf x t).le) hT.1 t x) (hf x t).le)
      ⟨y, mem_univ _, mul_pos hy (hf y t)⟩

/-- [proved-derived; formal-checked] **`forward_telescope`: the forward mixture's code telescopes.**
For a prior `F₀`, positive faces and a stochastic kernel, every total `Σ_x F_t(x)` is positive and
the mixture's product over the passage is the total forward weight:
`∏_(t<n) q_t = Σ_x F_n(x)`. -/
theorem forward_telescope {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : IsPrior F0)
    (hf : ∀ x t, 0 < f x t) (hT : Stochastic T) :
    (∀ t, 0 < ∑ x, fwd F0 f T t x) ∧
      ∀ n, ∏ t ∈ range n, fwdMix F0 f T t = ∑ x, fwd F0 f T n x := by
  refine ⟨fwd_sum_pos hF hf hT, fun n => ?_⟩
  induction n with
  | zero => simp [fwd_zero, hF.2]
  | succ n ih =>
    rw [prod_range_succ, ih, fwd_sum_succ hT, fwdMix,
      mul_div_cancel₀ _ (fwd_sum_pos hF hf hT n).ne']

/-- [proved-derived; formal-checked] **`forward_dominance`: the mixture codes within its prior's
code of every face sequence.** For every sequence of faces `σ`,
`F₀(σ_0) ∏_(t<n) f_(σ_t)(t) T(σ_t, σ_(t+1)) ≤ F_n(σ_n) ≤ ∏_(t<n) q_t`, and in bits, when those
entries are positive,
`−log₂ ∏ q ≤ −log₂ F₀(σ_0) − Σ_t log₂ T(σ_t, σ_(t+1)) − Σ_t log₂ f_(σ_t)(t)`. -/
theorem forward_dominance {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : IsPrior F0)
    (hf : ∀ x t, 0 < f x t) (hT : Stochastic T) (σ : ℕ → ι) (n : ℕ) :
    F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) ≤ fwd F0 f T n (σ n) ∧
      fwd F0 f T n (σ n) ≤ ∏ t ∈ range n, fwdMix F0 f T t ∧
      (0 < F0 (σ 0) → (∀ t < n, 0 < T (σ t) (σ (t + 1))) →
        -Real.logb 2 ((∏ t ∈ range n, fwdMix F0 f T t : ℚ) : ℝ) ≤
          -Real.logb 2 (F0 (σ 0) : ℝ) - ∑ t ∈ range n, Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ) -
            ∑ t ∈ range n, Real.logb 2 (f (σ t) t : ℝ)) := by
  have hnn := fwd_nonneg hF.1 (fun x t => (hf x t).le) hT.1
  have hdom : ∀ n, F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) ≤
      fwd F0 f T n (σ n) := by
    intro n
    induction n with
    | zero => simp [fwd_zero]
    | succ n ih =>
      rw [prod_range_succ, ← mul_assoc, fwd_succ]
      have hm : 0 ≤ f (σ n) n * T (σ n) (σ (n + 1)) := mul_nonneg (hf _ _).le (hT.1 _ _)
      calc (F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
            (f (σ n) n * T (σ n) (σ (n + 1)))
          ≤ fwd F0 f T n (σ n) * (f (σ n) n * T (σ n) (σ (n + 1))) :=
            mul_le_mul_of_nonneg_right ih hm
        _ = fwd F0 f T n (σ n) * f (σ n) n * T (σ n) (σ (n + 1)) := by ring
        _ ≤ ∑ y, fwd F0 f T n y * f y n * T y (σ (n + 1)) :=
            single_le_sum (f := fun y => fwd F0 f T n y * f y n * T y (σ (n + 1)))
              (fun y _ => mul_nonneg (mul_nonneg (hnn n y) (hf y n).le) (hT.1 _ _)) (mem_univ _)
  have hle : fwd F0 f T n (σ n) ≤ ∏ t ∈ range n, fwdMix F0 f T t := by
    rw [(forward_telescope hF hf hT).2 n]
    exact single_le_sum (f := fun x => fwd F0 f T n x) (fun x _ => hnn n x) (mem_univ _)
  refine ⟨hdom n, hle, fun h0 hTpos => ?_⟩
  have hpos : 0 < F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) :=
    mul_pos h0 (prod_pos fun t ht => mul_pos (hf _ _) (hTpos t (mem_range.mp ht)))
  have hR := neg_logb_le_of_le (by exact_mod_cast hpos)
    (show ((F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) : ℚ) : ℝ) ≤
      ((∏ t ∈ range n, fwdMix F0 f T t : ℚ) : ℝ) by exact_mod_cast (hdom n).trans hle)
  push_cast at hR
  rw [Real.logb_mul (by exact_mod_cast h0.ne') (prod_ne_zero_iff.mpr fun t ht =>
      (mul_pos (by exact_mod_cast hf _ _) (by exact_mod_cast hTpos t (mem_range.mp ht))).ne'),
    Real.logb_prod _ _ fun t ht =>
      (mul_pos (by exact_mod_cast hf _ _) (by exact_mod_cast hTpos t (mem_range.mp ht))).ne'] at hR
  rw [sum_congr rfl fun t ht => Real.logb_mul (by exact_mod_cast (hf (σ t) t).ne')
      (by exact_mod_cast (hTpos t (mem_range.mp ht)).ne'), sum_add_distrib] at hR
  push_cast
  linarith

/-- [definition] **The posterior weight** of face `x` at cell `t`: its forward weight normalized. -/
def fwdWeight (F0 : ι → ℚ) (f : ι → ℕ → ℚ) (T : ι → ι → ℚ) (t : ℕ) (x : ι) : ℚ :=
  fwd F0 f T t x / ∑ y, fwd F0 f T t y

/-- [proved-derived; formal-checked] **`forward_weight_step`: Bayes, then the kernel.** The mixture's
face is the posterior-weighted face, `q_t = Σ_x v_t(x) f_x(t)`, and the posterior weights step by
`v_(t+1)(x) = Σ_y (v_t(y) f_y(t)/q_t) T(y, x)`: the likelihood ratio of each face at the cell, then
the kernel's move. -/
theorem forward_weight_step {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : IsPrior F0)
    (hf : ∀ x t, 0 < f x t) (hT : Stochastic T) (t : ℕ) :
    fwdMix F0 f T t = ∑ x, fwdWeight F0 f T t x * f x t ∧
      ∀ x, fwdWeight F0 f T (t + 1) x =
        ∑ y, (fwdWeight F0 f T t y * f y t / fwdMix F0 f T t) * T y x := by
  have hS := fwd_sum_pos hF hf hT t
  have hN : 0 < ∑ y, fwd F0 f T t y * f y t := by
    rw [← fwd_sum_succ hT]; exact fwd_sum_pos hF hf hT (t + 1)
  refine ⟨?_, fun x => ?_⟩
  · simp only [fwdMix, fwdWeight, div_mul_eq_mul_div, ← sum_div]
  · rw [fwdWeight, fwd_sum_succ hT, fwd_succ, sum_div]
    refine sum_congr rfl fun y _ => ?_
    simp only [fwdWeight, fwdMix]
    field_simp

/-- [definition] **The executed forward mixture**: the weights propagated with the charted faces
`f̃_x(t) = f_x(t) ρ_x(t)` (a rational chart and a rebase, `ρ > 0`), the face scored with the true
faces, `q̂_t = Σ_x F̃_t(x) f_x(t) / Σ_x F̃_t(x)`. -/
def fwdExec (F0 : ι → ℚ) (f ρ : ι → ℕ → ℚ) (T : ι → ι → ℚ) (t : ℕ) : ℚ :=
  (∑ x, fwd F0 (fun x t => f x t * ρ x t) T t x * f x t) /
    ∑ x, fwd F0 (fun x t => f x t * ρ x t) T t x

/-- [proved-derived; formal-checked] **`forward_executed`: the chart's drift adds once over the
passage.** With the weights carried by charted faces `f̃ = f ρ`, `r_t ≤ ρ_x(t) ≤ R_t`, and every face
sequence `σ`: `F₀(σ_0) ∏_t f_(σ_t)(t) T(σ_t, σ_(t+1)) ∏_t (r_t/R_t) ≤ ∏_t q̂_t`, so
`−log₂ ∏ q̂ ≤ −log₂ F₀(σ_0) − Σ log₂ T(σ_t, σ_(t+1)) − Σ log₂ f_(σ_t)(t) + Σ_t log₂(R_t/r_t)`.
At two faces with the chart on one side (`ρ_a = 1`, `ρ_b = ρ`) the last sum is `Σ|log₂ ρ_t|`,
`Tree.sequential_mixture_executed`'s. -/
theorem forward_executed {F0 : ι → ℚ} {f ρ : ι → ℕ → ℚ} {T : ι → ι → ℚ} {R r : ℕ → ℚ}
    (hF : IsPrior F0) (hf : ∀ x t, 0 < f x t) (hT : Stochastic T) (hρ : ∀ x t, 0 < ρ x t)
    (hR : ∀ x t, ρ x t ≤ R t) (hr : ∀ x t, r t ≤ ρ x t) (hr0 : ∀ t, 0 < r t)
    (σ : ℕ → ι) (n : ℕ) (h0 : 0 < F0 (σ 0)) (hTpos : ∀ t < n, 0 < T (σ t) (σ (t + 1))) :
    F0 (σ 0) * (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) * ∏ t ∈ range n, (r t / R t) ≤
        ∏ t ∈ range n, fwdExec F0 f ρ T t ∧
      -Real.logb 2 ((∏ t ∈ range n, fwdExec F0 f ρ T t : ℚ) : ℝ) ≤
        -Real.logb 2 (F0 (σ 0) : ℝ) - ∑ t ∈ range n, Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ) -
          ∑ t ∈ range n, Real.logb 2 (f (σ t) t : ℝ) +
            ∑ t ∈ range n, Real.logb 2 ((R t / r t : ℚ) : ℝ) := by
  set g : ι → ℕ → ℚ := fun x t => f x t * ρ x t with hg
  have hgpos : ∀ x t, 0 < g x t := fun x t => mul_pos (hf x t) (hρ x t)
  have hRpos : ∀ t, 0 < R t := fun t => (hr0 t).trans_le ((hr (σ 0) t).trans (hR (σ 0) t))
  have hnn := fwd_nonneg hF.1 (fun x t => (hgpos x t).le) hT.1
  -- each executed face is at least the charted mixture's face over `R_t`
  have hterm : ∀ t, fwdMix F0 g T t ≤ fwdExec F0 f ρ T t * R t := by
    intro t
    have hS := fwd_sum_pos hF hgpos hT t
    rw [fwdMix, fwdExec, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hS, sum_mul]
    refine sum_le_sum fun x _ => ?_
    rw [hg, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hR x t) (hf x t).le) (hnn t x)
  have hexec_pos : ∀ t, 0 < fwdExec F0 f ρ T t := by
    intro t
    have hS := fwd_sum_pos hF hgpos hT t
    obtain ⟨y, _, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ))
      (g := fwd F0 g T t) (by simpa using hS)
    exact div_pos (sum_pos' (fun x _ => mul_nonneg (hnn t x) (hf x t).le)
      ⟨y, mem_univ _, mul_pos hy (hf y t)⟩) hS
  obtain ⟨hdom, hle, -⟩ := forward_dominance hF hgpos hT σ n
  have hprod_g : (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) * ∏ t ∈ range n, r t ≤
      ∏ t ∈ range n, (g (σ t) t * T (σ t) (σ (t + 1))) := by
    rw [← prod_mul_distrib]
    refine prod_le_prod (fun t ht => mul_nonneg (mul_pos (hf _ _)
      (hTpos t (mem_range.mp ht))).le (hr0 t).le) fun t ht => ?_
    have hT0 := hTpos t (mem_range.mp ht)
    rw [hg]
    have := mul_le_mul_of_nonneg_left (hr (σ t) t) (mul_pos (hf (σ t) t) hT0).le
    nlinarith
  have hup : ∏ t ∈ range n, fwdMix F0 g T t ≤
      (∏ t ∈ range n, fwdExec F0 f ρ T t) * ∏ t ∈ range n, R t := by
    rw [← prod_mul_distrib]
    exact prod_le_prod (fun t _ => by
      have := fwd_sum_pos hF hgpos hT t
      exact div_nonneg (sum_nonneg fun x _ => mul_nonneg (hnn t x) (hgpos x t).le) this.le)
      fun t _ => hterm t
  have hRprod : 0 < ∏ t ∈ range n, R t := prod_pos fun t _ => hRpos t
  have hmain : F0 (σ 0) * (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
      ∏ t ∈ range n, (r t / R t) ≤ ∏ t ∈ range n, fwdExec F0 f ρ T t := by
    rw [prod_div_distrib, mul_div_assoc', div_le_iff₀ hRprod]
    calc F0 (σ 0) * (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) * ∏ t ∈ range n, r t
        = F0 (σ 0) * ((∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
            ∏ t ∈ range n, r t) := by ring
      _ ≤ F0 (σ 0) * ∏ t ∈ range n, (g (σ t) t * T (σ t) (σ (t + 1))) :=
          mul_le_mul_of_nonneg_left hprod_g h0.le
      _ ≤ ∏ t ∈ range n, fwdMix F0 g T t := hdom.trans hle
      _ ≤ (∏ t ∈ range n, fwdExec F0 f ρ T t) * ∏ t ∈ range n, R t := hup
  refine ⟨hmain, ?_⟩
  have hfT : ∀ t ∈ range n, (0 : ℝ) < ((f (σ t) t * T (σ t) (σ (t + 1)) : ℚ) : ℝ) :=
    fun t ht => by exact_mod_cast mul_pos (hf _ _) (hTpos t (mem_range.mp ht))
  have hrR : ∀ t ∈ range n, (0 : ℝ) < ((r t / R t : ℚ) : ℝ) :=
    fun t _ => by exact_mod_cast div_pos (hr0 t) (hRpos t)
  have hpos : (0 : ℝ) < ((F0 (σ 0) * (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
      ∏ t ∈ range n, (r t / R t) : ℚ) : ℝ) := by
    exact_mod_cast mul_pos (mul_pos h0 (prod_pos fun t ht =>
      mul_pos (hf _ _) (hTpos t (mem_range.mp ht)))) (prod_pos fun t _ => div_pos (hr0 t) (hRpos t))
  have hb := neg_logb_le_of_le (b := ((∏ t ∈ range n, fwdExec F0 f ρ T t : ℚ) : ℝ)) hpos
    (by exact_mod_cast hmain)
  have e1 : ((F0 (σ 0) * (∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
      ∏ t ∈ range n, (r t / R t) : ℚ) : ℝ) = (F0 (σ 0) : ℝ) *
        (∏ t ∈ range n, ((f (σ t) t * T (σ t) (σ (t + 1)) : ℚ) : ℝ)) *
          ∏ t ∈ range n, ((r t / R t : ℚ) : ℝ) := by push_cast; ring
  rw [e1, Real.logb_mul (mul_pos (by exact_mod_cast h0) (prod_pos fun t ht => hfT t ht)).ne'
      (prod_ne_zero_iff.mpr fun t ht => (hrR t ht).ne'),
    Real.logb_mul (by exact_mod_cast h0.ne') (prod_ne_zero_iff.mpr fun t ht => (hfT t ht).ne'),
    Real.logb_prod _ _ fun t ht => (hfT t ht).ne', Real.logb_prod _ _ fun t ht => (hrR t ht).ne']
    at hb
  have e2 : ∀ t ∈ range n, Real.logb 2 ((f (σ t) t * T (σ t) (σ (t + 1)) : ℚ) : ℝ) =
      Real.logb 2 (f (σ t) t : ℝ) + Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ) := fun t ht => by
    push_cast
    exact Real.logb_mul (by exact_mod_cast (hf _ _).ne')
      (by exact_mod_cast (hTpos t (mem_range.mp ht)).ne')
  have e3 : ∀ t ∈ range n, Real.logb 2 ((r t / R t : ℚ) : ℝ) =
      -Real.logb 2 ((R t / r t : ℚ) : ℝ) := fun t _ => by
    rw [← Real.logb_inv]
    congr 1
    push_cast
    rw [inv_div]
  rw [sum_congr rfl e2, sum_add_distrib, sum_congr rfl e3, sum_neg_distrib] at hb
  linarith

/-- [definition] **The identity kernel**: the static mixture, whose faces never move. -/
def idKernel [DecidableEq ι] : ι → ι → ℚ := fun y x => if y = x then 1 else 0

theorem idKernel_stochastic [DecidableEq ι] : Stochastic (idKernel (ι := ι)) :=
  ⟨fun y x => by unfold idKernel; split_ifs <;> norm_num, fun y => by simp [idKernel]⟩

/-- [proved-derived; formal-checked] **`static_mixture`: the Bayes mixture of faces under a declared
prior** (the identity kernel). Each forward weight is the face's prior times its prequential
likelihood, `F_n(x) = π_x A_x(n)`, `A_x(n) = ∏_(t<n) f_x(t)`; the mixture's product telescopes to
`Σ_x π_x A_x(n)`; and it codes within `−log₂ π_x` of every face:
`−log₂ ∏ q ≤ −log₂ π_x − log₂ A_x(n)`. -/
theorem static_mixture [DecidableEq ι] {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 < f x t) (n : ℕ) :
    (∀ x, fwd π f idKernel n x = π x * seqLik (f x) n) ∧
      ∏ t ∈ range n, fwdMix π f idKernel t = ∑ x, π x * seqLik (f x) n ∧
      ∀ x, 0 < π x → -Real.logb 2 ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ) ≤
        -Real.logb 2 (π x : ℝ) - Real.logb 2 (seqLik (f x) n : ℝ) := by
  have hfwd : ∀ n x, fwd π f idKernel n x = π x * seqLik (f x) n := by
    intro n
    induction n with
    | zero => intro x; simp [fwd_zero, seqLik_zero]
    | succ n ih =>
      intro x
      simp only [fwd_succ, idKernel, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true,
        ih, seqLik_succ]
      ring
  have htel := (forward_telescope hπ hf idKernel_stochastic).2 n
  refine ⟨hfwd n, by rw [htel]; simp only [hfwd n], fun x hx => ?_⟩
  have hA := seqLik_pos (hf x) n
  have hle : π x * seqLik (f x) n ≤ ∏ t ∈ range n, fwdMix π f idKernel t := by
    rw [htel, ← hfwd n x]
    exact single_le_sum (f := fun y => fwd π f idKernel n y)
      (fun y _ => fwd_nonneg hπ.1 (fun x t => (hf x t).le) idKernel_stochastic.1 n y) (mem_univ _)
  have hb := neg_logb_le_of_le (a := ((π x * seqLik (f x) n : ℚ) : ℝ))
    (b := ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ)) (by exact_mod_cast mul_pos hx hA)
    (by exact_mod_cast hle)
  push_cast at hb
  rw [Real.logb_mul (by exact_mod_cast hx.ne') (by exact_mod_cast hA.ne')] at hb
  push_cast
  linarith

end Forward

/-! ### Two faces under a declared prior, and the fixed share -/

section TwoFaces

/-- [definition] **Two faces as a family over `Bool`**: `true` the first (the incumbent), `false`
the second. -/
def boolFace (a b : ℕ → ℚ) : Bool → ℕ → ℚ := fun x => if x then a else b

/-- [definition] **The two-face prior** `(π, 1 − π)`. -/
def boolPrior (π : ℚ) : Bool → ℚ := fun x => if x then π else 1 - π

theorem boolPrior_isPrior {π : ℚ} (h0 : 0 ≤ π) (h1 : π ≤ 1) : IsPrior (boolPrior π) :=
  ⟨fun x => by cases x <;> simp [boolPrior, h0, h1], by simp [boolPrior]⟩

/-- [definition] **The two-face ratio under the prior**: `β_t = π A_t/((1 − π) B_t)`. -/
def priorRatio (π : ℚ) (a b : ℕ → ℚ) (t : ℕ) : ℚ := π * seqLik a t / ((1 - π) * seqLik b t)

/-- [definition] **The two-face mixture under the prior** at cell `t`: `q_t = λ_t a_t + (1 − λ_t) b_t`,
`λ_t = π A_t/(π A_t + (1 − π) B_t)`. -/
def priorMix (π : ℚ) (a b : ℕ → ℚ) (t : ℕ) : ℚ :=
  π * seqLik a t / (π * seqLik a t + (1 - π) * seqLik b t) * a t +
    (1 - π * seqLik a t / (π * seqLik a t + (1 - π) * seqLik b t)) * b t

/-- [proved-derived; formal-checked] **`two_face_prior`: two faces weighed by their own evidence
from a declared prior.** For `π ∈ (0, 1)` and positive faces `a`, `b`:
* the mixture is the static forward mixture over `Bool` (`static_mixture`);
* the ratio opens at `β_0 = π/(1 − π)` and steps `β_(t+1) = β_t a_t/b_t`, the weight `β/(1 + β)`;
* the product telescopes, `∏_(t<n) q_t = π A_n + (1 − π) B_n`, so the mixture codes within
  `−log₂ π` of the first face and `−log₂(1 − π)` of the second;
* at `π = ½` it is Decision 30's mixture (`Tree.seqMix`); on the dyadic ladder
  `π = 1 − 2^(−j)` the founding ratio is the integer `2^j − 1` (`Tree.ladder_founding`). -/
theorem two_face_prior {π : ℚ} (hπ0 : 0 < π) (hπ1 : π < 1) {a b : ℕ → ℚ} (ha : ∀ t, 0 < a t)
    (hb : ∀ t, 0 < b t) :
    (∀ t, priorMix π a b t = fwdMix (boolPrior π) (boolFace a b) idKernel t) ∧
      priorRatio π a b 0 = π / (1 - π) ∧
      (∀ t, priorRatio π a b (t + 1) = priorRatio π a b t * a t / b t) ∧
      (∀ t, π * seqLik a t / (π * seqLik a t + (1 - π) * seqLik b t) =
        priorRatio π a b t / (1 + priorRatio π a b t)) ∧
      (∀ n, ∏ t ∈ range n, priorMix π a b t = π * seqLik a n + (1 - π) * seqLik b n) ∧
      (∀ n, -Real.logb 2 ((∏ t ∈ range n, priorMix π a b t : ℚ) : ℝ) ≤
          -Real.logb 2 (π : ℝ) - Real.logb 2 (seqLik a n : ℝ) ∧
        -Real.logb 2 ((∏ t ∈ range n, priorMix π a b t : ℚ) : ℝ) ≤
          -Real.logb 2 ((1 - π : ℚ) : ℝ) - Real.logb 2 (seqLik b n : ℝ)) ∧
      priorMix (1 / 2) a b = seqMix a b ∧
      (∀ j, 1 ≤ j → priorRatio (ladder j) a b 0 = 2 ^ j - 1) := by
  have hπ1' : (0 : ℚ) < 1 - π := sub_pos.mpr hπ1
  have hP := boolPrior_isPrior hπ0.le hπ1.le
  have hf : ∀ x t, 0 < boolFace a b x t := fun x t => by cases x <;> simp [boolFace, ha, hb]
  have hmix : ∀ t, priorMix π a b t = fwdMix (boolPrior π) (boolFace a b) idKernel t := by
    intro t
    have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    have hden : 0 < π * seqLik a t + (1 - π) * seqLik b t := by positivity
    rw [fwdMix, Fintype.sum_bool, Fintype.sum_bool, (static_mixture hP hf t).1 true,
      (static_mixture hP hf t).1 false]
    simp only [boolPrior, boolFace, if_true, Bool.false_eq_true, if_false, priorMix]
    field_simp
    ring
  have hprod : ∀ n, ∏ t ∈ range n, priorMix π a b t = π * seqLik a n + (1 - π) * seqLik b n := by
    intro n
    rw [prod_congr rfl fun t _ => hmix t, (static_mixture hP hf n).2.1, Fintype.sum_bool]
    simp [boolPrior, boolFace]
  refine ⟨hmix, by simp [priorRatio, seqLik_zero], fun t => ?_, fun t => ?_, hprod, fun n => ?_,
    ?_, fun j hj => ?_⟩
  · have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    have := hb t
    simp only [priorRatio, seqLik_succ]
    field_simp
  · have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    simp only [priorRatio]
    field_simp
    ring
  · have e : ∏ t ∈ range n, priorMix π a b t = ∏ t ∈ range n, fwdMix (boolPrior π) (boolFace a b)
        idKernel t := prod_congr rfl fun t _ => hmix t
    rw [e]
    have h1 := (static_mixture hP hf n).2.2 true hπ0
    have h2 := (static_mixture hP hf n).2.2 false hπ1'
    simp only [boolPrior, boolFace, if_true, Bool.false_eq_true, if_false] at h1 h2
    exact ⟨h1, h2⟩
  · funext t
    have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    have h1 : seqLik a t + seqLik b t ≠ 0 := by positivity
    have h2 : 1 / 2 * seqLik a t + (1 - 1 / 2) * seqLik b t ≠ 0 := by positivity
    simp only [priorMix, seqMix]
    field_simp
    ring
  · obtain ⟨-, -, hlad, -⟩ := ladder_founding hj
    simp only [priorRatio, seqLik_zero, mul_one]
    exact hlad

/-- [definition] **The fixed-share kernel** at rate `α`: a face stays with `1 − α` and switches
with `α`. -/
def shareKernel (α : ℚ) : Bool → Bool → ℚ := fun y x => if y = x then 1 - α else α

theorem shareKernel_stochastic {α : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : Stochastic (shareKernel α) :=
  ⟨fun y x => by unfold shareKernel; split_ifs <;> linarith, fun y => by
    cases y <;> simp [shareKernel]⟩

/-- [definition] **The switches of a face sequence** over its first `n` cells. -/
def switches (σ : ℕ → Bool) (n : ℕ) : ℕ := ((range n).filter fun t => ¬ σ t = σ (t + 1)).card

/-- [definition] **The stays of a face sequence** over its first `n` cells. -/
def stays (σ : ℕ → Bool) (n : ℕ) : ℕ := ((range n).filter fun t => σ t = σ (t + 1)).card

theorem stays_add_switches (σ : ℕ → Bool) (n : ℕ) : stays σ n + switches σ n = n := by
  unfold stays switches
  rw [card_filter_add_card_filter_not, card_range]

theorem share_prod (α : ℚ) (σ : ℕ → Bool) (n : ℕ) :
    ∏ t ∈ range n, shareKernel α (σ t) (σ (t + 1)) = (1 - α) ^ stays σ n * α ^ switches σ n := by
  unfold shareKernel stays switches
  rw [prod_ite, prod_const, prod_const]

/-- [definition] **The half prior** `½/½`. -/
def halfPrior : Bool → ℚ := fun _ => 1 / 2

theorem halfPrior_isPrior : IsPrior halfPrior :=
  ⟨fun _ => by norm_num [halfPrior], by simp [halfPrior]⟩

/-- [proved-derived; formal-checked] **`fixed_share`: switching between two faces at a declared
price per switch** (Herbster–Warmuth's fixed share). From the prior `½/½`, with the share kernel at
rate `α ∈ (0, 1)`, for every face sequence `σ` with `k` switches and `n − k` stays over `n` cells,
`−log₂ ∏_(t<n) q_t ≤ −Σ_t log₂ f_(σ_t)(t) + 1 + k (−log₂ α) + (n − k)(−log₂(1 − α))`: the best
switching sequence's code plus its switch costs. -/
theorem fixed_share {α : ℚ} (hα0 : 0 < α) (hα1 : α < 1) {f : Bool → ℕ → ℚ} (hf : ∀ x t, 0 < f x t)
    (σ : ℕ → Bool) (n : ℕ) :
    stays σ n = n - switches σ n ∧
      -Real.logb 2 ((∏ t ∈ range n, fwdMix halfPrior f (shareKernel α) t : ℚ) : ℝ) ≤
        -∑ t ∈ range n, Real.logb 2 (f (σ t) t : ℝ) + 1 +
          switches σ n * -Real.logb 2 (α : ℝ) + stays σ n * -Real.logb 2 ((1 - α : ℚ) : ℝ) := by
  refine ⟨by have := stays_add_switches σ n; omega, ?_⟩
  have hT := shareKernel_stochastic hα0.le hα1.le
  have hTpos : ∀ t < n, 0 < shareKernel α (σ t) (σ (t + 1)) := fun t _ => by
    unfold shareKernel; split_ifs <;> linarith
  have h := (forward_dominance halfPrior_isPrior hf hT σ n).2.2 (by norm_num [halfPrior]) hTpos
  have hprodT : ∑ t ∈ range n, Real.logb 2 (shareKernel α (σ t) (σ (t + 1)) : ℝ) =
      stays σ n * Real.logb 2 ((1 - α : ℚ) : ℝ) + switches σ n * Real.logb 2 (α : ℝ) := by
    rw [← Real.logb_prod _ _ fun t ht => by exact_mod_cast (hTpos t (mem_range.mp ht)).ne']
    have e : ∏ t ∈ range n, ((shareKernel α (σ t) (σ (t + 1)) : ℚ) : ℝ) =
        ((1 - α : ℚ) : ℝ) ^ stays σ n * (α : ℝ) ^ switches σ n := by
      rw [← Rat.cast_prod, share_prod]; push_cast; ring
    have hα1' : (0 : ℝ) < ((1 - α : ℚ) : ℝ) := by exact_mod_cast sub_pos.mpr hα1
    have hα0' : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα0
    rw [e, Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
  have hhalf : Real.logb 2 ((halfPrior (σ 0) : ℚ) : ℝ) = -1 := by
    simp only [halfPrior]
    push_cast
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [hprodT, hhalf] at h
  linarith

/-- [definition] **The share map** `S_α(β) = ((1 − α) β + α)/((1 − α) + α β)`: the fixed share's move
of the two-face ratio after its likelihood step. -/
def shareMap (α x : ℚ) : ℚ := ((1 - α) * x + α) / ((1 - α) + α * x)

theorem shareMap_num_pos {α x : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (hx : 0 < x) :
    0 < (1 - α) * x + α := by
  rcases h0.lt_or_eq with h | h
  · nlinarith
  · subst h; simpa using hx

theorem shareMap_den_pos {α x : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (hx : 0 < x) :
    0 < (1 - α) + α * x := by
  rcases h1.lt_or_eq with h | h
  · nlinarith
  · subst h; simpa using hx

/-- [proved-derived; formal-checked] **`share_ratio_step`: the fixed share's executed step.** From
the prior `½/½` with positive faces and `α ∈ (0, 1)`, the ratio `β_t = F_t(true)/F_t(false)` of the
forward weights steps by the likelihood ratio, then the share map:
`β_(t+1) = S_α(β₊)`, `β₊ = β_t a_t/b_t`; on the dyadic ladder `α = 2^(−j)`,
`S_α(β₊) = ((2^j − 1) β₊ + 1)/((2^j − 1) + β₊)`. -/
theorem share_ratio_step {α : ℚ} (hα0 : 0 < α) (hα1 : α < 1) {f : Bool → ℕ → ℚ}
    (hf : ∀ x t, 0 < f x t) (t : ℕ) :
    fwd halfPrior f (shareKernel α) (t + 1) true / fwd halfPrior f (shareKernel α) (t + 1) false =
        shareMap α (fwd halfPrior f (shareKernel α) t true /
          fwd halfPrior f (shareKernel α) t false * f true t / f false t) ∧
      ∀ j : ℕ, ∀ x : ℚ, 0 < x →
        shareMap ((1 / 2) ^ j) x = ((2 ^ j - 1) * x + 1) / ((2 ^ j - 1) + x) := by
  have hpos : ∀ t x, 0 < fwd halfPrior f (shareKernel α) t x :=
    fwd_pos (fun _ => by norm_num [halfPrior]) hf fun y x => by
      unfold shareKernel; split_ifs <;> linarith
  refine ⟨?_, fun j x hx => ?_⟩
  · have hT := hpos t true
    have hF := hpos t false
    have ha := hf true t
    have hb := hf false t
    rw [fwd_succ, fwd_succ, Fintype.sum_bool, Fintype.sum_bool]
    simp only [shareKernel, shareMap, if_true, Bool.true_eq_false, Bool.false_eq_true, if_false]
    have hd : 0 < (1 - α) + α * (fwd halfPrior f (shareKernel α) t true /
        fwd halfPrior f (shareKernel α) t false * f true t / f false t) :=
      shareMap_den_pos hα0.le hα1.le (by positivity)
    have hd2 : 0 < fwd halfPrior f (shareKernel α) t true * f true t * α +
        fwd halfPrior f (shareKernel α) t false * f false t * (1 - α) := by
      have : 0 < 1 - α := sub_pos.mpr hα1
      positivity
    field_simp
    ring
  · have h2 : (0 : ℚ) < 2 ^ j := by positivity
    have h1 : (1 : ℚ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hd : 0 < (2 ^ j - 1 : ℚ) + x := by linarith
    have hp : (1 / 2 : ℚ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
    rw [shareMap, hp]
    have hd' : 0 < (1 - 1 / 2 ^ j : ℚ) + 1 / 2 ^ j * x := by
      rw [show (1 - 1 / 2 ^ j : ℚ) + 1 / 2 ^ j * x = ((2 ^ j - 1) + x) / 2 ^ j by field_simp]
      positivity
    field_simp

/-- [proved-derived; formal-checked] **`share_log_lipschitz`: the share never amplifies a drift.**
For `α ∈ [0, 1]` and `0 < x ≤ y`, `S_α(y)/S_α(x) ≤ y/x` and `S_α(x)/S_α(y) ≤ y/x`; so
`|log S_α(y) − log S_α(x)| ≤ |log y − log x|` for all positive `x`, `y`: a carried ratio's drift in
`log β` passes the share step at most unchanged. -/
theorem share_log_lipschitz {α : ℚ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (∀ x y : ℚ, 0 < x → x ≤ y →
      shareMap α y / shareMap α x ≤ y / x ∧ shareMap α x / shareMap α y ≤ y / x) ∧
      ∀ x y : ℚ, 0 < x → 0 < y →
        |Real.log (shareMap α y : ℝ) - Real.log (shareMap α x : ℝ)| ≤
          |Real.log (y : ℝ) - Real.log (x : ℝ)| := by
  have hS : ∀ x : ℚ, 0 < x → 0 < shareMap α x := fun x hx =>
    div_pos (shareMap_num_pos h0 h1 hx) (shareMap_den_pos h0 h1 hx)
  have hratio : ∀ x y : ℚ, 0 < x → x ≤ y →
      shareMap α y / shareMap α x ≤ y / x ∧ shareMap α x / shareMap α y ≤ y / x := by
    intro x y hx hxy
    have hy : 0 < y := hx.trans_le hxy
    have nx := shareMap_num_pos h0 h1 hx
    have ny := shareMap_num_pos h0 h1 hy
    have dx := shareMap_den_pos h0 h1 hx
    have dy := shareMap_den_pos h0 h1 hy
    have hu : 0 ≤ 1 - α := sub_nonneg.mpr h1
    constructor
    · rw [shareMap, shareMap, div_div_div_eq, div_le_div_iff₀ (mul_pos dy nx) hx, ← sub_nonneg]
      have key : y * (((1 - α) + α * y) * ((1 - α) * x + α)) -
          ((1 - α) * y + α) * ((1 - α) + α * x) * x =
          (y - x) * ((1 - α) * α * x * y + α * (1 - α) + α ^ 2 * (x + y)) := by ring
      rw [key]
      exact mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
    · rw [shareMap, shareMap, div_div_div_eq, div_le_div_iff₀ (mul_pos dx ny) hx, ← sub_nonneg]
      have key : y * (((1 - α) + α * x) * ((1 - α) * y + α)) -
          ((1 - α) * x + α) * ((1 - α) + α * y) * x =
          (y - x) * ((1 - α) ^ 2 * (x + y) + (1 - α) * α * x * y + α * (1 - α)) := by ring
      rw [key]
      exact mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
  refine ⟨hratio, ?_⟩
  have hlog : ∀ x y : ℚ, 0 < x → x ≤ y →
      |Real.log (shareMap α y : ℝ) - Real.log (shareMap α x : ℝ)| ≤
        |Real.log (y : ℝ) - Real.log (x : ℝ)| := by
    intro x y hx hxy
    have hy : 0 < y := hx.trans_le hxy
    obtain ⟨r1, r2⟩ := hratio x y hx hxy
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    have hSx : (0 : ℝ) < shareMap α x := by exact_mod_cast hS x hx
    have hSy : (0 : ℝ) < shareMap α y := by exact_mod_cast hS y hy
    have hlogxy : Real.log (x : ℝ) ≤ Real.log (y : ℝ) :=
      Real.log_le_log hxR (by exact_mod_cast hxy)
    have l1 : Real.log (shareMap α y : ℝ) - Real.log (shareMap α x : ℝ) ≤
        Real.log (y : ℝ) - Real.log (x : ℝ) := by
      rw [← Real.log_div hSy.ne' hSx.ne', ← Real.log_div hyR.ne' hxR.ne']
      exact Real.log_le_log (div_pos hSy hSx) (by exact_mod_cast r1)
    have l2 : Real.log (shareMap α x : ℝ) - Real.log (shareMap α y : ℝ) ≤
        Real.log (y : ℝ) - Real.log (x : ℝ) := by
      rw [← Real.log_div hSx.ne' hSy.ne', ← Real.log_div hyR.ne' hxR.ne']
      exact Real.log_le_log (div_pos hSx hSy) (by exact_mod_cast r2)
    rw [abs_of_nonneg (sub_nonneg.mpr hlogxy)]
    exact abs_le.mpr ⟨by linarith, l1⟩
  intro x y hx hy
  rcases le_total x y with h | h
  · exact hlog x y hx h
  · rw [abs_sub_comm, abs_sub_comm (Real.log (y : ℝ))]
    exact hlog y x hy h

end TwoFaces

/-! ## 2. The landmark tree with own weights: node-local mixing -/

section Own

universe u

variable {Ltr : Type u} [Fintype Ltr] [DecidableEq Ltr]

/-! The tree over own weights (`Tree.ownWeight`, `ownSplit`, `ownLik`, `ownWeight_pos`,
`ownLik_pos`, `own_mixture_over_trees`, `own_kraft_and_dominance`, `ownWeight_kt`, `ownLik_kt`,
`ownWeight_one`) is stated once in `Tree`, sections 4 and 5: it is every node law's weighting
(Decision 39), and the stop law's is its case at KT. Node-local mixing reads it here. -/

omit [DecidableEq Ltr] in
/-- The likelihood of a product of own weights is the product of their likelihoods. -/
theorem ownLik_mul (E G : List Ltr → ℚ) : ∀ m s (S : PrunedTree Ltr m),
    ownLik (fun s => E s * G s) m s S = ownLik E m s S * ownLik G m s S
  | 0, _, _ => rfl
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [ownLik, Option.elim]
    | some f => simp only [ownLik, Option.elim, ownLik_mul E G m, Finset.prod_mul_distrib]

omit [DecidableEq Ltr] in
/-- The likelihood of a pruned tree is monotone in nonnegative own weights. -/
theorem ownLik_mono {E G : List Ltr → ℚ} (hG : ∀ s, 0 ≤ G s) (hGE : ∀ s, G s ≤ E s) :
    ∀ m s (S : PrunedTree Ltr m), 0 ≤ ownLik G m s S ∧ ownLik G m s S ≤ ownLik E m s S
  | 0, s, _ => ⟨hG s, hGE s⟩
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [ownLik, Option.elim]; exact ⟨hG s, hGE s⟩
    | some f =>
      simp only [ownLik, Option.elim]
      exact ⟨Finset.prod_nonneg fun b _ => (ownLik_mono hG hGE m _ _).1,
        Finset.prod_le_prod (fun b _ => (ownLik_mono hG hGE m _ _).1)
          fun b _ => (ownLik_mono hG hGE m _ _).2⟩

/-- [proved-derived; formal-checked] **`node_local_dominance`: each landmark pays at most `−log₂` of
its prior weight.** With node-local own weights `E_s = Σ_k π_k X_k(s)` (each landmark's sequential
mixture of its faces over its routed digits, `static_mixture`; `π > 0`, `X > 0`), for every pruned
tree `S` and every choice of face at the landmarks `σ`:
`−log₂ W ≤ −log₂ prior_w(S) + Σ_(leaves ℓ) (−log₂ π_(σ ℓ)) − log₂ ∏_(leaves ℓ) X_(σ ℓ)(ℓ)`.
With `Σ_k π_k = 1` the joint prior over pruned trees and leaf choices is complete: at unit face
likelihoods the tree's weight is one (`ownWeight_one`). -/
theorem node_local_dominance {κ : Type*} [Fintype κ] {w : ℕ → ℚ} (hw : StopLaw w)
    (π : κ → ℚ) (X : κ → List Ltr → ℚ) (hπ : ∀ k, 0 < π k) (hX : ∀ k s, 0 < X k s)
    (m : ℕ) (s : List Ltr) :
    (∑ k, π k = 1 → ownWeight w (fun _ => ∑ k, π k * 1) m s = 1) ∧
      ∀ (S : PrunedTree Ltr m) (σ : List Ltr → κ),
        -Real.logb 2 (ownWeight w (fun s => ∑ k, π k * X k s) m s : ℝ) ≤
          -Real.logb 2 (PrunedTree.prior w m s.length S : ℝ) -
            Real.logb 2 (ownLik (fun s => π (σ s)) m s S : ℝ) -
              Real.logb 2 (ownLik (fun s => X (σ s) s) m s S : ℝ) := by
  refine ⟨fun h1 => by simp only [mul_one, h1]; exact ownWeight_one w m s, fun S σ => ?_⟩
  set E : List Ltr → ℚ := fun s => ∑ k, π k * X k s with hEdef
  have hE : ∀ s, 0 < E s := fun s => by
    obtain ⟨k⟩ : Nonempty κ := ⟨σ s⟩
    exact Finset.sum_pos (fun k _ => mul_pos (hπ k) (hX k s)) ⟨k, Finset.mem_univ _⟩
  have hGE : ∀ s, π (σ s) * X (σ s) s ≤ E s := fun s =>
    Finset.single_le_sum (f := fun k => π k * X k s)
      (fun k _ => (mul_pos (hπ k) (hX k s)).le) (Finset.mem_univ _)
  have hmono := (ownLik_mono (G := fun s => π (σ s) * X (σ s) s) (E := E)
    (fun s => (mul_pos (hπ _) (hX _ s)).le) hGE m s S).2
  rw [ownLik_mul] at hmono
  have hπL := ownLik_pos (E := fun s => π (σ s)) (fun s => hπ _) m s S
  have hXL := ownLik_pos (E := fun s => X (σ s) s) (fun s => hX _ s) m s S
  have hpr := PrunedTree.prior_pos hw m s.length S
  have hdom := ((own_kraft_and_dominance hw hE m s).2 S).1
  have hchain : PrunedTree.prior w m s.length S *
      (ownLik (fun s => π (σ s)) m s S * ownLik (fun s => X (σ s) s) m s S) ≤ ownWeight w E m s :=
    (mul_le_mul_of_nonneg_left hmono hpr.le).trans hdom
  have hpos : (0 : ℝ) < ((PrunedTree.prior w m s.length S *
      (ownLik (fun s => π (σ s)) m s S * ownLik (fun s => X (σ s) s) m s S) : ℚ) : ℝ) := by
    exact_mod_cast mul_pos hpr (mul_pos hπL hXL)
  have hR : ((PrunedTree.prior w m s.length S *
      (ownLik (fun s => π (σ s)) m s S * ownLik (fun s => X (σ s) s) m s S) : ℚ) : ℝ) ≤
      ((ownWeight w E m s : ℚ) : ℝ) := by exact_mod_cast hchain
  have hb := neg_logb_le_of_le hpos hR
  push_cast at hb
  rw [Real.logb_mul (by exact_mod_cast hpr.ne') (by positivity),
    Real.logb_mul (by exact_mod_cast hπL.ne') (by exact_mod_cast hXL.ne')] at hb
  linarith

/-- [proved-derived; formal-checked] **`own_face_normalized`: a landmark's own face is a
normalized face.** For `μ ∈ [0, 1]` and positive normalized faces `k` (the KT face) and `x` (the
admitted external face's split), `μ k + (1 − μ) x` is positive and normalized; so the opened path
over own faces is positive and normalized under any stop weights (`path_face_normalized`). -/
theorem own_face_normalized {A : Type*} [Fintype A] :
    (∀ (μ : ℚ) (k x : A → ℚ), 0 ≤ μ → μ ≤ 1 → (∀ c, 0 < k c) → ∑ c, k c = 1 →
      (∀ c, 0 < x c) → ∑ c, x c = 1 →
        (∀ c, 0 < μ * k c + (1 - μ) * x c) ∧ ∑ c, (μ * k c + (1 - μ) * x c) = 1) ∧
    ∀ (k x : ℕ → A → ℚ) (μ lam : ℕ → ℚ) (D : ℕ),
      (∀ d ≤ D, ∀ c, 0 < k d c) → (∀ d ≤ D, ∑ c, k d c = 1) →
      (∀ d ≤ D, ∀ c, 0 < x d c) → (∀ d ≤ D, ∑ c, x d c = 1) →
      (∀ d ≤ D, 0 ≤ μ d ∧ μ d ≤ 1) → (∀ d < D, 0 ≤ lam d ∧ lam d ≤ 1) →
      ∀ d ≤ D, (∀ c, 0 < pathFace (fun d c => μ d * k d c + (1 - μ d) * x d c) lam D d c) ∧
        ∑ c, pathFace (fun d c => μ d * k d c + (1 - μ d) * x d c) lam D d c = 1 := by
  have hone : ∀ (μ : ℚ) (k x : A → ℚ), 0 ≤ μ → μ ≤ 1 → (∀ c, 0 < k c) → ∑ c, k c = 1 →
      (∀ c, 0 < x c) → ∑ c, x c = 1 →
        (∀ c, 0 < μ * k c + (1 - μ) * x c) ∧ ∑ c, (μ * k c + (1 - μ) * x c) = 1 := by
    intro μ k x h0 h1 hk hks hx hxs
    refine ⟨fun c => mix_pos h0 h1 (hk c) (hx c), ?_⟩
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hks, hxs]
    ring
  refine ⟨hone, fun k x μ lam D hk hks hx hxs hμ hl => ?_⟩
  exact path_face_normalized _ lam D
    (fun d hd => (hone (μ d) (k d) (x d) (hμ d hd).1 (hμ d hd).2 (hk d hd) (hks d hd) (hx d hd)
      (hxs d hd)).1)
    (fun d hd => (hone (μ d) (k d) (x d) (hμ d hd).1 (hμ d hd).2 (hk d hd) (hks d hd) (hx d hd)
      (hxs d hd)).2) hl

/-- [proved-derived; formal-checked] **`node_local_founding`: an unfounded landmark reads its prior
mixture.** At the founding the KT mass and the external face's likelihood are both `1` (nothing
routed), so the own mixture's weight on KT is its prior `π`, and the landmark's own face is
`π/|A| + (1 − π) x` (KT's empty face is uniform, `ktFace_zero`). On the dyadic ladder
`π = 1 − 2^(−j)` the founding ratio `π/(1 − π)` is `2^j − 1` (`Tree.ladder_founding`). -/
theorem node_local_founding {A : Type*} [Fintype A] [Nonempty A] (π : ℚ) (x : A → ℚ) (c : A) :
    π * ktMass (fun _ : A => 0) / (π * ktMass (fun _ : A => 0) + (1 - π) * 1) = π ∧
      π * ktFace (fun _ : A => 0) c + (1 - π) * x c = π / Fintype.card A + (1 - π) * x c := by
  refine ⟨by rw [ktMass_zero]; ring, ?_⟩
  rw [ktFace_zero]
  ring

/-! The opened-path step over own weights (`Tree.ownLam`, `ownRatio`, `ownLam_mem`,
`ownWeight_off`, `ownSplit_arrive`, `own_weight_step₀`, `own_weight_step`, `own_ratio_step`) is
stated once in `Tree`, section 4. -/

/-! ## 3. The stop-weight mixture per digit tree -/

section StopMixture

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`stop_mixture_per_tree`: each digit tree mixes the declared
stop weights by its own evidence.** For stop-weight laws `w_k` with a prior `π_k > 0`,
`Σ_k π_k = 1`, the digit tree's weight `Σ_k π_k W^(w_k)` is the mixture over (law, pruned tree)
with prior `π_k prior_(w_k)(S)`; those weights sum to one; and for every law `k` and pruned tree `S`,
`−log₂ Σ_k π_k W^(w_k) ≤ −log₂ π_k − log₂ prior_(w_k)(S) − log₂ ∏_(leaves) E`. Its sequential form
is `static_mixture` of the laws' faces, cell by cell in the digit tree. -/
theorem stop_mixture_per_tree [Nonempty A] {κ : Type*} [Fintype κ] {w : κ → ℕ → ℚ}
    (hw : ∀ k, StopLaw (w k)) {π : κ → ℚ} (hπ : ∀ k, 0 < π k) (hπs : ∑ k, π k = 1)
    (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr) :
    ∑ k, π k * stopWeight (w k) N m s =
        ∑ k, ∑ S : PrunedTree Ltr m, π k * PrunedTree.prior (w k) m s.length S * treeLik N m s S ∧
      ∑ k, ∑ S : PrunedTree Ltr m, π k * PrunedTree.prior (w k) m s.length S = 1 ∧
      ∀ k (S : PrunedTree Ltr m),
        -Real.logb 2 ((∑ k, π k * stopWeight (w k) N m s : ℚ) : ℝ) ≤
          -Real.logb 2 (π k : ℝ) - Real.logb 2 (PrunedTree.prior (w k) m s.length S : ℝ) -
            Real.logb 2 (treeLik N m s S : ℝ) := by
  refine ⟨?_, ?_, fun k S => ?_⟩
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [stop_mixture_over_trees (w k) N m s, Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by ring
  · rw [Finset.sum_congr rfl fun k _ => by
      rw [← Finset.mul_sum, PrunedTree.prior_sum (w k) m s.length, mul_one], hπs]
  · have hdom := ((stop_kraft_and_dominance (hw k) N m s).2 S).1
    have hpr := PrunedTree.prior_pos (hw k) m s.length S
    have hL := treeLik_pos N m s S
    have hle : π k * (PrunedTree.prior (w k) m s.length S * treeLik N m s S) ≤
        ∑ k, π k * stopWeight (w k) N m s :=
      (mul_le_mul_of_nonneg_left hdom (hπ k).le).trans
        (Finset.single_le_sum (f := fun k => π k * stopWeight (w k) N m s)
          (fun k _ => (mul_pos (hπ k) (stopWeight_pos (hw k) N m s)).le) (Finset.mem_univ k))
    have hpos : (0 : ℝ) <
        ((π k * (PrunedTree.prior (w k) m s.length S * treeLik N m s S) : ℚ) : ℝ) := by
      exact_mod_cast mul_pos (hπ k) (mul_pos hpr hL)
    have hR : ((π k * (PrunedTree.prior (w k) m s.length S * treeLik N m s S) : ℚ) : ℝ) ≤
        ((∑ k, π k * stopWeight (w k) N m s : ℚ) : ℝ) := by exact_mod_cast hle
    have hb := neg_logb_le_of_le hpos hR
    rw [Rat.cast_mul, Rat.cast_mul, Real.logb_mul (by exact_mod_cast (hπ k).ne')
      (by exact_mod_cast (mul_pos hpr hL).ne'),
      Real.logb_mul (by exact_mod_cast hpr.ne') (by exact_mod_cast hL.ne')] at hb
    linarith

end StopMixture

end Own

section Audit

#print axioms neg_logb_le_of_le
#print axioms fwd_zero
#print axioms fwd_succ
#print axioms fwd_nonneg
#print axioms fwd_pos
#print axioms fwd_sum_succ
#print axioms fwd_sum_pos
#print axioms forward_telescope
#print axioms forward_dominance
#print axioms forward_weight_step
#print axioms forward_executed
#print axioms idKernel_stochastic
#print axioms static_mixture
#print axioms boolPrior_isPrior
#print axioms two_face_prior
#print axioms shareKernel_stochastic
#print axioms stays_add_switches
#print axioms share_prod
#print axioms halfPrior_isPrior
#print axioms fixed_share
#print axioms shareMap_num_pos
#print axioms shareMap_den_pos
#print axioms share_ratio_step
#print axioms share_log_lipschitz
#print axioms ownLik_mul
#print axioms ownLik_mono
#print axioms node_local_dominance
#print axioms own_face_normalized
#print axioms node_local_founding
#print axioms stop_mixture_per_tree

end Audit

end Holonics.Compression.Landmark.Context.LocalWeighing
