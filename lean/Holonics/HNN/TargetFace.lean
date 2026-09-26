import Holonics.HNN.LatticeWord
import Holonics.HNN.Ratio

/-!
# HNN.TargetFace: the target's code face, and the receiving locus's exogenous normal law

[definition; agent-inferred] Decision 26 of the step 4 design (`docs/plans/THE_REBUILD.md`,
campaign 1's repair), from the located failure and Sol's derivation. The loss is `ℓ = log R` with
`R = Ĝ_(T←H)`; the real part of its additive chart is the difference of log faces, of which the
covector `p − q` is the codec chart's part (`HNN/Ratio`). The receiving locus's normal law
`W H = B` needs an **exogenous** target: one fixed by the target Holon, not by the map being
deposited. A one-hot target has no finite logit (§1), so the receiver declares a finite,
gauge-fixed rational chart, the target's **code face** `χ_R(T) = m·e_t`, with `m` the least
margin whose face codes the target within the receiver's tolerance of one grain per cell (§2).
The receiving locus then retains the statistic `(H, B)` of the comparisons whose covectors reached
it and executes the exogenous step at its certified chart (§3):

```text
face        p_c = 2^(f_c) / Σ_d 2^(f_d) > 0 for every finite f      (no finite f is one-hot)
margin      (2^m + |A| − 1)^(L_R) ≤ 2^(m L_R + 1)  ⟺  −log₂ p_t ≤ 1/L_R      (exact integers)
statistic   H' = H + F ,  B' = B + T ,  F = Σ w f fᵀ ,  T = Σ w χ_R(T) fᵀ
exogenous   B' H'⁻¹ = W + (T − W F) H'⁻¹ ,   W H = B
chart       W' = W + (T − W F) X̂ ,  W' H' − B' = −(T − W F)(1 − X̂ H')
prior       W_n = W_0 H_0 H_n⁻¹ + T_n H_n⁻¹ ;  T_n = W_* F_n  ⟹  W_n − W_* = (W_0 − W_*) H_0 H_n⁻¹
```

The prox step `HNN/Normal.normal_prox_step` stays the identity of its **proxy**: it is the
exogenous step at the self-referential target `W f + γ g`, whose innovation `T − W F` is the
covector alone (`proxy_target_innovation`), so it never cancels the map's own prediction against
an exterior target. It is kept, unrenamed, for the internal loci.

[proved-derived; formal-checked] What is proved.

1. **The finite-chart obstruction** (`finite_chart_obstruction`, `finite_chart_obstruction_fin`):
   for every finite logit vector `f` (rational, as the receiver's charts are) over at least two
   classes, the owner's face `p ∝ 2^f` (`codeLength_eq_face`) gives every class positive mass,
   every mass is below one, the face is not one-hot, and the target's code length is strictly
   positive. The general form is `positive_section_not_one_hot`.
2. **The margin rule** (`MarginCodes`, `margin_rule_codeLength`): the chart `χ_R(T) = m·e_t` has
   face mass `2^m / (2^m + |A| − 1)` at the target (`codeFace_mass`), and codes the target within
   `1/L_R` bits exactly when `(2^m + (|A| − 1))^(L_R) ≤ 2^(m L_R + 1)` in integers. The margin
   law holds for some `m` at every alphabet and grain (`margin_exists`, from Bernoulli's
   inequality at `2^m ≥ 2 L_R (|A| − 1)`), is upward closed in `m` (`margin_mono`), and is
   antitone in the alphabet and the grain (`margin_anti_alphabet`, `margin_anti_grain`), so the
   least margin `marginLeast` exists, characterizes the law (`marginLeast_spec`) and is monotone
   in `(|A|, L_R)` (`marginLeast_mono`). Campaign 1's receiver (`|A| = 2^8`, `L_R = 2^4`) has
   least margin `13`: `13` satisfies the law and `12` does not, by `decide` on the integers
   (`margin_campaign_one`).
3. **The exogenous normal law** over any field. `exogenous_normal_step`: at a solved locus the
   next solve is `B'H'⁻¹ = W + (T − WF)H'⁻¹`, and it is the only map solving `W'H' = B'`.
   `exogenous_chart_residual` (and its `ℚ` certificate `exogenous_chart_certificate`, in
   `HNN/LatticeWord`'s `rowNorm`): the executed chart step leaves exactly the chart's left
   residual. `exogenousDeposit_solves`: the receiving locus's deposit on its window is solved.
   `prior_weight_identity`, `prior_decay_fixed_target`, `prior_weight_eigen`: the prior's weight
   is `W_0 H_0 H_n⁻¹`; under a fixed exact target it is the whole deviation; at `H_0 = 1` it is
   `1/(1 + λ)` along an eigen-direction of eigenvalue `λ ≥ 0`.
   `normal_statistic_future_sufficient`: the next map is a function of `(H, B)` and the window,
   and `W` alone is not sufficient (`W = 0`, `B = 0`, `H = 1` versus `H = 2`, one sample
   `f = y = 1`: `1/2` versus `1/3`).

[open] Descent of the scored cross-entropy face is **not** claimed. The quadratic objective this
law minimizes is the squared additive-chart log ratio against the declared code face, named as
such. A descent statement needs a relation between `χ_R(T) − W f` and the reached covector
`q − p̃`, which no law here provides; the exposure's exact ordering of code lengths decides the
repair (Decision 26). Owed in #62 ("Step 4 (#73) owed").

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.TargetFace

open Matrix
open Holonics
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.HNN.Ratio (codeLength codeLength_eq_face two_rpow_eq_exp)
open Holonics.HNN.LatticeWord (rowNorm rowNorm_neg rowNorm_mul_le)
open Holonics.HNN.Normal (LocusState Window windowGram windowCovector proxCross_eq)

/-! ## 1. The finite-chart obstruction -/

section Obstruction

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **A positive face is never one-hot.** A receiver section
with positive masses summing to one, over at least two classes, has every mass below one, so it
is not the one-hot target `e_t`. -/
theorem positive_section_not_one_hot [DecidableEq Index] (p : PositiveProbabilitySection Index)
    (t : Index) (hc : ∃ c, c ≠ t) :
    p.mass t < 1 ∧ p.mass ≠ Pi.single t 1 := by
  obtain ⟨c, hct⟩ := hc
  have hlt : p.mass t < 1 := by
    rw [← p.normalized, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    have : 0 < ∑ i ∈ Finset.univ.erase t, p.mass i :=
      Finset.sum_pos (fun i _ => p.positive i) ⟨c, Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩⟩
    linarith
  refine ⟨hlt, fun h => ?_⟩
  have hc0 := congrFun h c
  rw [Pi.single_eq_of_ne hct] at hc0
  exact (p.positive c).ne' hc0

/-- [proved-derived; formal-checked] The owner's face at the potentials `f ln 2` has masses
`2^(f_c) / Σ_d 2^(f_d)`: the receiver's face `p ∝ 2^f`. -/
theorem face_mass_two_rpow [Nonempty Index] (f : Index → ℝ) (c : Index) :
    (face fun c => f c * Real.log 2).mass c = (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d := by
  simp only [face, NormalizedExponential.partition, two_rpow_eq_exp]

/-- [proved-derived; formal-checked] **The finite-chart obstruction.** For every finite rational
logit vector `f` over at least two classes, the receiver's face `p ∝ 2^f`:
* gives every class positive mass;
* gives the target mass below one, so it is not the one-hot target `e_t`;
* leaves the target a strictly positive code length `−log₂ p_t > 0`.

In HNN terms: the one-hot target `q = e_t` is no finite logit's face, so it cannot be the
exogenous side of a normal law on the receiving map's logits; the receiver must declare a finite
chart of the target Holon's face (§2). -/
theorem finite_chart_obstruction [DecidableEq Index] [Nonempty Index] (f : Index → ℚ)
    (t : Index) (hc : ∃ c, c ≠ t) :
    (∀ c, 0 < (face fun c => (f c : ℝ) * Real.log 2).mass c) ∧
      (face fun c => (f c : ℝ) * Real.log 2).mass t < 1 ∧
      (face fun c => (f c : ℝ) * Real.log 2).mass ≠ Pi.single t 1 ∧
      0 < codeLength (fun c => (f c : ℝ)) t := by
  obtain ⟨hlt, hne⟩ := positive_section_not_one_hot (face fun c => (f c : ℝ) * Real.log 2) t hc
  refine ⟨(face _).positive, hlt, hne, ?_⟩
  rw [codeLength_eq_face, neg_pos]
  exact Real.logb_neg (by norm_num) ((face _).positive t) hlt

/-- [proved-derived; formal-checked] **The obstruction on `Fin k`, `k ≥ 2`**: the brief's form of
`finite_chart_obstruction` for an alphabet of `k` classes. -/
theorem finite_chart_obstruction_fin {k : ℕ} [NeZero k] (hk : 2 ≤ k) (f : Fin k → ℚ)
    (t : Fin k) :
    (∀ c, 0 < (face fun c => (f c : ℝ) * Real.log 2).mass c) ∧
      (face fun c => (f c : ℝ) * Real.log 2).mass t < 1 ∧
      (face fun c => (f c : ℝ) * Real.log 2).mass ≠ Pi.single t 1 ∧
      0 < codeLength (fun c => (f c : ℝ)) t := by
  have hc : ∃ c : Fin k, c ≠ t := by
    by_cases h : t.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
  exact finite_chart_obstruction f t hc

end Obstruction

/-! ## 2. The margin rule: the target's code face -/

section Margin

/-- [definition] **The target's code face** `χ_R(T) = m·e_t`: the finite, gauge-fixed chart of
the target Holon's face at the receiver's grain, integral with margin `m`. -/
def codeFace {Index 𝕜 : Type*} [DecidableEq Index] [AddMonoidWithOne 𝕜] (m : ℕ) (t : Index) :
    Index → 𝕜 :=
  Pi.single t (m : 𝕜)

/-- [definition] **The margin law** in exact integers: `(2^m + (|A| − 1))^L ≤ 2^(m L + 1)`. At
`L = L_R` it says the code face with margin `m` codes the target within one grain,
`−log₂ p_t ≤ 1/L_R` (`margin_rule_codeLength`). -/
def MarginCodes (A L m : ℕ) : Prop := (2 ^ m + (A - 1)) ^ L ≤ 2 ^ (m * L + 1)

instance (A L m : ℕ) : Decidable (MarginCodes A L m) := by
  unfold MarginCodes
  infer_instance

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [proved-derived; formal-checked] The partition of the code face:
`Σ_c 2^(χ_c) = 2^m + (|A| − 1)`. -/
theorem codeFace_partition (m : ℕ) (t : Index) :
    ∑ c, (2 : ℝ) ^ (codeFace m t c : ℝ) = (2 : ℝ) ^ m + ((Fintype.card Index - 1 : ℕ) : ℝ) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  have hrest : ∑ c ∈ Finset.univ.erase t, (2 : ℝ) ^ (codeFace m t c : ℝ) =
      ((Finset.univ.erase t).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hct : c ≠ t := (Finset.mem_erase.mp hc).1
    simp [codeFace, Pi.single_eq_of_ne hct]
  rw [hrest, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ]
  simp [codeFace, Real.rpow_natCast]

/-- [proved-derived; formal-checked] **The code face's target mass** is
`p_t = 2^m / (2^m + |A| − 1)`. -/
theorem codeFace_mass [Nonempty Index] (m : ℕ) (t : Index) :
    (face fun c => (codeFace m t c : ℝ) * Real.log 2).mass t =
      (2 : ℝ) ^ m / ((2 : ℝ) ^ m + ((Fintype.card Index - 1 : ℕ) : ℝ)) := by
  rw [face_mass_two_rpow, codeFace_partition]
  simp [codeFace, Real.rpow_natCast]

/-- [proved-derived; formal-checked] **The margin rule.** At a positive grain `L`, the code face
`χ_R(T) = m·e_t` codes the target within the receiver's tolerance of one grain,
`−log₂ p_t ≤ 1/L`, exactly when `(2^m + (|A| − 1))^L ≤ 2^(m L + 1)` in integers. The code length
is the owner's `codeLength` (`−log₂` of the face, `codeLength_eq_face`). -/
theorem margin_rule_codeLength [Nonempty Index] {L : ℕ} (hL : 0 < L) (m : ℕ) (t : Index) :
    MarginCodes (Fintype.card Index) L m ↔ codeLength (codeFace m t) t ≤ 1 / L := by
  set S : ℝ := (2 : ℝ) ^ m + ((Fintype.card Index - 1 : ℕ) : ℝ) with hSdef
  have hS : 0 < S := by positivity
  have hcode : codeLength (codeFace m t) t = -(m : ℝ) + Real.logb 2 S := by
    simp only [codeLength]
    rw [codeFace_partition]
    simp [codeFace, hSdef]
  rw [hcode]
  have h1 : -(m : ℝ) + Real.logb 2 S ≤ 1 / L ↔ Real.logb 2 S ≤ (m : ℝ) + 1 / L := by
    constructor <;> intro h <;> linarith
  rw [h1, Real.logb_le_iff_le_rpow (by norm_num) hS]
  have hLne : L ≠ 0 := hL.ne'
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : ((2 : ℝ) ^ ((m : ℝ) + 1 / L)) ^ L = (2 : ℝ) ^ (m * L + 1) := by
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  rw [← pow_le_pow_iff_left₀ hS.le (by positivity) hLne, hpow, hSdef]
  unfold MarginCodes
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rfl

/-- [proved-derived; formal-checked] **A large margin codes the target** (Bernoulli): if
`N ≥ 2 L r` with `N > 0`, then `(N + r)^L ≤ 2 N^L`. With `x = r/N`, `L x ≤ 1/2`,
`(1 + x)^L (1 − L x) ≤ (1 + x)^L (1 − x)^L = (1 − x²)^L ≤ 1`. -/
theorem margin_of_large {r L N : ℕ} (hN : 2 * L * r ≤ N) (hNpos : 0 < N) :
    (N + r) ^ L ≤ 2 * N ^ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  have hNq : (0 : ℚ) < N := by exact_mod_cast hNpos
  set x : ℚ := r / N with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hLx : (L : ℚ) * x ≤ 1 / 2 := by
    rw [hxdef, show (L : ℚ) * (r / N) = L * r / N by ring, div_le_iff₀ hNq]
    have : (2 * L * r : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have hL1 : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hx1 : x ≤ 1 / 2 := by nlinarith
  have hbern := one_add_mul_le_pow (a := -x) (by linarith) L
  have hprod : (1 + x) ^ L * (1 + -x) ^ L ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 ≤ (1 + x) ^ L := by positivity
  have key : (1 + x) ^ L ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hbern hpos
    nlinarith
  have hscale : ((N + r : ℕ) : ℚ) ^ L = (N : ℚ) ^ L * (1 + x) ^ L := by
    rw [← mul_pow]
    congr 1
    rw [hxdef]
    push_cast
    field_simp
  have hq : ((N + r : ℕ) : ℚ) ^ L ≤ 2 * (N : ℚ) ^ L := by
    rw [hscale]
    have := pow_pos hNq L
    nlinarith
  exact_mod_cast hq

/-- [proved-derived; formal-checked] **Some margin codes the target**, at every alphabet and
grain: `m = 2 L (|A| − 1)` gives `2^m ≥ 2 L (|A| − 1)`. -/
theorem margin_exists (A L : ℕ) : ∃ m, MarginCodes A L m := by
  refine ⟨2 * L * (A - 1), ?_⟩
  unfold MarginCodes
  have hN : 2 * L * (A - 1) ≤ 2 ^ (2 * L * (A - 1)) := Nat.lt_two_pow_self.le
  have h := margin_of_large hN (by positivity)
  have e : 2 ^ (2 * L * (A - 1) * L + 1) = 2 * (2 ^ (2 * L * (A - 1))) ^ L := by
    rw [pow_succ, pow_mul, mul_comm]
  rw [e]
  exact h

/-- [proved-derived; formal-checked] **The margin law is upward closed**: a margin that codes the
target, raised by one, still codes it. -/
theorem margin_succ {A L m : ℕ} (h : MarginCodes A L m) : MarginCodes A L (m + 1) := by
  unfold MarginCodes at *
  calc (2 ^ (m + 1) + (A - 1)) ^ L ≤ (2 * (2 ^ m + (A - 1))) ^ L :=
        Nat.pow_le_pow_left (by rw [pow_succ]; omega) L
    _ = 2 ^ L * (2 ^ m + (A - 1)) ^ L := by rw [mul_pow]
    _ ≤ 2 ^ L * 2 ^ (m * L + 1) := Nat.mul_le_mul_left _ h
    _ = 2 ^ ((m + 1) * L + 1) := by rw [← pow_add]; congr 1; ring

/-- [proved-derived; formal-checked] **The margin law is monotone in `m`.** -/
theorem margin_mono {A L m m' : ℕ} (hm : m ≤ m') (h : MarginCodes A L m) :
    MarginCodes A L m' := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact margin_succ ih

/-- [proved-derived; formal-checked] **A smaller alphabet is coded at the same margin.** -/
theorem margin_anti_alphabet {A A' L m : ℕ} (hA : A ≤ A') (h : MarginCodes A' L m) :
    MarginCodes A L m := by
  unfold MarginCodes at *
  exact (Nat.pow_le_pow_left (by omega) L).trans h

/-- [proved-derived; formal-checked] **A coarser grain is coded at the same margin**: the law at
`L'` gives it at every `L ≤ L'`. -/
theorem margin_anti_grain {A L L' m : ℕ} (hL : L ≤ L') (h : MarginCodes A L' m) :
    MarginCodes A L m := by
  induction L', hL using Nat.le_induction with
  | base => exact h
  | succ n _ ih =>
    apply ih
    unfold MarginCodes at *
    have hN : 0 < 2 ^ m := by positivity
    have hstep : (2 ^ m + (A - 1)) ^ n * 2 ^ m ≤ 2 ^ (m * n + 1) * 2 ^ m := by
      calc (2 ^ m + (A - 1)) ^ n * 2 ^ m ≤ (2 ^ m + (A - 1)) ^ n * (2 ^ m + (A - 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (2 ^ m + (A - 1)) ^ (n + 1) := by rw [pow_succ]
        _ ≤ 2 ^ (m * (n + 1) + 1) := h
        _ = 2 ^ (m * n + 1) * 2 ^ m := by rw [← pow_add]; congr 1; ring
    exact Nat.le_of_mul_le_mul_right hstep hN

/-- [definition] **The least margin** `m(|A|, L)` whose code face codes the target within one
grain. -/
def marginLeast (A L : ℕ) : ℕ := Nat.find (margin_exists A L)

/-- [proved-derived; formal-checked] **The least margin characterizes the law**: it satisfies the
law, and a margin satisfies the law exactly when it is at least the least margin. -/
theorem marginLeast_spec (A L : ℕ) :
    MarginCodes A L (marginLeast A L) ∧ ∀ m, MarginCodes A L m ↔ marginLeast A L ≤ m :=
  ⟨Nat.find_spec (margin_exists A L), fun _ =>
    ⟨fun h => Nat.find_min' _ h, fun h => margin_mono h (Nat.find_spec (margin_exists A L))⟩⟩

/-- [proved-derived; formal-checked] **The least margin is monotone** in the alphabet and the
grain: a larger alphabet or a finer grain never needs a smaller margin. -/
theorem marginLeast_mono {A A' L L' : ℕ} (hA : A ≤ A') (hL : L ≤ L') :
    marginLeast A L ≤ marginLeast A' L' :=
  ((marginLeast_spec A L).2 _).mp
    (margin_anti_alphabet hA (margin_anti_grain hL (marginLeast_spec A' L').1))

/-- [proved-derived; formal-checked] **Campaign 1's margin is `13`** at `|A| = 2^8`,
`L_R = 2^4`: `(2^13 + 255)^16 ≤ 2^209` and `(2^12 + 255)^16 > 2^193`, decided on the integers,
so `m(2^8, 2^4) = 13`. -/
theorem margin_campaign_one :
    MarginCodes (2 ^ 8) (2 ^ 4) 13 ∧ ¬ MarginCodes (2 ^ 8) (2 ^ 4) 12 ∧
      marginLeast (2 ^ 8) (2 ^ 4) = 13 := by
  have h13 : MarginCodes (2 ^ 8) (2 ^ 4) 13 := by unfold MarginCodes; decide
  have h12 : ¬ MarginCodes (2 ^ 8) (2 ^ 4) 12 := by unfold MarginCodes; decide
  refine ⟨h13, h12, ?_⟩
  rw [marginLeast, Nat.find_eq_iff]
  exact ⟨h13, fun n hn hcodes => h12 (margin_mono (by omega) hcodes)⟩

end Margin

/-! ## 3. The exogenous normal law of the receiving locus -/

section Exogenous

variable {𝕜 : Type*} [Field 𝕜] {σ τ : Type*} [Fintype σ] [DecidableEq σ]

/-- [definition] **The exogenous step** executed at a chart `X` of `H'⁻¹`: `W + (T − W F) X`. The
innovation `T − W F` is the window's target cross moment less the map's own prediction of it. -/
def exogenousStep (W : Matrix τ σ 𝕜) (F : Matrix σ σ 𝕜) (T : Matrix τ σ 𝕜)
    (X : Matrix σ σ 𝕜) : Matrix τ σ 𝕜 :=
  W + (T - W * F) * X

/-- [proved-derived; formal-checked] **The exogenous normal step.** At a solved locus `W H = B`,
with the window's Gram `F = Σ w f fᵀ` and target cross moment `T = Σ w χ_R(T) fᵀ`, and
`H' = H + F` invertible:
* the next solve is `B' H'⁻¹ = W + (T − W F) H'⁻¹`, `B' = B + T`;
* it is the only map solving `W' H' = B'`.

The term `−W F` cancels the map's own prediction: the step moves the map only by the part of the
exterior target it does not already predict. -/
theorem exogenous_normal_step {W : Matrix τ σ 𝕜} {H : Matrix σ σ 𝕜} {B : Matrix τ σ 𝕜}
    (hsolve : W * H = B) (F : Matrix σ σ 𝕜) (T : Matrix τ σ 𝕜) (hunit : IsUnit (H + F).det) :
    (B + T) * (H + F)⁻¹ = W + (T - W * F) * (H + F)⁻¹ ∧
      ∀ W' : Matrix τ σ 𝕜, W' * (H + F) = B + T ↔ W' = W + (T - W * F) * (H + F)⁻¹ := by
  have hcross : B + T = W * (H + F) + (T - W * F) := by
    rw [← hsolve, Matrix.mul_add]
    abel
  have h1 : (B + T) * (H + F)⁻¹ = W + (T - W * F) * (H + F)⁻¹ := by
    rw [hcross, Matrix.add_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hunit]
  refine ⟨h1, fun W' => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← h1, ← h, Matrix.mul_nonsing_inv_cancel_right _ _ hunit]
  · rw [h, ← h1, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

/-- [proved-derived; formal-checked] **The exogenous step at a chart keeps an exact receipt.** At a
solved locus `W H = B`, the step executed through any chart `X̂` of `H'⁻¹`,
`W' = W + (T − W F) X̂`, leaves `W' H' − B' = −(T − W F)(1 − X̂ H')`: the chart's left residual
(`HNN/LatticeWord`, Decision 24), released and reported with the deposit. -/
theorem exogenous_chart_residual {W : Matrix τ σ 𝕜} {H : Matrix σ σ 𝕜} {B : Matrix τ σ 𝕜}
    (hsolve : W * H = B) (F : Matrix σ σ 𝕜) (T : Matrix τ σ 𝕜) (Xh : Matrix σ σ 𝕜) :
    exogenousStep W F T Xh * (H + F) - (B + T) = -((T - W * F) * (1 - Xh * (H + F))) := by
  unfold exogenousStep
  rw [← hsolve]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

/-- [proved-derived; formal-checked] **The exogenous step's certificate** over `ℚ`:
`‖W'H' − B'‖∞ ≤ ‖T − W F‖∞ · ‖1 − X̂H'‖∞`, in `HNN/LatticeWord`'s exact `rowNorm`. -/
theorem exogenous_chart_certificate [Fintype τ] {W : Matrix τ σ ℚ} {H : Matrix σ σ ℚ}
    {B : Matrix τ σ ℚ} (hsolve : W * H = B) (F : Matrix σ σ ℚ) (T : Matrix τ σ ℚ)
    (Xh : Matrix σ σ ℚ) :
    rowNorm (exogenousStep W F T Xh * (H + F) - (B + T)) ≤
      rowNorm (T - W * F) * rowNorm (1 - Xh * (H + F)) := by
  rw [exogenous_chart_residual hsolve, rowNorm_neg]
  exact rowNorm_mul_le _ _

omit [DecidableEq σ] in
/-- [proved-derived; formal-checked] **The prox step is the exogenous step at the proxy target.**
With `F = w f fᵀ` and the proxy target `T = w (W f + γ g) fᵀ`, the innovation is the covector
alone, `T − W F = w γ g fᵀ`: the proxy cancels the map's own prediction by construction, so
`HNN/Normal.normal_prox_step` and `HNN/LatticeWord.prox_chart_residual` are this law's instance
at a target the map itself supplies, never an exterior one. -/
theorem proxy_target_innovation (W : Matrix τ σ 𝕜) (w γ : 𝕜) (f : σ → 𝕜) (g : τ → 𝕜) :
    w • vecMulVec (W *ᵥ f + γ • g) f - W * (w • vecMulVec f f) = (w * γ) • vecMulVec g f := by
  rw [proxCross_eq, add_sub_cancel_left]

/-- [definition] **The receiving window** of the exogenous law: each reached comparison's weight,
feature and target code face `χ_R(T) = m·e_t`. Its `windowGram` is `F` and its `windowCovector`
(the window's cross moment, here against the target face) is `T`. -/
def targetWindow (m : ℕ) (data : List (𝕜 × (σ → 𝕜) × τ)) [DecidableEq τ] : Window 𝕜 σ τ :=
  data.map fun d => (d.1, d.2.1, codeFace m d.2.2)

/-- [definition] **The receiving locus's exogenous deposit**: the statistic sums over the window,
`(H, B) ← (H + F, B + T)`, and the map is the exogenous step at the exact inverse. The executed
form replaces `(H + F)⁻¹` by the certified chart (`exogenous_chart_residual`). -/
def exogenousDeposit (θ : LocusState 𝕜 σ τ) (data : Window 𝕜 σ τ) : LocusState 𝕜 σ τ where
  map := exogenousStep θ.map (windowGram data) (windowCovector data)
    (θ.gram + windowGram data)⁻¹
  gram := θ.gram + windowGram data
  cross := θ.cross + windowCovector data

/-- [proved-derived; formal-checked] **The exogenous deposit carries the solved state**, and its map
is the solve of its own statistic, `W' = B' H'⁻¹`. -/
theorem exogenousDeposit_solves (θ : LocusState 𝕜 σ τ) (data : Window 𝕜 σ τ)
    (hsolve : θ.map * θ.gram = θ.cross) (hunit : IsUnit (θ.gram + windowGram data).det) :
    (exogenousDeposit θ data).map * (exogenousDeposit θ data).gram =
        (exogenousDeposit θ data).cross ∧
      (exogenousDeposit θ data).map =
        (exogenousDeposit θ data).cross * (exogenousDeposit θ data).gram⁻¹ := by
  obtain ⟨h1, h2⟩ := exogenous_normal_step hsolve (windowGram data) (windowCovector data) hunit
  exact ⟨(h2 _).mpr rfl, h1.symm⟩

/-- [proved-derived; formal-checked] **The prior's weight.** If the locus opened solved at
`B_0 = W_0 H_0` and its statistic after the reached comparisons is `(H_0 + F_n, B_0 + T_n)`, the
solved map is `W_n = W_0 H_0 H_n⁻¹ + T_n H_n⁻¹`: the prior enters only through `W_0 H_0 H_n⁻¹`. -/
theorem prior_weight_identity {W0 : Matrix τ σ 𝕜} {H0 : Matrix σ σ 𝕜} {B0 Wn : Matrix τ σ 𝕜}
    {Fn : Matrix σ σ 𝕜} {Tn : Matrix τ σ 𝕜}
    (h0 : B0 = W0 * H0) (hn : Wn * (H0 + Fn) = B0 + Tn) (hunit : IsUnit (H0 + Fn).det) :
    Wn = W0 * H0 * (H0 + Fn)⁻¹ + Tn * (H0 + Fn)⁻¹ := by
  calc Wn = Wn * (H0 + Fn) * (H0 + Fn)⁻¹ :=
        (Matrix.mul_nonsing_inv_cancel_right _ _ hunit).symm
    _ = _ := by rw [hn, h0, Matrix.add_mul]

/-- [proved-derived; formal-checked] **Under a fixed exact target the prior is the whole
deviation.** If every reached comparison is coded by one map, `T_n = W_* F_n`, then
`W_n − W_* = (W_0 − W_*) H_0 H_n⁻¹`: the solved map leaves `W_*` only by the prior's weight. -/
theorem prior_decay_fixed_target {W0 : Matrix τ σ 𝕜} {H0 : Matrix σ σ 𝕜}
    {B0 Wn Wstar : Matrix τ σ 𝕜} {Fn : Matrix σ σ 𝕜} (h0 : B0 = W0 * H0)
    (hn : Wn * (H0 + Fn) = B0 + Wstar * Fn) (hunit : IsUnit (H0 + Fn).det) :
    Wn - Wstar = (W0 - Wstar) * H0 * (H0 + Fn)⁻¹ := by
  have hid := prior_weight_identity h0 hn hunit
  have hstar : Wstar * H0 * (H0 + Fn)⁻¹ + Wstar * Fn * (H0 + Fn)⁻¹ = Wstar := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_nonsing_inv_cancel_right _ _ hunit]
  rw [hid, Matrix.sub_mul, Matrix.sub_mul, eq_sub_of_add_eq' hstar]
  abel

/-- [proved-derived; formal-checked] **The prior's weight along an eigen-direction.** At the
declared prior Gram `H_0 = 1`, let `v` be an eigenvector of the reached Gram, `F_n v = λ v` with
`λ ≥ 0`, and `H_n = 1 + F_n` invertible. Then:
* `H_n⁻¹ v = (1 + λ)⁻¹ v`;
* the prior's term reads `(W_0 H_0 H_n⁻¹) v = (1 + λ)⁻¹ W_0 v`;
* under a fixed exact target `T_n = W_* F_n`, `(W_n − W_*) v = (1 + λ)⁻¹ (W_0 − W_*) v`.

So the prior's weight in that direction is exactly `1/(1 + λ)`; fourfold growth of that
direction's Gram contribution makes it `1/(1 + 4λ)`. Growth of the total feature energy alone
bounds no single `λ`, so no rate follows from it. -/
theorem prior_weight_eigen {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Fn : Matrix σ σ K} {v : σ → K} {lam : K} (hv : Fn *ᵥ v = lam • v) (hlam : 0 ≤ lam)
    (hunit : IsUnit (1 + Fn).det) :
    (1 + Fn)⁻¹ *ᵥ v = (1 + lam)⁻¹ • v ∧
      (∀ W0 : Matrix τ σ K, (W0 * (1 + Fn)⁻¹) *ᵥ v = (1 + lam)⁻¹ • (W0 *ᵥ v)) ∧
      ∀ W0 Wn Wstar : Matrix τ σ K, Wn * (1 + Fn) = W0 + Wstar * Fn →
        (Wn - Wstar) *ᵥ v = (1 + lam)⁻¹ • ((W0 - Wstar) *ᵥ v) := by
  have hne : (1 + lam) ≠ 0 := by positivity
  have h1 : (1 + Fn) *ᵥ v = (1 + lam) • v := by
    rw [add_mulVec, one_mulVec, hv, add_smul, one_smul]
  have hv' : (1 + lam) • ((1 + Fn)⁻¹ *ᵥ v) = v := by
    rw [← mulVec_smul, ← h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, one_mulVec]
  have key : (1 + Fn)⁻¹ *ᵥ v = (1 + lam)⁻¹ • v := by
    calc (1 + Fn)⁻¹ *ᵥ v = (1 + lam)⁻¹ • ((1 + lam) • ((1 + Fn)⁻¹ *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (1 + lam)⁻¹ • v := by rw [hv']
  have hprior : ∀ W0 : Matrix τ σ K, (W0 * (1 + Fn)⁻¹) *ᵥ v = (1 + lam)⁻¹ • (W0 *ᵥ v) :=
    fun W0 => by rw [← mulVec_mulVec, key, mulVec_smul]
  refine ⟨key, hprior, fun W0 Wn Wstar hn => ?_⟩
  have hdecay := prior_decay_fixed_target (Matrix.mul_one W0).symm hn hunit
  rw [Matrix.mul_one] at hdecay
  rw [hdecay, hprior]

/-- [proved-derived; formal-checked] **`(H, B)` is future-sufficient; the map alone is not.**
* Two solved maps of one statistic, `W₁ H = B = W₂ H`, take the same next map at every future
  window `(F, T)` with `H + F` invertible, namely `(B + T)(H + F)⁻¹`; the next statistic is
  `(H + F, B + T)`. The future solutions are a function of `(H, B)`.
* The map alone is not sufficient: on `ℚ¹`, the states `W = 0, H = 1, B = 0` and
  `W = 0, H = 2, B = 0` are both solved with one map, and one sample `w = f = y = 1`
  (`F = T = f fᵀ`) solves them to `1/2` and `1/3`.

A carried `W` is a solved chart of the statistic, subject to its certificate, never a replacement
for `B`. Retaining `(H, B)` retains no comparison list (`HNN/Normal.normalStatistic_standing`). -/
theorem normal_statistic_future_sufficient {W₁ W₂ : Matrix τ σ 𝕜} {H : Matrix σ σ 𝕜}
    {B : Matrix τ σ 𝕜} (h₁ : W₁ * H = B) (h₂ : W₂ * H = B) :
    (∀ (F : Matrix σ σ 𝕜) (T : Matrix τ σ 𝕜), IsUnit (H + F).det →
      exogenousStep W₁ F T (H + F)⁻¹ = (B + T) * (H + F)⁻¹ ∧
        exogenousStep W₁ F T (H + F)⁻¹ = exogenousStep W₂ F T (H + F)⁻¹) ∧
    ((!![0] : Matrix (Fin 1) (Fin 1) ℚ) * !![1] = !![0] ∧
      (!![0] : Matrix (Fin 1) (Fin 1) ℚ) * !![2] = !![0] ∧
      exogenousStep (!![0] : Matrix (Fin 1) (Fin 1) ℚ) ((1 : ℚ) • vecMulVec ![1] ![1])
          ((1 : ℚ) • vecMulVec ![1] ![1]) (!![1] + (1 : ℚ) • vecMulVec ![1] ![1])⁻¹ = !![1 / 2] ∧
      exogenousStep (!![0] : Matrix (Fin 1) (Fin 1) ℚ) ((1 : ℚ) • vecMulVec ![1] ![1])
          ((1 : ℚ) • vecMulVec ![1] ![1]) (!![2] + (1 : ℚ) • vecMulVec ![1] ![1])⁻¹ = !![1 / 3] ∧
      (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℚ) ≠ !![1 / 3]) := by
  refine ⟨fun F T hunit => ?_, ?_⟩
  · have e₁ := (exogenous_normal_step h₁ F T hunit).1
    have e₂ := (exogenous_normal_step h₂ F T hunit).1
    exact ⟨e₁.symm, e₁.symm.trans e₂⟩
  have hF : (1 : ℚ) • vecMulVec (![1] : Fin 1 → ℚ) ![1] = !![1] := by
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec]
  have h2 : (!![1] : Matrix (Fin 1) (Fin 1) ℚ) + !![1] = !![2] := by
    ext i j; fin_cases i; fin_cases j; norm_num
  have h3 : (!![2] : Matrix (Fin 1) (Fin 1) ℚ) + !![1] = !![3] := by
    ext i j; fin_cases i; fin_cases j; norm_num
  have hinv2 : (!![2] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1 / 2] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j; simp
  have hinv3 : (!![3] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1 / 3] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j; simp
  rw [hF, h2, h3, hinv2, hinv3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp
  · ext i j; fin_cases i; fin_cases j; simp
  · ext i j; fin_cases i; fin_cases j; simp [exogenousStep]
  · ext i j; fin_cases i; fin_cases j; simp [exogenousStep]
  · intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

end Exogenous

section Audit

#print axioms positive_section_not_one_hot
#print axioms face_mass_two_rpow
#print axioms finite_chart_obstruction
#print axioms finite_chart_obstruction_fin
#print axioms codeFace_partition
#print axioms codeFace_mass
#print axioms margin_rule_codeLength
#print axioms margin_of_large
#print axioms margin_exists
#print axioms margin_succ
#print axioms margin_mono
#print axioms margin_anti_alphabet
#print axioms margin_anti_grain
#print axioms marginLeast_spec
#print axioms marginLeast_mono
#print axioms margin_campaign_one
#print axioms exogenous_normal_step
#print axioms exogenous_chart_residual
#print axioms exogenous_chart_certificate
#print axioms proxy_target_innovation
#print axioms exogenousDeposit_solves
#print axioms prior_weight_identity
#print axioms prior_decay_fixed_target
#print axioms prior_weight_eigen
#print axioms normal_statistic_future_sufficient

end Audit

end Holonics.HNN.TargetFace
