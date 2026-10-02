import Holonics.HNN.Ratio
import Holonics.HNN.Ratio.Resolution
import Holonics.Holon.Law.Fisher
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# HNN.Ratio.Certificate: the receiver's step certified in its own Fisher form

[definition; agent-inferred] The receiving map `R` reads a window's readings `z = W x` as bits,
`p_c ∝ 2^(z_c)`, and pays the code length `−log₂ p_t` at each target `t` (`HNN/Ratio.codeLength`).
Its deposit is certified when the code a step moves to is bounded above by a quadratic model and
the model falls. The worst-case model (`HNN/Ratio/Resolution.codeLength_quadratic_upper`) bounds the
code's curvature by `ln 2/2` bits in every class direction, the Hessian bound
`ln 2 (diag p − ppᵀ) ⪯ (ln 2/2) I`. Near a uniform reading over `n` classes the code's own
curvature, the receiver's Fisher form `ln 2·J_p` with `J_p = diag p − ppᵀ`
(`Holon/Law.softmaxJacobian`, `Holon/Law/Fisher`), is about `ln 2/n` per class direction, so the
worst case makes the step about `n/2` times too stiff (the contact-loop record §17). This module
proves the model in the Fisher form itself, with a factor that reads only how far the step spreads
the classes.

**The bound.** With `p = softmax(z)`, `g = p − e_t`, `μ = ⟨p, Δ⟩`, `Var_p(Δ) = Σ p_c (Δ_c − μ)²`
(`faceVariance`, which is `Δᵀ J_p Δ`) and `osc Δ = max Δ − min Δ`:

```text
f(z + Δ) ≤ f(z) + ⟨g, Δ⟩ + (e^(osc Δ)/2) · Var_p(Δ)            (nats, f = −z_t + log Σ e^z)
codeLength(z + Δ) ≤ codeLength(z) + ⟨g, Δ⟩ + (ln 2/2) · 2^(osc Δ) · Var_p(Δ)      (bits, R's chart)
```

[proved-derived; formal-checked] What is proved.

1. **The exponential's remainder** (`exp_remainder_le_of_nonpos`, `exp_remainder_le_of_nonneg`,
   `exp_remainder_le`): `e^x − 1 − x ≤ (x²/2)·e^c` whenever `x ≤ c` and `0 ≤ c`; below zero the
   factor is `1`, above it `e^x`. Both are monotonicity arguments on the whole line.
2. **The log-partition step** (`log_sum_exp_add_le`, `log_sum_exp_add_le_osc`). Writing the moved
   partition as `S·e^μ·Σ p e^(Δ−μ)`, its logarithm is `log S + μ + log T` with
   `log T ≤ T − 1 = Σ p (e^(Δ−μ) − 1 − (Δ − μ))`, and each term is at most
   `p (Δ−μ)²/2 · e^(max Δ − μ)`. The factor is `e^(max Δ − μ) ≤ e^(osc Δ)`, since `μ` lies
   between `min Δ` and `max Δ`. This route needs no integral. Integrating the second derivative
   twice, with each ratio `p′_c/p_c` within `e^(±osc Δ)` and the moved variance within
   `e^(t osc Δ)` of `Var_p`, gives the same factor.
3. **In `R`'s chart** (`codeLength_add_le`, `codeLength_add_le_fisher`, `codeLength_add_le_face`):
   the code length in bits at exponents `f + Δ` is at most the code at `f`, plus `⟨p − e_t, Δ⟩`,
   plus `(ln 2/2)·2^ω·Var_p(Δ)` whenever every pair of classes differs by at most `ω` under `Δ`
   (`Δ_c − Δ_d ≤ ω`). The variance is the Fisher form `Δᵀ J_p Δ`. Read at the face owner
   (`Computation/HolonicAdjointNormalization.face`), the bound has the same first-order term as
   the worst case `HNN/Ratio/Resolution.codeLength_quadratic_upper`, so the two differ only in
   their curvature terms.
4. **The step descends** (`codeLength_step_descends`). For the step `Δ = −η v` with first-order
   decrease `a = ⟨p − e_t, v⟩`, Fisher form `b = Var_p(v)` and the spread capped,
   `η (v_c − v_d) ≤ ω`: if `η · ln 2 · 2^ω · b ≤ a` the code falls by at least `η a/2`.
5. **A window of readings in the linear form** (`window_code_add_le`, `linear_first_order`,
   `window_step_descends`). Over readings `k` with caps `ω_k`, the window's code is bounded by the
   sum of the per-reading bounds. For `Δ_k = (ΔW) x_k` the first-order term is `⟨ΔW, G⟩` with
   `G = Σ_k g_k x_kᵀ`. A step `Δ_k = −η u_k` (for `R`, `u_k = V x_k`) with
   `η (u_k,c − u_k,d) ≤ ω_k` and `η · ln 2 · Σ_k 2^(ω_k) Var_(p_k)(u_k) ≤ Σ_k ⟨g_k, u_k⟩` lowers
   the window's code by at least half its first-order decrease.
6. **The accumulated certificate** (`reading_code_le`, `accumulated_code_le`,
   `bound_statistics`, `statistics_insert`). Each reading `i`, read at its own base point `W_i`,
   bounds its code at any later `W` by the item 3 bound with `Δ_i = (W − W_i) x_i`, provided that
   drift's spread is at most `ω`. Summed over the readings, the bound is read from six running
   statistics alone (`Statistics`): `Σ code_i(W_i)`, `A = Σ x_i x_iᵀ ⊗ J_(p_i)`,
   `b = Σ (p_i − e_(t_i)) x_iᵀ`, `Σ A_i vec W_i`, and the two scalars `Σ ⟨vec W_i, b_i⟩` and
   `Σ vec W_iᵀ A_i vec W_i`:
   `Σ_i code_i(W) ≤ Σ code_i(W_i) + ⟨vec W, b⟩ − Σ⟨vec W_i, b_i⟩ +
   (ln 2/2)·2^ω·(vec Wᵀ A vec W − 2⟨vec W, Σ A_i vec W_i⟩ + Σ vec W_iᵀ A_i vec W_i)`.
   A new reading adds its own statistics (`statistics_insert`), so the certificate keeps no record
   of the readings. The two scalars do not depend on `W`: they fix the bound's value, not its
   minimizer, and a step only needs `A`, `b` and `Σ A_i vec W_i`.
7. **The drift check** (`drift_spread_le`, `accumulated_code_le_of_path`). With every input
   `|x_ij| ≤ X` and `2X` times the path length of `W` since reading `i` at most `ω`, the length
   measured in the row norm `max_c Σ_j |V_cj|` (the operator norm from `ℓ∞` inputs to `ℓ∞`
   logits), the drift's spread is at most `ω`, so the accumulated certificate holds along the path.
8. **In the odometer chart, as the Rust step reads it** (`faceVariance_le_of_mass_le`,
   `face_mass_le_odometer_on_grain`, `codeLength_add_le_chart`, `codeLength_add_le_odometer`).
   If `p_c ≤ κ r_c` then `Var_p ≤ κ Var_r` (the variance is the least second moment over
   centres). On the grain the face's masses are at most `2/(e ln 2) < 17/16` times the odometer
   chart's, so with the spread capped at `1` the curvature term is at most
   `ln 2 · (17/16) · Var_p̃(Δ) ≤ (119/160) Var_p̃(Δ)`. Its double, `(119/80) Var_p̃(Δ)`, is the
   second-derivative bound `hnn::constitution::receiving_fisher_face` reads along the unit step;
   the first-order term here is still the face's `⟨p − e_t, Δ⟩`, while the Rust step pairs the
   odometer covector `p̃ − q`, whose shortfall is `HNN/Ratio/Resolution.odometer_pairing_ratio`.
   The `17/16` holds at the grain representative only. Off the grain the factor is
   `2^(1/L)·2/(e ln 2)`, below `8/7` at `L = 16` (`Resolution.face_mass_le_odometer`,
   `Resolution.odometer_ratio_sixteen`), and the second-derivative constant would be
   `2 ln 2·(8/7) ≤ 8/5`, not `119/80`.
9. **The factored certificate** (`faceVariance_le_centred`, `faceVariance_uniform`,
   `centred_le_weighted`, `factored_reading_code_le`, `factored_accumulated_code_le`,
   `factoredStatistics_insert`, `factored_bound_statistics`, `FactoredStatistics.bound_add`). If
   every mass of the face is at most `μ`, then `Var_p(v) ≤ μ Σ_c (v_c − v̄)²` with `v̄` the
   classes' plain mean. At a uniform face `μ = 1/|A|` and the bound is an equality
   (`faceVariance_uniform`). There `1/|A|` is also the mean zero-sum Fisher eigenvalue `λ̄` of
   `hnn::constitution::receiving_class_metric`, which steps at `2^⌊log₂(1/λ̄)⌋`. That is
   `1/μ = |A|` exactly when `|A|` is a power of two (campaign 1's `256 = 2^8`), and the power of
   two below `|A|` otherwise. With each
   reading's mass bound `μ_i`, item 6's bound holds with `A` replaced by `P₀ ⊗ G`, where `P₀`
   centres over the classes and `G = Σ μ_i x_i x_iᵀ`. Its statistics are `Σ code_i(W_i)`, `b`,
   `Σ⟨vec W_i, b_i⟩`, the feature Gram `G`, the anchor `M = Σ μ_i (cen W_i x_i) x_iᵀ` and the
   scalar `Σ μ_i ‖cen W_i x_i‖²`:
   `Σ_i code_i(W) ≤ Σ code_i(W_i) + ⟨vec W, b⟩ − Σ⟨vec W_i, b_i⟩ +
   (ln 2/2)·2^ω·(⟨cen W, cen W⟩_G − 2⟨cen W, M⟩ + Σ μ_i ‖cen W_i x_i‖²)`.
   Their sizes are the features squared and the classes times the features, not the product of
   the two squared. The bound is a quadratic in `W` with Hessian `ln 2·2^ω·(P₀ ⊗ G)`
   (`FactoredStatistics.bound_add`), so its minimizing step `D` solves
   `cen D · G = M − cen W · G − b/(ln 2·2^ω)` on the centred classes. That is one solve in the
   features, shared by every class. It is looser than item 6 by at most the factor `μ_i/p_ic` in
   each class direction (`centred_le_weighted`), and exact at a uniform face.

[definition] The factor `2^ω` is the price of reading the curvature at the current face instead
of along the whole step: as `ω → 0` the model is the second-order Taylor model
`(ln 2/2) Δᵀ J_p Δ`. Its curvature term `(ln 2/2)·2^ω·Var_p(Δ)` is below the worst case's
`(ln 2/4) Σ Δ_c²` exactly when `2^ω Var_p(Δ) ≤ ½ Σ Δ_c²`; near a uniform face over `n` classes
`Var_p(Δ)` is about `Σ Δ_c²/n`, so the Fisher model wins by about `n/2^(ω+1)`. Both are theorems,
so a certificate may read whichever term is smaller. Hoeffding's bound
(`HNN/Ratio/Resolution.log_mean_exp_sub_mean_le`, `(ln 2/8)·osc²`) reads the spread alone and does
not shrink with the face's variance. The Rust owner of the one-reading certificate is
`hnn::constitution::receiving_fisher_face` (item 8). The accumulated certificate has no Rust owner:
item 6's `A` has the classes times the features squared entries, while item 9's statistics are
the form a Rust owner can keep. That owner, the stored factored statistics with the step solving
item 9's equation, is unbuilt. It belongs to the main line's receiving map and is gated on held-out
code.

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Ratio.Certificate

open Matrix
open Holonics.HNN.Ratio (codeLength two_rpow_eq_exp)
open Holonics.HolonCore (softmaxJacobian softmaxJacobian_quadratic_eq_variance)
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential (face partition)

/-! ## 1. The exponential's second-order remainder -/

section Remainder

/-- [proved-derived; formal-checked] **Below zero the remainder is at most `x²/2`.** -/
theorem exp_remainder_le_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hd : ∀ y, HasDerivAt g (-1 + y + Real.exp (-y)) y := by
    intro y
    have h := ((((hasDerivAt_id y).const_sub 1).add ((hasDerivAt_pow 2 y).div_const 2)).sub
      (hasDerivAt_neg y).exp)
    refine h.congr_deriv ?_
    norm_num
  have hmono : Monotone g := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    fun y => by rw [(hd y).deriv]; linarith [Real.add_one_le_exp (-y)]
  have h := hmono (show (0 : ℝ) ≤ -x by linarith)
  simp only [g, neg_neg, neg_zero, Real.exp_zero] at h
  nlinarith

/-- [proved-derived; formal-checked] **Above zero the remainder is at most `(x²/2) e^x`.** -/
theorem exp_remainder_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp x := by
  let g : ℝ → ℝ := fun y => y ^ 2 / 2 * Real.exp y - Real.exp y + 1 + y
  have hd : ∀ y, HasDerivAt g
      (y * Real.exp y + y ^ 2 / 2 * Real.exp y - Real.exp y + 1) y := by
    intro y
    have h := (((((hasDerivAt_pow 2 y).div_const 2).mul (Real.hasDerivAt_exp y)).sub
      (Real.hasDerivAt_exp y)).add_const 1).add (hasDerivAt_id y)
    refine h.congr_deriv ?_
    norm_num
  have hmono : Monotone g := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    fun y => by
      rw [(hd y).deriv]
      have hpos := Real.exp_pos y
      have hone : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      have key : Real.exp y * (1 - y - y ^ 2 / 2) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left (by nlinarith [Real.add_one_le_exp (-y), sq_nonneg y]) hpos.le
      nlinarith
  have h := hmono hx
  simp only [g, Real.exp_zero] at h
  nlinarith

/-- [proved-derived; formal-checked] **The remainder below a nonnegative ceiling**:
`e^x − 1 − x ≤ (x²/2)·e^c` for `x ≤ c`, `0 ≤ c`. -/
theorem exp_remainder_le {x c : ℝ} (hx : x ≤ c) (hc : 0 ≤ c) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp c := by
  have hsq : 0 ≤ x ^ 2 / 2 := by positivity
  rcases le_total x 0 with h | h
  · have hone : 1 ≤ Real.exp c := by simpa using Real.exp_le_exp.mpr hc
    nlinarith [exp_remainder_le_of_nonpos h]
  · have hmono : Real.exp x ≤ Real.exp c := Real.exp_le_exp.mpr hx
    nlinarith [exp_remainder_le_of_nonneg h]

end Remainder

/-! ## 2. The log-partition step -/

section Partition

variable {ι : Type*} [Fintype ι]

/-- [definition] **The variance of `v` under the face `p`**, `Σ p_c (v_c − ⟨p, v⟩)²`: on the simplex
it is the Fisher form `vᵀ J_p v` (`faceVariance_eq_fisher`). -/
def faceVariance (p v : ι → ℝ) : ℝ := ∑ i, p i * (v i - ∑ j, p j * v j) ^ 2

theorem faceVariance_nonneg (p v : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ faceVariance p v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)

/-- [proved-derived; formal-checked] On the simplex the face variance is the Fisher form. -/
theorem faceVariance_eq_fisher [DecidableEq ι] (p v : ι → ℝ) (h1 : ∑ i, p i = 1) :
    faceVariance p v = v ⬝ᵥ (softmaxJacobian p *ᵥ v) :=
  (softmaxJacobian_quadratic_eq_variance p v h1).symm

/-- [proved-derived; formal-checked] **A scaled direction's variance scales by the square.** -/
theorem faceVariance_smul (p v : ι → ℝ) (η : ℝ) :
    faceVariance p (fun i => η * v i) = η ^ 2 * faceVariance p v := by
  unfold faceVariance
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∑ j, p j * (η * v j) = η * ∑ j, p j * v j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

variable [Nonempty ι]

/-- A face given by its masses is the face owner's softmax at `z`. -/
theorem face_eq_mass (z p : ι → ℝ) (hp : ∀ i, p i = Real.exp (z i) / ∑ j, Real.exp (z j)) :
    p = (face z).mass :=
  funext fun i => by rw [hp i]; rfl

theorem face_nonneg (z p : ι → ℝ) (hp : ∀ i, p i = Real.exp (z i) / ∑ j, Real.exp (z j))
    (i : ι) : 0 ≤ p i := by
  rw [face_eq_mass z p hp]; exact ((face z).positive i).le

theorem face_sum_one (z p : ι → ℝ) (hp : ∀ i, p i = Real.exp (z i) / ∑ j, Real.exp (z j)) :
    ∑ i, p i = 1 := by
  rw [face_eq_mass z p hp]; exact (face z).normalized

/-- [proved-derived; formal-checked] **The log-partition step at the face's own variance.** With
`p = softmax(z)`, `μ = ⟨p, Δ⟩` and `Δ ≤ M` everywhere,
`log Σ e^(z+Δ) ≤ log Σ e^z + μ + (e^(M−μ)/2) Var_p(Δ)`. -/
theorem log_sum_exp_add_le (z Δ p : ι → ℝ)
    (hp : ∀ i, p i = Real.exp (z i) / ∑ j, Real.exp (z j)) {M : ℝ} (hM : ∀ i, Δ i ≤ M) :
    Real.log (∑ i, Real.exp (z i + Δ i)) ≤
      Real.log (∑ i, Real.exp (z i)) + ∑ i, p i * Δ i +
        Real.exp (M - ∑ i, p i * Δ i) / 2 * faceVariance p Δ := by
  set S := ∑ j, Real.exp (z j) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hp0 := face_nonneg z p hp
  have hp1 := face_sum_one z p hp
  have hppos : ∀ i, 0 < p i := fun i => by rw [hp i]; positivity
  unfold faceVariance
  set μ := ∑ j, p j * Δ j with hμ
  have hμM : μ ≤ M := by
    calc μ ≤ ∑ i, p i * M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp0 i)
      _ = M := by rw [← Finset.sum_mul, hp1, one_mul]
  set T := ∑ i, p i * Real.exp (Δ i - μ) with hT
  have hTpos : 0 < T :=
    Finset.sum_pos (fun i _ => mul_pos (hppos i) (Real.exp_pos _)) Finset.univ_nonempty
  have hsplit : ∑ i, Real.exp (z i + Δ i) = S * Real.exp μ * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp i, Real.exp_add, Real.exp_sub]
    field_simp
  have hlog : Real.log (∑ i, Real.exp (z i + Δ i)) = Real.log S + μ + Real.log T := by
    rw [hsplit, Real.log_mul (by positivity) hTpos.ne',
      Real.log_mul hSpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hT1 : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hTpos
  have hcentre : ∑ i, p i * (Δ i - μ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← hμ, sub_self]
  have hrem : T - 1 = ∑ i, p i * (Real.exp (Δ i - μ) - 1 - (Δ i - μ)) := by
    have e : ∀ i, p i * (Real.exp (Δ i - μ) - 1 - (Δ i - μ)) =
        p i * Real.exp (Δ i - μ) - p i - p i * (Δ i - μ) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hcentre, hp1, ← hT]
    ring
  have hbound : ∑ i, p i * (Real.exp (Δ i - μ) - 1 - (Δ i - μ)) ≤
      Real.exp (M - μ) / 2 * ∑ i, p i * (Δ i - μ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := exp_remainder_le (x := Δ i - μ) (c := M - μ) (by linarith [hM i]) (by linarith)
    calc p i * (Real.exp (Δ i - μ) - 1 - (Δ i - μ))
        ≤ p i * ((Δ i - μ) ^ 2 / 2 * Real.exp (M - μ)) := mul_le_mul_of_nonneg_left h (hp0 i)
      _ = Real.exp (M - μ) / 2 * (p i * (Δ i - μ) ^ 2) := by ring
  rw [hlog]
  linarith

/-- [proved-derived; formal-checked] **The log-partition step at the step's spread.** With
`m ≤ Δ ≤ M` everywhere, the factor is at most `e^(M−m)`, the oscillation of `Δ`. -/
theorem log_sum_exp_add_le_osc (z Δ p : ι → ℝ)
    (hp : ∀ i, p i = Real.exp (z i) / ∑ j, Real.exp (z j)) {m M : ℝ} (hm : ∀ i, m ≤ Δ i)
    (hM : ∀ i, Δ i ≤ M) :
    Real.log (∑ i, Real.exp (z i + Δ i)) ≤
      Real.log (∑ i, Real.exp (z i)) + ∑ i, p i * Δ i +
        Real.exp (M - m) / 2 * faceVariance p Δ := by
  have h := log_sum_exp_add_le z Δ p hp hM
  have hp0 := face_nonneg z p hp
  have hp1 := face_sum_one z p hp
  have hmμ : m ≤ ∑ i, p i * Δ i := by
    calc m = ∑ i, p i * m := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ ∑ i, p i * Δ i := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i) (hp0 i)
  have hexp : Real.exp (M - ∑ i, p i * Δ i) ≤ Real.exp (M - m) :=
    Real.exp_le_exp.mpr (by linarith)
  have hV := faceVariance_nonneg p Δ hp0
  nlinarith

end Partition

/-! ## 3. In the receiver's chart: bits -/

section Bits

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- [proved-derived; formal-checked] **The code length's step in `R`'s chart.** With the face
`p_c = 2^(f_c)/Σ 2^f` and a step whose classes differ pairwise by at most `ω`,
`codeLength (f + Δ) t ≤ codeLength f t + ⟨p − e_t, Δ⟩ + (ln 2/2)·2^ω·Var_p(Δ)`. -/
theorem codeLength_add_le [DecidableEq ι] (f Δ p : ι → ℝ)
    (hp : ∀ c, p c = (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d) {ω : ℝ}
    (hosc : ∀ c d, Δ c - Δ d ≤ ω) (t : ι) :
    codeLength (fun c => f c + Δ c) t ≤ codeLength f t +
      ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * Δ c +
        Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance p Δ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set z : ι → ℝ := fun c => f c * Real.log 2 with hz
  set Δ' : ι → ℝ := fun c => Δ c * Real.log 2 with hΔ'
  have hpz : ∀ c, p c = Real.exp (z c) / ∑ d, Real.exp (z d) := fun c => by
    rw [hp c]; simp only [z, two_rpow_eq_exp]
  obtain ⟨top, -, htop⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty Δ
  have hM : ∀ c, Δ' c ≤ Δ top * Real.log 2 := fun c =>
    mul_le_mul_of_nonneg_right (htop ▸ Finset.le_sup' Δ (Finset.mem_univ c)) hl.le
  have hm : ∀ c, (Δ top - ω) * Real.log 2 ≤ Δ' c := fun c =>
    mul_le_mul_of_nonneg_right (by linarith [hosc top c]) hl.le
  have h := log_sum_exp_add_le_osc z Δ' p hpz hm hM
  have hsum' : ∑ c, (2 : ℝ) ^ (f c + Δ c) = ∑ c, Real.exp (z c + Δ' c) :=
    Finset.sum_congr rfl fun c _ => by rw [two_rpow_eq_exp]; simp only [z, Δ']; ring_nf
  have hsum : ∑ c, (2 : ℝ) ^ f c = ∑ c, Real.exp (z c) :=
    Finset.sum_congr rfl fun c _ => by rw [two_rpow_eq_exp]
  have hfac : Real.exp (Δ top * Real.log 2 - (Δ top - ω) * Real.log 2) = (2 : ℝ) ^ ω := by
    rw [two_rpow_eq_exp]; ring_nf
  have hμ : ∑ c, p c * Δ' c = Real.log 2 * ∑ c, p c * Δ c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by simp only [Δ']; ring
  have hvar : faceVariance p Δ' = Real.log 2 ^ 2 * faceVariance p Δ := by
    have : Δ' = fun c => Real.log 2 * Δ c := funext fun c => by simp only [Δ']; ring
    rw [this, faceVariance_smul]
  have hfirst : ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * Δ c = ∑ c, p c * Δ c - Δ t := by
    simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  rw [hfac, hμ, hvar, ← hsum, ← hsum'] at h
  rw [hfirst]
  simp only [codeLength, Real.logb]
  have key : Real.log (∑ c, (2 : ℝ) ^ (f c + Δ c)) / Real.log 2 ≤
      Real.log (∑ c, (2 : ℝ) ^ f c) / Real.log 2 + ∑ c, p c * Δ c +
        Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance p Δ := by
    rw [div_le_iff₀ hl]
    have e : (Real.log (∑ c, (2 : ℝ) ^ f c) / Real.log 2 + ∑ c, p c * Δ c +
        Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance p Δ) * Real.log 2 =
        Real.log (∑ c, (2 : ℝ) ^ f c) + Real.log 2 * ∑ c, p c * Δ c +
          (2 : ℝ) ^ ω / 2 * (Real.log 2 ^ 2 * faceVariance p Δ) := by
      field_simp
    rw [e]
    exact h
  linarith

/-- [proved-derived; formal-checked] **The same step in the Fisher form**: the curvature term is
`(ln 2/2)·2^ω·Δᵀ J_p Δ`. -/
theorem codeLength_add_le_fisher [DecidableEq ι] (f Δ p : ι → ℝ)
    (hp : ∀ c, p c = (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d) {ω : ℝ}
    (hosc : ∀ c d, Δ c - Δ d ≤ ω) (t : ι) :
    codeLength (fun c => f c + Δ c) t ≤ codeLength f t +
      ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * Δ c +
        Real.log 2 / 2 * (2 : ℝ) ^ ω * (Δ ⬝ᵥ (softmaxJacobian p *ᵥ Δ)) := by
  have hpz : ∀ c, p c = Real.exp (f c * Real.log 2) / ∑ d, Real.exp (f d * Real.log 2) :=
    fun c => by rw [hp c]; simp only [two_rpow_eq_exp]
  rw [← faceVariance_eq_fisher p Δ (face_sum_one _ p hpz)]
  exact codeLength_add_le f Δ p hp hosc t

/-- [proved-derived; formal-checked] **The same step at the face owner.** With the face read as
`face (f · ln 2)`, as in `HNN/Ratio/Resolution.codeLength_quadratic_upper`, the Fisher model has
the worst case's first-order term; only the curvature terms `(ln 2/2)·2^ω·Var_p(Δ)` and
`½ (ln 2/2) Σ Δ_c²` differ. -/
theorem codeLength_add_le_face [DecidableEq ι] (f Δ : ι → ℝ) {ω : ℝ}
    (hosc : ∀ c d, Δ c - Δ d ≤ ω) (t : ι) :
    codeLength (fun c => f c + Δ c) t ≤ codeLength f t +
      ∑ c, ((face fun c => f c * Real.log 2).mass c - if c = t then 1 else 0) * Δ c +
        Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance (face fun c => f c * Real.log 2).mass Δ := by
  have hmass : ∀ c, (face fun c => f c * Real.log 2).mass c =
      (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d := fun c => by
    simp only [face, partition, two_rpow_eq_exp]
  have h := codeLength_add_le f Δ _ hmass hosc t
  simp only [Pi.single_apply] at h
  exact h

/-- [proved-derived; formal-checked] **`R`'s step descends.** For `Δ = −η v` with first-order
decrease `a = ⟨p − e_t, v⟩`, Fisher form `b = Var_p(v)` and spread capped,
`η (v_c − v_d) ≤ ω`: if `η · ln 2 · 2^ω · b ≤ a`, the code falls by at least `η a/2`. -/
theorem codeLength_step_descends [DecidableEq ι] (f v p : ι → ℝ)
    (hp : ∀ c, p c = (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d) {η ω : ℝ} (hη : 0 ≤ η)
    (hosc : ∀ c d, η * (v d - v c) ≤ ω) (t : ι)
    (hstep : η * (Real.log 2 * (2 : ℝ) ^ ω * faceVariance p v) ≤
      ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * v c) :
    codeLength (fun c => f c - η * v c) t ≤ codeLength f t -
      η * (∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * v c) / 2 := by
  have h := codeLength_add_le f (fun c => -η * v c) p hp
    (ω := ω) (fun c d => by have := hosc c d; linarith) t
  have hfun : (fun c => f c + -η * v c) = fun c => f c - η * v c := funext fun c => by ring
  rw [hfun, faceVariance_smul] at h
  have hfirst : ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * (-η * v c) =
      -η * ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * v c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  rw [hfirst] at h
  have hmul := mul_le_mul_of_nonneg_left hstep hη
  nlinarith

end Bits

/-! ## 4. A window of readings in the linear form -/

section Window

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {K X : Type*} [Fintype K] [Fintype X]

/-- [proved-derived; formal-checked] **A window's code under a step**: over readings `k` with
faces `p_k` of exponents `f_k`, targets `t_k` and spreads capped by `ω_k`, the window's code at
`f_k + Δ_k` is at most its code at `f_k` plus the summed first-order term and the summed Fisher
terms. -/
theorem window_code_add_le (f Δ p : K → ι → ℝ) (t : K → ι)
    (hp : ∀ k c, p k c = (2 : ℝ) ^ f k c / ∑ d, (2 : ℝ) ^ f k d) (ω : K → ℝ)
    (hosc : ∀ k c d, Δ k c - Δ k d ≤ ω k) :
    ∑ k, codeLength (fun c => f k c + Δ k c) (t k) ≤ ∑ k, codeLength (f k) (t k) +
      ∑ k, ∑ c, (p k c - (Pi.single (t k) (1 : ℝ) : ι → ℝ) c) * Δ k c +
        Real.log 2 / 2 * ∑ k, (2 : ℝ) ^ ω k * faceVariance (p k) (Δ k) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := codeLength_add_le (f k) (Δ k) (p k) (hp k) (hosc k) (t k)
  linarith

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The linear form's first-order term**: for
`Δ_k = (ΔW) x_k`, `Σ_k ⟨g_k, Δ_k⟩ = ⟨ΔW, G⟩` with `G = Σ_k g_k x_kᵀ`, the window's gradient. -/
theorem linear_first_order (g : K → ι → ℝ) (ΔW : Matrix ι X ℝ) (x : K → X → ℝ) :
    ∑ k, ∑ c, g k c * (ΔW *ᵥ x k) c = ∑ c, ∑ j, ΔW c j * ∑ k, g k c * x k j := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- [proved-derived; formal-checked] **`R`'s window step descends.** For `Δ_k = −η u_k` (for `R`,
`u_k = V x_k`) with each reading's spread capped, `η (u_k,d − u_k,c) ≤ ω_k`, and
`η · ln 2 · Σ_k 2^(ω_k) Var_(p_k)(u_k) ≤ a = Σ_k ⟨p_k − e_(t_k), u_k⟩`, the window's code falls by
at least `η a/2`. -/
theorem window_step_descends (f u p : K → ι → ℝ) (t : K → ι)
    (hp : ∀ k c, p k c = (2 : ℝ) ^ f k c / ∑ d, (2 : ℝ) ^ f k d) {η : ℝ} (ω : K → ℝ)
    (hη : 0 ≤ η) (hosc : ∀ k c d, η * (u k d - u k c) ≤ ω k)
    (hstep : η * (Real.log 2 * ∑ k, (2 : ℝ) ^ ω k * faceVariance (p k) (u k)) ≤
      ∑ k, ∑ c, (p k c - (Pi.single (t k) (1 : ℝ) : ι → ℝ) c) * u k c) :
    ∑ k, codeLength (fun c => f k c - η * u k c) (t k) ≤ ∑ k, codeLength (f k) (t k) -
      η * (∑ k, ∑ c, (p k c - (Pi.single (t k) (1 : ℝ) : ι → ℝ) c) * u k c) / 2 := by
  have h := window_code_add_le f (fun k c => -η * u k c) p t hp ω
    (fun k c d => by have := hosc k c d; linarith)
  have hfun : ∀ k, (fun c => f k c + -η * u k c) = fun c => f k c - η * u k c :=
    fun k => funext fun c => by ring
  simp only [hfun] at h
  have hvar : ∑ k, (2 : ℝ) ^ ω k * faceVariance (p k) (fun c => -η * u k c) =
      η ^ 2 * ∑ k, (2 : ℝ) ^ ω k * faceVariance (p k) (u k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [faceVariance_smul]; ring
  have hfirst : ∑ k, ∑ c, (p k c - (Pi.single (t k) (1 : ℝ) : ι → ℝ) c) * (-η * u k c) =
      -η * ∑ k, ∑ c, (p k c - (Pi.single (t k) (1 : ℝ) : ι → ℝ) c) * u k c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hvar, hfirst] at h
  have hmul := mul_le_mul_of_nonneg_left hstep hη
  nlinarith

end Window

/-! ## 5. The accumulated certificate: every reading at its own base point -/

section Accumulated

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {K X : Type*} [Fintype X]

/-- [definition] **The face in bits**, `p_c = 2^(f_c)/Σ_d 2^(f_d)`, as `R` reads its logits. -/
def bitFace (f : ι → ℝ) : ι → ℝ := fun c => (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d

omit [DecidableEq ι] in
/-- The face in bits is the face owner's softmax at `f · ln 2`, as
`HNN/Ratio/Resolution.codeLength_quadratic_upper` reads it. -/
theorem bitFace_eq_face (f : ι → ℝ) : bitFace f = (face fun c => f c * Real.log 2).mass :=
  funext fun c => by simp only [bitFace, face, partition, two_rpow_eq_exp]

/-- [definition] **A matrix read as a vector**, `vec W (c, j) = W c j`. -/
def vecW (W : Matrix ι X ℝ) : ι × X → ℝ := fun a => W a.1 a.2

/-- [definition] **One reading's Fisher term** `A_i = x_i x_iᵀ ⊗ J_(p_i)` on `vec W`. -/
def readingFisher (x : X → ℝ) (p : ι → ℝ) : Matrix (ι × X) (ι × X) ℝ :=
  fun a b => softmaxJacobian p a.1 b.1 * (x a.2 * x b.2)

/-- [definition] **One reading's gradient** `g_i x_iᵀ` on `vec W`. -/
def readingGrad (g : ι → ℝ) (x : X → ℝ) : ι × X → ℝ := fun a => g a.1 * x a.2

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype X] in
/-- `vec` is linear in the matrix. -/
theorem vecW_sub (W V : Matrix ι X ℝ) : vecW (W - V) = vecW W - vecW V := rfl

omit [Nonempty ι] in
/-- [proved-derived; formal-checked] **The reading's Fisher form on `vec W`**:
`(V x)ᵀ J_p (V x) = vec Vᵀ (x xᵀ ⊗ J_p) vec V`. -/
theorem readingFisher_quadratic (x : X → ℝ) (p : ι → ℝ) (V : Matrix ι X ℝ) :
    (V *ᵥ x) ⬝ᵥ (softmaxJacobian p *ᵥ (V *ᵥ x)) =
      vecW V ⬝ᵥ (readingFisher x p *ᵥ vecW V) := by
  simp only [dotProduct, mulVec, vecW, readingFisher, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The reading's first-order term on `vec W`**:
`⟨g, V x⟩ = ⟨vec V, g xᵀ⟩`. -/
theorem readingGrad_pairing (g : ι → ℝ) (x : X → ℝ) (V : Matrix ι X ℝ) :
    ∑ c, g c * (V *ᵥ x) c = vecW V ⬝ᵥ readingGrad g x := by
  simp only [dotProduct, mulVec, vecW, readingGrad, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype ι] [Nonempty ι] [Fintype X] in
/-- [proved-derived; formal-checked] `x xᵀ ⊗ J_p` is symmetric. -/
theorem readingFisher_transpose (x : X → ℝ) (p : ι → ℝ) :
    (readingFisher x p)ᵀ = readingFisher x p := by
  ext a b
  simp only [Matrix.transpose_apply, readingFisher, softmaxJacobian, Matrix.sub_apply,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  by_cases h : a.1 = b.1
  · rw [h]; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

omit [Nonempty ι] in
/-- [proved-derived; formal-checked] **The drift's Fisher form expanded about the base point**:
`vec(W − W_i)ᵀ A_i vec(W − W_i) = vec Wᵀ A_i vec W − 2 vec Wᵀ A_i vec W_i + vec W_iᵀ A_i vec W_i`. -/
theorem readingFisher_drift (x : X → ℝ) (p : ι → ℝ) (W Wi : Matrix ι X ℝ) :
    vecW (W - Wi) ⬝ᵥ (readingFisher x p *ᵥ vecW (W - Wi)) =
      vecW W ⬝ᵥ (readingFisher x p *ᵥ vecW W) - 2 * (vecW W ⬝ᵥ (readingFisher x p *ᵥ vecW Wi)) +
        vecW Wi ⬝ᵥ (readingFisher x p *ᵥ vecW Wi) := by
  have hsym : vecW Wi ⬝ᵥ (readingFisher x p *ᵥ vecW W) =
      vecW W ⬝ᵥ (readingFisher x p *ᵥ vecW Wi) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, readingFisher_transpose, dotProduct_comm]
  rw [vecW_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym]
  ring

/-- [definition] **The statistics a running certificate stores**: the summed code at the base
points, the Fisher term `A = Σ x_i x_iᵀ ⊗ J_(p_i)`, the gradient `b = Σ (p_i − e_(t_i)) x_iᵀ`, the
anchor `Σ A_i vec W_i`, and two scalars, `Σ ⟨vec W_i, b_i⟩` and `Σ vec W_iᵀ A_i vec W_i`. Their
size does not grow with the readings. -/
@[ext] structure Statistics (ι X : Type*) where
  code : ℝ
  gram : Matrix (ι × X) (ι × X) ℝ
  grad : ι × X → ℝ
  anchor : ι × X → ℝ
  gradAnchor : ℝ
  anchorEnergy : ℝ

instance : Add (Statistics ι X) :=
  ⟨fun S T => ⟨S.code + T.code, S.gram + T.gram, S.grad + T.grad, S.anchor + T.anchor,
    S.gradAnchor + T.gradAnchor, S.anchorEnergy + T.anchorEnergy⟩⟩

/-- [definition] **One reading's statistics**, read at its own base point `W_i`. -/
def readingStatistics (x : X → ℝ) (t : ι) (Wi : Matrix ι X ℝ) : Statistics ι X :=
  let p := bitFace (Wi *ᵥ x)
  let g : ι → ℝ := fun c => p c - if c = t then 1 else 0
  ⟨codeLength (Wi *ᵥ x) t, readingFisher x p, readingGrad g x, readingFisher x p *ᵥ vecW Wi,
    vecW Wi ⬝ᵥ readingGrad g x, vecW Wi ⬝ᵥ (readingFisher x p *ᵥ vecW Wi)⟩

/-- [definition] **The statistics of the readings in `s`**, each read at its own base point. -/
def statistics (s : Finset K) (x : K → X → ℝ) (t : K → ι) (Wb : K → Matrix ι X ℝ) :
    Statistics ι X :=
  ⟨∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).code,
    ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).gram,
    ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).grad,
    ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).anchor,
    ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).gradAnchor,
    ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).anchorEnergy⟩

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Fintype X] in
/-- [proved-derived; formal-checked] **The statistics update by addition**: a new reading adds
its own statistics, so the certificate keeps no record of the readings. -/
theorem statistics_insert [DecidableEq K] [Fintype ι] [DecidableEq ι] [Fintype X] (s : Finset K)
    {k : K} (hk : k ∉ s) (x : K → X → ℝ) (t : K → ι) (Wb : K → Matrix ι X ℝ) :
    statistics (insert k s) x t Wb = statistics s x t Wb + readingStatistics (x k) (t k) (Wb k) := by
  ext <;> simp only [statistics, Finset.sum_insert hk] <;> exact add_comm _ _

/-- [definition] **The bound read from the statistics alone**, at a later `W`:
`code + (⟨vec W, b⟩ − Σ⟨vec W_i, b_i⟩) + (ln 2/2)·2^ω·(vec Wᵀ A vec W − 2⟨vec W, Σ A_i vec W_i⟩ +
Σ vec W_iᵀ A_i vec W_i)`. -/
def Statistics.bound (S : Statistics ι X) (ω : ℝ) (W : Matrix ι X ℝ) : ℝ :=
  S.code + (vecW W ⬝ᵥ S.grad - S.gradAnchor) +
    Real.log 2 / 2 * (2 : ℝ) ^ ω *
      (vecW W ⬝ᵥ (S.gram *ᵥ vecW W) - 2 * (vecW W ⬝ᵥ S.anchor) + S.anchorEnergy)

omit [Nonempty ι] in
/-- [proved-derived; formal-checked] **The bound is additive in the statistics.** -/
theorem bound_statistics (s : Finset K) (x : K → X → ℝ) (t : K → ι) (Wb : K → Matrix ι X ℝ)
    (ω : ℝ) (W : Matrix ι X ℝ) :
    (statistics s x t Wb).bound ω W = ∑ k ∈ s, (readingStatistics (x k) (t k) (Wb k)).bound ω W := by
  simp only [Statistics.bound, statistics, sum_mulVec, dotProduct_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_add, mul_sub]

/-- [proved-derived; formal-checked] **One reading at a later `W`**: the per-reading bound
(`codeLength_add_le`) at the reading's own base point `W_i`, with the drift `Δ = (W − W_i) x_i`
of spread at most `ω`, is the bound read from that reading's statistics. -/
theorem reading_code_le (x : X → ℝ) (t : ι) (Wi W : Matrix ι X ℝ) {ω : ℝ}
    (hosc : ∀ c d, ((W - Wi) *ᵥ x) c - ((W - Wi) *ᵥ x) d ≤ ω) :
    codeLength (W *ᵥ x) t ≤ (readingStatistics x t Wi).bound ω W := by
  set p := bitFace (Wi *ᵥ x) with hpdef
  have hp : ∀ c, p c = (2 : ℝ) ^ (Wi *ᵥ x) c / ∑ d, (2 : ℝ) ^ (Wi *ᵥ x) d := fun c => rfl
  have h := codeLength_add_le_fisher (Wi *ᵥ x) ((W - Wi) *ᵥ x) p hp hosc t
  have hW : (fun c => (Wi *ᵥ x) c + ((W - Wi) *ᵥ x) c) = W *ᵥ x := by
    rw [sub_mulVec]; funext c; simp only [Pi.sub_apply]; ring
  rw [hW, readingFisher_quadratic, readingFisher_drift] at h
  have hfirst : ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * ((W - Wi) *ᵥ x) c =
      vecW W ⬝ᵥ readingGrad (fun c => p c - if c = t then 1 else 0) x -
        vecW Wi ⬝ᵥ readingGrad (fun c => p c - if c = t then 1 else 0) x := by
    rw [readingGrad_pairing, vecW_sub, sub_dotProduct]
    simp only [Pi.single_apply]
  rw [hfirst] at h
  simp only [Statistics.bound, readingStatistics]
  linarith

/-- [proved-derived; formal-checked] **The accumulated certificate.** Every reading `i ∈ s`, read
at its own base point `W_i`, bounds its code at any later `W` whose drift `(W − W_i) x_i` has spread
at most `ω`; the readings' bounds sum to a bound read from the statistics alone:
`Σ_i code_i(W) ≤ (statistics s).bound ω W`. -/
theorem accumulated_code_le (s : Finset K) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) (W : Matrix ι X ℝ) {ω : ℝ}
    (hosc : ∀ k ∈ s, ∀ c d, ((W - Wb k) *ᵥ x k) c - ((W - Wb k) *ᵥ x k) d ≤ ω) :
    ∑ k ∈ s, codeLength (W *ᵥ x k) (t k) ≤ (statistics s x t Wb).bound ω W := by
  rw [bound_statistics]
  exact Finset.sum_le_sum fun k hk => reading_code_le (x k) (t k) (Wb k) W (hosc k hk)

/-! ### The drift check from the path length -/

/-- [definition] **The row norm** `max_c Σ_j |V_cj|`, the operator norm from `ℓ∞` inputs to `ℓ∞`
logits. -/
def rowNorm (V : Matrix ι X ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun c => ∑ j, |V c j|

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] `|(V x)_c| ≤ ‖V‖ · X` when every `|x_j| ≤ X`. -/
theorem abs_mulVec_le (V : Matrix ι X ℝ) (x : X → ℝ) {Xb : ℝ} (hXb : 0 ≤ Xb)
    (hx : ∀ j, |x j| ≤ Xb) (c : ι) : |(V *ᵥ x) c| ≤ rowNorm V * Xb := by
  calc |(V *ᵥ x) c| = |∑ j, V c j * x j| := rfl
    _ ≤ ∑ j, |V c j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |V c j| * Xb := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |V c j|) * Xb := by rw [Finset.sum_mul]
    _ ≤ rowNorm V * Xb := mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun c => ∑ j, |V c j|) (Finset.mem_univ c)) hXb

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] The row norm is subadditive over a sum of steps. -/
theorem rowNorm_sum_le {S : Type*} (u : Finset S) (D : S → Matrix ι X ℝ) :
    rowNorm (∑ s ∈ u, D s) ≤ ∑ s ∈ u, rowNorm (D s) := by
  refine Finset.sup'_le _ _ fun c _ => ?_
  calc ∑ j, |(∑ s ∈ u, D s) c j| = ∑ j, |∑ s ∈ u, D s c j| := by simp only [Matrix.sum_apply]
    _ ≤ ∑ j, ∑ s ∈ u, |D s c j| := Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s ∈ u, ∑ j, |D s c j| := Finset.sum_comm
    _ ≤ ∑ s ∈ u, rowNorm (D s) := Finset.sum_le_sum fun s _ =>
        Finset.le_sup' (fun c => ∑ j, |D s c j|) (Finset.mem_univ c)

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Fintype X] in
/-- [proved-derived; formal-checked] A path's displacement is the sum of its steps. -/
theorem path_displacement (Wpath : ℕ → Matrix ι X ℝ) {a n : ℕ} (han : a ≤ n) :
    Wpath n - Wpath a = ∑ u ∈ Finset.Ico a n, (Wpath (u + 1) - Wpath u) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]; abel

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The drift check.** With every `|x_j| ≤ X` and the path
length of `W` since the reading at most `ω/(2X)` in the row norm, `2X · Σ_u ‖W_(u+1) − W_u‖ ≤ ω`,
the drift `(W_n − W_a) x` has spread at most `ω`. -/
theorem drift_spread_le (Wpath : ℕ → Matrix ι X ℝ) {a n : ℕ} (han : a ≤ n) (x : X → ℝ)
    {Xb ω : ℝ} (hXb : 0 ≤ Xb) (hx : ∀ j, |x j| ≤ Xb)
    (hlen : 2 * Xb * ∑ u ∈ Finset.Ico a n, rowNorm (Wpath (u + 1) - Wpath u) ≤ ω) (c d : ι) :
    ((Wpath n - Wpath a) *ᵥ x) c - ((Wpath n - Wpath a) *ᵥ x) d ≤ ω := by
  have hV : rowNorm (Wpath n - Wpath a) ≤
      ∑ u ∈ Finset.Ico a n, rowNorm (Wpath (u + 1) - Wpath u) := by
    rw [path_displacement Wpath han]; exact rowNorm_sum_le _ _
  have hc := abs_mulVec_le (Wpath n - Wpath a) x hXb hx c
  have hd := abs_mulVec_le (Wpath n - Wpath a) x hXb hx d
  have hm := mul_le_mul_of_nonneg_right hV hXb
  have h1 := le_abs_self (((Wpath n - Wpath a) *ᵥ x) c)
  have h2 := neg_abs_le (((Wpath n - Wpath a) *ᵥ x) d)
  nlinarith

/-- [proved-derived; formal-checked] **The accumulated certificate along a path.** Readings
`i ∈ s` taken at times `τ_i ≤ n` with base points `W_(τ_i)` on one path, inputs `|x_ij| ≤ X`, and
`2X` times the path length since each reading at most `ω`: the code at `W_n` summed over the
readings is at most the bound read from the statistics. -/
theorem accumulated_code_le_of_path (s : Finset K) (x : K → X → ℝ) (t : K → ι) (τ : K → ℕ)
    (Wpath : ℕ → Matrix ι X ℝ) {n : ℕ} (hτ : ∀ k ∈ s, τ k ≤ n) {Xb ω : ℝ} (hXb : 0 ≤ Xb)
    (hx : ∀ k ∈ s, ∀ j, |x k j| ≤ Xb)
    (hlen : ∀ k ∈ s,
      2 * Xb * ∑ u ∈ Finset.Ico (τ k) n, rowNorm (Wpath (u + 1) - Wpath u) ≤ ω) :
    ∑ k ∈ s, codeLength (Wpath n *ᵥ x k) (t k) ≤
      (statistics s x t fun k => Wpath (τ k)).bound ω (Wpath n) :=
  accumulated_code_le s x t _ _ fun k hk =>
    drift_spread_le Wpath (hτ k hk) (x k) hXb (hx k hk) (hlen k hk)

end Accumulated

/-! ## 6. In the odometer chart: the Rust step's reading -/

section Odometer

variable {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] **A variance about another centre.** With `Σ p = 1`,
`Σ p (v − m)² = Var_p(v) + (⟨p, v⟩ − m)²`. -/
theorem faceVariance_add_sq (p v : ι → ℝ) (hp1 : ∑ i, p i = 1) (m : ℝ) :
    ∑ i, p i * (v i - m) ^ 2 = faceVariance p v + (∑ i, p i * v i - m) ^ 2 := by
  unfold faceVariance
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ j, p j * v j := ⟨_, rfl⟩
  rw [← hμ]
  have e : ∀ (c : ℝ) i, p i * (v i - c) ^ 2 = p i * v i ^ 2 - 2 * c * (p i * v i) + c ^ 2 * p i :=
    fun c i => by ring
  rw [Finset.sum_congr rfl fun i _ => e m i, Finset.sum_congr rfl fun i _ => e μ i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hμ, hp1]
  ring

/-- [proved-derived; formal-checked] **A face's variance through a dominating chart.** With
`Σ p = 1` and `p_c ≤ κ r_c` for every class, `Var_p(v) ≤ κ Var_r(v)`: the variance is
the least second moment over centres, and `r`'s mean is one of them. -/
theorem faceVariance_le_of_mass_le (p r v : ι → ℝ) (hp1 : ∑ i, p i = 1) {κ : ℝ} (hpr : ∀ i, p i ≤ κ * r i) : faceVariance p v ≤ κ * faceVariance r v := by
  have h := faceVariance_add_sq p v hp1 (∑ j, r j * v j)
  have hle : ∑ i, p i * (v i - ∑ j, r j * v j) ^ 2 ≤
      κ * ∑ i, r i * (v i - ∑ j, r j * v j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_right (hpr i) (sq_nonneg (v i - ∑ j, r j * v j))
    linarith
  unfold faceVariance at h hle ⊢
  nlinarith [sq_nonneg (∑ i, p i * v i - ∑ j, r j * v j)]

/-- [proved-standard; formal-checked] **`2/(e ln 2) < 17/16`.** -/
theorem two_div_e_log_two_lt : 2 / (Real.exp 1 * Real.log 2) < 17 / 16 := by
  have he := Real.exp_one_gt_d9
  have hl := Real.log_two_gt_d9
  have hpos : 0 < Real.exp 1 * Real.log 2 := by positivity
  rw [div_lt_iff₀ hpos]
  nlinarith

variable [Nonempty ι]

/-- [proved-derived; formal-checked] **At the grain the face's masses lie within `17/16` of the
odometer chart's.** With every exponent on the grain, `x_c = n_c + k_c/L`, `k_c ≤ L`, the face's
mass is at most `2/(e ln 2) < 17/16` times the odometer mass `p̃_c = ω_c/Σ ω`: the face's weight is
at most the chart's (`face_weight_le_odometer`), and the face's partition at least `e ln 2/2` of the
chart's (`Resolution.odometer_le_face_weight`). Off the grain `Resolution.face_mass_le_odometer`
carries the further `2^(1/L)`. -/
theorem face_mass_le_odometer_on_grain (n : ι → ℤ) (k : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hk : ∀ c, k c ≤ L) (c : ι) :
    (2 : ℝ) ^ ((n c : ℝ) + (k c : ℝ) / L) / ∑ d, (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) ≤
      17 / 16 * (odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) := by
  have hμ : 0 < Real.exp 1 * Real.log 2 / 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have hω : ∀ d, 0 < odometerWeight (n d) (k d) L := fun d => by
    unfold odometerWeight; have := zpow_pos (show (0 : ℝ) < 2 by norm_num) (n d); positivity
  have hW : 0 < ∑ d, odometerWeight (n d) (k d) L :=
    Finset.sum_pos (fun d _ => hω d) Finset.univ_nonempty
  have hA : 0 < ∑ d, (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) :=
    Finset.sum_pos (fun d _ => by positivity) Finset.univ_nonempty
  have hwc := face_weight_le_odometer (n c) hL (hk c)
  have hWA : Real.exp 1 * Real.log 2 / 2 * ∑ d, odometerWeight (n d) (k d) L ≤
      ∑ d, (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d _ => Resolution.odometer_le_face_weight (n d) (k d) L
  have hK : 1 / (Real.exp 1 * Real.log 2 / 2) < 17 / 16 := by
    have := two_div_e_log_two_lt
    rwa [one_div_div]
  rw [div_le_iff₀ hA]
  calc (2 : ℝ) ^ ((n c : ℝ) + (k c : ℝ) / L) ≤ odometerWeight (n c) (k c) L := hwc
    _ = 1 / (Real.exp 1 * Real.log 2 / 2) *
          (odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) *
          (Real.exp 1 * Real.log 2 / 2 * ∑ d, odometerWeight (n d) (k d) L) := by
        field_simp
    _ ≤ 17 / 16 * (odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) *
          ∑ d, (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) := by
        have hq : 0 ≤ odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L :=
          div_nonneg (hω c).le hW.le
        apply mul_le_mul _ hWA (mul_nonneg hμ.le hW.le) (by positivity)
        exact mul_le_mul_of_nonneg_right hK.le hq

/-- [proved-derived; formal-checked] **The bound read in a dominating chart.** If the face's
masses at `f` are at most `κ` times the masses `r` (`p_c ≤ κ r_c`) and the step's spread is at
most `ω ≤ 1`, the curvature term is at most `ln 2 · κ · Var_r(Δ)`:
`code(f + Δ) ≤ code(f) + ⟨p − e_t, Δ⟩ + ln 2 · κ · Var_r(Δ)`. -/
theorem codeLength_add_le_chart [DecidableEq ι] (f Δ r : ι → ℝ) {κ : ℝ}
    (hpr : ∀ c, (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d ≤ κ * r c) {ω : ℝ} (hω : ω ≤ 1)
    (hosc : ∀ c d, Δ c - Δ d ≤ ω) (t : ι) :
    codeLength (fun c => f c + Δ c) t ≤ codeLength f t +
      ∑ c, ((2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d - (Pi.single t (1 : ℝ) : ι → ℝ) c) * Δ c +
        Real.log 2 * κ * faceVariance r Δ := by
  set p : ι → ℝ := fun c => (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d with hpdef
  have h := codeLength_add_le f Δ p (fun c => rfl) hosc t
  have hpz : ∀ c, p c = Real.exp (f c * Real.log 2) / ∑ d, Real.exp (f d * Real.log 2) :=
    fun c => by simp only [hpdef, two_rpow_eq_exp]
  have hp1 := face_sum_one _ p hpz
  have hp0 := face_nonneg _ p hpz
  have hvar := faceVariance_le_of_mass_le p r Δ hp1 hpr
  have h2 : (2 : ℝ) ^ ω ≤ 2 := by
    calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hω
      _ = 2 := Real.rpow_one 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV0 := faceVariance_nonneg p Δ hp0
  have h2ω : 0 < (2 : ℝ) ^ ω := by positivity
  have : Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance p Δ ≤ Real.log 2 * κ * faceVariance r Δ := by
    calc Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance p Δ ≤ Real.log 2 / 2 * 2 * faceVariance p Δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hV0
      _ = Real.log 2 * faceVariance p Δ := by ring
      _ ≤ Real.log 2 * (κ * faceVariance r Δ) := mul_le_mul_of_nonneg_left hvar hl.le
      _ = _ := by ring
  linarith

/-- [proved-derived; formal-checked] **The receiving map's step as the Rust reads it.** On the
grain (`f_c = n_c + k_c/L`, `k_c ≤ L`) with the odometer chart `p̃_c = ω_c/Σ ω` and a step of spread
at most `1`, the curvature term is at most `(119/160) Var_p̃(Δ)`:
`code(f + Δ) ≤ code(f) + ⟨p − e_t, Δ⟩ + (119/160) Var_p̃(Δ)`, from `ln 2 < 7/10` and
`p ≤ (17/16) p̃`. `(119/80) Var_p̃(Δ)` is its second-derivative bound along the ray, the
magnitude part of `hnn::constitution::receiving_fisher_face`'s curvature. -/
theorem codeLength_add_le_odometer [DecidableEq ι] (n : ι → ℤ) (k : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hk : ∀ c, k c ≤ L) (Δ : ι → ℝ) {ω : ℝ} (hω : ω ≤ 1) (hosc : ∀ c d, Δ c - Δ d ≤ ω)
    (t : ι) :
    codeLength (fun c => ((n c : ℝ) + (k c : ℝ) / L) + Δ c) t ≤
      codeLength (fun c => (n c : ℝ) + (k c : ℝ) / L) t +
      ∑ c, ((2 : ℝ) ^ ((n c : ℝ) + (k c : ℝ) / L) /
          ∑ d, (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) - (Pi.single t (1 : ℝ) : ι → ℝ) c) * Δ c +
        119 / 160 * faceVariance
          (fun c => odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) Δ := by
  have hω0 : ∀ d, 0 < odometerWeight (n d) (k d) L := fun d => by
    unfold odometerWeight; have := zpow_pos (show (0 : ℝ) < 2 by norm_num) (n d); positivity
  have hW : 0 < ∑ d, odometerWeight (n d) (k d) L :=
    Finset.sum_pos (fun d _ => hω0 d) Finset.univ_nonempty
  have hr : ∀ c, 0 ≤ odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L :=
    fun c => div_nonneg (hω0 c).le hW.le
  have h := codeLength_add_le_chart (fun c => (n c : ℝ) + (k c : ℝ) / L) Δ _
    (face_mass_le_odometer_on_grain n k hL hk) hω hosc t
  have hV := faceVariance_nonneg
    (fun c => odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) Δ hr
  have hl := Real.log_two_lt_d9
  have : Real.log 2 * (17 / 16) *
      faceVariance (fun c => odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) Δ ≤
      119 / 160 *
      faceVariance (fun c => odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) Δ :=
    mul_le_mul_of_nonneg_right (by nlinarith) hV
  linarith

end Odometer

/-! ## 7. The factored certificate: statistics of the feature and class sizes -/

section Factored

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {K X : Type*} [Fintype X]

/-- [definition] **A matrix centred over the classes**, column by column:
`(cen V)_cj = V_cj − (1/|ι|) Σ_d V_dj`, the zero-sum projection `P₀ = I − 𝟙𝟙ᵀ/|ι|` on its
columns. -/
def cen (V : Matrix ι X ℝ) : Matrix ι X ℝ :=
  fun c j => V c j - (∑ d, V d j) / Fintype.card ι

/-- [definition] **The feature-weighted pairing** `⟨U, V⟩_G = Σ_c Σ_(j,l) U_cj G_jl V_cl`. -/
def gPair (G : Matrix X X ℝ) (U V : Matrix ι X ℝ) : ℝ := ∑ c, ∑ j, ∑ l, U c j * G j l * V c l

/-- [definition] **The entrywise pairing** `⟨U, V⟩ = Σ_(c,j) U_cj V_cj`. -/
def fPair (U V : Matrix ι X ℝ) : ℝ := ∑ c, ∑ j, U c j * V c j

omit [Nonempty ι] [DecidableEq ι] [Fintype X] in
theorem cen_sub (W V : Matrix ι X ℝ) : cen (W - V) = cen W - cen V := by
  ext c j
  simp only [cen, Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

omit [Nonempty ι] [DecidableEq ι] in
/-- Centring commutes with reading: `(V x)_c − (1/|ι|) Σ_d (V x)_d = (cen V · x)_c`. -/
theorem cen_mulVec (V : Matrix ι X ℝ) (x : X → ℝ) (c : ι) :
    (V *ᵥ x) c - (∑ d, (V *ᵥ x) d) / Fintype.card ι = (cen V *ᵥ x) c := by
  simp only [mulVec, dotProduct, cen, sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]

omit [Nonempty ι] [DecidableEq ι] in
theorem gPair_add (G H : Matrix X X ℝ) (U V : Matrix ι X ℝ) :
    gPair (G + H) U V = gPair G U V + gPair H U V := by
  simp only [gPair, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

omit [Nonempty ι] [DecidableEq ι] in
theorem gPair_zero (U V : Matrix ι X ℝ) : gPair (0 : Matrix X X ℝ) U V = 0 := by
  simp [gPair]

omit [Nonempty ι] [DecidableEq ι] in
theorem gPair_sum (s : Finset K) (G : K → Matrix X X ℝ) (U V : Matrix ι X ℝ) :
    gPair (∑ k ∈ s, G k) U V = ∑ k ∈ s, gPair (G k) U V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gPair_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, gPair_add, ih]

omit [Nonempty ι] [DecidableEq ι] in
theorem fPair_sum (s : Finset K) (U : Matrix ι X ℝ) (V : K → Matrix ι X ℝ) :
    fPair U (∑ k ∈ s, V k) = ∑ k ∈ s, fPair U (V k) := by
  simp only [fPair, Matrix.sum_apply, Finset.mul_sum]
  calc ∑ c, ∑ j, ∑ k ∈ s, U c j * V k c j = ∑ c, ∑ k ∈ s, ∑ j, U c j * V k c j :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ c, ∑ j, U c j * V k c j := Finset.sum_comm

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **One reading's pairing is the feature-weighted pairing at
`x xᵀ`**: `Σ_c (U x)_c (V x)_c = ⟨U, V⟩_(x xᵀ)`. -/
theorem gPair_reading (x : X → ℝ) (U V : Matrix ι X ℝ) :
    gPair (vecMulVec x x) U V = ∑ c, (U *ᵥ x) c * (V *ᵥ x) c := by
  simp only [gPair, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The pairing is symmetric at a symmetric weight.** -/
theorem gPair_comm {G : Matrix X X ℝ} (hG : Gᵀ = G) (U V : Matrix ι X ℝ) :
    gPair G U V = gPair G V U := by
  unfold gPair
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  have : G j l = G l j := by rw [← Matrix.transpose_apply G l j, hG]
  rw [this]; ring

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The face's variance within its largest mass.** If every
mass of the face is at most `μ`, `Var_p(v) ≤ μ Σ_c (v_c − v̄)²`, `v̄` the classes' plain mean
(`faceVariance_le_of_mass_le` against the uniform chart, `p_c ≤ (μ|ι|)·(1/|ι|)`). At a uniform
face `μ = 1/|ι|` and it is an equality (`faceVariance_uniform`). -/
theorem faceVariance_le_centred (p v : ι → ℝ) (hp1 : ∑ i, p i = 1) {μ : ℝ}
    (hμ : ∀ i, p i ≤ μ) :
    faceVariance p v ≤ μ * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := faceVariance_le_of_mass_le p (fun _ => 1 / (Fintype.card ι : ℝ)) v hp1
    (κ := μ * Fintype.card ι) fun i => by
      rw [mul_assoc, mul_one_div_cancel hn.ne', mul_one]; exact hμ i
  have hmean : ∑ j, 1 / (Fintype.card ι : ℝ) * v j = (∑ d, v d) / Fintype.card ι := by
    rw [← Finset.mul_sum]; ring
  have hr : faceVariance (fun _ => 1 / (Fintype.card ι : ℝ)) v =
      1 / (Fintype.card ι : ℝ) * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 := by
    unfold faceVariance
    rw [hmean, Finset.mul_sum]
  rw [hr] at h
  calc faceVariance p v ≤ _ := h
    _ = μ * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 := by field_simp

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **At a uniform face the bound is exact**: with every mass
`1/|ι|`, `Var_p(v) = (1/|ι|) Σ_c (v_c − v̄)²`, so `faceVariance_le_centred` at `μ = 1/|ι|` is an
equality. `1/|ι|` is also the uniform face's zero-sum Fisher eigenvalue, the `λ̄` of
`hnn::constitution::receiving_class_metric`. -/
theorem faceVariance_uniform (v : ι → ℝ) :
    faceVariance (fun _ => 1 / (Fintype.card ι : ℝ)) v =
      1 / (Fintype.card ι : ℝ) * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 := by
  have hmean : ∑ j, 1 / (Fintype.card ι : ℝ) * v j = (∑ d, v d) / Fintype.card ι := by
    rw [← Finset.mul_sum]; ring
  unfold faceVariance
  rw [hmean, Finset.mul_sum]

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The plain mean minimizes the plain squares**:
`Σ_c (v_c − v̄)² ≤ Σ_c (v_c − a)²` for every `a`. -/
theorem centred_sq_le (v : ι → ℝ) (a : ℝ) :
    ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 ≤ ∑ c, (v c - a) ^ 2 := by
  set m := (∑ d, v d) / Fintype.card ι with hm
  have hsum : ∑ c, (v c - m) = 0 := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm,
      mul_div_cancel₀ _ hn, sub_self]
  have hexp : ∑ c, (v c - a) ^ 2 =
      ∑ c, (v c - m) ^ 2 + 2 * (m - a) * ∑ c, (v c - m) + ∑ _c : ι, (m - a) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hnn : 0 ≤ ∑ _c : ι, (m - a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hexp, hsum, mul_zero, add_zero]
  linarith

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The factored term is looser by at most `μ/p_c` in each
class direction**: `μ Σ_c (v_c − v̄)² ≤ Σ_c (μ/p_c)·p_c (v_c − E_p v)²`, the right side the face
variance with class `c`'s share raised by `μ/p_c` (`centred_sq_le` at `a = E_p v`). -/
theorem centred_le_weighted (p v : ι → ℝ) (hp : ∀ c, 0 < p c) {μ : ℝ} (hμ : 0 ≤ μ) :
    μ * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 ≤
      ∑ c, μ / p c * (p c * (v c - ∑ d, p d * v d) ^ 2) := by
  refine (mul_le_mul_of_nonneg_left (centred_sq_le v (∑ d, p d * v d)) hμ).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, div_mul_cancel₀ _ (hp c).ne']

/-- [definition] **The factored statistics a running certificate stores**: the summed code at the
base points, the gradient `b = Σ (p_i − e_(t_i)) x_iᵀ` and `Σ⟨vec W_i, b_i⟩` (as in `Statistics`),
the weighted feature Gram `G = Σ μ_i x_i x_iᵀ`, the anchor `M = Σ μ_i (cen W_i x_i) x_iᵀ` and the
scalar `Σ μ_i ‖cen W_i x_i‖²`. Their sizes are the feature square and the classes times the
features, never their product squared. -/
@[ext] structure FactoredStatistics (ι X : Type*) where
  code : ℝ
  grad : ι × X → ℝ
  gradAnchor : ℝ
  gram : Matrix X X ℝ
  anchor : Matrix ι X ℝ
  anchorEnergy : ℝ

instance : Add (FactoredStatistics ι X) :=
  ⟨fun S T => ⟨S.code + T.code, S.grad + T.grad, S.gradAnchor + T.gradAnchor, S.gram + T.gram,
    S.anchor + T.anchor, S.anchorEnergy + T.anchorEnergy⟩⟩

/-- [definition] **One reading's factored statistics**, read at its own base point `W_i` with the
mass bound `μ`. -/
def factoredReading (μ : ℝ) (x : X → ℝ) (t : ι) (Wi : Matrix ι X ℝ) : FactoredStatistics ι X :=
  let p := bitFace (Wi *ᵥ x)
  let g : ι → ℝ := fun c => p c - if c = t then 1 else 0
  ⟨codeLength (Wi *ᵥ x) t, readingGrad g x, vecW Wi ⬝ᵥ readingGrad g x, μ • vecMulVec x x,
    fun c l => μ * (cen Wi *ᵥ x) c * x l, μ * ∑ c, ((cen Wi *ᵥ x) c) ^ 2⟩

/-- [definition] **The factored statistics of the readings in `s`.** -/
def factoredStatistics (s : Finset K) (μ : K → ℝ) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) : FactoredStatistics ι X :=
  ⟨∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).code,
    ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).grad,
    ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).gradAnchor,
    ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).gram,
    ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).anchor,
    ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).anchorEnergy⟩

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Fintype X] in
/-- [proved-derived; formal-checked] **The factored statistics update by addition.** -/
theorem factoredStatistics_insert [DecidableEq K] [Fintype ι] [DecidableEq ι] [Fintype X]
    (s : Finset K) {k : K} (hk : k ∉ s) (μ : K → ℝ) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) :
    factoredStatistics (insert k s) μ x t Wb =
      factoredStatistics s μ x t Wb + factoredReading (μ k) (x k) (t k) (Wb k) := by
  ext <;> simp only [factoredStatistics, Finset.sum_insert hk] <;> exact add_comm _ _

/-- [definition] **The factored bound read from the statistics alone**, at a later `W`:
`code + (⟨vec W, b⟩ − Σ⟨vec W_i, b_i⟩) +
(ln 2/2)·2^ω·(⟨cen W, cen W⟩_G − 2⟨cen W, M⟩ + Σ μ_i ‖cen W_i x_i‖²)`. -/
def FactoredStatistics.bound (S : FactoredStatistics ι X) (ω : ℝ) (W : Matrix ι X ℝ) : ℝ :=
  S.code + (vecW W ⬝ᵥ S.grad - S.gradAnchor) +
    Real.log 2 / 2 * (2 : ℝ) ^ ω *
      (gPair S.gram (cen W) (cen W) - 2 * fPair (cen W) S.anchor + S.anchorEnergy)

omit [Nonempty ι] in
/-- [proved-derived; formal-checked] **The factored bound is additive in the statistics.** -/
theorem factored_bound_statistics (s : Finset K) (μ : K → ℝ) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) (ω : ℝ) (W : Matrix ι X ℝ) :
    (factoredStatistics s μ x t Wb).bound ω W =
      ∑ k ∈ s, (factoredReading (μ k) (x k) (t k) (Wb k)).bound ω W := by
  simp only [FactoredStatistics.bound, factoredStatistics, gPair_sum, fPair_sum, dotProduct_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_add, mul_sub]

omit [Nonempty ι] in
/-- [proved-derived; formal-checked] **The stored Gram is symmetric.** -/
theorem factoredStatistics_gram_symm (s : Finset K) (μ : K → ℝ) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) : (factoredStatistics s μ x t Wb).gramᵀ =
      (factoredStatistics s μ x t Wb).gram := by
  ext j l
  simp only [factoredStatistics, factoredReading, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- [proved-derived; formal-checked] **One reading at a later `W`, factored.** If every mass of the
reading's face at its base point is at most `μ` and the drift `(W − W_i) x_i` has spread at most
`ω`, its code at `W` is at most the bound read from its factored statistics: the Fisher term
`Var_p(Δ)` is at most `μ ‖cen Δ‖²` (`faceVariance_le_centred`), and `cen Δ = cen W x − cen W_i x`
expands into the stored Gram, anchor and energy. -/
theorem factored_reading_code_le (μ : ℝ) (x : X → ℝ) (t : ι) (Wi W : Matrix ι X ℝ) {ω : ℝ}
    (hμ : ∀ c, bitFace (Wi *ᵥ x) c ≤ μ)
    (hosc : ∀ c d, ((W - Wi) *ᵥ x) c - ((W - Wi) *ᵥ x) d ≤ ω) :
    codeLength (W *ᵥ x) t ≤ (factoredReading μ x t Wi).bound ω W := by
  set p := bitFace (Wi *ᵥ x) with hpdef
  have hp : ∀ c, p c = (2 : ℝ) ^ (Wi *ᵥ x) c / ∑ d, (2 : ℝ) ^ (Wi *ᵥ x) d := fun c => rfl
  have hp1 : ∑ c, p c = 1 := by
    have hpos : 0 < ∑ d, (2 : ℝ) ^ (Wi *ᵥ x) d :=
      Finset.sum_pos (fun d _ => Real.rpow_pos_of_pos (by norm_num) _) Finset.univ_nonempty
    simp only [hp, ← Finset.sum_div, div_self hpos.ne']
  have h := codeLength_add_le (Wi *ᵥ x) ((W - Wi) *ᵥ x) p hp hosc t
  have hW : (fun c => (Wi *ᵥ x) c + ((W - Wi) *ᵥ x) c) = W *ᵥ x := by
    rw [sub_mulVec]; funext c; simp only [Pi.sub_apply]; ring
  rw [hW] at h
  have hvar := faceVariance_le_centred p ((W - Wi) *ᵥ x) hp1 hμ
  have hcen : ∑ c, (((W - Wi) *ᵥ x) c - (∑ d, ((W - Wi) *ᵥ x) d) / Fintype.card ι) ^ 2 =
      gPair (vecMulVec x x) (cen W) (cen W) - 2 * ∑ c, (cen Wi *ᵥ x) c * (cen W *ᵥ x) c +
        ∑ c, ((cen Wi *ᵥ x) c) ^ 2 := by
    have hc : ∀ c, ((W - Wi) *ᵥ x) c - (∑ d, ((W - Wi) *ᵥ x) d) / Fintype.card ι =
        (cen W *ᵥ x) c - (cen Wi *ᵥ x) c := by
      intro c; rw [cen_mulVec, cen_sub, sub_mulVec, Pi.sub_apply]
    simp only [hc, gPair_reading]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hanchor : fPair (cen W) (fun c l => μ * (cen Wi *ᵥ x) c * x l) =
      μ * ∑ c, (cen Wi *ᵥ x) c * (cen W *ᵥ x) c := by
    simp only [fPair]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    generalize (cen Wi *ᵥ x) c = a
    simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgram : gPair (μ • vecMulVec x x) (cen W) (cen W) =
      μ * gPair (vecMulVec x x) (cen W) (cen W) := by
    simp only [gPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have hfirst : ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * ((W - Wi) *ᵥ x) c =
      vecW W ⬝ᵥ readingGrad (fun c => p c - if c = t then 1 else 0) x -
        vecW Wi ⬝ᵥ readingGrad (fun c => p c - if c = t then 1 else 0) x := by
    rw [readingGrad_pairing, vecW_sub, sub_dotProduct]
    simp only [Pi.single_apply]
  rw [hfirst] at h
  have hκ : 0 ≤ Real.log 2 / 2 * (2 : ℝ) ^ ω :=
    mul_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num))
      (Real.rpow_nonneg (by norm_num) _)
  have hle := mul_le_mul_of_nonneg_left hvar hκ
  simp only [FactoredStatistics.bound, factoredReading]
  rw [hgram, hanchor]
  rw [hcen] at hle
  nlinarith

/-- [proved-derived; formal-checked] **The factored accumulated certificate.** Every reading
`i ∈ s`, read at its own base point `W_i` with every face mass at most `μ_i`, bounds its code at
any later `W` whose drift has spread at most `ω`; the bounds sum to one read from the factored
statistics alone: `Σ_i code_i(W) ≤ (factoredStatistics s).bound ω W`. -/
theorem factored_accumulated_code_le (s : Finset K) (μ : K → ℝ) (x : K → X → ℝ) (t : K → ι)
    (Wb : K → Matrix ι X ℝ) (W : Matrix ι X ℝ) {ω : ℝ}
    (hμ : ∀ k ∈ s, ∀ c, bitFace (Wb k *ᵥ x k) c ≤ μ k)
    (hosc : ∀ k ∈ s, ∀ c d, ((W - Wb k) *ᵥ x k) c - ((W - Wb k) *ᵥ x k) d ≤ ω) :
    ∑ k ∈ s, codeLength (W *ᵥ x k) (t k) ≤ (factoredStatistics s μ x t Wb).bound ω W := by
  rw [factored_bound_statistics]
  exact Finset.sum_le_sum fun k hk =>
    factored_reading_code_le (μ k) (x k) (t k) (Wb k) W (hμ k hk) (hosc k hk)

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The factored bound is a quadratic in `W` with Hessian
`(ln 2)·2^ω (P₀ ⊗ G)`.** At a symmetric stored Gram, moving `W` by `D`:
`bound(W + D) = bound(W) + ⟨vec D, b⟩ +
(ln 2/2)·2^ω·(2⟨cen W, cen D⟩_G + ⟨cen D, cen D⟩_G − 2⟨cen D, M⟩)`. So the factored step solves
`cen D · G = M − cen W · G − b/((ln 2)·2^ω)` on the zero-sum classes: the feature Gram's inverse
on the right, the classes untouched, a Kronecker-factored natural step. -/
theorem FactoredStatistics.bound_add (S : FactoredStatistics ι X) (hG : S.gramᵀ = S.gram)
    (ω : ℝ) (W D : Matrix ι X ℝ) :
    S.bound ω (W + D) = S.bound ω W + vecW D ⬝ᵥ S.grad +
      Real.log 2 / 2 * (2 : ℝ) ^ ω *
        (2 * gPair S.gram (cen W) (cen D) + gPair S.gram (cen D) (cen D) -
          2 * fPair (cen D) S.anchor) := by
  have hcen : cen (W + D) = cen W + cen D := by
    ext c j; simp only [cen, Matrix.add_apply, Finset.sum_add_distrib]; ring
  have hvec : vecW (W + D) = vecW W + vecW D := rfl
  have hbil : gPair S.gram (cen W + cen D) (cen W + cen D) =
      gPair S.gram (cen W) (cen W) + gPair S.gram (cen W) (cen D) +
        gPair S.gram (cen D) (cen W) + gPair S.gram (cen D) (cen D) := by
    simp only [gPair, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hf : fPair (cen W + cen D) S.anchor = fPair (cen W) S.anchor + fPair (cen D) S.anchor := by
    simp only [fPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  simp only [FactoredStatistics.bound]
  rw [hcen, hvec, add_dotProduct, hbil, hf, gPair_comm hG (cen D) (cen W)]
  ring

end Factored

/-! ## Audit -/

#print axioms exp_remainder_le
#print axioms log_sum_exp_add_le
#print axioms log_sum_exp_add_le_osc
#print axioms codeLength_add_le
#print axioms codeLength_add_le_fisher
#print axioms codeLength_add_le_face
#print axioms codeLength_step_descends
#print axioms window_code_add_le
#print axioms linear_first_order
#print axioms window_step_descends
#print axioms bitFace_eq_face
#print axioms readingFisher_quadratic
#print axioms readingFisher_drift
#print axioms statistics_insert
#print axioms bound_statistics
#print axioms reading_code_le
#print axioms accumulated_code_le
#print axioms drift_spread_le
#print axioms accumulated_code_le_of_path
#print axioms faceVariance_le_of_mass_le
#print axioms two_div_e_log_two_lt
#print axioms face_mass_le_odometer_on_grain
#print axioms codeLength_add_le_chart
#print axioms codeLength_add_le_odometer
#print axioms faceVariance_le_centred
#print axioms faceVariance_uniform
#print axioms centred_sq_le
#print axioms centred_le_weighted
#print axioms gPair_reading
#print axioms gPair_comm
#print axioms factoredStatistics_insert
#print axioms factored_bound_statistics
#print axioms factoredStatistics_gram_symm
#print axioms factored_reading_code_le
#print axioms factored_accumulated_code_le
#print axioms FactoredStatistics.bound_add

end Holonics.HNN.Ratio.Certificate
