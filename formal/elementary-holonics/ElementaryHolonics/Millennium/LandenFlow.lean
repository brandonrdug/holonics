import ElementaryHolonics.Millennium.LandenLattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# LandenFlow: the theta means converge to one along the doubling chart

**The convergent half of Gauss's theta–AGM theorem.**  One step of the scale flow
`t ↦ 2t` is one step of the arithmetic–geometric mean on `(θ₃², θ₄²)`
(`LandenLattice`); this file rides the flow to its fixed point:

* **`theThetaLegsApproachOne`** — both distances to one are bounded by the
  certified geometric tail `2q/(1−q)`, `q = e^{−πt}`;
* **`theDoublingFlowConvergesToOne`** — along `t, 2t, 4t, …` both squared legs
  converge to `1`: the arithmetic–geometric mean of `(θ₃(t)², θ₄(t)²)` is `1`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.LandenFlow

open Real Filter
open Soma.Holonics.Millennium.LandenLattice

/-! ## 0. Plumbing -/

private lemma key_nat {t : ℝ} (ht : 0 < t) (b : ℝ) :
    Summable fun n : ℕ => rexp (-π * t * ((n : ℝ) + b) ^ 2) := by
  have hc : 0 < π * t := by positivity
  have hbound : ∀ n : ℕ, rexp (-π * t * ((n : ℝ) + b) ^ 2)
      ≤ rexp ((π * t) * (1 - 2 * b)) * rexp (-(2 * (π * t))) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_nonneg hc.le (sq_nonneg ((n : ℝ) + b - 1))]
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hbound ?_
  refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

private lemma summable_tail {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => rexp (-π * ((k : ℝ) + 1) ^ 2 * t) :=
  (key_nat ht 1).congr fun k => by congr 1; ring

private lemma summable_pos_side {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => rexp (-π * ((n : ℤ) : ℝ) ^ 2 * t) :=
  (key_nat ht 0).congr fun n => by congr 1; push_cast; ring

private lemma summable_neg_side {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => rexp (-π * (((-(n + 1) : ℤ)) : ℝ) ^ 2 * t) :=
  (key_nat ht 1).congr fun n => by congr 1; push_cast; ring

/-! ## 1. The tail bound -/

private lemma tail_le {t : ℝ} (ht : 1 ≤ t) :
    (∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t)) ≤
      rexp (-π * t) / (1 - rexp (-π * t)) := by
  have ht0 : 0 < t := by linarith
  have hq0 : 0 < rexp (-π * t) := Real.exp_pos _
  have hq1 : rexp (-π * t) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith [pi_pos]
  have hbound : ∀ k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t)
      ≤ rexp (-π * t) * rexp (-π * t) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have h1 : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h2 : (π * t) * ((k : ℝ) + 1) ≤ (π * t) * ((k : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [h2]
  have hgeom : Summable fun k : ℕ => rexp (-π * t) * rexp (-π * t) ^ k :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  calc (∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t))
      ≤ ∑' k : ℕ, rexp (-π * t) * rexp (-π * t) ^ k :=
        (summable_tail ht0).tsum_le_tsum hbound hgeom
    _ = rexp (-π * t) * (1 - rexp (-π * t))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    _ = rexp (-π * t) / (1 - rexp (-π * t)) := by
        rw [div_eq_mul_inv]

/-! ## 2. The legs split at zero -/

set_option maxHeartbeats 1000000 in
private lemma T3_split {t : ℝ} (ht : 0 < t) :
    T3 t = 1 + 2 * ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
  rw [T3, tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * t))
    (summable_pos_side ht) (summable_neg_side ht)]
  have h1 : (∑' n : ℕ, rexp (-π * ((n : ℤ) : ℝ) ^ 2 * t))
      = 1 + ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
    rw [(summable_pos_side ht).tsum_eq_zero_add]
    congr 1
    · show rexp (-π * (((0 : ℕ) : ℤ) : ℝ) ^ 2 * t) = 1
      norm_num
    · refine tsum_congr fun k => ?_
      congr 1
      push_cast
      ring
  have h2 : (∑' n : ℕ, rexp (-π * (((-(n + 1) : ℤ)) : ℝ) ^ 2 * t))
      = ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
    refine tsum_congr fun k => ?_
    congr 1
    push_cast
    ring
  rw [h1, h2]
  ring

private lemma sign_neg_side (k : ℕ) :
    ((-1 : ℝ)) ^ ((-(k + 1) : ℤ)) = (-1 : ℝ) ^ ((k : ℤ) + 1) := by
  have hself : ((-1 : ℝ)) ^ ((k : ℤ) + 1) * (-1) ^ ((k : ℤ) + 1) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    exact Even.neg_one_zpow ⟨(k : ℤ) + 1, rfl⟩
  have h1 : ((-(k + 1) : ℤ)) = -((k : ℤ) + 1) := by push_cast; ring
  rw [h1, zpow_neg]
  exact inv_eq_of_mul_eq_one_left hself

set_option maxHeartbeats 2000000 in
private lemma T4_dist {t : ℝ} (ht : 0 < t) :
    |T4 t - 1| ≤ 2 * ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
  have habs : ∀ (j : ℤ) (r : ℝ), ‖(-1 : ℝ) ^ j * rexp r‖ = rexp r := by
    intro j r
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hposS : Summable fun n : ℕ =>
      (-1 : ℝ) ^ ((n : ℤ)) * rexp (-π * ((n : ℤ) : ℝ) ^ 2 * t) := by
    refine Summable.of_norm ?_
    exact (summable_pos_side ht).congr fun n => (habs _ _).symm
  have hnegS : Summable fun n : ℕ =>
      (-1 : ℝ) ^ ((-(n + 1) : ℤ)) * rexp (-π * (((-(n + 1) : ℤ)) : ℝ) ^ 2 * t) := by
    refine Summable.of_norm ?_
    exact (summable_neg_side ht).congr fun n => (habs _ _).symm
  rw [T4, tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (-1 : ℝ) ^ n * rexp (-π * (n : ℝ) ^ 2 * t)) hposS hnegS]
  set S : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ ((k : ℤ) + 1) * rexp (-π * ((k : ℝ) + 1) ^ 2 * t)
    with hS
  have h1 : (∑' n : ℕ, (-1 : ℝ) ^ ((n : ℤ)) * rexp (-π * ((n : ℤ) : ℝ) ^ 2 * t))
      = 1 + S := by
    rw [hposS.tsum_eq_zero_add]
    congr 1
    · show (-1 : ℝ) ^ (((0 : ℕ) : ℤ)) * rexp (-π * (((0 : ℕ) : ℤ) : ℝ) ^ 2 * t) = 1
      norm_num
    · rw [hS]
      refine tsum_congr fun k => ?_
      have he : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [he]
      congr 1
      congr 1
      push_cast
      ring
  have h2 : (∑' n : ℕ, (-1 : ℝ) ^ ((-(n + 1) : ℤ)) *
      rexp (-π * (((-(n + 1) : ℤ)) : ℝ) ^ 2 * t)) = S := by
    rw [hS]
    refine tsum_congr fun k => ?_
    congr 1
    · exact sign_neg_side k
    · congr 1
      push_cast
      ring
  rw [h1, h2]
  have hsum : Summable fun k : ℕ =>
      (-1 : ℝ) ^ ((k : ℤ) + 1) * rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
    refine Summable.of_norm ?_
    exact (summable_tail ht).congr fun k => (habs _ _).symm
  have hSabs : |S| ≤ ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by
    rw [hS, ← Real.norm_eq_abs]
    have hnrm : Summable fun k : ℕ =>
        ‖(-1 : ℝ) ^ ((k : ℤ) + 1) * rexp (-π * ((k : ℝ) + 1) ^ 2 * t)‖ :=
      (summable_tail ht).congr fun k => (habs _ _).symm
    calc ‖∑' k : ℕ, (-1 : ℝ) ^ ((k : ℤ) + 1) * rexp (-π * ((k : ℝ) + 1) ^ 2 * t)‖
        ≤ ∑' k : ℕ, ‖(-1 : ℝ) ^ ((k : ℤ) + 1) * rexp (-π * ((k : ℝ) + 1) ^ 2 * t)‖ :=
          norm_tsum_le_tsum_norm hnrm
      _ = ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) :=
          tsum_congr fun k => habs _ _
  calc |1 + S + S - 1| = |2 * S| := by ring_nf
    _ = 2 * |S| := by rw [abs_mul, abs_two]
    _ ≤ 2 * ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := by linarith

set_option maxHeartbeats 1000000 in
/-- **The theta legs approach one**, at the certified geometric rate. -/
theorem theThetaLegsApproachOne {t : ℝ} (ht : 1 ≤ t) :
    |T3 t - 1| ≤ 2 * (rexp (-π * t) / (1 - rexp (-π * t))) ∧
    |T4 t - 1| ≤ 2 * (rexp (-π * t) / (1 - rexp (-π * t))) := by
  have ht0 : 0 < t := by linarith
  have htail := tail_le ht
  have htailpos : 0 ≤ ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  constructor
  · rw [T3_split ht0,
      show (1 : ℝ) + 2 * (∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t)) - 1
        = 2 * ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) from by ring,
      abs_of_nonneg (by positivity)]
    linarith
  · calc |T4 t - 1| ≤ 2 * ∑' k : ℕ, rexp (-π * ((k : ℝ) + 1) ^ 2 * t) := T4_dist ht0
      _ ≤ 2 * (rexp (-π * t) / (1 - rexp (-π * t))) := by linarith

/-! ## 3. The flow converges -/

private lemma tendsto_bound :
    Tendsto (fun t => 2 * (rexp (-π * t) / (1 - rexp (-π * t)))) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => rexp (-π * t)) atTop (nhds 0) := by
    have h2 : Tendsto (fun t : ℝ => -π * t) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by nlinarith [pi_pos]) tendsto_id
    exact Real.tendsto_exp_atBot.comp h2
  have h3 : Tendsto (fun t : ℝ => 1 - rexp (-π * t)) atTop (nhds 1) := by
    have := h1.const_sub 1
    simpa using this
  have h4 : Tendsto (fun t : ℝ => rexp (-π * t) / (1 - rexp (-π * t)))
      atTop (nhds (0 / 1)) := h1.div h3 one_ne_zero
  rw [zero_div] at h4
  simpa using h4.const_mul 2

private lemma tendsto_leg {f : ℝ → ℝ}
    (hb : ∀ t : ℝ, 1 ≤ t → |f t - 1| ≤ 2 * (rexp (-π * t) / (1 - rexp (-π * t)))) :
    Tendsto f atTop (nhds 1) := by
  have h5 : Tendsto (fun t => f t - 1) atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ tendsto_bound
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa using hb t ht
  have := h5.add_const 1
  simpa using this

/-- **THE DOUBLING FLOW CONVERGES TO ONE**: along `t, 2t, 4t, …` both squared legs
converge to `1` — with the mean step, the arithmetic–geometric mean of
`(θ₃(t)², θ₄(t)²)` is `1`, the scale-invariant content of the lattice. -/
theorem theDoublingFlowConvergesToOne {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => T3 (2 ^ k * t) ^ 2) atTop (nhds 1) ∧
    Tendsto (fun k : ℕ => T4 (2 ^ k * t) ^ 2) atTop (nhds 1) := by
  have horbit : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * t) atTop atTop := by
    apply Tendsto.atTop_mul_const ht
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hT3 : Tendsto (fun t => T3 t) atTop (nhds 1) :=
    tendsto_leg fun t ht => (theThetaLegsApproachOne ht).1
  have hT4 : Tendsto (fun t => T4 t) atTop (nhds 1) :=
    tendsto_leg fun t ht => (theThetaLegsApproachOne ht).2
  constructor
  · have h1 : Tendsto (fun k : ℕ => T3 (2 ^ k * t)) atTop (nhds 1) := hT3.comp horbit
    have h2 := h1.mul h1
    simpa [sq] using h2
  · have h1 : Tendsto (fun k : ℕ => T4 (2 ^ k * t)) atTop (nhds 1) := hT4.comp horbit
    have h2 := h1.mul h1
    simpa [sq] using h2

end Soma.Holonics.Millennium.LandenFlow
