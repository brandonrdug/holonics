import Holonics.HNN.Ratio.Certificate

/-!
# The complement Fisher bound licenses the native readout's metric weight

The native receiving flow (`hnn::constitution::epoch::flow::native_fisher_weight`, atlas
`hnn.native-fisher-weight`, record `2026-10-22_THE_NATIVE_FACE_READS_ITS_OWN_RECEIVING_TREE`)
weights each native sample's contribution to the readout's metric by
`μ = min(p_max, 2(1 − p_max))`, held at its dyadic ceiling. The first half of that minimum is the
factored certificate `Certificate.faceVariance_le_centred`: when every mass is at most `μ`,
`Var_p(v) ≤ μ Σ_c (v_c − v̄)²`. #410 owes the second half, the complement bound. This file proves it
and the minimum the Rust step reads.

[proved-standard; formal-checked] What is proved.

1. **The variance is the least second moment** (`faceVariance_le_moment`): for a normalized face,
   `Var_p(v) ≤ Σ_i p_i (v_i − a)²` for every centre `a`.
2. **The complement Fisher bound** (`faceVariance_le_complement`): for every class `k` and every
   centre `c`, `Var_p(v) ≤ 2(1 − p_k) Σ_i (v_i − c)²`. Centring at `v_k`, every other class lies at
   squared distance at most `2 Σ_i (v_i − c)²` from it, and those classes carry mass `1 − p_k`.
3. **The native readout's weight** (`faceVariance_le_fisher_weight`): with `p_k` the largest mass,
   `Var_p(v) ≤ min(p_k, 2(1 − p_k)) Σ_c (v_c − v̄)²`, `v̄` the classes' plain mean; and any weight
   above that minimum, the dyadic ceiling `native_fisher_weight` returns among them, bounds it too
   (`faceVariance_le_of_weight_le`).

The two halves cross at `p_max = 2/3`: below it the largest mass is the sharper weight, above it the
complement is, so a face already read sharply adds little curvature to the readout's metric.

The computational object is the helical pair interaction: the face is the receiver's reading at a
pair contact, and its variance is the curvature that contact adds to the metric. Of the winding
guide's six general objects this touches faces and placement (the receiving face); the helix, the
pair, the cell holonomy, the tube and the tower thread stay attached.

Consumers: `native_fisher_weight` in `crates/holonics/src/hnn/constitution/epoch/flow.rs` and the
atlas row `hnn.native-fisher-weight`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ComplementFisher

open Holonics.HNN.Ratio.Certificate (faceVariance faceVariance_le_centred)

variable {ι : Type*} [Fintype ι]

/-- [proved-standard; formal-checked] **The variance is the least second moment:** for a normalized
face, `Var_p(v) ≤ Σ_i p_i (v_i − a)²` for every centre `a`. -/
theorem faceVariance_le_moment (p v : ι → ℝ) (hp1 : ∑ i, p i = 1) (a : ℝ) :
    faceVariance p v ≤ ∑ i, p i * (v i - a) ^ 2 := by
  set m := ∑ j, p j * v j with hm
  have key : ∑ i, p i * (v i - a) ^ 2 = faceVariance p v + (m - a) ^ 2 := by
    have hterm : ∀ i, p i * (v i - a) ^ 2 =
        p i * (v i - m) ^ 2 + (m - a) * (2 * (p i * v i) - (a + m) * p i) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, ← hm]
    unfold faceVariance
    rw [← hm]
    ring
  rw [key]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- [proved-standard; formal-checked] **The complement Fisher bound:** for every class `k` and every
centre `c`, `Var_p(v) ≤ 2(1 − p_k) Σ_i (v_i − c)²`. -/
theorem faceVariance_le_complement [DecidableEq ι] (p v : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (k : ι) (c : ℝ) :
    faceVariance p v ≤ 2 * (1 - p k) * ∑ i, (v i - c) ^ 2 := by
  set S := ∑ i, (v i - c) ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpair : ∀ i, (v i - v k) ^ 2 ≤ 2 * S := by
    intro i
    by_cases hik : i = k
    · rw [hik]
      nlinarith [hS0]
    · have hsub : (v i - c) ^ 2 + (v k - c) ^ 2 ≤ S := by
        have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, k})
          (f := fun j => (v j - c) ^ 2) fun j _ _ => sq_nonneg _
        rw [Finset.sum_pair hik] at h
        exact h
      nlinarith [sq_nonneg (v i + v k - 2 * c), hsub]
  have hterm : ∀ i, p i * (v i - v k) ^ 2 ≤
      2 * S * p i - (if i = k then 2 * S * p k else 0) := by
    intro i
    by_cases hik : i = k
    · rw [if_pos hik, hik]
      nlinarith
    · rw [if_neg hik, sub_zero]
      have h := mul_le_mul_of_nonneg_left (hpair i) (hp0 i)
      linarith
  have hsum : ∑ i, p i * (v i - v k) ^ 2 ≤ 2 * S * (1 - p k) := by
    calc ∑ i, p i * (v i - v k) ^ 2
        ≤ ∑ i, (2 * S * p i - (if i = k then 2 * S * p k else 0)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * S * (1 - p k) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ k)]
        ring
  calc faceVariance p v ≤ ∑ i, p i * (v i - v k) ^ 2 := faceVariance_le_moment p v hp1 (v k)
    _ ≤ 2 * S * (1 - p k) := hsum
    _ = 2 * (1 - p k) * S := by ring

/-- [proved-standard; formal-checked] **The native readout's weight:** with `p_k` the largest mass,
`Var_p(v) ≤ min(p_k, 2(1 − p_k)) Σ_c (v_c − v̄)²`. -/
theorem faceVariance_le_fisher_weight [Nonempty ι] [DecidableEq ι] (p v : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (k : ι) (hk : ∀ i, p i ≤ p k) :
    faceVariance p v ≤
      min (p k) (2 * (1 - p k)) * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 := by
  have hS : 0 ≤ ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [min_mul_of_nonneg _ _ hS]
  exact le_min (faceVariance_le_centred p v hp1 hk)
    (faceVariance_le_complement p v hp0 hp1 k _)

/-- [proved-standard; formal-checked] **Any weight above the minimum bounds the variance**, so the
dyadic ceiling `native_fisher_weight` returns is a lawful metric weight. -/
theorem faceVariance_le_of_weight_le [Nonempty ι] [DecidableEq ι] (p v : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (k : ι) (hk : ∀ i, p i ≤ p k) {μ : ℝ}
    (hμ : min (p k) (2 * (1 - p k)) ≤ μ) :
    faceVariance p v ≤ μ * ∑ c, (v c - (∑ d, v d) / Fintype.card ι) ^ 2 :=
  (faceVariance_le_fisher_weight p v hp0 hp1 k hk).trans
    (mul_le_mul_of_nonneg_right hμ (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Holonics.HNN.ComplementFisher
