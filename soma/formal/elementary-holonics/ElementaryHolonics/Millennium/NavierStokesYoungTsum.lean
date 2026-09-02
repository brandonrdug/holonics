import ElementaryHolonics.Millennium.NavierStokesYoungFeed

/-!
# Young `ℓ¹ * ℓ² → ℓ²` on the frequency lattice, for complete populations

For nonnegative populations `a` (absolutely summable) and `b` (square summable) on the integer
frequency lattice, every finite family of receivers satisfies

```text
Σ_{k∈F} ( Σ'_p a_p b_{k−p} )² ≤ ( Σ'_p a_p )² · Σ'_q b_q².
```

The proof is the finite Cauchy--Schwarz on every partial sum of the convolution, passed to the
complete population through the supremum of nonnegative partial sums, then the exchange of the
finite receiver sum with the complete advecting sum and the reindexing `q = k − p`.  This pays
the whole feed, band and tail alike, with no split and no count.
-/

noncomputable section

open Set Filter Topology
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesYoungTsum

open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- A square summable nonnegative population is bounded by its complete square sum. -/
theorem sq_le_tsum_sq {b : SpatialFrequency → ℝ} (hb2 : Summable fun q ↦ b q ^ 2)
    (q : SpatialFrequency) : b q ^ 2 ≤ ∑' q, b q ^ 2 :=
  hb2.le_tsum q fun _ _ ↦ sq_nonneg _

/-- The convolution population at one receiver is summable. -/
theorem summable_conv {a b : SpatialFrequency → ℝ} (ha0 : ∀ p, 0 ≤ a p) (hb0 : ∀ q, 0 ≤ b q)
    (ha : Summable a) (hb2 : Summable fun q ↦ b q ^ 2) (k : SpatialFrequency) :
    Summable fun p ↦ a p * b (k - p) := by
  refine Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (ha0 p) (hb0 _)) (fun p ↦ ?_)
    (ha.mul_right (Real.sqrt (∑' q, b q ^ 2)))
  apply mul_le_mul_of_nonneg_left _ (ha0 p)
  rw [← Real.sqrt_sq (hb0 (k - p))]
  exact Real.sqrt_le_sqrt (sq_le_tsum_sq hb2 (k - p))

theorem summable_conv_sq {a b : SpatialFrequency → ℝ} (ha0 : ∀ p, 0 ≤ a p)
    (ha : Summable a) (hb2 : Summable fun q ↦ b q ^ 2) (k : SpatialFrequency) :
    Summable fun p ↦ a p * b (k - p) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p ↦ mul_nonneg (ha0 p) (sq_nonneg _)) (fun p ↦ ?_)
    (ha.mul_right (∑' q, b q ^ 2))
  exact mul_le_mul_of_nonneg_left (sq_le_tsum_sq hb2 (k - p)) (ha0 p)

/-- **Cauchy--Schwarz on the complete convolution at one receiver.** -/
theorem conv_sq_le {a b : SpatialFrequency → ℝ} (ha0 : ∀ p, 0 ≤ a p) (hb0 : ∀ q, 0 ≤ b q)
    (ha : Summable a) (hb2 : Summable fun q ↦ b q ^ 2) (k : SpatialFrequency) :
    (∑' p, a p * b (k - p)) ^ 2 ≤ (∑' p, a p) * ∑' p, a p * b (k - p) ^ 2 := by
  have hA0 : 0 ≤ ∑' p, a p := tsum_nonneg ha0
  have hS0 : 0 ≤ ∑' p, a p * b (k - p) ^ 2 :=
    tsum_nonneg fun p ↦ mul_nonneg (ha0 p) (sq_nonneg _)
  have hconv0 : 0 ≤ ∑' p, a p * b (k - p) := tsum_nonneg fun p ↦ mul_nonneg (ha0 p) (hb0 _)
  have hle : ∑' p, a p * b (k - p) ≤ Real.sqrt ((∑' p, a p) * ∑' p, a p * b (k - p) ^ 2) := by
    refine Real.tsum_le_of_sum_le (fun p ↦ mul_nonneg (ha0 p) (hb0 _)) ?_
    intro G
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq G (fun p ↦ Real.sqrt (a p))
      (fun p ↦ Real.sqrt (a p) * b (k - p))
    have hrw : ∀ p ∈ G, Real.sqrt (a p) * (Real.sqrt (a p) * b (k - p)) = a p * b (k - p) := by
      intro p _
      rw [← mul_assoc, Real.mul_self_sqrt (ha0 p)]
    have h1 : ∑ p ∈ G, Real.sqrt (a p) ^ 2 = ∑ p ∈ G, a p :=
      Finset.sum_congr rfl fun p _ ↦ Real.sq_sqrt (ha0 p)
    have h2 : ∑ p ∈ G, (Real.sqrt (a p) * b (k - p)) ^ 2 = ∑ p ∈ G, a p * b (k - p) ^ 2 :=
      Finset.sum_congr rfl fun p _ ↦ by rw [mul_pow, Real.sq_sqrt (ha0 p)]
    rw [Finset.sum_congr rfl hrw, h1, h2] at hcs
    have hG1 : ∑ p ∈ G, a p ≤ ∑' p, a p := ha.sum_le_tsum G fun p _ ↦ ha0 p
    have hG2 : ∑ p ∈ G, a p * b (k - p) ^ 2 ≤ ∑' p, a p * b (k - p) ^ 2 :=
      (summable_conv_sq ha0 ha hb2 k).sum_le_tsum G fun p _ ↦ mul_nonneg (ha0 p) (sq_nonneg _)
    have hG0 : 0 ≤ ∑ p ∈ G, a p * b (k - p) :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (ha0 p) (hb0 _)
    have hB0 : 0 ≤ ∑ p ∈ G, a p * b (k - p) ^ 2 :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (ha0 p) (sq_nonneg _)
    rw [← Real.sqrt_sq hG0]
    apply Real.sqrt_le_sqrt
    calc (∑ p ∈ G, a p * b (k - p)) ^ 2 ≤ (∑ p ∈ G, a p) * ∑ p ∈ G, a p * b (k - p) ^ 2 := hcs
      _ ≤ (∑' p, a p) * ∑' p, a p * b (k - p) ^ 2 :=
          mul_le_mul hG1 hG2 hB0 hA0
  have := pow_le_pow_left₀ hconv0 hle 2
  rwa [Real.sq_sqrt (mul_nonneg hA0 hS0)] at this

/-- **Young `ℓ¹ * ℓ² → ℓ²` on any finite family of receivers.** -/
theorem young_l1_l2 {a b : SpatialFrequency → ℝ} (ha0 : ∀ p, 0 ≤ a p) (hb0 : ∀ q, 0 ≤ b q)
    (ha : Summable a) (hb2 : Summable fun q ↦ b q ^ 2) (F : Finset SpatialFrequency) :
    ∑ k ∈ F, (∑' p, a p * b (k - p)) ^ 2 ≤ (∑' p, a p) ^ 2 * ∑' q, b q ^ 2 := by
  have hA0 : 0 ≤ ∑' p, a p := tsum_nonneg ha0
  calc ∑ k ∈ F, (∑' p, a p * b (k - p)) ^ 2
      ≤ ∑ k ∈ F, (∑' p, a p) * ∑' p, a p * b (k - p) ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ conv_sq_le ha0 hb0 ha hb2 k
    _ = (∑' p, a p) * ∑' p, a p * ∑ k ∈ F, b (k - p) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun k _ ↦ summable_conv_sq ha0 ha hb2 k)]
        apply tsum_congr
        intro p
        rw [Finset.mul_sum]
    _ ≤ (∑' p, a p) * ∑' p, a p * ∑' q, b q ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hA0
        have hsum1 : Summable fun p ↦ a p * ∑ k ∈ F, b (k - p) ^ 2 :=
          summable_sum (fun k _ ↦ summable_conv_sq ha0 ha hb2 k) |>.congr (fun p ↦ by rw [Finset.mul_sum])
        refine Summable.tsum_le_tsum (fun p ↦ ?_) hsum1 (ha.mul_right _)
        apply mul_le_mul_of_nonneg_left _ (ha0 p)
        have hinj : Set.InjOn (fun k : SpatialFrequency ↦ k - p) F := fun x _ y _ h ↦ by simpa using h
        calc ∑ k ∈ F, b (k - p) ^ 2 = ∑ q ∈ F.image (fun k ↦ k - p), b q ^ 2 :=
              (Finset.sum_image (f := fun q ↦ b q ^ 2) hinj).symm
          _ ≤ ∑' q, b q ^ 2 := hb2.sum_le_tsum _ fun q _ ↦ sq_nonneg _
    _ = (∑' p, a p) ^ 2 * ∑' q, b q ^ 2 := by
        rw [tsum_mul_right]
        ring

section Audit

#print axioms conv_sq_le
#print axioms young_l1_l2

end Audit

end Soma.Holonics.Millennium.NavierStokesYoungTsum
