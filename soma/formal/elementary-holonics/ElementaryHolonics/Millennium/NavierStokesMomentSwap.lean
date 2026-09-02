import ElementaryHolonics.Millennium.NavierStokesFourthMomentRiccati

/-!
# The swap: the fourth-moment tail cost is the eleventh moment

Each tail mode `k` pays its Jacobian tail mass beyond its half radius, and that mass is paid by the
fourth moment of the modes beyond that radius.  Summing `|k|_∞⁴ · tailJ(⌊(|k|_∞−1)/2⌋)²` over a
finite family and swapping the order of summation puts every mode `q` against the modes `k` it can
feed, those with `|k|_∞ ≤ 2 |q|_∞`, whose weighted count is at most `26 · 2⁷ · |q|_∞⁷`:

```text
Σ_k |k|_∞⁴ tailJ(⌊(|k|_∞−1)/2⌋)²  ≤  52 · 26 · 2⁷ · Σ_q |q|_∞¹¹ E_q.
```

The exponent `11 = 4 + 7` is exact: the weight `4` of the receiver, the shell face `2`, the weight
`4` of the feeding mode, and one more from the count of shells.  Against the dissipation at weight
`6` of the fourth-moment Riccati this is the ladder gap `5`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesMomentSwap

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The eleventh-moment population. -/
def eleventhMoment (τ : ℝ) (q : SpatialFrequency) : ℝ :=
  ((frequencySup q : ℕ) : ℝ) ^ 11 * modalEnergy (velocity := velocity) q τ

/-- The fourth-moment tail population beyond sup-norm `r + 1`, with the zero indicator. -/
def tailFourth (τ : ℝ) (r : ℕ) (q : SpatialFrequency) : ℝ :=
  if r + 1 ≤ frequencySup q then ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q τ
  else 0

theorem tailFourth_nonneg (τ : ℝ) (r : ℕ) (q : SpatialFrequency) :
    0 ≤ tailFourth (velocity := velocity) τ r q := by
  unfold tailFourth
  split_ifs
  · exact mul_nonneg (by positivity) (modalEnergy_nonneg q τ)
  · exact le_rfl

theorem tailFourth_le_eleventh (τ : ℝ) (r : ℕ) (q : SpatialFrequency) :
    tailFourth (velocity := velocity) τ r q ≤ eleventhMoment (velocity := velocity) τ q := by
  unfold tailFourth eleventhMoment
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ frequencySup q)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by norm_num)) (modalEnergy_nonneg q τ)
  · exact mul_nonneg (by positivity) (modalEnergy_nonneg q τ)

theorem summable_tailFourth (τ : ℝ) (r : ℕ)
    (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    Summable (tailFourth (velocity := velocity) τ r) :=
  Summable.of_nonneg_of_le (tailFourth_nonneg τ r) (tailFourth_le_eleventh τ r) hsum

/-- The Jacobian tail mass beyond the cube of radius `m` is paid by the fourth moment of the modes
of sup-norm at least `m + 1`; no threshold on `m`. -/
theorem tailMass_le_of_weighted_succ {m : ℕ} {C : ℝ}
    (hC : ∀ F : Finset SpatialFrequency, (∀ q ∈ F, m + 1 ≤ frequencySup q) →
      ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 ≤ C) :
    openPeriodicJacobianCoefficientTailMass solution t (frequencyCube m) ≤ Real.sqrt (52 * C) := by
  unfold openPeriodicJacobianCoefficientTailMass
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
  refine Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) ?_
  intro G
  have hmap : ∀ q ∈ G.map (Function.Embedding.subtype _), m + 1 ≤ frequencySup q := by
    intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨⟨q', hq'⟩, _, rfl⟩ := hq
    rw [mem_frequencyCube_iff_frequencySup_le] at hq'
    change m + 1 ≤ frequencySup q'
    omega
  have h1 : ∀ q ∈ G.map (Function.Embedding.subtype _), 1 ≤ frequencySup q :=
    fun q hq ↦ by have := hmap q hq; omega
  have := sum_norm_jacobianMode_le solution t (G.map (Function.Embedding.subtype _)) h1 i j
    (hC _ hmap)
  rw [Finset.sum_map] at this
  exact this

/-- The squared Jacobian tail mass beyond radius `r` is paid by the fourth-moment tail. -/
theorem tailJ_sq_le (r : ℕ) (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    openPeriodicJacobianCoefficientTailMass solution t (frequencyCube r) ^ 2 ≤
      52 * ∑' q, tailFourth (velocity := velocity) t.1 r q := by
  have hC : ∀ F : Finset SpatialFrequency, (∀ q ∈ F, r + 1 ≤ frequencySup q) →
      ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 ≤
        ∑' q, tailFourth (velocity := velocity) t.1 r q := by
    intro F hF
    have heq : ∀ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 =
        tailFourth (velocity := velocity) t.1 r q := by
      intro q hq
      unfold tailFourth
      rw [if_pos (hF q hq)]
    rw [Finset.sum_congr rfl heq]
    exact (summable_tailFourth t.1 r hsum).sum_le_tsum F (fun q _ ↦ tailFourth_nonneg t.1 r q)
  have hle := tailMass_le_of_weighted_succ solution t (m := r) hC
  have h0 : 0 ≤ ∑' q, tailFourth (velocity := velocity) t.1 r q :=
    tsum_nonneg fun q ↦ tailFourth_nonneg t.1 r q
  have := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [Real.sq_sqrt (by positivity)] at this

/-- The condition that `q` lies beyond the half radius of `k` is `|k|_∞ ≤ 2 |q|_∞`. -/
theorem halfRadius_succ_le_iff {k : SpatialFrequency} (hk : 1 ≤ frequencySup k) (s : ℕ) :
    halfRadius k + 1 ≤ s ↔ frequencySup k ≤ 2 * s := by
  unfold halfRadius
  omega

/-- **The weighted count of feedable modes.**  The modes with `|k|_∞ ≤ 2s` carry fourth-moment
weight at most `26 · 2⁷ · s⁷`. -/
theorem sum_pow_four_filter_le (F : Finset SpatialFrequency) (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (s : ℕ) :
    ∑ k ∈ F with frequencySup k ≤ 2 * s, ((frequencySup k : ℕ) : ℝ) ^ 4 ≤
      26 * 2 ^ 7 * (s : ℝ) ^ 7 := by
  set G := F.filter (fun k ↦ frequencySup k ≤ 2 * s) with hG
  rw [← Finset.sum_fiberwise_of_maps_to (g := frequencySup) (t := G.image frequencySup)
    (fun q hq ↦ Finset.mem_image_of_mem _ hq)]
  have hfiber : ∀ j ∈ G.image frequencySup,
      ∑ q ∈ G with frequencySup q = j, ((frequencySup q : ℕ) : ℝ) ^ 4 ≤ 26 * (j : ℝ) ^ 6 := by
    intro j hj
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hj
    have hq₀F : q₀ ∈ F := (Finset.mem_filter.mp hq₀).1
    have hj1 : 1 ≤ frequencySup q₀ := hF q₀ hq₀F
    have hconst : ∀ q ∈ G.filter (fun q ↦ frequencySup q = frequencySup q₀),
        ((frequencySup q : ℕ) : ℝ) ^ 4 = ((frequencySup q₀ : ℕ) : ℝ) ^ 4 := by
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_shell_le (frequencySup q₀) hj1 G
    calc ((G.filter fun q ↦ frequencySup q = frequencySup q₀).card : ℝ) *
          ((frequencySup q₀ : ℕ) : ℝ) ^ 4
        ≤ 26 * ((frequencySup q₀ : ℕ) : ℝ) ^ 2 * ((frequencySup q₀ : ℕ) : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 26 * ((frequencySup q₀ : ℕ) : ℝ) ^ 6 := by ring
  refine (Finset.sum_le_sum hfiber).trans ?_
  have hsub : G.image frequencySup ⊆ Finset.Icc 1 (2 * s) := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_Icc]
    exact ⟨hF q (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
  have hterm : ∀ j ∈ Finset.Icc 1 (2 * s), 26 * (j : ℝ) ^ 6 ≤ 26 * ((2 * s : ℕ) : ℝ) ^ 6 := by
    intro j hj
    have : (j : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this 6) (by norm_num)
  calc ∑ j ∈ G.image frequencySup, 26 * (j : ℝ) ^ 6
      ≤ ∑ j ∈ Finset.Icc 1 (2 * s), 26 * (j : ℝ) ^ 6 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ _j ∈ Finset.Icc 1 (2 * s), 26 * ((2 * s : ℕ) : ℝ) ^ 6 := Finset.sum_le_sum hterm
    _ = ((2 * s : ℕ) : ℝ) * (26 * ((2 * s : ℕ) : ℝ) ^ 6) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring
    _ = 26 * 2 ^ 7 * (s : ℝ) ^ 7 := by push_cast; ring

/-- **The swap.**  The fourth-moment tail cost of a finite family is paid by the eleventh moment. -/
theorem sum_pow_four_tailJ_sq_le (F : Finset SpatialFrequency)
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 ≤
      52 * (26 * 2 ^ 7) * ∑' q, eleventhMoment (velocity := velocity) t.1 q := by
  -- termwise: |k|⁴ tailJ(r_k)² ≤ |k|⁴ · 52 · Σ' tailFourth r_k
  have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 ≤
        ∑' q, ((frequencySup k : ℕ) : ℝ) ^ 4 * (52 * tailFourth (velocity := velocity) t.1 (halfRadius k) q) := by
    intro k _
    rw [tsum_mul_left, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tailJ_sq_le solution t (halfRadius k) hsum) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsummable : ∀ k ∈ F, Summable fun q ↦
      ((frequencySup k : ℕ) : ℝ) ^ 4 * (52 * tailFourth (velocity := velocity) t.1 (halfRadius k) q) :=
    fun k _ ↦ ((summable_tailFourth t.1 (halfRadius k) hsum).mul_left 52).mul_left _
  rw [← Summable.tsum_finsetSum hsummable]
  -- inner: Σ_k |k|⁴ 52 tailFourth r_k q ≤ 52 · 26 · 2⁷ · eleventh q
  have hinner : ∀ q, ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      (52 * tailFourth (velocity := velocity) t.1 (halfRadius k) q) ≤
        52 * (26 * 2 ^ 7) * eleventhMoment (velocity := velocity) t.1 q := by
    intro q
    have hsplit : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        (52 * tailFourth (velocity := velocity) t.1 (halfRadius k) q) =
        52 * (((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1) *
          (if frequencySup k ≤ 2 * frequencySup q then ((frequencySup k : ℕ) : ℝ) ^ 4 else 0) := by
      intro k hk
      unfold tailFourth
      by_cases h : halfRadius k + 1 ≤ frequencySup q
      · rw [if_pos h, if_pos ((halfRadius_succ_le_iff (hF k hk) _).mp h)]
        ring
      · rw [if_neg h, if_neg (fun h' ↦ h ((halfRadius_succ_le_iff (hF k hk) _).mpr h'))]
        ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, ← Finset.sum_filter]
    have hcount := sum_pow_four_filter_le F hF (frequencySup q)
    have hE : 0 ≤ ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 :=
      mul_nonneg (by positivity) (modalEnergy_nonneg q t.1)
    calc 52 * (((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1) *
          ∑ k ∈ F with frequencySup k ≤ 2 * frequencySup q, ((frequencySup k : ℕ) : ℝ) ^ 4
        ≤ 52 * (((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1) *
            (26 * 2 ^ 7 * ((frequencySup q : ℕ) : ℝ) ^ 7) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = 52 * (26 * 2 ^ 7) * eleventhMoment (velocity := velocity) t.1 q := by
          unfold eleventhMoment
          ring
  have hsumInner : Summable fun q ↦ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      (52 * tailFourth (velocity := velocity) t.1 (halfRadius k) q) :=
    summable_sum hsummable
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hinner hsumInner (hsum.mul_left _)

section Audit

#print axioms tailJ_sq_le
#print axioms sum_pow_four_filter_le
#print axioms sum_pow_four_tailJ_sq_le

end Audit

end Soma.Holonics.Millennium.NavierStokesMomentSwap
