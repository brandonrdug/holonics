import ElementaryHolonics.Millennium.NavierStokesMomentSwap

/-!
# The exact gap: the fourth-moment Riccati is driven by the eleventh moment

The drive of the fourth-moment Riccati, `Σ_k |k|_∞⁴ · incoherentCost(⌊(|k|_∞−1)/2⌋)²`, is read
entirely in moments of the modal vorticity energy `W_w = Σ'_q |q|_∞^w E_q`:

```text
momentCost ≤ 2 (ℓ¹(û(0)) + √(52·3/(2π)²) √W₂)² · 52·26·2⁷ · W₁₁
             + 2 · 52 W₄ · 52·(3/(2π)²) · 26·2⁷ · W₉.
```

The band factor is paid by `W₂`, the Jacobian tail by `W₁₁`, the velocity tail by `W₉`, the total
Jacobian mass by `W₄`.  With dissipation at weight six, the controlled moment is four and the
driving moment is eleven.  The ladder gap is five.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesMomentGap

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
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesMomentSwap

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## Moments and their summability -/

/-- The `w`-th moment population of the modal energy. -/
def momentPop (w : ℕ) (τ : ℝ) (q : SpatialFrequency) : ℝ :=
  ((frequencySup q : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) q τ

theorem momentPop_nonneg (w : ℕ) (τ : ℝ) (q : SpatialFrequency) :
    0 ≤ momentPop (velocity := velocity) w τ q :=
  mul_nonneg (by positivity) (modalEnergy_nonneg q τ)

theorem momentPop_le {w w' : ℕ} (hw : 1 ≤ w) (hww' : w ≤ w') (τ : ℝ) (q : SpatialFrequency) :
    momentPop (velocity := velocity) w τ q ≤ momentPop (velocity := velocity) w' τ q := by
  unfold momentPop
  rcases Nat.eq_zero_or_pos (frequencySup q) with h0 | hpos
  · rw [h0]
    simp [Nat.pos_iff_ne_zero.mp (by omega : 0 < w), Nat.pos_iff_ne_zero.mp (by omega : 0 < w')]
  · have h1 : (1 : ℝ) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hpos
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 hww') (modalEnergy_nonneg q τ)

theorem summable_momentPop {w : ℕ} (hw : 1 ≤ w) (hw11 : w ≤ 11) (τ : ℝ)
    (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    Summable (momentPop (velocity := velocity) w τ) :=
  Summable.of_nonneg_of_le (momentPop_nonneg w τ) (fun q ↦ momentPop_le hw hw11 τ q) hsum

/-- The `w`-th moment. -/
def moment (w : ℕ) (τ : ℝ) : ℝ := ∑' q, momentPop (velocity := velocity) w τ q

theorem moment_nonneg (w : ℕ) (τ : ℝ) : 0 ≤ moment (velocity := velocity) w τ :=
  tsum_nonneg fun q ↦ momentPop_nonneg w τ q

theorem eleventhMoment_eq (τ : ℝ) :
    eleventhMoment (velocity := velocity) τ = momentPop (velocity := velocity) 11 τ := rfl

/-! ## The generic swap with weight `w` -/

/-- The `w`-th moment tail population beyond sup-norm `r + 1`. -/
def tailMoment (w : ℕ) (τ : ℝ) (r : ℕ) (q : SpatialFrequency) : ℝ :=
  if r + 1 ≤ frequencySup q then momentPop (velocity := velocity) w τ q else 0

theorem tailMoment_nonneg (w : ℕ) (τ : ℝ) (r : ℕ) (q : SpatialFrequency) :
    0 ≤ tailMoment (velocity := velocity) w τ r q := by
  unfold tailMoment; split_ifs
  · exact momentPop_nonneg w τ q
  · exact le_rfl

theorem tailMoment_le (w : ℕ) (τ : ℝ) (r : ℕ) (q : SpatialFrequency) :
    tailMoment (velocity := velocity) w τ r q ≤ momentPop (velocity := velocity) w τ q := by
  unfold tailMoment; split_ifs
  · exact le_rfl
  · exact momentPop_nonneg w τ q

theorem summable_tailMoment {w : ℕ} (hw : 1 ≤ w) (hw11 : w ≤ 11) (τ : ℝ) (r : ℕ)
    (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    Summable (tailMoment (velocity := velocity) w τ r) :=
  Summable.of_nonneg_of_le (tailMoment_nonneg w τ r) (tailMoment_le w τ r)
    (summable_momentPop hw hw11 τ hsum)

/-- **The generic swap.**  Weight `4` on the receiver against the `w`-th moment tail beyond the
half radius returns the `(w + 7)`-th moment. -/
theorem sum_pow_four_tailMoment_le {w : ℕ} (hw : 1 ≤ w) (hw4 : w + 7 ≤ 11)
    (F : Finset SpatialFrequency) (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        ∑' q, tailMoment (velocity := velocity) w t.1 (halfRadius k) q ≤
      26 * 2 ^ 7 * moment (velocity := velocity) (w + 7) t.1 := by
  have hsummable : ∀ k ∈ F, Summable fun q ↦
      ((frequencySup k : ℕ) : ℝ) ^ 4 * tailMoment (velocity := velocity) w t.1 (halfRadius k) q :=
    fun k _ ↦ (summable_tailMoment hw (by omega) t.1 (halfRadius k) hsum).mul_left _
  have hrw : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      ∑' q, tailMoment (velocity := velocity) w t.1 (halfRadius k) q =
      ∑' q, ((frequencySup k : ℕ) : ℝ) ^ 4 * tailMoment (velocity := velocity) w t.1 (halfRadius k) q :=
    fun k _ ↦ (tsum_mul_left).symm
  rw [Finset.sum_congr rfl hrw, ← Summable.tsum_finsetSum hsummable]
  have hinner : ∀ q, ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      tailMoment (velocity := velocity) w t.1 (halfRadius k) q ≤
        26 * 2 ^ 7 * momentPop (velocity := velocity) (w + 7) t.1 q := by
    intro q
    have hsplit : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        tailMoment (velocity := velocity) w t.1 (halfRadius k) q =
        momentPop (velocity := velocity) w t.1 q *
          (if frequencySup k ≤ 2 * frequencySup q then ((frequencySup k : ℕ) : ℝ) ^ 4 else 0) := by
      intro k hk
      unfold tailMoment
      by_cases h : halfRadius k + 1 ≤ frequencySup q
      · rw [if_pos h, if_pos ((halfRadius_succ_le_iff (hF k hk) _).mp h)]
        ring
      · rw [if_neg h, if_neg (fun h' ↦ h ((halfRadius_succ_le_iff (hF k hk) _).mpr h'))]
        ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, ← Finset.sum_filter]
    have hcount := sum_pow_four_filter_le F hF (frequencySup q)
    calc momentPop (velocity := velocity) w t.1 q *
          ∑ k ∈ F with frequencySup k ≤ 2 * frequencySup q, ((frequencySup k : ℕ) : ℝ) ^ 4
        ≤ momentPop (velocity := velocity) w t.1 q *
            (26 * 2 ^ 7 * ((frequencySup q : ℕ) : ℝ) ^ 7) :=
          mul_le_mul_of_nonneg_left hcount (momentPop_nonneg w t.1 q)
      _ = 26 * 2 ^ 7 * momentPop (velocity := velocity) (w + 7) t.1 q := by
          unfold momentPop
          ring
  have hsumInner : Summable fun q ↦ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      tailMoment (velocity := velocity) w t.1 (halfRadius k) q :=
    summable_sum hsummable
  unfold moment
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hinner hsumInner
    ((summable_momentPop (by omega) hw4 t.1 hsum).mul_left _)

/-! ## The three factors of the cost, read in moments -/

/-- Cauchy--Schwarz on any finite family of nonzero modes: the velocity `ℓ¹` population is paid
by the second moment. -/
theorem sum_l1_le (G : Finset SpatialFrequency) (hG : ∀ p ∈ G, 1 ≤ frequencySup p) :
    ∑ p ∈ G, complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ≤
      Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p) := by
  set a : SpatialFrequency → ℝ := fun p ↦ 1 / ((frequencySup p : ℕ) : ℝ) ^ 2 with ha
  set b : SpatialFrequency → ℝ := fun p ↦
    ((frequencySup p : ℕ) : ℝ) ^ 2 * complexVectorL1 (openPeriodicVelocityFourierMode solution t p)
    with hb
  have hprod : ∀ p ∈ G, complexVectorL1 (openPeriodicVelocityFourierMode solution t p) = a p * b p := by
    intro p hp
    have hp0 : (0 : ℝ) < ((frequencySup p : ℕ) : ℝ) := by exact_mod_cast hG p hp
    simp only [ha, hb]
    field_simp
  rw [Finset.sum_congr rfl hprod]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq G a b
  have hA : ∑ p ∈ G, a p ^ 2 ≤ 52 := by
    have : ∀ p ∈ G, a p ^ 2 = 1 / ((frequencySup p : ℕ) : ℝ) ^ 4 := by
      intro p _
      simp only [ha]
      field_simp
    rw [Finset.sum_congr rfl this]
    exact sum_inv_pow_four_le G hG
  have hB : ∑ p ∈ G, b p ^ 2 ≤ 3 / (2 * Real.pi) ^ 2 * ∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    simp only [hb, momentPop]
    have := fourthMoment_tooth_le solution t p
    calc (((frequencySup p : ℕ) : ℝ) ^ 2 * complexVectorL1 (openPeriodicVelocityFourierMode solution t p)) ^ 2
        = ((frequencySup p : ℕ) : ℝ) ^ 4 * complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ^ 2 := by ring
      _ ≤ 3 / (2 * Real.pi) ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 2 * modalEnergy (velocity := velocity) p t.1) := this
  have hsum_nonneg : 0 ≤ ∑ p ∈ G, a p * b p :=
    Finset.sum_nonneg fun p _ ↦ mul_nonneg (by positivity) (mul_nonneg (by positivity) (complexVectorL1_nonneg _))
  have hB0 : 0 ≤ ∑ p ∈ G, b p ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hM0 : 0 ≤ ∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p :=
    Finset.sum_nonneg fun p _ ↦ momentPop_nonneg 2 t.1 p
  have hsq : (∑ p ∈ G, a p * b p) ^ 2 ≤
      52 * (3 / (2 * Real.pi) ^ 2) * ∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p := by
    calc (∑ p ∈ G, a p * b p) ^ 2 ≤ (∑ p ∈ G, a p ^ 2) * ∑ p ∈ G, b p ^ 2 := hcs
      _ ≤ 52 * (3 / (2 * Real.pi) ^ 2 * ∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p) :=
          mul_le_mul hA hB hB0 (by norm_num)
      _ = 52 * (3 / (2 * Real.pi) ^ 2) * ∑ p ∈ G, momentPop (velocity := velocity) 2 t.1 p := by ring
  rw [← Real.sqrt_sq hsum_nonneg, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hsq

/-- The velocity tail beyond radius `r`, squared, is paid by the second-moment tail. -/
theorem velocityTailMass_sq_le (r : ℕ) (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    velocityTailMass solution t r ^ 2 ≤
      52 * (3 / (2 * Real.pi) ^ 2) * ∑' q, tailMoment (velocity := velocity) 2 t.1 r q := by
  have hT0 : 0 ≤ ∑' q, tailMoment (velocity := velocity) 2 t.1 r q :=
    tsum_nonneg fun q ↦ tailMoment_nonneg 2 t.1 r q
  have hle : velocityTailMass solution t r ≤
      Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2) * ∑' q, tailMoment (velocity := velocity) 2 t.1 r q) := by
    unfold velocityTailMass
    refine Real.tsum_le_of_sum_le (fun _ ↦ complexVectorL1_nonneg _) ?_
    intro G
    have hG : ∀ p ∈ G.map (Function.Embedding.subtype _), 1 ≤ frequencySup p := by
      intro p hp
      rw [Finset.mem_map] at hp
      obtain ⟨⟨p', hp'⟩, _, rfl⟩ := hp
      rw [mem_frequencyCube_iff_frequencySup_le] at hp'
      change 1 ≤ frequencySup p'
      omega
    have hcs := sum_l1_le solution t (G.map (Function.Embedding.subtype _)) hG
    have hbound : ∑ p ∈ G.map (Function.Embedding.subtype _), momentPop (velocity := velocity) 2 t.1 p ≤
        ∑' q, tailMoment (velocity := velocity) 2 t.1 r q := by
      have heq : ∀ p ∈ G.map (Function.Embedding.subtype _),
          momentPop (velocity := velocity) 2 t.1 p = tailMoment (velocity := velocity) 2 t.1 r p := by
        intro p hp
        rw [Finset.mem_map] at hp
        obtain ⟨⟨p', hp'⟩, _, rfl⟩ := hp
        rw [mem_frequencyCube_iff_frequencySup_le] at hp'
        change momentPop (velocity := velocity) 2 t.1 p' = tailMoment (velocity := velocity) 2 t.1 r p'
        unfold tailMoment
        rw [if_pos (by omega)]
      rw [Finset.sum_congr rfl heq]
      exact (summable_tailMoment (by norm_num) (by norm_num) t.1 r hsum).sum_le_tsum _
        (fun q _ ↦ tailMoment_nonneg 2 t.1 r q)
    rw [Finset.sum_map] at hcs
    refine hcs.trans ?_
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hbound
  have := pow_le_pow_left₀ (tsum_nonneg fun _ ↦ complexVectorL1_nonneg _) hle 2
  rwa [Real.sq_sqrt (by positivity)] at this

/-- The zero mode of the Jacobian vanishes. -/
theorem jacobianMode_zero (i j : Fin 3) : openPeriodicJacobianFourierMode solution t 0 i j = 0 := by
  rw [congrFun (congrFun (openPeriodicJacobianFourierMode_eq_fourierJacobianMode solution t 0) i) j]
  simp [fourierJacobianMode]

/-- The total Jacobian mass, squared, is paid by the fourth moment. -/
theorem totalJ_sq_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    openPeriodicJacobianCoefficientTailMass solution t ∅ ^ 2 ≤
      52 * moment (velocity := velocity) 4 t.1 := by
  have hM0 := moment_nonneg (velocity := velocity) 4 t.1
  have hle : openPeriodicJacobianCoefficientTailMass solution t ∅ ≤
      Real.sqrt (52 * moment (velocity := velocity) 4 t.1) := by
    unfold openPeriodicJacobianCoefficientTailMass
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
    refine Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) ?_
    intro G
    set G' := (G.map (Function.Embedding.subtype _)).erase 0 with hG'
    have hG'1 : ∀ q ∈ G', 1 ≤ frequencySup q :=
      fun q hq ↦ one_le_frequencySup_of_ne_zero (Finset.ne_of_mem_erase hq)
    have hC : ∑ q ∈ G', ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 ≤
        moment (velocity := velocity) 4 t.1 :=
      (summable_momentPop (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum G'
        (fun q _ ↦ momentPop_nonneg 4 t.1 q)
    have hcs := sum_norm_jacobianMode_le solution t G' hG'1 i j hC
    have hsum_eq : ∑ q ∈ G, ‖openPeriodicJacobianFourierMode solution t q.1 i j‖ =
        ∑ q ∈ G', ‖openPeriodicJacobianFourierMode solution t q i j‖ := by
      rw [hG', Finset.sum_erase _ (by simp [jacobianMode_zero]), Finset.sum_map]
      rfl
    rw [hsum_eq]
    exact hcs
  have := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [Real.sq_sqrt (by positivity)] at this

/-- The band's second moment is at most the second moment. -/
theorem bandSecondMoment_le (r : ℕ) (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    bandSecondMoment (velocity := velocity) t r ≤ moment (velocity := velocity) 2 t.1 :=
  (summable_momentPop (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum _
    (fun q _ ↦ momentPop_nonneg 2 t.1 q)

/-- The band factor of the incoherent cost, paid by the second moment. -/
def bandFactor (τ : ℝ) : ℝ :=
  complexVectorL1 (openPeriodicVelocityFourierMode solution t 0) +
    Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) * Real.sqrt (moment (velocity := velocity) 2 τ)

theorem incoherentCost_le (r : ℕ) (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    incoherentCost solution t r ≤
      bandFactor (velocity := velocity) solution t t.1 *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube r) +
        velocityTailMass solution t r * openPeriodicJacobianCoefficientTailMass solution t ∅ := by
  unfold incoherentCost bandFactor
  refine add_le_add (mul_le_mul_of_nonneg_right (add_le_add le_rfl ?_) (norm_nonneg _)) le_rfl
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (bandSecondMoment_le (velocity := velocity) t r hsum))
    (Real.sqrt_nonneg _)

/-! ## The exact gap -/

/-- **The fourth-moment cost, read in moments.** -/
theorem momentCost_le (F : Finset SpatialFrequency) (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    momentCost solution t F ≤
      2 * bandFactor (velocity := velocity) solution t t.1 ^ 2 * (52 * (26 * 2 ^ 7)) *
          moment (velocity := velocity) 11 t.1 +
        2 * (52 * moment (velocity := velocity) 4 t.1) * (52 * (3 / (2 * Real.pi) ^ 2)) *
          (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1 := by
  set A := bandFactor (velocity := velocity) solution t t.1 with hA
  set Z := openPeriodicJacobianCoefficientTailMass solution t ∅ with hZ
  have hA0 : 0 ≤ A := add_nonneg (complexVectorL1_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hZ0 : 0 ≤ Z := norm_nonneg _
  -- termwise square bound
  have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * incoherentCost solution t (halfRadius k) ^ 2 ≤
      ((frequencySup k : ℕ) : ℝ) ^ 4 *
        (2 * A ^ 2 * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 +
          2 * Z ^ 2 * velocityTailMass solution t (halfRadius k) ^ 2) := by
    intro k _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hc := incoherentCost_le solution t (halfRadius k) hsum
    have hc0 : 0 ≤ incoherentCost solution t (halfRadius k) := by
      unfold incoherentCost
      have h1 : 0 ≤ velocityTailMass solution t (halfRadius k) :=
        tsum_nonneg fun _ ↦ complexVectorL1_nonneg _
      have h2 : 0 ≤ openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) :=
        norm_nonneg _
      have h3 : 0 ≤ openPeriodicJacobianCoefficientTailMass solution t ∅ := norm_nonneg _
      exact add_nonneg (mul_nonneg (add_nonneg (complexVectorL1_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) h2) (mul_nonneg h1 h3)
    set a := A * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k))
    set b := velocityTailMass solution t (halfRadius k) * Z
    have hsq : incoherentCost solution t (halfRadius k) ^ 2 ≤ (a + b) ^ 2 :=
      pow_le_pow_left₀ hc0 hc 2
    have hab : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    calc incoherentCost solution t (halfRadius k) ^ 2 ≤ (a + b) ^ 2 := hsq
      _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := hab
      _ = 2 * A ^ 2 * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 +
          2 * Z ^ 2 * velocityTailMass solution t (halfRadius k) ^ 2 := by
          simp only [a, b]
          ring
  unfold momentCost
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsplit : ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      (2 * A ^ 2 * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 +
        2 * Z ^ 2 * velocityTailMass solution t (halfRadius k) ^ 2) =
      2 * A ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 +
        2 * Z ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit]
  -- the Jacobian tail: eleventh moment
  have hJ := sum_pow_four_tailJ_sq_le solution t F hF hsum
  rw [eleventhMoment_eq] at hJ
  -- the velocity tail: ninth moment
  have hV : ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2 ≤
      (52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1 := by
    have hswap := sum_pow_four_tailMoment_le (velocity := velocity) t (w := 2) (by norm_num) (by norm_num) F hF hsum
    have hterm2 : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2 ≤
        (52 * (3 / (2 * Real.pi) ^ 2)) * (((frequencySup k : ℕ) : ℝ) ^ 4 *
          ∑' q, tailMoment (velocity := velocity) 2 t.1 (halfRadius k) q) := by
      intro k _
      have := mul_le_mul_of_nonneg_left (velocityTailMass_sq_le solution t (halfRadius k) hsum)
        (by positivity : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4)
      linarith [this]
    refine (Finset.sum_le_sum hterm2).trans ?_
    rw [← Finset.mul_sum]
    have hswap' : ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
        ∑' q, tailMoment (velocity := velocity) 2 t.1 (halfRadius k) q ≤
        26 * 2 ^ 7 * moment (velocity := velocity) 9 t.1 := hswap
    calc (52 * (3 / (2 * Real.pi) ^ 2)) * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
          ∑' q, tailMoment (velocity := velocity) 2 t.1 (halfRadius k) q
        ≤ (52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7 * moment (velocity := velocity) 9 t.1) :=
          mul_le_mul_of_nonneg_left hswap' (by positivity)
      _ = (52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1 := by
          ring
  have hZsq := totalJ_sq_le solution t hsum
  have hM9 := moment_nonneg (velocity := velocity) 9 t.1
  have hM11 := moment_nonneg (velocity := velocity) 11 t.1
  have hSJ : 0 ≤ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (sq_nonneg _)
  have hSV : 0 ≤ ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 2 * A ^ 2)
  have hcoef : 0 ≤ (52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1 := by
    positivity
  have h2 : 2 * Z ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2 ≤
      2 * (52 * moment (velocity := velocity) 4 t.1) *
        ((52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1) := by
    have hZ2 : Z ^ 2 ≤ 52 * moment (velocity := velocity) 4 t.1 := hZsq
    calc 2 * Z ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2
        ≤ 2 * Z ^ 2 * ((52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ ≤ 2 * (52 * moment (velocity := velocity) 4 t.1) *
          ((52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1) := by
          apply mul_le_mul_of_nonneg_right _ hcoef
          linarith
  calc 2 * A ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube (halfRadius k)) ^ 2 +
        2 * Z ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * velocityTailMass solution t (halfRadius k) ^ 2
      ≤ 2 * A ^ 2 * (52 * (26 * 2 ^ 7) * moment (velocity := velocity) 11 t.1) +
        2 * (52 * moment (velocity := velocity) 4 t.1) *
          ((52 * (3 / (2 * Real.pi) ^ 2)) * (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **The exact gap.**  The fourth-moment Riccati inequality with its drive read in moments: the
controlled moment is four, the dissipation is at weight six, the driving moments are eleven and
nine (times four).  The ladder gap is five. -/
theorem momentEnergy_riccati_moments (hnu : 0 < nu) {F : Finset SpatialFrequency}
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 4 F) D t.1 ∧
      D ≤ -(nu * (2 * Real.pi) ^ 2) * momentEnergy (velocity := velocity) 6 F t.1 +
        3 ^ 5 / nu *
          (2 * bandFactor (velocity := velocity) solution t t.1 ^ 2 * (52 * (26 * 2 ^ 7)) *
              moment (velocity := velocity) 11 t.1 +
            2 * (52 * moment (velocity := velocity) 4 t.1) * (52 * (3 / (2 * Real.pi) ^ 2)) *
              (26 * 2 ^ 7) * moment (velocity := velocity) 9 t.1) := by
  obtain ⟨D, hD, hle⟩ := momentEnergy_riccati solution hnu t hF
  refine ⟨D, hD, hle.trans ?_⟩
  have h35 : (0 : ℝ) ≤ 3 ^ 5 / nu := by positivity
  have := mul_le_mul_of_nonneg_left (momentCost_le solution t F hF hsum) h35
  linarith

section Audit

#print axioms sum_pow_four_tailMoment_le
#print axioms velocityTailMass_sq_le
#print axioms totalJ_sq_le
#print axioms momentCost_le
#print axioms momentEnergy_riccati_moments

end Audit

end Soma.Holonics.Millennium.NavierStokesMomentGap
