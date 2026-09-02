import ElementaryHolonics.Millennium.NavierStokesMomentTailRelevance
import ElementaryHolonics.Millennium.NavierStokesIncoherentSource
import Mathlib.NumberTheory.ZetaValues

/-!
# The `ℓ¹` moment of order `s` from the energy moment of order `2s + 2`

The three-dimensional lattice sum `Σ_{k ≠ 0} sup(k)^{−4}` converges: the shell `sup(k) = n`
has at most `26 n²` points, so the sum is at most `26 · ζ(2)`.  With the arithmetic--geometric
mean inequality `sup^s · ‖û_k‖ ≤ ½ (sup^{−4} + sup^{2s+4} ‖û_k‖²)`, the vorticity energy moment
of order `2s + 2` (which dominates `sup^{2s+4} ‖û_k‖²` through `ω̂ = 2πi k × û`) makes the `ℓ¹`
velocity moment of order `s` finite.  This is the rung the moment-ladder record asked for, with
the record's `2s + 4` weakened to `2s + 2`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Finset
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesIncoherentSource
open Soma.Holonics.Millennium.NavierStokesMomentTailRelevance

namespace Soma.Holonics.Millennium.NavierStokesL1MomentLadder

/-! ## The three-dimensional lattice sum -/

/-- The shell of sup-norm `n` inside the cube of radius `N`. -/
noncomputable def shell (N n : ℕ) : Finset SpatialFrequency :=
  (frequencyCube N).filter fun k ↦ frequencySup k = n

theorem shell_subset_sdiff {N n : ℕ} (hn : 1 ≤ n) :
    shell N n ⊆ frequencyCube n \ frequencyCube (n - 1) := by
  intro k hk
  rw [shell, Finset.mem_filter] at hk
  rw [Finset.mem_sdiff, mem_frequencyCube_iff_frequencySup_le, mem_frequencyCube_iff_frequencySup_le]
  omega

theorem card_shell_le {N n : ℕ} (hn : 1 ≤ n) : (shell N n).card ≤ 26 * n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc (shell N (m + 1)).card ≤ (frequencyCube (m + 1) \ frequencyCube (m + 1 - 1)).card :=
        Finset.card_le_card (shell_subset_sdiff hn)
    _ = (frequencyCube (m + 1)).card - (frequencyCube (m + 1 - 1)).card :=
        Finset.card_sdiff_of_subset (frequencyCube_mono (by omega))
    _ = (2 * (m + 1) + 1) ^ 3 - (2 * m + 1) ^ 3 := by
        simp only [card_frequencyCube, Nat.add_sub_cancel]
    _ ≤ 26 * (m + 1) ^ 2 := by
        have h : (2 * (m + 1) + 1) ^ 3 ≤ (2 * m + 1) ^ 3 + 26 * (m + 1) ^ 2 := by nlinarith
        omega

theorem shell_term_le (N n : ℕ) :
    ((shell N n).card : ℝ) * (1 / (n : ℝ) ^ 4) ≤ 26 * (1 / (n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hc : ((shell N n).card : ℝ) ≤ 26 * (n : ℝ) ^ 2 := by exact_mod_cast card_shell_le hpos
    have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    calc ((shell N n).card : ℝ) * (1 / (n : ℝ) ^ 4) ≤ 26 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 4) := by
          gcongr
      _ = 26 * (1 / (n : ℝ) ^ 2) := by field_simp

theorem sum_inv_sup_pow_four_le (S : Finset SpatialFrequency) :
    ∑ k ∈ S, 1 / ((frequencySup k : ℕ) : ℝ) ^ 4 ≤ 26 * (Real.pi ^ 2 / 6) := by
  set N := S.sup frequencySup with hN
  have hsub : S ⊆ frequencyCube N := by
    intro k hk
    rw [mem_frequencyCube_iff_frequencySup_le]
    exact Finset.le_sup (f := frequencySup) hk
  have hmaps : ∀ k ∈ frequencyCube N, frequencySup k ∈ Finset.range (N + 1) := by
    intro k hk
    rw [mem_frequencyCube_iff_frequencySup_le] at hk
    rw [Finset.mem_range]
    omega
  calc ∑ k ∈ S, 1 / ((frequencySup k : ℕ) : ℝ) ^ 4
      ≤ ∑ k ∈ frequencyCube N, 1 / ((frequencySup k : ℕ) : ℝ) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = ∑ n ∈ Finset.range (N + 1), ∑ k ∈ shell N n, 1 / ((frequencySup k : ℕ) : ℝ) ^ 4 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ n ∈ Finset.range (N + 1), ((shell N n).card : ℝ) * (1 / (n : ℝ) ^ 4) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_congr rfl (fun k hk => by
          rw [(Finset.mem_filter.mp hk).2] : ∀ k ∈ shell N n,
            1 / ((frequencySup k : ℕ) : ℝ) ^ 4 = 1 / (n : ℝ) ^ 4), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.range (N + 1), 26 * (1 / (n : ℝ) ^ 2) :=
        Finset.sum_le_sum fun n _ => shell_term_le N n
    _ = 26 * ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 26 * (Real.pi ^ 2 / 6) := by
        gcongr
        exact sum_le_hasSum _ (fun n _ => by positivity) hasSum_zeta_two

/-- **The lattice sum converges.** -/
theorem summable_inv_sup_pow_four :
    Summable fun k : SpatialFrequency ↦ 1 / ((frequencySup k : ℕ) : ℝ) ^ 4 :=
  summable_of_sum_le (fun k => by positivity) sum_inv_sup_pow_four_le

/-! ## The rung -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

theorem l1Pop_sq_le (k : SpatialFrequency) : l1Pop solution t k ^ 2 ≤ 3 * velPop solution t k := by
  unfold l1Pop complexVectorL1 velPop
  rw [Fin.sum_univ_three]
  nlinarith [sq_nonneg (‖openPeriodicVelocityFourierMode solution t k 0‖ -
      ‖openPeriodicVelocityFourierMode solution t k 1‖),
    sq_nonneg (‖openPeriodicVelocityFourierMode solution t k 0‖ -
      ‖openPeriodicVelocityFourierMode solution t k 2‖),
    sq_nonneg (‖openPeriodicVelocityFourierMode solution t k 1‖ -
      ‖openPeriodicVelocityFourierMode solution t k 2‖)]

theorem l1Pop_le_sqrt (k : SpatialFrequency) :
    l1Pop solution t k ≤ Real.sqrt 3 * Real.sqrt (velPop solution t k) := by
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.le_sqrt_of_sq_le
  exact l1Pop_sq_le solution t k

/-- The vorticity moment of order `w` dominates `sup^{w+2} · velPop`. -/
theorem sup_pow_add_two_velPop_le (w : ℕ) (q : SpatialFrequency) :
    ((frequencySup q : ℕ) : ℝ) ^ (w + 2) * velPop solution t q ≤
      momentPop (velocity := velocity) w t.1 q / (2 * Real.pi) ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  unfold momentPop
  rw [modalEnergy_eq_velPop solution t q]
  have hfs := frequencySup_sq_le_frequencySquared q
  have hv := velPop_nonneg solution t q
  have hc : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ w :=
    mul_nonneg (mul_nonneg (by positivity) hv) (by positivity)
  have key := mul_le_mul_of_nonneg_left hfs hc
  calc ((frequencySup q : ℕ) : ℝ) ^ (w + 2) * velPop solution t q * (2 * Real.pi) ^ 2
      = (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ w *
          ((frequencySup q : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ (2 * Real.pi) ^ 2 * velPop solution t q * ((frequencySup q : ℕ) : ℝ) ^ w *
          frequencySquared q := key
    _ = _ := by ring

/-- The arithmetic--geometric mean step: for `k ≠ 0`,
`sup^s · ‖û_k‖₁ ≤ (√3/2) (sup^{−4} + sup^{2s+4} · velPop)`. -/
theorem l1MomentTerm_le_of_ne (s : ℕ) {k : SpatialFrequency} (hk : frequencySup k ≠ 0) :
    ((frequencySup k : ℕ) : ℝ) ^ s * l1Pop solution t k ≤
      Real.sqrt 3 / 2 * (1 / ((frequencySup k : ℕ) : ℝ) ^ 4 +
        ((frequencySup k : ℕ) : ℝ) ^ (2 * s + 4) * velPop solution t k) := by
  set n : ℝ := ((frequencySup k : ℕ) : ℝ) with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hk
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hk
  set v := velPop solution t k with hv
  have hv0 : 0 ≤ v := velPop_nonneg solution t k
  have h1 := l1Pop_le_sqrt solution t k
  rw [← hv] at h1
  have hamgm : 2 * (1 / n ^ 2) * (n ^ (s + 2) * Real.sqrt v) ≤
      (1 / n ^ 2) ^ 2 + (n ^ (s + 2) * Real.sqrt v) ^ 2 := two_mul_le_add_sq _ _
  have e1 : (1 / n ^ 2) * (n ^ (s + 2) * Real.sqrt v) = n ^ s * Real.sqrt v := by
    field_simp
    ring
  have e2 : (1 / n ^ 2) ^ 2 = 1 / n ^ 4 := by
    field_simp
  have e3 : (n ^ (s + 2) * Real.sqrt v) ^ 2 = n ^ (2 * s + 4) * v := by
    rw [mul_pow, Real.sq_sqrt hv0, ← pow_mul]
    ring_nf
  rw [mul_assoc, e1, e2, e3] at hamgm
  calc n ^ s * l1Pop solution t k ≤ n ^ s * (Real.sqrt 3 * Real.sqrt v) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hnpos.le _)
    _ = Real.sqrt 3 * (n ^ s * Real.sqrt v) := by ring
    _ ≤ Real.sqrt 3 * ((1 / n ^ 4 + n ^ (2 * s + 4) * v) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
        linarith
    _ = Real.sqrt 3 / 2 * (1 / n ^ 4 + n ^ (2 * s + 4) * v) := by ring

/-- **The rung.**  The `ℓ¹` velocity moment of order `s` is summable whenever the vorticity
energy moment of order `2s + 2` is. -/
theorem summable_l1MomentTerm (s : ℕ)
    (hsum : Summable (momentPop (velocity := velocity) (2 * s + 2) t.1)) :
    Summable fun k : SpatialFrequency ↦
      ((frequencySup k : ℕ) : ℝ) ^ s * complexVectorL1 (openPeriodicVelocityFourierMode solution t k) := by
  classical
  have hmom : Summable fun k : SpatialFrequency ↦
      ((frequencySup k : ℕ) : ℝ) ^ (2 * s + 4) * velPop solution t k :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (velPop_nonneg solution t k))
      (fun k => by
        have := sup_pow_add_two_velPop_le solution t (2 * s + 2) k
        rwa [show 2 * s + 2 + 2 = 2 * s + 4 by ring] at this)
      (hsum.div_const _)
  have hzero : Summable fun k : SpatialFrequency ↦
      (if frequencySup k = 0 then l1Pop solution t k else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    have hk' : k ≠ 0 := by simpa using hk
    have : frequencySup k ≠ 0 := by
      intro h0
      apply hk'
      funext c
      have := Finset.sup_le_iff.mp h0.le c (Finset.mem_univ c)
      simp only [Nat.le_zero, Int.natAbs_eq_zero] at this
      exact this
    simp [this]
  refine Summable.of_nonneg_of_le (fun k => l1MomentTerm_nonneg solution t s k)
    (fun k => ?_) (((summable_inv_sup_pow_four.add hmom).mul_left (Real.sqrt 3 / 2)).add hzero)
  show ((frequencySup k : ℕ) : ℝ) ^ s * l1Pop solution t k ≤ _
  by_cases hk : frequencySup k = 0
  · rw [if_pos hk]
    have hl : 0 ≤ Real.sqrt 3 / 2 * (1 / ((frequencySup k : ℕ) : ℝ) ^ 4 +
        ((frequencySup k : ℕ) : ℝ) ^ (2 * s + 4) * velPop solution t k) := by
      have := velPop_nonneg solution t k
      positivity
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [pow_zero, one_mul]
      linarith
    · have hz : ((frequencySup k : ℕ) : ℝ) = 0 := by rw [hk]; simp
      have hl0 := l1Pop_nonneg solution t k
      calc ((frequencySup k : ℕ) : ℝ) ^ s * l1Pop solution t k = 0 := by
            rw [hz, zero_pow (Nat.pos_iff_ne_zero.mp hs), zero_mul]
        _ ≤ _ := by linarith
  · rw [if_neg hk, add_zero]
    exact l1MomentTerm_le_of_ne solution t s hk

/-- The record's finish line, with the energy moment of order `2s + 4`. -/
theorem summable_l1MomentTerm_of_four (s : ℕ)
    (hsum : Summable (momentPop (velocity := velocity) (2 * s + 4) t.1)) :
    Summable fun k : SpatialFrequency ↦
      ((frequencySup k : ℕ) : ℝ) ^ s * complexVectorL1 (openPeriodicVelocityFourierMode solution t k) :=
  summable_l1MomentTerm solution t s
    (Summable.of_nonneg_of_le (momentPop_nonneg _ _)
      (fun q => momentPop_le (by omega) (by omega) t.1 q) hsum)

end Soma.Holonics.Millennium.NavierStokesL1MomentLadder
