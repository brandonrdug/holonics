import ElementaryHolonics.Millennium.NavierStokesModeLagrange
import ElementaryHolonics.Millennium.NavierStokesHalfRadiusReach
import ElementaryHolonics.Millennium.NavierStokesTailBoundedControl
import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

/-!
# The periodic official alternative follows from a bounded fourth-moment tail energy

The finish line.  If, for every admitted solution, the weighted tail energy

```text
W₄(t) = Σ_{|k|_∞ ≥ m} |k|_∞⁴ · E_k(t)
```

has every finite partial sum below one constant on a terminal tail `[s, T)`, then `StatementB`.

The passage is three exact steps.  Lagrange on the torus modes bounds every Jacobian entry by the
square root of the modal vorticity energy.  The lattice weight bounds every finite partial sum of
`|k|_∞⁻⁴` over nonzero modes by `52`: the shell at sup-norm `j` carries `(2j+1)³ − (2j−1)³ ≤ 26 j²`
modes, and `Σ j⁻² ≤ 2`.  Cauchy--Schwarz on finite families then bounds the Jacobian tail mass by
`√(52 · W₄)`, which is the bounded relevance control.

No analytic vocabulary remains in the hypothesis: a count of modes per shell, the fourth power of
the sup-norm, the modal energy, and one constant.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy

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
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesTailRelevance
open Soma.Holonics.Millennium.NavierStokesTailBoundedControl
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

/-! ## The lattice weight -/

theorem sum_inv_sq_Icc_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        have hn' : (0 : ℝ) < n := by exact_mod_cast hpos
        rw [div_sub_div _ _ hn'.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      linarith [ih hpos]

theorem sum_inv_sq_le_two {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j) :
    ∑ j ∈ S, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : S ⊆ Finset.Icc 1 (S.sup id) := by
      intro j hj
      rw [Finset.mem_Icc]
      exact ⟨hS j hj, Finset.le_sup (f := id) hj⟩
    have hmax : 1 ≤ S.sup id := by
      obtain ⟨j, hj⟩ := hne
      exact (hS j hj).trans (Finset.le_sup (f := id) hj)
    calc ∑ j ∈ S, (1 : ℝ) / (j : ℝ) ^ 2
        ≤ ∑ j ∈ Finset.Icc 1 (S.sup id), (1 : ℝ) / (j : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ ≤ 2 - 1 / ((S.sup id : ℕ) : ℝ) := sum_inv_sq_Icc_le _ hmax
      _ ≤ 2 := by
          have : (0 : ℝ) ≤ 1 / ((S.sup id : ℕ) : ℝ) := by positivity
          linarith

/-- The shell at sup-norm `j ≥ 1` carries at most `26 j²` modes. -/
theorem card_shell_le (j : ℕ) (hj : 1 ≤ j) (F : Finset SpatialFrequency) :
    ((F.filter fun q ↦ frequencySup q = j).card : ℝ) ≤ 26 * (j : ℝ) ^ 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hsub : F.filter (fun q ↦ frequencySup q = i + 1) ⊆
      frequencyCube (i + 1) \ frequencyCube i := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_sdiff, mem_frequencyCube_iff_frequencySup_le,
      mem_frequencyCube_iff_frequencySup_le]
    omega
  have hcube : frequencyCube i ⊆ frequencyCube (i + 1) := frequencyCube_mono (by omega)
  have hcard : (frequencyCube (i + 1) \ frequencyCube i).card = 24 * (i + 1) ^ 2 + 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcube, card_frequencyCube, card_frequencyCube]
    have : (2 * (i + 1) + 1) ^ 3 = (2 * i + 1) ^ 3 + (24 * (i + 1) ^ 2 + 2) := by ring
    omega
  have := Finset.card_le_card hsub
  rw [hcard] at this
  have hreal : ((F.filter fun q ↦ frequencySup q = i + 1).card : ℝ) ≤
      24 * ((i + 1 : ℕ) : ℝ) ^ 2 + 2 := by exact_mod_cast this
  have hi : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ i + 1)
  nlinarith

/-- **The lattice weight.**  Every finite partial sum of `|k|_∞⁻⁴` over nonzero modes is at most
`52 = 26 · 2`. -/
theorem sum_inv_pow_four_le (F : Finset SpatialFrequency) (hF : ∀ q ∈ F, 1 ≤ frequencySup q) :
    ∑ q ∈ F, (1 : ℝ) / ((frequencySup q : ℕ) : ℝ) ^ 4 ≤ 52 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := frequencySup) (t := F.image frequencySup)
    (fun q hq ↦ Finset.mem_image_of_mem _ hq)]
  have hfiber : ∀ j ∈ F.image frequencySup,
      ∑ q ∈ F with frequencySup q = j, (1 : ℝ) / ((frequencySup q : ℕ) : ℝ) ^ 4 ≤
        26 * ((1 : ℝ) / (j : ℝ) ^ 2) := by
    intro j hj
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hj
    have hj1 : 1 ≤ frequencySup q₀ := hF q₀ hq₀
    have hconst : ∀ q ∈ F.filter (fun q ↦ frequencySup q = frequencySup q₀),
        (1 : ℝ) / ((frequencySup q : ℕ) : ℝ) ^ 4 = 1 / ((frequencySup q₀ : ℕ) : ℝ) ^ 4 := by
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard := card_shell_le (frequencySup q₀) hj1 F
    have hj0 : (0 : ℝ) < ((frequencySup q₀ : ℕ) : ℝ) := by exact_mod_cast hj1
    calc ((F.filter fun q ↦ frequencySup q = frequencySup q₀).card : ℝ) *
          (1 / ((frequencySup q₀ : ℕ) : ℝ) ^ 4)
        ≤ 26 * ((frequencySup q₀ : ℕ) : ℝ) ^ 2 * (1 / ((frequencySup q₀ : ℕ) : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 26 * (1 / ((frequencySup q₀ : ℕ) : ℝ) ^ 2) := by
          field_simp
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  have himage : ∀ j ∈ F.image frequencySup, 1 ≤ j := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hF q hq
  have := sum_inv_sq_le_two himage
  linarith

/-! ## Cauchy--Schwarz on a finite family of the tail -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The modal energy of a mode is the vorticity mode's energy on the actual slice. -/
theorem modalEnergy_eq_sum_norm_sq_curl (t : Ioo 0 T) (q : SpatialFrequency) :
    modalEnergy (velocity := velocity) q t.1 =
      ∑ i : Fin 3,
        ‖frequencyCurlMultiplier q (openPeriodicVelocityFourierMode solution t q) i‖ ^ 2 := by
  rw [modalEnergy_eq_sum_norm_sq]
  unfold vorticityModeCurve
  have hmode : velocityMode velocity q t.1 = openPeriodicVelocityFourierMode solution t q := by
    funext component
    exact velocityModeComponent_eq_openPeriodicVelocityFourierMode solution t q component
  rw [hmode]

/-- **Every Jacobian entry is paid by the modal energy of the actual solution.** -/
theorem norm_jacobianMode_sq_le_modalEnergy (t : Ioo 0 T) (q : SpatialFrequency)
    (i j : Fin 3) :
    ‖openPeriodicJacobianFourierMode solution t q i j‖ ^ 2 ≤
      modalEnergy (velocity := velocity) q t.1 := by
  rw [modalEnergy_eq_sum_norm_sq_curl solution t q]
  have h := congrFun (congrFun (openPeriodicJacobianFourierMode_eq_fourierJacobianMode solution t q) i) j
  rw [h]
  exact norm_fourierJacobianMode_sq_le q _ (openPeriodicVelocityFourierMode_divergenceFree solution t q) i j

/-- **Cauchy--Schwarz on a finite family of the tail.** -/
theorem sum_norm_jacobianMode_le (t : Ioo 0 T) (F : Finset SpatialFrequency)
    (hF : ∀ q ∈ F, 1 ≤ frequencySup q) (i j : Fin 3) {C : ℝ}
    (hC : ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 ≤ C) :
    ∑ q ∈ F, ‖openPeriodicJacobianFourierMode solution t q i j‖ ≤ Real.sqrt (52 * C) := by
  set a : SpatialFrequency → ℝ := fun q ↦ 1 / ((frequencySup q : ℕ) : ℝ) ^ 2 with ha
  set b : SpatialFrequency → ℝ := fun q ↦
    ((frequencySup q : ℕ) : ℝ) ^ 2 * ‖openPeriodicJacobianFourierMode solution t q i j‖ with hb
  have hprod : ∀ q ∈ F, ‖openPeriodicJacobianFourierMode solution t q i j‖ = a q * b q := by
    intro q hq
    have hq0 : (0 : ℝ) < ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hF q hq
    simp only [ha, hb]
    field_simp
  rw [Finset.sum_congr rfl hprod]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F a b
  have hA : ∑ q ∈ F, a q ^ 2 ≤ 52 := by
    have : ∀ q ∈ F, a q ^ 2 = 1 / ((frequencySup q : ℕ) : ℝ) ^ 4 := by
      intro q _
      simp only [ha]
      field_simp
    rw [Finset.sum_congr rfl this]
    exact sum_inv_pow_four_le F hF
  have hB : ∑ q ∈ F, b q ^ 2 ≤ C := by
    refine le_trans ?_ hC
    apply Finset.sum_le_sum
    intro q _
    simp only [hb]
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (norm_jacobianMode_sq_le_modalEnergy solution t q i j)
      (by positivity)
  have hsum_nonneg : 0 ≤ ∑ q ∈ F, a q * b q :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by positivity) (by positivity)
  have hC0 : 0 ≤ C := le_trans (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by positivity)
    (modalEnergy_nonneg q t.1)) hC
  have hsq : (∑ q ∈ F, a q * b q) ^ 2 ≤ 52 * C := by
    refine hcs.trans ?_
    have hA0 : 0 ≤ ∑ q ∈ F, a q ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hB0 : 0 ≤ ∑ q ∈ F, b q ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    exact mul_le_mul hA hB hB0 (by norm_num)
  rw [← Real.sqrt_sq hsum_nonneg]
  exact Real.sqrt_le_sqrt hsq

/-! ## The finish line -/

/-- **The weighted tail energy control.**  For every admitted positive-viscosity solution there
are a sup-norm threshold `m ≥ 1`, a start `s`, and a constant `C` such that every finite partial
sum of `|k|_∞⁴ · E_k(t)` over modes with `|k|_∞ ≥ m` is at most `C` on `[s, T)`. -/
def WeightedTailEnergyControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (m : ℕ) (s C : ℝ), 1 ≤ m ∧ 0 < s ∧ s < T ∧
        ∀ t ∈ Ioo s T, ∀ F : Finset SpatialFrequency, (∀ q ∈ F, m ≤ frequencySup q) →
          ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t ≤ C

/-- The Jacobian tail mass beyond the cube of radius `m` is paid by `√(52 C)`. -/
theorem tailMass_le_of_weighted (t : Ioo 0 T) {m : ℕ} (hm : 1 ≤ m) {C : ℝ}
    (hC : ∀ F : Finset SpatialFrequency, (∀ q ∈ F, m ≤ frequencySup q) →
      ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q t.1 ≤ C) :
    openPeriodicJacobianCoefficientTailMass solution t (frequencyCube m) ≤ Real.sqrt (52 * C) := by
  unfold openPeriodicJacobianCoefficientTailMass
  have hC0 : 0 ≤ C := by
    have := hC ∅ (by simp)
    simpa using this
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
  refine Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) ?_
  intro G
  have hmap : ∀ q ∈ G.map (Function.Embedding.subtype _), m ≤ frequencySup q := by
    intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨⟨q', hq'⟩, _, rfl⟩ := hq
    rw [mem_frequencyCube_iff_frequencySup_le] at hq'
    change m ≤ frequencySup q'
    omega
  have h1 : ∀ q ∈ G.map (Function.Embedding.subtype _), 1 ≤ frequencySup q :=
    fun q hq ↦ hm.trans (hmap q hq)
  have := sum_norm_jacobianMode_le solution t (G.map (Function.Embedding.subtype _)) h1 i j
    (hC _ hmap)
  rw [Finset.sum_map] at this
  exact this

theorem tailBoundedControl_of_weightedTailEnergy (h : WeightedTailEnergyControl) :
    TailBoundedControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨m, s, C, hm, hs, hsT, hC⟩ := h hnu solution
  refine ⟨m, s, Real.sqrt (52 * C), hs, hsT, ?_⟩
  intro t ht
  have htT : t ∈ Ioo 0 T := ⟨hs.trans ht.1, ht.2⟩
  unfold tailMass
  rw [dif_pos htT]
  exact tailMass_le_of_weighted solution ⟨t, htT⟩ hm (fun F hF ↦ hC t ht F hF)

/-- **The finish line.**  A bounded fourth-moment tail energy on a terminal tail returns the
periodic official alternative. -/
theorem statementB_of_weightedTailEnergy (h : WeightedTailEnergyControl) : StatementB :=
  statementB_of_tailBounded (tailBoundedControl_of_weightedTailEnergy h)

theorem officialProblem_of_weightedTailEnergy (h : WeightedTailEnergyControl) :
    TheOfficialNavierStokesProblem :=
  Or.inr (Or.inl (statementB_of_weightedTailEnergy h))

section Audit

#print axioms sum_inv_pow_four_le
#print axioms norm_jacobianMode_sq_le_modalEnergy
#print axioms sum_norm_jacobianMode_le
#print axioms tailMass_le_of_weighted
#print axioms statementB_of_weightedTailEnergy
#print axioms officialProblem_of_weightedTailEnergy

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
