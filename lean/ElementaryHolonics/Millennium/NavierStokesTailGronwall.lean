import ElementaryHolonics.Millennium.NavierStokesHalfRadiusReach

/-!
# The tail energy is bounded by the total half-radius cost

Summing the half-radius Riccati inequality over any finite family of modes with sup-norm at
least `m` gives a family inequality whose dissipation is at least `ν (2π)² m²` times the family
energy and whose drive is `3⁵/ν` times the family's total squared cost.  The weighted maximum
principle integrates it: if the total squared half-radius cost of the tail stays below `M` on a
terminal tail `[s, T)`, then the tail energy beyond sup-norm `m` stays below

```text
max ( tailEnergy_m(s),  3⁵ M / (ν² (2π)² m²) )
```

on that tail.  The volume drawn by the tail over time is paid by its surface cost.  The passage
from finite families to the tail is the supremum of nonnegative partial sums.

The open obligation is now: the total squared half-radius cost of the tail,
`Σ_{|k|_∞ ≥ m} feedBound(⌊(|k|_∞−1)/2⌋)²`, stays bounded up to the terminal time.  Each cost is
the count `(2r+1)³` times the half-density of the initial energy times the Jacobian tail mass
beyond `r`, plus the velocity tail beyond `r` times the total Jacobian mass, with
`r = ⌊(|k|_∞−1)/2⌋`; the shell at sup-norm `m` carries `(2m+1)³ − (2m−1)³` modes.  Nothing here
discharges it.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesTailGronwall

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
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach

/-! ## The scalar weighted maximum principle -/

/-- If `f' ≤ −a f + G` on `[s, τ]` with `a > 0`, then `f τ ≤ max (f s) (G / a)`. -/
theorem le_max_of_hasDerivAt_le {f : ℝ → ℝ} {a G s τ : ℝ} (ha : 0 < a) (hsτ : s ≤ τ)
    (hf : ∀ σ ∈ Icc s τ, ∃ D, HasDerivAt f D σ ∧ D ≤ -a * f σ + G) :
    f τ ≤ max (f s) (G / a) := by
  set c : ℝ := G / a with hc
  have hc_eq : a * c = G := by
    rw [hc]
    field_simp
  set h : ℝ → ℝ := fun σ ↦ (f σ - c) * Real.exp (a * (σ - s)) with hh
  have hexp : ∀ σ : ℝ, HasDerivAt (fun σ ↦ Real.exp (a * (σ - s)))
      (a * Real.exp (a * (σ - s))) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ ↦ a * (σ - s)) a σ := by
      simpa using ((hasDerivAt_id σ).sub_const s).const_mul a
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hderivAt : ∀ σ ∈ Icc s τ, ∃ D, HasDerivAt h D σ ∧ D ≤ 0 := by
    intro σ hσ
    obtain ⟨D, hD, hle⟩ := hf σ hσ
    refine ⟨D * Real.exp (a * (σ - s)) + (f σ - c) * (a * Real.exp (a * (σ - s))),
      (hD.sub_const c).mul (hexp σ), ?_⟩
    have hepos : 0 < Real.exp (a * (σ - s)) := Real.exp_pos _
    have hkey : D + (f σ - c) * a ≤ 0 := by
      calc D + (f σ - c) * a ≤ (-a * f σ + G) + (f σ - c) * a := by linarith
        _ = G - a * c := by ring
        _ = 0 := by rw [hc_eq]; ring
    have : D * Real.exp (a * (σ - s)) + (f σ - c) * (a * Real.exp (a * (σ - s))) =
        (D + (f σ - c) * a) * Real.exp (a * (σ - s)) := by ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg hkey hepos.le
  have hanti : AntitoneOn h (Icc s τ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s τ) ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨D, hD, _⟩ := hderivAt σ hσ
      exact hD.continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      obtain ⟨D, hD, _⟩ := hderivAt σ (Ioo_subset_Icc_self hσ)
      exact hD.differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      obtain ⟨D, hD, hD0⟩ := hderivAt σ (Ioo_subset_Icc_self hσ)
      rw [hD.deriv]
      exact hD0
  have hmono := hanti ⟨le_rfl, hsτ⟩ ⟨hsτ, le_rfl⟩ hsτ
  have hhs : h s = f s - c := by simp [hh]
  rw [hhs] at hmono
  have hmono' : (f τ - c) * Real.exp (a * (τ - s)) ≤ f s - c := hmono
  have hexp1 : 1 ≤ Real.exp (a * (τ - s)) :=
    Real.one_le_exp (mul_nonneg ha.le (sub_nonneg.mpr hsτ))
  by_cases hcase : f s - c ≤ 0
  · have : (f τ - c) * Real.exp (a * (τ - s)) ≤ 0 := hmono'.trans hcase
    have hfτ : f τ - c ≤ 0 := nonpos_of_mul_nonpos_left this (Real.exp_pos _)
    exact le_max_of_le_right (by linarith)
  · push Not at hcase
    have hfτ : f τ - c ≤ f s - c := by
      have hepos := Real.exp_pos (a * (τ - s))
      by_contra hcontra
      push Not at hcontra
      have : (f s - c) * Real.exp (a * (τ - s)) < (f τ - c) * Real.exp (a * (τ - s)) :=
        mul_lt_mul_of_pos_right hcontra hepos
      have h1 : f s - c ≤ (f s - c) * Real.exp (a * (τ - s)) :=
        le_mul_of_one_le_right hcase.le hexp1
      linarith [hmono', this, h1]
    exact le_max_of_le_left (by linarith)

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-! ## Finite families -/

/-- The energy of a finite family of modes. -/
def familyEnergy (family : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ k ∈ family, modalEnergy (velocity := velocity) k τ

/-- The total squared half-radius cost of a finite family. -/
def familyCost (t : Ioo 0 T) (family : Finset SpatialFrequency) : ℝ :=
  ∑ k ∈ family, halfRadiusCost solution t k ^ 2

theorem familyEnergy_nonneg (family : Finset SpatialFrequency) (τ : ℝ) :
    0 ≤ familyEnergy (velocity := velocity) family τ :=
  Finset.sum_nonneg fun k _ ↦ modalEnergy_nonneg k τ

/-- **The family Riccati inequality.**  Every mode of sup-norm at least `m` dissipates at least
at `ν (2π)² m²`, and the drive is the family cost. -/
theorem familyEnergy_riccati (hnu : 0 < nu) (t : Ioo 0 T) {m : ℕ} (hm : 1 ≤ m)
    {family : Finset SpatialFrequency} (hfamily : ∀ k ∈ family, m ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (familyEnergy (velocity := velocity) family) D t.1 ∧
      D ≤ -(nu * ((2 * Real.pi) ^ 2 * (m : ℝ) ^ 2)) *
            familyEnergy (velocity := velocity) family t.1 +
          3 ^ 5 / nu * familyCost solution t family := by
  have hmode : ∀ k ∈ family, ∃ D : ℝ,
      HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
        D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
          3 ^ 5 / nu * halfRadiusCost solution t k ^ 2 :=
    fun k hk ↦ modalEnergy_riccati_halfRadius solution hnu t (hm.trans (hfamily k hk))
  choose! D hD using hmode
  refine ⟨∑ k ∈ family, D k, ?_, ?_⟩
  · unfold familyEnergy
    have hfun : (fun τ ↦ ∑ k ∈ family, modalEnergy (velocity := velocity) k τ) =
        ∑ k ∈ family, modalEnergy (velocity := velocity) k := by
      funext τ
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum fun k hk ↦ (hD k hk).1
  · unfold familyEnergy familyCost
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    refine (hD k hk).2.trans ?_
    have hE := modalEnergy_nonneg (velocity := velocity) k t.1
    have hlam : (2 * Real.pi) ^ 2 * (m : ℝ) ^ 2 ≤ torusStokesEigenvalue k := by
      refine le_trans ?_ (torusStokesEigenvalue_ge k)
      have : (m : ℝ) ≤ (frequencySup k : ℕ) := by exact_mod_cast hfamily k hk
      have hm0 : (0 : ℝ) ≤ m := by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 this 2) (by positivity)
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam hnu.le) hE
    linarith

/-- **The family Gronwall bound.** -/
theorem familyEnergy_le_of_familyCost_le (hnu : 0 < nu) {m : ℕ} (hm : 1 ≤ m)
    {family : Finset SpatialFrequency} (hfamily : ∀ k ∈ family, m ≤ frequencySup k)
    {s : ℝ} (hs : s ∈ Ioo 0 T) {M : ℝ}
    (hM : ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ → familyCost solution ⟨σ, hσ⟩ family ≤ M)
    {τ : ℝ} (hτ : τ ∈ Ico s T) :
    familyEnergy (velocity := velocity) family τ ≤
      max (familyEnergy (velocity := velocity) family s)
        (3 ^ 5 / nu * M / (nu * ((2 * Real.pi) ^ 2 * (m : ℝ) ^ 2))) := by
  have ha : 0 < nu * ((2 * Real.pi) ^ 2 * (m : ℝ) ^ 2) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  refine le_max_of_hasDerivAt_le ha hτ.1 ?_
  intro σ hσ
  have hσT : σ ∈ Ioo 0 T := ⟨hs.1.trans_le hσ.1, hσ.2.trans_lt hτ.2⟩
  obtain ⟨D, hD, hle⟩ := familyEnergy_riccati solution hnu ⟨σ, hσT⟩ hm hfamily
  refine ⟨D, hD, hle.trans ?_⟩
  have hcost := hM σ hσT hσ.1
  have h35 : 0 ≤ 3 ^ 5 / nu := by positivity
  have := mul_le_mul_of_nonneg_left hcost h35
  linarith

/-! ## The tail -/

/-- The modes of sup-norm at least `m`. -/
abbrev TailMode (m : ℕ) := {k : SpatialFrequency // m ≤ frequencySup k}

/-- The tail energy beyond sup-norm `m`. -/
def tailEnergy (m : ℕ) (τ : ℝ) : ℝ :=
  ∑' k : TailMode m, modalEnergy (velocity := velocity) k.1 τ

/-- The total squared half-radius cost of the tail beyond sup-norm `m`. -/
def tailCost (t : Ioo 0 T) (m : ℕ) : ℝ :=
  ∑' k : TailMode m, halfRadiusCost solution t k.1 ^ 2

theorem familyEnergy_map_le_tailEnergy {m : ℕ} (family : Finset (TailMode m)) (τ : ℝ)
    (hsum : Summable fun k : TailMode m ↦ modalEnergy (velocity := velocity) k.1 τ) :
    familyEnergy (velocity := velocity) (family.map (Function.Embedding.subtype _)) τ ≤
      tailEnergy (velocity := velocity) m τ := by
  unfold familyEnergy tailEnergy
  rw [Finset.sum_map]
  exact hsum.sum_le_tsum family (fun k _ ↦ modalEnergy_nonneg k.1 τ)

/-- **The tail Gronwall bound.**  If the total squared half-radius cost of the tail is bounded by
`M` on `[s, T)`, the tail energy beyond sup-norm `m` is bounded on `[s, T)` by the maximum of
its value at `s` and `3⁵ M / (ν² (2π)² m²)`. -/
theorem tailEnergy_le_of_tailCost_le (hnu : 0 < nu) {m : ℕ} (hm : 1 ≤ m) {s : ℝ}
    (hs : s ∈ Ioo 0 T)
    (hsum_s : Summable fun k : TailMode m ↦ modalEnergy (velocity := velocity) k.1 s)
    {M : ℝ}
    (hcost : ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
      (Summable fun k : TailMode m ↦ halfRadiusCost solution ⟨σ, hσ⟩ k.1 ^ 2) ∧
        tailCost solution ⟨σ, hσ⟩ m ≤ M)
    {τ : ℝ} (hτ : τ ∈ Ico s T) :
    tailEnergy (velocity := velocity) m τ ≤
      max (tailEnergy (velocity := velocity) m s)
        (3 ^ 5 / nu * M / (nu * ((2 * Real.pi) ^ 2 * (m : ℝ) ^ 2))) := by
  unfold tailEnergy
  refine Real.tsum_le_of_sum_le (fun k ↦ modalEnergy_nonneg k.1 τ) ?_
  intro family
  have hfamily : ∀ k ∈ family.map (Function.Embedding.subtype _), m ≤ frequencySup k := by
    intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨⟨k', hk'⟩, _, rfl⟩ := hk
    exact hk'
  have hM : ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
      familyCost solution ⟨σ, hσ⟩ (family.map (Function.Embedding.subtype _)) ≤ M := by
    intro σ hσ hsσ
    obtain ⟨hsumc, hle⟩ := hcost σ hσ hsσ
    refine le_trans ?_ hle
    unfold familyCost tailCost
    rw [Finset.sum_map]
    exact hsumc.sum_le_tsum family (fun k _ ↦ sq_nonneg _)
  have hfam := familyEnergy_le_of_familyCost_le solution hnu hm hfamily hs hM hτ
  have hs_le := familyEnergy_map_le_tailEnergy (velocity := velocity) family s hsum_s
  have hsum_eq : ∑ k ∈ family, modalEnergy (velocity := velocity) k.1 τ =
      familyEnergy (velocity := velocity) (family.map (Function.Embedding.subtype _)) τ := by
    unfold familyEnergy
    rw [Finset.sum_map]
    rfl
  rw [hsum_eq]
  refine hfam.trans (max_le_max_right _ ?_)
  unfold tailEnergy at hs_le
  exact hs_le

section Audit

#print axioms le_max_of_hasDerivAt_le
#print axioms familyEnergy_riccati
#print axioms familyEnergy_le_of_familyCost_le
#print axioms tailEnergy_le_of_tailCost_le

end Audit

end Soma.Holonics.Millennium.NavierStokesTailGronwall
