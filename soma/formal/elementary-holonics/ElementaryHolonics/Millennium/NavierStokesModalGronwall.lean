import ElementaryHolonics.Millennium.NavierStokesModalRiccati

/-!
# A bounded shell-step cost keeps every tail mode bounded

The modal Riccati inequality is put into its arithmetic-geometric form,

```text
E_k' ≤ −ν lam_k E_k + 243 · B_N² / ν,
```

and integrated.  If the shell-step cost stays below `M` on a terminal tail `[s, T)`, then every
tail mode's energy stays below `max (E_k(s), 243 M² / (ν² lam_k))` on that tail.  The bound decays
with the Stokes eigenvalue: a mode farther out is held closer to its equilibrium
`243 M² / (ν² lam_k)` by its own dissipation.

The integration is the weighted maximum principle already used for transported scalars: the
weighted excess `(E_k − c) · e^{ν lam_k (τ − s)}` has nonpositive derivative once `B_N ≤ M`, so it
is antitone.

This is a bounded-cost theorem, not a closure.  It converts the open obligation from "the tail
mass is integrable" to "the shell-step cost is bounded on a terminal tail", and it does not sum
over the tail.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesModalGronwall

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-! ## The eigenvalue of a tail mode is positive -/

theorem one_le_frequencySquared_of_not_mem {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube radius) : 1 ≤ frequencySquared k := by
  rw [mem_frequencyCube_iff] at hk
  push Not at hk
  obtain ⟨coordinate, hcoordinate⟩ := hk
  have hne : k coordinate ≠ 0 := by
    intro h0
    rw [h0] at hcoordinate
    omega
  have hsq : (1 : ℝ) ≤ (k coordinate : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k coordinate) ^ 2 := by
      rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
    exact_mod_cast this
  unfold frequencySquared
  refine hsq.trans (Finset.single_le_sum (f := fun j : Fin 3 ↦ (k j : ℝ) ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ coordinate))

theorem torusStokesEigenvalue_pos_of_not_mem {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube radius) : 0 < torusStokesEigenvalue k := by
  unfold torusStokesEigenvalue
  have := one_le_frequencySquared_of_not_mem hk
  positivity

/-! ## The arithmetic-geometric form -/

theorem amgm_step (hnu : 0 < nu) (x y : ℝ) :
    18 * x * y ≤ nu / 3 * x ^ 2 + 243 / nu * y ^ 2 := by
  have hrewrite : nu / 3 * x ^ 2 + 243 / nu * y ^ 2 =
      (nu ^ 2 / 3 * x ^ 2 + 243 * y ^ 2) / nu := by
    field_simp
  rw [hrewrite, le_div_iff₀ hnu]
  nlinarith [sq_nonneg (nu * x - 27 * y)]

/-- **The modal Riccati inequality in arithmetic-geometric form.** -/
theorem modalEnergy_riccati_amgm (hnu : 0 < nu) (t : Ioo 0 T) {radius : ℕ}
    {k : SpatialFrequency} (hk : k ∉ frequencyCube (2 * radius)) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
        243 / nu * feedBound solution t radius ^ 2 := by
  obtain ⟨D, hD, hle⟩ := modalEnergy_riccati solution hnu.le t hk
  refine ⟨D, hD, hle.trans ?_⟩
  set lam := torusStokesEigenvalue k with hlam
  set E := modalEnergy (velocity := velocity) k t.1 with hE
  set L := complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) with hL
  set B := feedBound solution t radius with hB
  have hlam0 : 0 ≤ lam := (torusStokesEigenvalue_pos_of_not_mem hk).le
  have hL2 : L ^ 2 ≤ 3 * E := complexVectorL1_sq_le_three_mul_modalEnergy k t.1
  have hstep := amgm_step hnu (L * Real.sqrt lam) B
  have hsqrt : (L * Real.sqrt lam) ^ 2 = L ^ 2 * lam := by
    rw [mul_pow, Real.sq_sqrt hlam0]
  have hcross : 2 * L * (9 * Real.sqrt lam * B) = 18 * (L * Real.sqrt lam) * B := by ring
  rw [hcross]
  have hmid : nu / 3 * (L * Real.sqrt lam) ^ 2 ≤ nu * lam * E := by
    rw [hsqrt]
    have : L ^ 2 * lam ≤ 3 * E * lam := mul_le_mul_of_nonneg_right hL2 hlam0
    nlinarith
  linarith

/-! ## Integration on a terminal tail -/

theorem feedBound_nonneg (t : Ioo 0 T) (radius : ℕ) : 0 ≤ feedBound solution t radius := by
  unfold feedBound
  have h1 : 0 ≤ openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) :=
    norm_nonneg _
  have h2 : 0 ≤ openPeriodicJacobianCoefficientTailMass solution t ∅ := norm_nonneg _
  have h3 : 0 ≤ velocityTailMass solution t radius :=
    tsum_nonneg fun _ ↦ complexVectorL1_nonneg _
  positivity

/-- **A bounded shell-step cost keeps a tail mode bounded.**  On \`[s, T)\`, if the cost at radius
\`N\` never exceeds \`M\`, every mode outside the cube of radius \`2N\` keeps its energy below
\`max (E_k(s), 243 M² / (ν² lam_k))\`. -/
theorem modalEnergy_le_of_feedBound_le (hnu : 0 < nu) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) {s : ℝ} (hs : s ∈ Ioo 0 T) {M : ℝ}
    (hM : ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ → feedBound solution ⟨σ, hσ⟩ radius ≤ M)
    {τ : ℝ} (hτ : τ ∈ Ico s T) :
    modalEnergy (velocity := velocity) k τ ≤
      max (modalEnergy (velocity := velocity) k s)
        (243 * M ^ 2 / (nu ^ 2 * torusStokesEigenvalue k)) := by
  set lam := torusStokesEigenvalue k with hlam
  have hlampos : 0 < lam := torusStokesEigenvalue_pos_of_not_mem hk
  set c : ℝ := 243 * M ^ 2 / (nu ^ 2 * lam) with hc
  set E := modalEnergy (velocity := velocity) k with hE
  have hc_eq : nu * lam * c = 243 / nu * M ^ 2 := by
    rw [hc]
    field_simp
  -- the weighted excess and its derivative
  set h : ℝ → ℝ := fun σ ↦ (E σ - c) * Real.exp (nu * lam * (σ - s)) with hh
  have hexp : ∀ σ : ℝ, HasDerivAt (fun σ ↦ Real.exp (nu * lam * (σ - s)))
      (nu * lam * Real.exp (nu * lam * (σ - s))) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ ↦ nu * lam * (σ - s)) (nu * lam) σ := by
      simpa using ((hasDerivAt_id σ).sub_const s).const_mul (nu * lam)
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hderivAt : ∀ σ ∈ Icc s τ, ∃ D, HasDerivAt h D σ ∧ D ≤ 0 := by
    intro σ hσ
    have hσT : σ ∈ Ioo 0 T := ⟨hs.1.trans_le hσ.1, hσ.2.trans_lt hτ.2⟩
    obtain ⟨D, hD, hle⟩ := modalEnergy_riccati_amgm solution hnu ⟨σ, hσT⟩ hk
    have hB := hM σ hσT hσ.1
    have hB0 := feedBound_nonneg solution ⟨σ, hσT⟩ radius
    have hB2 : feedBound solution ⟨σ, hσT⟩ radius ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hB0 hB 2
    have hD' : D ≤ -(nu * lam) * E σ + 243 / nu * M ^ 2 := by
      have h243 : 0 ≤ 243 / nu := by positivity
      have := mul_le_mul_of_nonneg_left hB2 h243
      linarith
    refine ⟨D * Real.exp (nu * lam * (σ - s)) + (E σ - c) * (nu * lam * Real.exp (nu * lam * (σ - s))),
      (hD.sub_const c).mul (hexp σ), ?_⟩
    have hepos : 0 < Real.exp (nu * lam * (σ - s)) := Real.exp_pos _
    have hkey : D + (E σ - c) * (nu * lam) ≤ 0 := by
      calc D + (E σ - c) * (nu * lam)
          ≤ (-(nu * lam) * E σ + 243 / nu * M ^ 2) + (E σ - c) * (nu * lam) := by linarith
        _ = 243 / nu * M ^ 2 - nu * lam * c := by ring
        _ = 0 := by rw [hc_eq]; ring
    have : D * Real.exp (nu * lam * (σ - s)) + (E σ - c) * (nu * lam * Real.exp (nu * lam * (σ - s))) =
        (D + (E σ - c) * (nu * lam)) * Real.exp (nu * lam * (σ - s)) := by ring
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
  have hτs : s ≤ τ := hτ.1
  have hmono := hanti ⟨le_rfl, hτs⟩ ⟨hτs, le_rfl⟩ hτs
  -- h τ ≤ h s = E s - c
  have hhs : h s = E s - c := by simp [hh]
  rw [hhs] at hmono
  have hmono' : (E τ - c) * Real.exp (nu * lam * (τ - s)) ≤ E s - c := hmono
  have hexp1 : 1 ≤ Real.exp (nu * lam * (τ - s)) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg hnu.le hlampos.le) (sub_nonneg.mpr hτs))
  by_cases hcase : E s - c ≤ 0
  · have : (E τ - c) * Real.exp (nu * lam * (τ - s)) ≤ 0 := hmono.trans hcase
    have hEτ : E τ - c ≤ 0 :=
      nonpos_of_mul_nonpos_left this (Real.exp_pos _)
    exact le_max_of_le_right (by linarith)
  · push Not at hcase
    have hEτ : E τ - c ≤ E s - c := by
      have hepos := Real.exp_pos (nu * lam * (τ - s))
      by_contra hcontra
      push Not at hcontra
      have : (E s - c) * Real.exp (nu * lam * (τ - s)) < (E τ - c) * Real.exp (nu * lam * (τ - s)) :=
        mul_lt_mul_of_pos_right hcontra hepos
      have h1 : E s - c ≤ (E s - c) * Real.exp (nu * lam * (τ - s)) :=
        le_mul_of_one_le_right hcase.le hexp1
      linarith [hmono', this, h1]
    exact le_max_of_le_left (by linarith)

section Audit

#print axioms modalEnergy_riccati_amgm
#print axioms modalEnergy_le_of_feedBound_le

end Audit

end Soma.Holonics.Millennium.NavierStokesModalGronwall
