import HolonicsResearch.RH.FosterClassFlux
import HolonicsResearch.RH.FosterClassHeatFlow
import HolonicsResearch.RH.FosterSplit
import HolonicsResearch.RH.TransverseCurrentBound

/-!
# Finite zero-current enclosures

The principal-value zero current is a receiver approximation with an explicit Foster tail.  This
owner keeps the local factor, multiplicity-one and disc hypotheses visible; it makes no global
zero ordering or convergence claim.
-/

noncomputable section

namespace Holonics.RH.FiniteZeroCurrent

open Complex Metric Set Filter Topology
open Holonics.RH.FosterClassFlux
open Holonics.RH.FosterSplit
open Holonics.RH.FosterClassLandau
open Holonics.RH.HeatFlowEntire
open Holonics.RH.RiemannXi
open Holonics.RH.FosterClassHeatFlow

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-- The finite zero current remaining after removing a simple zero and its
same-height reflected partner from the half-disc divisor. -/
noncomputable def reflectedFiniteSurplus (f : ℂ → ℂ) (A B σ : ℝ)
    [FosterClass f A B σ] {R : ℝ} (hR : 0 < R) (z₀ : ℂ) : ℂ :=
  ∑ ρ ∈ ((FosterClassSplit.Zfac (f := f) hR).zeros.erase z₀).erase
      (Holonics.RH.PairPopulation.reflect z₀),
    ((FosterClassSplit.Zfac (f := f) hR).mult ρ : ℂ) / (z₀ - ρ)

/-- Exact finite-disc decomposition of the punctured Foster comb into its
reflected partner current and the remaining finite surplus. The partner's
membership and multiplicity are explicit hypotheses: a factorization centered
at `1/2` only records the holomorphic symmetry `z ↦ 1-z`, whereas this
same-height pair uses `1-conj z`.
-/
theorem comb'_eq_reflected_pair_add_surplus {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hreflectmem : Holonics.RH.PairPopulation.reflect z₀ ∈
      (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflect_ne : Holonics.RH.PairPopulation.reflect z₀ ≠ z₀)
    (hmreflect : (FosterClassSplit.Zfac (f := f) hR).mult
      (Holonics.RH.PairPopulation.reflect z₀) = 1) :
    (comb' (f := f) hR z₀ z₀) =
      ((1 : ℂ) / (z₀ - Holonics.RH.PairPopulation.reflect z₀)) +
        reflectedFiniteSurplus f A B σ hR z₀ := by
  unfold comb' reflectedFiniteSurplus
  have hmemErase : Holonics.RH.PairPopulation.reflect z₀ ∈
      (FosterClassSplit.Zfac (f := f) hR).zeros.erase z₀ :=
    Finset.mem_erase.mpr ⟨hreflect_ne, hreflectmem⟩
  rw [← Finset.add_sum_erase _ _ hmemErase]
  simp [hmreflect]

/-- The local logarithmic current at a simple zero differs from the centered
reflected-pair plus finite-surplus current by at most the explicit Foster tail.
This is the bounded bridge from the finite divisor receiver to the local source
current; no uniform-in-height bound is asserted.
-/
theorem logDeriv_local_eq_reflected_pair_add_surplus_with_tail
    {z₀ : ℂ} {g : ℂ → ℂ} {δ R : ℝ}
    (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - z₀) * g y)
    (hR : 0 < R)
    (hz₀mem : z₀ ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflectmem : Holonics.RH.PairPopulation.reflect z₀ ∈
      (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflect_ne : Holonics.RH.PairPopulation.reflect z₀ ≠ z₀)
    (hm : (FosterClassSplit.Zfac (f := f) hR).mult z₀ = 1)
    (hmreflect : (FosterClassSplit.Zfac (f := f) hR).mult
      (Holonics.RH.PairPopulation.reflect z₀) = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8) :
    ‖logDeriv g z₀ -
        ((1 : ℂ) / (z₀ - Holonics.RH.PairPopulation.reflect z₀) +
          reflectedFiniteSurplus f A B σ hR z₀)‖ ≤
      2 * (‖z₀ - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R := by
  have hcomb := (comb'_sub_le (f := f)) hδ hball hR hz₀mem hm hRa
  rw [comb'_eq_reflected_pair_add_surplus (f := f) hR hreflectmem
    hreflect_ne hmreflect] at hcomb
  simpa only [norm_sub_rev] using hcomb

omit hf in
theorem heatE_logDeriv_local_eq_reflected_pair_add_surplus_with_tail
    {τ : ℝ} {A B σ : ℝ} {z₀ : ℂ} {g : ℂ → ℂ} {δ R : ℝ}
    [hflow : FosterClass (heatE (-τ) riemannXi) A B σ]
    (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧
        heatE (-τ) riemannXi y = (y - z₀) * g y)
    (hR : 0 < R)
    (hz₀mem : z₀ ∈
      (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros)
    (hreflectmem : Holonics.RH.PairPopulation.reflect z₀ ∈
      (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros)
    (hreflect_ne : Holonics.RH.PairPopulation.reflect z₀ ≠ z₀)
    (hm : (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).mult z₀ = 1)
    (hmreflect : (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).mult
      (Holonics.RH.PairPopulation.reflect z₀) = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8) :
    ‖logDeriv g z₀ -
        ((1 : ℂ) / (z₀ - Holonics.RH.PairPopulation.reflect z₀) +
          reflectedFiniteSurplus (heatE (-τ) riemannXi) A B σ hR z₀)‖ ≤
      2 * (‖z₀ - 1 / 2‖ + δ / 2) *
        FosterClassSplit.tailInvSq (heatE (-τ) riemannXi) R := by
  exact logDeriv_local_eq_reflected_pair_add_surplus_with_tail
    (f := heatE (-τ) riemannXi) hδ hball hR hz₀mem hreflectmem
    hreflect_ne hm hmreflect hRa

theorem norm_negative_zero_velocity_sub_comb_le {z₀ : ℂ} {g : ℂ → ℂ} {δ R : ℝ}
    (hz₀ : f z₀ = 0) (hs : deriv f z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ = deriv f z₀)
    (hev : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) * g z)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - z₀) * g y)
    (hR : 0 < R)
    (hz₀mem : z₀ ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hm : (FosterClassSplit.Zfac (f := f) hR).mult z₀ = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8) :
    ‖-deriv (deriv f) z₀ / deriv f z₀ -
        (-2 * (comb' (f := f)) hR z₀ z₀)‖ ≤
      4 * (‖z₀ - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R := by
  have hcomb := (comb'_sub_le (f := f)) hδ hball hR hz₀mem hm hRa
  have hlog : logDeriv g z₀ = deriv g z₀ / g z₀ := by
    rw [logDeriv_apply]
  have hratio : deriv (deriv f) z₀ / deriv f z₀ = 2 * logDeriv g z₀ := by
    rw [deriv_deriv_eq hg hev, hlog, ← hg0]
    ring
  have hratio_neg : -deriv (deriv f) z₀ / deriv f z₀ =
      -(2 * logDeriv g z₀) := by
    rw [neg_div, hratio]
  rw [hratio_neg]
  calc
    ‖- (2 * logDeriv g z₀) - -2 * (comb' (f := f)) hR z₀ z₀‖ =
        ‖2 * ((comb' (f := f)) hR z₀ z₀ - logDeriv g z₀)‖ := by
          congr 1
          ring
    _ = 2 * ‖(comb' (f := f)) hR z₀ z₀ - logDeriv g z₀‖ := by
          rw [norm_mul]
          norm_num
    _ ≤ 4 * (‖z₀ - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R := by
          nlinarith [hcomb]

/-- The actual finite Foster bound supplies the error operand in transverse descent. -/
theorem re_negative_zero_velocity_le {z₀ : ℂ} {g : ℂ → ℂ} {δ R d J : ℝ}
    (hz₀ : f z₀ = 0) (hs : deriv f z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ = deriv f z₀)
    (hev : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) * g z)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - z₀) * g y)
    (hR : 0 < R)
    (hz₀mem : z₀ ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hm : (FosterClassSplit.Zfac (f := f) hR).mult z₀ = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8)
    (hsplit : (2 * (comb' (f := f)) hR z₀ z₀).re = 1 / d + J) :
    (-deriv (deriv f) z₀ / deriv f z₀).re ≤
      -1 / d - J + 4 * (‖z₀ - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R :=
  TransverseCurrentBound.re_velocity_le_of_complex_error
    (norm_negative_zero_velocity_sub_comb_le hz₀ hs hg hg0 hev hδ hball hR hz₀mem hm hRa)
    hsplit

/-! The same local theorem is available at the actual flowed xi source through its Foster instance. -/

omit hf in
theorem heatE_norm_negative_zero_velocity_sub_comb_le {τ : ℝ} {z₀ : ℂ} {g : ℂ → ℂ} {δ R : ℝ}
    (hz₀ : heatE (-τ) riemannXi z₀ = 0)
    (hs : deriv (heatE (-τ) riemannXi) z₀ ≠ 0)
    (hg : AnalyticAt ℂ g z₀)
    (hg0 : g z₀ = deriv (heatE (-τ) riemannXi) z₀)
    (hev : ∀ᶠ z in 𝓝 z₀,
      heatE (-τ) riemannXi z = (z - z₀) * g z)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y z₀ < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧
        heatE (-τ) riemannXi y = (y - z₀) * g y)
    (hR : 0 < R)
    (hz₀mem : z₀ ∈ (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros)
    (hm : (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).mult z₀ = 1)
    (hRa : ‖z₀ - 1 / 2‖ + δ / 2 ≤ R / 8) :
    ‖-deriv (deriv (heatE (-τ) riemannXi)) z₀ /
          deriv (heatE (-τ) riemannXi) z₀ -
        (-2 * (comb' (f := heatE (-τ) riemannXi)) hR z₀ z₀)‖ ≤
      4 * (‖z₀ - 1 / 2‖ + δ / 2) *
        FosterClassSplit.tailInvSq (heatE (-τ) riemannXi) R := by
  letI := FosterClassHeatFlow.instFosterClassHeatE (-τ)
  exact norm_negative_zero_velocity_sub_comb_le hz₀ hs hg hg0 hev hδ hball hR hz₀mem hm hRa

end Holonics.RH.FiniteZeroCurrent

section Audit
open Holonics.RH.FiniteZeroCurrent
#print axioms norm_negative_zero_velocity_sub_comb_le
#print axioms re_negative_zero_velocity_le
#print axioms heatE_norm_negative_zero_velocity_sub_comb_le
#print axioms comb'_eq_reflected_pair_add_surplus
#print axioms logDeriv_local_eq_reflected_pair_add_surplus_with_tail
#print axioms heatE_logDeriv_local_eq_reflected_pair_add_surplus_with_tail
end Audit
