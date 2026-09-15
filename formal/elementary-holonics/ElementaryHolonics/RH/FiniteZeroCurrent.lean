import ElementaryHolonics.RH.FosterClassFlux
import ElementaryHolonics.RH.FosterClassHeatFlow
import ElementaryHolonics.RH.FosterSplit
import ElementaryHolonics.RH.TransverseCurrentBound

/-!
# Finite zero-current enclosures

The principal-value zero current is a receiver approximation with an explicit Foster tail.  This
owner keeps the local factor, multiplicity-one and disc hypotheses visible; it makes no global
zero ordering or convergence claim.
-/

noncomputable section

namespace Soma.Holonics.RH.FiniteZeroCurrent

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.FosterClassFlux
open Soma.Holonics.RH.FosterSplit
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.FosterClassHeatFlow

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

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

end Soma.Holonics.RH.FiniteZeroCurrent

section Audit
open Soma.Holonics.RH.FiniteZeroCurrent
#print axioms norm_negative_zero_velocity_sub_comb_le
#print axioms re_negative_zero_velocity_le
#print axioms heatE_norm_negative_zero_velocity_sub_comb_le
end Audit
