import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# A ring's fade as its own state: its covector is the skin's homogeneity

Atlas: `store.ring-fade-as-state`. Record: `research/records/2026-11-24_HER_RINGS_HOLD_THEIR_FADES_AS_HER_OWN_STATE_…` (§1).

A turned ring's skin reads her clock only through `γ |s|`, `γ = 2^ℓ` the ring's fade and `s` a pair's variation
(`Declaration::fade`). So a loss `L(γ s)` of the product moves with the fade as `ln 2` times the product times its own
derivative, and that equals `ln 2 · s · ∂L/∂s` at the fade it stands at: the engine's `fade_term`, one pair's share
`−release(ln 2 · release(|s| term, MATERIAL_BITS − FACE_BITS), LN2_FACE_BITS)` with `term` the clock covector's share,
summed over the ring's pairs.

1. `fade_homogeneity`: `d/dℓ f(2^ℓ s) = ln 2 · (2^ℓ s) · f′(2^ℓ s)`.
2. `fade_covector_eq`: the same derivative is `ln 2 · s · d/ds f(2^ℓ s)`, the variation times the loss's derivative
   in it at the fade that stands.
3. `fade_covector_sum`: over a ring's pairs the fade's covector is `ln 2 Σ_i s_i ∂L/∂s_i`.
-/

namespace Holonics.HNN.FadeHomogeneity

open Real

/-- The fade moves a skin of the product `γ s` as `ln 2` times the product times the skin's own derivative. -/
theorem fade_homogeneity (f : ℝ → ℝ) (s ℓ : ℝ) (hf : DifferentiableAt ℝ f ((2 : ℝ) ^ ℓ * s)) :
    HasDerivAt (fun l : ℝ => f ((2 : ℝ) ^ l * s)) (Real.log 2 * ((2 : ℝ) ^ ℓ * s) * deriv f ((2 : ℝ) ^ ℓ * s)) ℓ := by
  have h2 : HasDerivAt (fun l : ℝ => (2 : ℝ) ^ l) ((2 : ℝ) ^ ℓ * Real.log 2) ℓ :=
    (Real.hasStrictDerivAt_const_rpow (by norm_num : (0 : ℝ) < 2) ℓ).hasDerivAt
  have hm : HasDerivAt (fun l : ℝ => (2 : ℝ) ^ l * s) ((2 : ℝ) ^ ℓ * Real.log 2 * s) ℓ := h2.mul_const s
  have hc := hf.hasDerivAt.comp ℓ hm
  exact hc.congr_deriv (by ring)

/-- The loss's derivative in the variation at a standing fade: `d/ds f(2^ℓ s) = 2^ℓ f′(2^ℓ s)`. -/
theorem variation_derivative (f : ℝ → ℝ) (s ℓ : ℝ) (hf : DifferentiableAt ℝ f ((2 : ℝ) ^ ℓ * s)) :
    HasDerivAt (fun u : ℝ => f ((2 : ℝ) ^ ℓ * u)) ((2 : ℝ) ^ ℓ * deriv f ((2 : ℝ) ^ ℓ * s)) s := by
  have hm : HasDerivAt (fun u : ℝ => (2 : ℝ) ^ ℓ * u) ((2 : ℝ) ^ ℓ) s := by
    simpa using (hasDerivAt_id s).const_mul ((2 : ℝ) ^ ℓ)
  have hc := hf.hasDerivAt.comp s hm
  exact hc.congr_deriv (by ring)

/-- The fade's covector is `ln 2` times the variation times the loss's derivative in it, at the fade that stands. -/
theorem fade_covector_eq (f : ℝ → ℝ) (s ℓ : ℝ) (hf : DifferentiableAt ℝ f ((2 : ℝ) ^ ℓ * s)) :
    deriv (fun l : ℝ => f ((2 : ℝ) ^ l * s)) ℓ = Real.log 2 * s * deriv (fun u : ℝ => f ((2 : ℝ) ^ ℓ * u)) s := by
  rw [(fade_homogeneity f s ℓ hf).deriv, (variation_derivative f s ℓ hf).deriv]
  ring

/-- Over a ring's pairs, each read through its own skin of the product `γ s_i`, the fade's covector is
`ln 2 Σ_i s_i ∂L/∂s_i`. -/
theorem fade_covector_sum {ι : Type*} (pairs : Finset ι) (f : ι → ℝ → ℝ) (s : ι → ℝ) (ℓ : ℝ)
    (hf : ∀ i ∈ pairs, DifferentiableAt ℝ (f i) ((2 : ℝ) ^ ℓ * s i)) :
    deriv (fun l : ℝ => ∑ i ∈ pairs, f i ((2 : ℝ) ^ l * s i)) ℓ
      = Real.log 2 * ∑ i ∈ pairs, s i * deriv (fun u : ℝ => f i ((2 : ℝ) ^ ℓ * u)) (s i) := by
  have hsum : HasDerivAt (fun l : ℝ => ∑ i ∈ pairs, f i ((2 : ℝ) ^ l * s i))
      (∑ i ∈ pairs, Real.log 2 * ((2 : ℝ) ^ ℓ * s i) * deriv (f i) ((2 : ℝ) ^ ℓ * s i)) ℓ := by
    have := HasDerivAt.sum (u := pairs) (fun i hi => fade_homogeneity (f i) (s i) ℓ (hf i hi))
    have hfun : (∑ i ∈ pairs, fun l : ℝ => f i ((2 : ℝ) ^ l * s i)) = fun l : ℝ => ∑ i ∈ pairs, f i ((2 : ℝ) ^ l * s i) := by
      funext l
      simp [Finset.sum_apply]
    rw [hfun] at this
    exact this
  rw [hsum.deriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(variation_derivative (f i) (s i) ℓ (hf i hi)).deriv]
  ring

end Holonics.HNN.FadeHomogeneity
