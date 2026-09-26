import Mathlib
import HolonicsResearch.Zeta.DescentZeros
import HolonicsResearch.Zeta.HeatKernelPhi

/-!
# A palette law that forces the seam cannot be closed under damping

The completed zeta is the seam transform of its palette `Φ`:
`heatE t ξ (z) = ∫ e^{−tu²} Φ(u) e^{(z−½)u} du` (`HeatKernelPhi.heatE_riemannXi`). Read as a
partition function (the primon gas: single-mode energies `log p`, Euler product = Fock
factorization), a natural candidate source law is a positivity or correlation inequality on the
palette that implies the Lee–Yang property (all zeros on the seam).

For every `t > 0` the damped palette `e^{−tu²}Φ` has an off-seam zero (`DescentZeros`,
Rodgers–Tao's direction). Hence [proved-derived; formal-checked]:

- `seamForcingLaw_not_dampingClosed`: a palette law that holds for `Φ` and forces every zero of
  every palette in its class onto the seam is **not** closed under multiplication by `e^{−tu²}`.
- `dampingClosedLaw_does_not_force_seam`: every damping-closed law that `Φ` satisfies is also
  satisfied by a palette whose transform has an off-seam zero.
- Instances: positivity (`palettePositivity_does_not_force_seam`) and log-concavity
  (`logConcavePalette_dampingClosed`) are damping-closed, so neither can be the source law.
  The Lee–Yang property itself is closed under `e^{+λu²}` (the sharpening direction), not under
  damping; as a law it is equivalent to RH by construction.

These are falsifier receipts for the source-to-neck campaign (#62): they reject candidate
source laws; they prove nothing toward RH.
-/

noncomputable section

namespace Holonics.Zeta.PaletteLaw

open Holonics.Zeta.HeatKernelPhi
open Holonics.Zeta.HeatFlowEntire
open Holonics.Zeta.RiemannXi
open Holonics.Zeta.DescentZeros

/-- The seam transform of a real palette: `∫ K(u) e^{(z−½)u} du`. -/
def paletteTransform (K : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (K u : ℂ) * Complex.exp ((z - 1 / 2) * u)

/-- The palette damped by the Gaussian `e^{−tu²}`. -/
def damp (t : ℝ) (K : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (-t * u ^ 2) * K u

/-- **The damped palette of `ξ` transforms to the flow.** -/
theorem paletteTransform_damp_Φ (t : ℝ) (z : ℂ) :
    paletteTransform (damp t Φ) z = heatE t riemannXi z := by
  rw [heatE_riemannXi]
  unfold paletteTransform damp flowLap lap
  congr 1
  funext u
  push_cast
  ring

/-- The damped palette's transform is an absolutely convergent integral at every point. -/
theorem integrable_damp_Φ {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    MeasureTheory.Integrable (fun u : ℝ => (damp t Φ u : ℂ) * Complex.exp ((z - 1 / 2) * u)) := by
  refine (integrable_lap z).norm.mono' ?_ ?_
  · unfold damp
    have hΦc := continuous_Φ
    have hc : Continuous fun u : ℝ =>
        ((Real.exp (-t * u ^ 2) * Φ u : ℝ) : ℂ) * Complex.exp ((z - 1 / 2) * u) := by
      fun_prop
    exact hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_lap, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    unfold damp
    rw [abs_of_pos (mul_pos (Real.exp_pos _) (Φ_pos u))]
    have hre : ((z - 1 / 2) * (u : ℂ)).re = (z.re - 1 / 2) * u := by simp
    rw [hre]
    have h1 : Real.exp (-t * u ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
    have h2 := (Φ_pos u).le
    have h3 := (Real.exp_pos ((z.re - 1 / 2) * u)).le
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 h3)]

/-- **A palette law closed under damping cannot force the seam** [proved-derived;
formal-checked]: if `Φ` satisfies it, so does the damped palette `e^{−u²}Φ`, whose transform
`heatE 1 ξ` is an absolutely convergent integral everywhere and has an off-seam zero. -/
theorem dampingClosedLaw_does_not_force_seam (P : (ℝ → ℝ) → Prop) (hΦ : P Φ)
    (hdamp : ∀ K, P K → ∀ t : ℝ, 0 < t → P (damp t K)) :
    ∃ K : ℝ → ℝ, P K ∧
      (∀ z : ℂ, MeasureTheory.Integrable fun u : ℝ => (K u : ℂ) * Complex.exp ((z - 1 / 2) * u)) ∧
      ∃ z : ℂ, paletteTransform K z = 0 ∧ z.re ≠ 1 / 2 := by
  refine ⟨damp 1 Φ, hdamp Φ hΦ 1 one_pos, integrable_damp_Φ zero_le_one, ?_⟩
  obtain ⟨z, hz, hre⟩ := exists_offSeam_zero (t := 1) one_pos
  exact ⟨z, by rw [paletteTransform_damp_Φ]; exact hz, hre⟩

/-- **A seam-forcing palette law satisfied by `Φ` is not damping-closed** [proved-derived;
formal-checked]. -/
theorem seamForcingLaw_not_dampingClosed (P : (ℝ → ℝ) → Prop) (hΦ : P Φ)
    (hforce : ∀ K, P K → ∀ z : ℂ, paletteTransform K z = 0 → z.re = 1 / 2) :
    ¬ ∀ K, P K → ∀ t : ℝ, 0 < t → P (damp t K) := by
  intro hdamp
  obtain ⟨K, hK, _, z, hz, hre⟩ := dampingClosedLaw_does_not_force_seam P hΦ hdamp
  exact hre (hforce K hK z hz)

/-- **Palette positivity does not force the seam** [proved-derived; formal-checked]. -/
theorem palettePositivity_does_not_force_seam :
    ∃ K : ℝ → ℝ, (∀ u, 0 < K u) ∧
      (∀ z : ℂ, MeasureTheory.Integrable fun u : ℝ => (K u : ℂ) * Complex.exp ((z - 1 / 2) * u)) ∧
      ∃ z : ℂ, paletteTransform K z = 0 ∧ z.re ≠ 1 / 2 :=
  dampingClosedLaw_does_not_force_seam (fun K => ∀ u, 0 < K u) Φ_pos
    (fun _ hK _ _ u => mul_pos (Real.exp_pos _) (hK u))

/-- A positive palette whose logarithm is concave (a Pólya-frequency-two, ferromagnetic-type
palette). -/
def LogConcavePalette (K : ℝ → ℝ) : Prop :=
  (∀ u, 0 < K u) ∧ ConcaveOn ℝ Set.univ (fun u => Real.log (K u))

/-- **Log-concavity is damping-closed**: `log(e^{−tu²}K) = −tu² + log K`. -/
theorem logConcavePalette_dampingClosed (K : ℝ → ℝ) (hK : LogConcavePalette K) (t : ℝ)
    (ht : 0 < t) : LogConcavePalette (damp t K) := by
  refine ⟨fun u => mul_pos (Real.exp_pos _) (hK.1 u), ?_⟩
  have hlog : (fun u => Real.log (damp t K u)) = fun u => -t * u ^ 2 + Real.log (K u) := by
    funext u
    unfold damp
    rw [Real.log_mul (Real.exp_pos _).ne' (hK.1 u).ne', Real.log_exp]
  rw [hlog]
  have hsq : ConvexOn ℝ Set.univ (fun u : ℝ => u ^ 2) := even_two.convexOn_pow
  have hq : ConcaveOn ℝ Set.univ (fun u : ℝ => -t * u ^ 2) := by
    have := (hsq.smul ht.le).neg
    refine this.congr ?_
    intro u _
    simp only [Pi.neg_apply, smul_eq_mul]
    ring
  exact hq.add hK.2

/-- **Log-concavity of the palette does not force the seam** [proved-derived; formal-checked]:
if `Φ` is log-concave, a log-concave palette with an off-seam zero exists. -/
theorem logConcavePalette_does_not_force_seam (hΦ : LogConcavePalette Φ) :
    ∃ K : ℝ → ℝ, LogConcavePalette K ∧
      (∀ z : ℂ, MeasureTheory.Integrable fun u : ℝ => (K u : ℂ) * Complex.exp ((z - 1 / 2) * u)) ∧
      ∃ z : ℂ, paletteTransform K z = 0 ∧ z.re ≠ 1 / 2 :=
  dampingClosedLaw_does_not_force_seam LogConcavePalette hΦ logConcavePalette_dampingClosed

end Holonics.Zeta.PaletteLaw

#print axioms Holonics.Zeta.PaletteLaw.seamForcingLaw_not_dampingClosed
#print axioms Holonics.Zeta.PaletteLaw.palettePositivity_does_not_force_seam
#print axioms Holonics.Zeta.PaletteLaw.logConcavePalette_does_not_force_seam
