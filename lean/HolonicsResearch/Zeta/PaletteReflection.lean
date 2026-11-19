import Mathlib
import HolonicsResearch.Zeta.PaletteLaw
import HolonicsResearch.Coupling.HeatArrow

/-!
# The palette of ξ is not reflection positive across its seam at any time of the heat clock, and positive type is closed under the palette's damping and does not force the seam

Sources.  Atlas rows `rh.palette-damping-no-go`, `rh.scale-window-off-line`,
`rh.finite-weil-criterion`, `coupling.reflected-positivity` and `coupling.reflection-choice-sign`
(`docs/atlas/targets.tsv`); the Lean owners `Zeta/PaletteLaw` (`damp`, `paletteTransform`,
`dampingClosedLaw_does_not_force_seam`), `Zeta/HeatKernelPhi` (`Φ`, `Φ_neg`, `Φ_pos`,
`integrable_flow_half`) and `Coupling/HeatArrow` (the two laws of a kernel on the line); the
record of this pass (November 19).

The occasion.  A reader proposed that Weil positivity is reflection positivity of the palette
across the seam `u = 0`, kept by sharpening and broken by damping, matching the one-way arrow of
de Bruijn and Newman.  `Coupling/HeatArrow` separates the two positivities the sentence joins.
This module reads the palette `Φ` of `ξ` against each.

**What is proved.**

1. `exchangePositive_even_integrable_seam_eq_zero` [proved-derived]: an even exchange-positive
   kernel that is integrable on the line vanishes at the seam.  It is least at the seam
   (`ExchangePositive.seam_le`), and a function bounded below by a positive constant is not
   integrable on the line.
2. `Φ_not_exchangePositive`, `Φ_flow_not_exchangePositive` [proved-derived]: `Φ` is not exchange
   positive, and neither is `e^{τu²} Φ` for any real `τ`, sharpened or damped: each is even,
   integrable and positive at the seam.
3. `translationPositive_dampingClosed` [proved-derived]: translation positivity is closed under
   the palette's damping `damp t`.
4. `translationPositive_offSeam_witness` [counterexample]: the damped turning mode
   `e^{−u²} cos u` is translation positive, its seam transform converges absolutely at every
   point, and the transform vanishes at `z = ½ + π`.  So translation positivity does not force
   the seam, with no hypothesis on `Φ`.
5. `exchangePositive_not_closed_under_palette_damp` [counterexample]: exchange positivity is not
   closed under `damp t`, so the damping no-go of `Zeta/PaletteLaw` does not reach it.  Item 2
   rejects it as the palette's law by a different reason: `Φ` fails it.

**Limits.**  Whether `Φ` itself is translation positive is not stated here.  The classical
reading is that it is not (by Bochner's theorem a continuous integrable kernel of positive type
has a nonnegative transform, and the transform of `Φ` on the seam, `Ξ(t) = ξ(½ + it)`, changes
sign at its zeros of odd order), so the conditional form of the damping no-go
(`PaletteLaw.dampingClosedLaw_does_not_force_seam` with the law's instance at `Φ`) would carry a
hypothesis nothing meets, and it is left out; item 4 gives the conclusion with no hypothesis on
`Φ`.  Item 4's witness is not the palette of `ξ` or of any zeta function; it shows only that the
law does not force the seam.
Item 2 concerns the palette variable `u` and the exchange `u ↦ −u`; it says nothing of a
positivity stated on test functions (Weil's form, `Zeta/FiniteWeilCriterion`).  The kernels and
test vectors are real.  Nothing here is a step toward the Riemann hypothesis: each reading
rejects a candidate source law.

Computational object: the helical pair interaction.  Of the winding guide's six general objects
this module touches the pair (`u`, `v` and the reflection that exchanges them) and faces and
placement (a positive form places a mode); the helix, the cell holonomy, the tube and the tower
thread stay attached.

**Consumers.**  The atlas row `rh.palette-damping-no-go` and the record of this pass.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Zeta.PaletteReflection

open Holonics.Coupling.HeatArrow Holonics.Zeta.HeatKernelPhi Holonics.Zeta.PaletteLaw

/-- [proved-derived; formal-checked] **An even exchange-positive kernel that is integrable on the
line vanishes at the seam.**  Such a kernel is least at the seam (`ExchangePositive.seam_le`), so
the constant `|K 0|` is integrable on the line, which has infinite length. -/
theorem exchangePositive_even_integrable_seam_eq_zero {K : ℝ → ℝ} (h : ExchangePositive K)
    (heven : ∀ u, K (-u) = K u) (hint : MeasureTheory.Integrable K) : K 0 = 0 := by
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => |K 0|) := by
    refine hint.mono' MeasureTheory.aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact h.seam_le heven u
  rw [MeasureTheory.integrable_const_iff] at hconst
  rcases hconst with h0 | hfin
  · exact abs_eq_zero.mp h0
  · have hlt := MeasureTheory.measure_lt_top (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      Set.univ
    rw [Real.volume_univ] at hlt
    exact absurd hlt (lt_irrefl _)

/-- [proved-derived; formal-checked] **The palette of `ξ` is not reflection positive across its
own seam.**  `Φ` is even and integrable on the line, so exchange positivity would give `Φ 0 = 0`
(`exchangePositive_even_integrable_seam_eq_zero`), and `Φ 0 > 0`. -/
theorem Φ_not_exchangePositive : ¬ ExchangePositive Φ := by
  intro h
  have hint : MeasureTheory.Integrable Φ := by simpa using integrable_flow_half 0
  exact (Φ_pos 0).ne' (exchangePositive_even_integrable_seam_eq_zero h Φ_neg hint)

/-- [proved-derived; formal-checked] **No time of the heat clock makes the palette reflection
positive**: for every real `τ` (sharpening for `τ > 0`, damping for `τ < 0`) the palette
`e^{τu²} Φ` is even, integrable on the line (`HeatKernelPhi.integrable_flow_half`) and positive
at the seam, so it is not exchange positive. -/
theorem Φ_flow_not_exchangePositive (τ : ℝ) :
    ¬ ExchangePositive (fun u => Real.exp (τ * u ^ 2) * Φ u) := by
  intro h
  have hint : MeasureTheory.Integrable (fun u : ℝ => Real.exp (τ * u ^ 2) * Φ u) := by
    simpa using integrable_flow_half (-τ)
  have h0 : Real.exp (τ * (0 : ℝ) ^ 2) * Φ 0 = 0 :=
    exchangePositive_even_integrable_seam_eq_zero h (fun u => by simp only [neg_sq, Φ_neg]) hint
  exact (mul_pos (Real.exp_pos _) (Φ_pos 0)).ne' h0

/-- [proved-derived; formal-checked] **Positive type is closed under the palette's damping**:
`damp t K` is the Gaussian damping of `Coupling/HeatArrow`'s `translationPositive_damp`. -/
theorem translationPositive_dampingClosed (K : ℝ → ℝ) (hK : TranslationPositive K) (t : ℝ)
    (ht : 0 < t) : TranslationPositive (damp t K) :=
  translationPositive_damp hK ht.le

/-- [proved-standard; formal-checked] The damped turning mode's integrand is the half sum of two
complex Gaussians. -/
private theorem damp_cos_integrand (z : ℂ) (u : ℝ) :
    (damp 1 Real.cos u : ℂ) * Complex.exp ((z - 1 / 2) * u)
      = 1 / 2 * Complex.exp ((-1 : ℂ) * (u : ℂ) ^ 2 + (z - 1 / 2 + Complex.I) * u + 0)
        + 1 / 2 * Complex.exp ((-1 : ℂ) * (u : ℂ) ^ 2 + (z - 1 / 2 - Complex.I) * u + 0) := by
  have hK : (damp 1 Real.cos u : ℂ) = Complex.exp (-1 * (u : ℂ) ^ 2)
      * ((Complex.exp ((u : ℂ) * Complex.I) + Complex.exp (-(u : ℂ) * Complex.I)) / 2) := by
    unfold damp
    push_cast
    rw [Complex.cos]
  have e1 : Complex.exp ((-1 : ℂ) * (u : ℂ) ^ 2 + (z - 1 / 2 + Complex.I) * u + 0)
      = Complex.exp (-1 * (u : ℂ) ^ 2) * Complex.exp ((u : ℂ) * Complex.I)
        * Complex.exp ((z - 1 / 2) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp ((-1 : ℂ) * (u : ℂ) ^ 2 + (z - 1 / 2 - Complex.I) * u + 0)
      = Complex.exp (-1 * (u : ℂ) ^ 2) * Complex.exp (-(u : ℂ) * Complex.I)
        * Complex.exp ((z - 1 / 2) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hK, e1, e2]
  ring

/-- [counterexample; formal-checked] **Positive type does not force the seam**, with its witness
and no hypothesis on `Φ`.  The damped turning mode `e^{−u²} cos u` is translation positive
(`translationPositive_cos` damped for unit time), its seam transform is an absolutely convergent
integral at every point, and the transform vanishes at `z = ½ + π`, off the seam: the two complex
Gaussians of `cos` contribute `e^{(π² − 1)/4} · (i + (−i))`. -/
theorem translationPositive_offSeam_witness :
    ∃ K : ℝ → ℝ, TranslationPositive K ∧
      (∀ z : ℂ, MeasureTheory.Integrable fun u : ℝ => (K u : ℂ) * Complex.exp ((z - 1 / 2) * u)) ∧
      ∃ z : ℂ, paletteTransform K z = 0 ∧ z.re ≠ 1 / 2 := by
  have hb : ((-1 : ℂ)).re < 0 := by norm_num
  refine ⟨damp 1 Real.cos,
    translationPositive_dampingClosed Real.cos translationPositive_cos 1 one_pos, ?_,
    1 / 2 + (Real.pi : ℂ), ?_, ?_⟩
  · intro z
    simp_rw [damp_cos_integrand]
    exact ((integrable_cexp_quadratic' hb _ _).const_mul _).add
      ((integrable_cexp_quadratic' hb _ _).const_mul _)
  · unfold paletteTransform
    simp_rw [damp_cos_integrand]
    rw [MeasureTheory.integral_add ((integrable_cexp_quadratic' hb _ _).const_mul _)
        ((integrable_cexp_quadratic' hb _ _).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_cexp_quadratic hb, integral_cexp_quadratic hb]
    have a1 : (0 : ℂ) - (1 / 2 + (Real.pi : ℂ) - 1 / 2 + Complex.I) ^ 2 / (4 * -1)
        = ((Real.pi : ℂ) ^ 2 - 1) / 4 + (Real.pi : ℂ) / 2 * Complex.I := by
      linear_combination (1 / 4 : ℂ) * Complex.I_sq
    have a2 : (0 : ℂ) - (1 / 2 + (Real.pi : ℂ) - 1 / 2 - Complex.I) ^ 2 / (4 * -1)
        = ((Real.pi : ℂ) ^ 2 - 1) / 4 + (-((Real.pi : ℂ) / 2)) * Complex.I := by
      linear_combination (1 / 4 : ℂ) * Complex.I_sq
    rw [a1, a2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  · simp [Real.pi_ne_zero]

/-- [counterexample; formal-checked] **Exchange positivity is not closed under the palette's
damping**, so `PaletteLaw.seamForcingLaw_not_dampingClosed` gives no verdict on it: the constant
kernel `1` is exchange positive and `damp 1` of it is not. -/
theorem exchangePositive_not_closed_under_palette_damp :
    ¬ ∀ K : ℝ → ℝ, ExchangePositive K → ∀ t : ℝ, 0 < t → ExchangePositive (damp t K) :=
  fun h => exchangePositive_not_dampingClosed fun K hK t ht => h K hK t ht

end Holonics.Zeta.PaletteReflection

#print axioms Holonics.Zeta.PaletteReflection.Φ_not_exchangePositive
#print axioms Holonics.Zeta.PaletteReflection.Φ_flow_not_exchangePositive
#print axioms Holonics.Zeta.PaletteReflection.translationPositive_offSeam_witness
#print axioms Holonics.Zeta.PaletteReflection.exchangePositive_not_closed_under_palette_damp
