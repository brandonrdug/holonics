import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import ElementaryHolonics.RH.GammaBound

/-!
# The Mellin magnitude is blind to the height: the horizon law, in analysis

The strip front stalled on a stated absence — *"mathlib has no strip version of
Phragmén–Lindelöf"*, which is **false** (`Mathlib/Analysis/Complex/PhragmenLindelof.lean` carries
`vertical_strip` and `horizontal_strip`) — and, worse, on the assumption that a strip bound needs
a maximum principle at all.

It does not.  `Λ₀` **is** a Mellin transform, and a Mellin transform's magnitude cannot see the
imaginary part of its argument:

```text
‖∫₀^∞ t^{s−1} f(t) dt‖  ≤  ∫₀^∞ |t^{s−1}| ‖f(t)‖ dt  =  ∫₀^∞ t^{Re s − 1} ‖f(t)‖ dt .
```

`|t^{s−1}| = t^{Re s − 1}` for `t > 0`: **the height contributes phase and nothing else.**  This is
the horizon law verbatim — a magnitude does not cross the frame boundary, only the ratio does — and
it is the same sentence as `GammaDecay`'s reflection identity one floor down.

The consequence is stronger than what Phragmén–Lindelöf would have given.  On a vertical strip the
bound is not polynomial in the height; it is **constant** in the height, and the constant is the
sum of the two edge weights, because `t^{σ−1} ≤ t^{a−1} + t^{b−1}` splits at `t = 1`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.MellinHorizon

open Complex MeasureTheory Set Real

/-- The magnitude weight of a Mellin transform at real abscissa `σ`: everything the transform's
size can depend on. -/
def mellinWeight (f : ℝ → ℂ) (σ : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖f t‖

/-- The weight is exactly the integral of the norm of the Mellin integrand. -/
theorem theWeightIsTheIntegratedNorm (f : ℝ → ℂ) (σ : ℝ) :
    mellinWeight f σ = ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • f t‖ := by
  refine (setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)).symm
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- Convergence at a real abscissa gives integrability of the weight's integrand. -/
theorem theWeightIntegrandIsIntegrable {f : ℝ → ℂ} {σ : ℝ}
    (h : MellinConvergent f (σ : ℂ)) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖f t‖) (Ioi 0) := by
  have h' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • f t) (Ioi 0) := h
  refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm h')
    (fun t ht => ?_) measurableSet_Ioi
  have htp : (0:ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htp]
  simp

/-- Same, at a general `s`, indexed by its real part. -/
theorem theWeightIntegrandIsIntegrableAtAnyHeight {f : ℝ → ℂ} {s : ℂ}
    (h : MellinConvergent f s) :
    IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖f t‖) (Ioi 0) := by
  have h' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi 0) := h
  refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm h')
    (fun t ht => ?_) measurableSet_Ioi
  have htp : (0:ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htp]
  simp

/-- **THE MELLIN MAGNITUDE SEES ONLY THE REAL PART.**  The height enters the integrand purely as
a phase `t^{i·Im s}`, of modulus one, so it cannot change the size of the transform at all. -/
theorem theMellinMagnitudeSeesOnlyTheRealPart (f : ℝ → ℂ) (s : ℂ) :
    ‖mellin f s‖ ≤ mellinWeight f s.re := by
  rw [mellin, mellinWeight]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- **THE ABSCISSA WEIGHT IS DOMINATED BY ITS TWO EDGES.**  `t^{σ−1} ≤ t^{a−1} + t^{b−1}` for
`a ≤ σ ≤ b` — the split is at `t = 1`, where the two rpow monotonicities exchange hands.  This is
the whole reason a strip needs no maximum principle. -/
theorem theWeightIsDominatedByItsEdges {f : ℝ → ℂ} {a b σ : ℝ}
    (ha : MellinConvergent f (a : ℂ)) (hb : MellinConvergent f (b : ℂ))
    (hσ : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖f t‖) (Ioi 0))
    (h1 : a ≤ σ) (h2 : σ ≤ b) :
    mellinWeight f σ ≤ mellinWeight f a + mellinWeight f b := by
  have hA := theWeightIntegrandIsIntegrable ha
  have hB := theWeightIntegrandIsIntegrable hb
  have hsum : mellinWeight f a + mellinWeight f b
      = ∫ t in Ioi (0:ℝ), (t ^ (a - 1) * ‖f t‖ + t ^ (b - 1) * ‖f t‖) := by
    rw [mellinWeight, mellinWeight, ← integral_add hA hB]
  rw [hsum, mellinWeight]
  refine setIntegral_mono_on hσ (hA.add hB) measurableSet_Ioi (fun t ht => ?_)
  have htp : (0:ℝ) < t := ht
  have hf : (0:ℝ) ≤ ‖f t‖ := norm_nonneg _
  have hpoint : t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
    rcases le_total t 1 with hle | hle
    · have : t ^ (σ - 1) ≤ t ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge htp hle (by linarith)
      have hb0 : (0:ℝ) ≤ t ^ (b - 1) := (Real.rpow_pos_of_pos htp _).le
      linarith
    · have : t ^ (σ - 1) ≤ t ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le hle (by linarith)
      have ha0 : (0:ℝ) ≤ t ^ (a - 1) := (Real.rpow_pos_of_pos htp _).le
      linarith
  calc t ^ (σ - 1) * ‖f t‖ ≤ (t ^ (a - 1) + t ^ (b - 1)) * ‖f t‖ := by
        exact mul_le_mul_of_nonneg_right hpoint hf
    _ = t ^ (a - 1) * ‖f t‖ + t ^ (b - 1) * ‖f t‖ := by ring

/-- **A MELLIN TRANSFORM IS BOUNDED ON A VERTICAL STRIP, UNIFORMLY IN THE HEIGHT.**  Not
polynomially — *constantly*.  The bound is the sum of the two edge weights and does not mention
`Im s` at all. -/
theorem theMellinIsUniformlyBoundedOnAStrip {f : ℝ → ℂ} {a b : ℝ}
    (ha : MellinConvergent f (a : ℂ)) (hb : MellinConvergent f (b : ℂ))
    {s : ℂ} (hs : MellinConvergent f s) (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖mellin f s‖ ≤ mellinWeight f a + mellinWeight f b :=
  (theMellinMagnitudeSeesOnlyTheRealPart f s).trans
    (theWeightIsDominatedByItsEdges ha hb (theWeightIntegrandIsIntegrableAtAnyHeight hs) h1 h2)

/-! ## The completed zeta is a Mellin transform, so it is bounded on every strip -/

open HurwitzZeta in
/-- `Λ₀` is literally a Mellin transform of the modified even kernel, halved. -/
theorem theCompletedZetaIsAMellinTransform (s : ℂ) :
    completedRiemannZeta₀ s = mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := rfl

open HurwitzZeta in
/-- Its integrand converges at every point of the plane. -/
theorem theEvenKernelConverges (w : ℂ) :
    MellinConvergent (hurwitzEvenFEPair 0).f_modif w :=
  let P := hurwitzEvenFEPair 0
  mellinConvergent_of_isBigO_rpow P.hf_modif_int
    ((P.isStrongFEPair_toStrongFEPair).hf_top (-(w.re + 1))) (by norm_num)
    ((P.isStrongFEPair_toStrongFEPair).hf_zero (-(w.re - 1))) (by norm_num)

open HurwitzZeta in
/-- **`Λ₀` IS BOUNDED ON EVERY VERTICAL STRIP, AND THE BOUND DOES NOT MENTION THE HEIGHT.**  The
front that was waiting on Phragmén–Lindelöf never needed it: the completed zeta is a Mellin
transform, and a Mellin transform's magnitude is a function of the abscissa alone. -/
theorem theCompletedZetaIsBoundedOnAStrip {a b : ℝ} {s : ℂ}
    (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖completedRiemannZeta₀ s‖
      ≤ (mellinWeight (hurwitzEvenFEPair 0).f_modif (a / 2)
          + mellinWeight (hurwitzEvenFEPair 0).f_modif (b / 2)) / 2 := by
  rw [theCompletedZetaIsAMellinTransform, norm_div]
  have h : ‖mellin (hurwitzEvenFEPair 0).f_modif (s / 2)‖
      ≤ mellinWeight (hurwitzEvenFEPair 0).f_modif (a / 2)
        + mellinWeight (hurwitzEvenFEPair 0).f_modif (b / 2) := by
    refine theMellinIsUniformlyBoundedOnAStrip
      (theEvenKernelConverges ((a / 2 : ℝ) : ℂ)) (theEvenKernelConverges ((b / 2 : ℝ) : ℂ))
      (theEvenKernelConverges (s / 2)) ?_ ?_
    · simp only [Complex.div_re]
      simp [Complex.normSq_ofNat]
      linarith
    · simp only [Complex.div_re]
      simp [Complex.normSq_ofNat]
      linarith
  simpa using div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)

open HurwitzZeta in
/-- **THE STRIP FRONT CLOSES, AND WITH EXPONENT ZERO.**  `GammaBound` posed the remaining content
as *"the slice bounds grow at most polynomially in the height"*.  They do not grow at all: the
Mellin representation bounds `Λ₀` by a constant across the whole strip `0 ≤ Re s ≤ 2`.  The
polynomial is a constant, and the maximum principle was never needed. -/
theorem theSliceBoundsArePolynomialInTheHeight :
    GammaBound.TheSliceBoundsArePolynomialInTheHeight := by
  set W : ℝ := (mellinWeight (hurwitzEvenFEPair 0).f_modif (0 / 2)
      + mellinWeight (hurwitzEvenFEPair 0).f_modif (2 / 2)) / 2 with hW
  refine ⟨max 1 W, 0, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  rintro t _ s ⟨x, hx, rfl⟩
  have hre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
  have hb := theCompletedZetaIsBoundedOnAStrip (a := 0) (b := 2)
      (s := (x : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2)
  calc ‖completedRiemannZeta₀ ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ W := by rw [hW]; exact hb
    _ ≤ max 1 W := le_max_right _ _
    _ = max 1 W * |t| ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_one]

end Soma.Holonics.RH.MellinHorizon
