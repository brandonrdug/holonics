import ElementaryHolonics.RH.MellinHorizon

/-!
# The functional equation is a symmetry the magnitude already had

`MellinHorizon` returns `‖Λ₀(s)‖ ≤ W(Re s/2)` where `W(σ) = ∫₀^∞ t^{σ−1}‖ker(t)‖dt`: **the entire
size of the completed zeta is a function of one real variable.**  This file asks what the
functional equation does to that variable, and the answer is sharper than expected.

The theta relation `ker(1/x) = x^{1/2}·ker(x)` survives the passage to magnitudes — the phase it
carries is exactly what the norm deletes — and what is left is

```text
W(σ) = W(1/2 − σ) ,
```

a reflection of the *abscissa* with fixed point `1/4`.  Since `Λ₀` reads `W` at `Re s/2`, that
fixed point is `Re s = 1/2`.

The consequence is the one worth carrying: `(1−σ)/2 = 1/2 − σ/2` is exactly the weight's own
reflection, so `‖Λ₀(s)‖ ≤ W(Re s/2)` and `‖Λ₀(1−s)‖ ≤ W((1−Re s)/2)` are **the same bound at every
point**, not two bounds that happen to meet on the critical line.  So the functional equation adds
nothing to the magnitude reading; the magnitude was already reflection-invariant, and the critical
line is where its abscissa is its own image.

That is the corpus's own statement — *a magnitude does not cross a frame boundary; only the ratio
does* — arriving as a theorem about `ζ`: the reflection is visible in the phase and invisible in
the size, which is precisely the phase-object reading.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.RH.WeightSymmetry

open Complex MeasureTheory Set Real HurwitzZeta
open Soma.Holonics.RH.MellinHorizon

/-- Shorthand for the kernel whose Mellin transform is `Λ₀`. -/
abbrev ker : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

/-- At `a = 0` the pair is its own mirror, so the modified kernel satisfies the functional
equation with itself. -/
theorem theKernelIsSelfMirrored {x : ℝ} (hx : 0 < x) :
    ker (1 / x) = ((x ^ (1/2 : ℝ) : ℝ) : ℂ) • ker x := by
  have h := (hurwitzEvenFEPair 0).hf_modif_FE x hx
  have hg : (hurwitzEvenFEPair 0).g_modif = ker := by
    have : (hurwitzEvenFEPair 0).symm.f_modif = (hurwitzEvenFEPair 0).g_modif := rfl
    rw [← this, hurwitzEvenFEPair_zero_symm]
  have hk : (hurwitzEvenFEPair 0).k = 1/2 := rfl
  have he : (hurwitzEvenFEPair 0).ε = 1 := rfl
  rw [hg, hk, he] at h
  simpa using h

/-- Hence the magnitude satisfies it too, with the phase gone. -/
theorem theKernelNormEquation {x : ℝ} (hx : 0 < x) :
    ‖ker x⁻¹‖ = x ^ (1/2 : ℝ) * ‖ker x‖ := by
  have := theKernelIsSelfMirrored hx
  rw [one_div] at this
  rw [this, norm_smul]
  simp [abs_of_nonneg (Real.rpow_nonneg hx.le _)]

/-! ## The bound is symmetric, and the critical line is the fixed abscissa -/

/-! ## The weight has its own functional equation -/

/-- The weight, as a genuine Mellin transform of the magnitude. -/
abbrev normKer : ℝ → ℂ := fun t => ((‖ker t‖ : ℝ) : ℂ)

/-- The real weight and the complex Mellin transform of the magnitude agree. -/
theorem theWeightIsAMellinTransform (σ : ℝ) :
    mellin normKer ((σ : ℝ) : ℂ) = ((mellinWeight ker σ : ℝ) : ℂ) := by
  rw [mellin, mellinWeight, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have htp : (0:ℝ) < t := ht
  have hc : ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, ← Complex.ofReal_cpow htp.le]
  simp [smul_eq_mul]

/-- **THE WEIGHT IS ITS OWN REFLECTION: `W(σ) = W(1/2 − σ)`.**  The theta functional equation
`ker(1/x) = x^{1/2} ker(x)` survives the passage to magnitudes — the phase it carries is exactly
what the norm deletes, and what is left is a symmetry of the *bound* rather than of the function.
Its fixed abscissa is `1/4`, which is `Re s = 1/2`. -/
theorem theWeightIsSymmetric (σ : ℝ) : mellinWeight ker σ = mellinWeight ker (1/2 - σ) := by
  set s : ℂ := ((σ : ℝ) : ℂ) - 1/2 with hs
  have hinv : mellin (fun t => normKer t⁻¹) s = mellin normKer (-s) := mellin_comp_inv normKer s
  have hshift : mellin (fun t => normKer t⁻¹) s = mellin normKer (s + 1/2) := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htp : (0:ℝ) < t := ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
    have hn : ‖ker t⁻¹‖ = t ^ (1/2 : ℝ) * ‖ker t‖ := theKernelNormEquation htp
    have hnc : normKer t⁻¹ = (t : ℂ) ^ (((1/2 : ℝ)) : ℂ) * normKer t := by
      simp only [normKer, hn]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow htp.le]
    have hadd : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (((1/2 : ℝ)) : ℂ) = (t : ℂ) ^ (s + 1/2 - 1) := by
      rw [← Complex.cpow_add _ _ htne]
      congr 1
      push_cast
      ring
    simp only [smul_eq_mul, hnc]
    rw [← mul_assoc, hadd]
  have hkey : mellin normKer (s + 1/2) = mellin normKer (-s) := by rw [← hshift, hinv]
  have h1 : s + 1/2 = ((σ : ℝ) : ℂ) := by rw [hs]; ring
  have h2 : -s = (((1/2 - σ : ℝ)) : ℂ) := by rw [hs]; push_cast; ring
  rw [h1, h2, theWeightIsAMellinTransform, theWeightIsAMellinTransform] at hkey
  exact_mod_cast hkey

/-- The Mellin bound at an arbitrary point, in abscissa form. -/
theorem theBoundAtAnyPoint (z : ℂ) :
    ‖completedRiemannZeta₀ z‖ ≤ mellinWeight ker (z.re / 2) := by
  have h := theMellinMagnitudeSeesOnlyTheRealPart ker (z / 2)
  have hre : (z / 2).re = z.re / 2 := by simp
  rw [hre] at h
  have hw : (0:ℝ) ≤ mellinWeight ker (z.re / 2) := le_trans (norm_nonneg _) h
  rw [theCompletedZetaIsAMellinTransform, norm_div, show ‖(2:ℂ)‖ = (2:ℝ) by simp]
  linarith [h, hw]

/-- **THE MAGNITUDE BOUND IS SYMMETRIC UNDER THE REFLECTION.**  `Λ₀(1−s) = Λ₀(s)`, and the Mellin
bound sees only the abscissa, so *two* bounds apply at every point and the smaller governs. -/
theorem theCompletedZetaBoundIsSymmetric (s : ℂ) :
    ‖completedRiemannZeta₀ s‖
      ≤ min (mellinWeight ker (s.re / 2)) (mellinWeight ker ((1 - s.re) / 2)) := by
  refine le_min (theBoundAtAnyPoint s) ?_
  have hfe : completedRiemannZeta₀ s = completedRiemannZeta₀ (1 - s) :=
    (completedRiemannZeta₀_one_sub s).symm
  have hre : (1 - s).re = 1 - s.re := by simp
  rw [hfe]
  have := theBoundAtAnyPoint (1 - s)
  rwa [hre] at this

/-- **AND THE TWO ABSCISSAE COINCIDE EXACTLY ON THE CRITICAL LINE.**  `σ/2 = (1−σ)/2 ↔ σ = 1/2`:
the critical line is the locus where the magnitude bound is its own reflection, so it is the
unique place where the two readings collapse to one.  Same shape as the coincidence of the two
involutions — a fixed locus, not a singularity. -/
theorem theAbscissaeCoincideExactlyOnTheCriticalLine (s : ℂ) :
    s.re / 2 = (1 - s.re) / 2 ↔ s.re = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **SO THE TWO BOUNDS ARE ONE BOUND.**  `(1−σ)/2 = 1/2 − σ/2`, which is exactly the weight's
own reflection, so the reflected reading returns the *same number* at every point — not merely on
the critical line.  The functional equation is not extra information about the magnitude; it is a
symmetry the magnitude already had. -/
theorem theTwoBoundsAreOneBound (s : ℂ) :
    mellinWeight ker ((1 - s.re) / 2) = mellinWeight ker (s.re / 2) := by
  rw [theWeightIsSymmetric (s.re / 2)]
  congr 1
  ring

/-- The weight is nonnegative: it integrates a nonnegative function. -/
theorem theWeightIsNonnegative (σ : ℝ) : 0 ≤ mellinWeight ker σ := by
  rw [mellinWeight]
  refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
  have htp : (0:ℝ) < t := ht
  positivity

end Soma.Holonics.RH.WeightSymmetry
