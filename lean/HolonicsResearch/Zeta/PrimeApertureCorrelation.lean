import HolonicsResearch.Zeta.ExplicitFormulaReceiver

/-!
# A finite aperture truncates the prime-power correlation

The unbounded translation receiver has a full Euler resolvent. A compactly
supported source test has a bounded log-line aperture: its autocorrelation
vanishes beyond the aperture diameter. This exact support law is independent
of any positivity claim and explains why a phase multiplier of the full
translation operator is not a pointwise sign certificate for an individual
compact test.
-/

noncomputable section

namespace Holonics.Zeta.PrimeApertureCorrelation

open MeasureTheory

/-- The oriented autocorrelation on the logarithmic line. -/
def apertureCorrelation (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, g (x + t) * (starRingEnd ℂ) (g x)

/-- No pair of points in the aperture can be separated by more than twice
its radius. The proof works directly on the source integrand, so no
integrability premise is needed for its zero conclusion. -/
theorem apertureCorrelation_eq_zero_of_two_mul_lt
    {g : ℝ → ℂ} {A t : ℝ}
    (hA : 0 ≤ A)
    (hg : ∀ x, A < |x| → g x = 0)
    (ht : 2 * A < t) :
    apertureCorrelation g t = 0 := by
  have hzero : (fun x : ℝ => g (x + t) * (starRingEnd ℂ) (g x)) = fun _ => 0 := by
    funext x
    by_cases hx : A < |x|
    · simp [hg x hx]
    · have hxb : -A ≤ x := by
        have habs : |x| ≤ A := le_of_not_gt hx
        exact (neg_le_of_abs_le habs)
      have hxt : A < x + t := by linarith
      have hxta : A < |x + t| := by
        rw [abs_of_pos (by linarith : 0 < x + t)]
        exact hxt
      simp [hg (x + t) hxta]
  rw [apertureCorrelation, hzero]
  simp

/-- The opposite orientation has the same aperture cutoff. -/
theorem apertureCorrelation_eq_zero_of_lt_neg_two_mul
    {g : ℝ → ℂ} {A t : ℝ}
    (hA : 0 ≤ A)
    (hg : ∀ x, A < |x| → g x = 0)
    (ht : t < -2 * A) :
    apertureCorrelation g t = 0 := by
  have hzero : (fun x : ℝ => g (x + t) * (starRingEnd ℂ) (g x)) = fun _ => 0 := by
    funext x
    by_cases hx : A < |x|
    · simp [hg x hx]
    · have hxb : x ≤ A := (abs_le.mp (le_of_not_gt hx)).2
      have hxt : x + t < -A := by linarith
      have hxta : A < |x + t| := by
        rw [abs_of_neg (by linarith : x + t < 0)]
        linarith
      simp [hg (x + t) hxta]
  rw [apertureCorrelation, hzero]
  simp

/-- Once the prime-power translation has crossed a compact log-line aperture,
every later power has zero contact in both orientations. The source population
of prime powers remains infinite; this receiver only admits finitely many. -/
theorem primePowerContact_vanishes_beyond_aperture
    {g : ℝ → ℂ} {A : ℝ} {p M m : ℕ}
    (hA : 0 ≤ A)
    (hg : ∀ x, A < |x| → g x = 0)
    (hp : 1 < p)
    (hM : 2 * A < (M : ℝ) * Real.log p)
    (hm : M ≤ m) :
    apertureCorrelation g ((m : ℝ) * Real.log p) = 0 ∧
      apertureCorrelation g (-((m : ℝ) * Real.log p)) = 0 := by
  have hlog : 0 ≤ Real.log p :=
    (Real.log_pos (by exact_mod_cast hp)).le
  have hMm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlag : 2 * A < (m : ℝ) * Real.log p :=
    lt_of_lt_of_le hM (mul_le_mul_of_nonneg_right hMm hlog)
  exact ⟨apertureCorrelation_eq_zero_of_two_mul_lt hA hg hlag,
    apertureCorrelation_eq_zero_of_lt_neg_two_mul hA hg (by linarith)⟩

section Audit

#print axioms apertureCorrelation_eq_zero_of_two_mul_lt
#print axioms apertureCorrelation_eq_zero_of_lt_neg_two_mul
#print axioms primePowerContact_vanishes_beyond_aperture

end Audit

end Holonics.Zeta.PrimeApertureCorrelation
