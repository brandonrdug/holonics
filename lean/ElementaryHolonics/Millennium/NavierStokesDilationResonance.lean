import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact jets of the regular-singular dilation transport

The swirl continuation uses `q L' - gamma L`. Differentiating this actual source operator shifts
its scalar coefficient. At a resonant integer derivative order, the corresponding source jet
must vanish; a zero multiplier is never treated as an invertible scalar.
-/

noncomputable section

open ContDiff
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDilationResonance

def dilationTransport (gamma : ℝ) (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  q * deriv f q - gamma * f q

theorem deriv_dilationTransport (gamma : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    deriv (dilationTransport gamma f) = dilationTransport (gamma - 1) (deriv f) := by
  have hfd : ContDiff ℝ ∞ (deriv f) := by fun_prop
  funext q
  have h := ((hasDerivAt_id q).mul ((hfd.differentiable (by simp) q).hasDerivAt)).sub
    (((hf.differentiable (by simp) q).hasDerivAt).const_mul gamma)
  convert h.deriv using 1 <;>
    first | rfl | (simp only [dilationTransport, mul_one, one_mul, id_eq] <;> ring)

theorem iteratedDeriv_dilationTransport (n : ℕ) (gamma : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (dilationTransport gamma f) =
      dilationTransport (gamma - n) (iteratedDeriv n f) := by
  induction n generalizing gamma f with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_dilationTransport gamma f hf]
    have hfd : ContDiff ℝ ∞ (deriv f) := by fun_prop
    rw [ih (gamma - 1) (deriv f) hfd, ← iteratedDeriv_succ']
    congr 1
    push_cast
    ring

theorem iteratedDeriv_dilationTransport_zero (n : ℕ) (gamma : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (dilationTransport gamma f) 0 =
      ((n : ℝ) - gamma) * iteratedDeriv n f 0 := by
  rw [iteratedDeriv_dilationTransport n gamma f hf]
  simp [dilationTransport]
  ring

/-- An actual smooth solution of the scalar transport equation must retain this complete jet
relation at the zero transport axis. -/
theorem source_jet_of_dilationTransport (n : ℕ) (gamma : ℝ) (f source : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hsource : dilationTransport gamma f = source) :
    iteratedDeriv n source 0 = ((n : ℝ) - gamma) * iteratedDeriv n f 0 := by
  rw [← hsource]
  exact iteratedDeriv_dilationTransport_zero n gamma f hf

theorem resonant_source_jet_eq_zero (n : ℕ) (f source : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hsource : dilationTransport (n : ℝ) f = source) :
    iteratedDeriv n source 0 = 0 := by
  rw [source_jet_of_dilationTransport n n f source hf hsource, sub_self, zero_mul]

theorem nonzero_resonant_jet_excludes_smooth_solution (n : ℕ) (source : ℝ → ℝ)
    (hjet : iteratedDeriv n source 0 ≠ 0) :
    ¬ ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ dilationTransport (n : ℝ) f = source := by
  rintro ⟨f,hf,hsource⟩
  exact hjet (resonant_source_jet_eq_zero n f source hf hsource)

theorem nonresonant_jet_reconstruction (n : ℕ) (gamma : ℝ) (f source : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hsource : dilationTransport gamma f = source)
    (hne : (n : ℝ) - gamma ≠ 0) :
    iteratedDeriv n f 0 = iteratedDeriv n source 0 / ((n : ℝ) - gamma) := by
  apply (eq_div_iff hne).mpr
  simpa only [mul_comm] using (source_jet_of_dilationTransport n gamma f source hf hsource).symm

theorem dilationTransport_monomial (n : ℕ) (gamma c : ℝ) :
    dilationTransport gamma (fun q ↦ c * q ^ n) = fun q ↦ ((n : ℝ) - gamma) * c * q ^ n := by
  funext q
  have hd : HasDerivAt (fun q : ℝ ↦ c * q ^ n) (c * ((n : ℝ) * q ^ (n - 1))) q := by
    convert (((hasDerivAt_id q).pow n).const_mul c) using 1 <;>
      first | rfl | (simp only [id_eq] <;> ring)
  rw [dilationTransport, hd.deriv]
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]; ring

theorem dilationTransport_add (gamma : ℝ) (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dilationTransport gamma (fun q ↦ f q + g q) =
      fun q ↦ dilationTransport gamma f q + dilationTransport gamma g q := by
  funext q
  rw [dilationTransport, deriv_fun_add (hf q) (hg q)]
  simp only [dilationTransport]
  ring

/-- The resonant homogeneous direction remains a full free fibre until another source relation
constrains it. The zero multiplier does not select the coefficient zero. -/
theorem resonant_monomial_preserves_source (n : ℕ) (c : ℝ) (f source : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hsource : dilationTransport (n : ℝ) f = source) :
    dilationTransport (n : ℝ) (fun q ↦ f q + c * q ^ n) = source := by
  rw [dilationTransport_add _ _ _ (hf.differentiable (by simp)) (by fun_prop),
    dilationTransport_monomial, hsource]
  simp

theorem nonresonant_monomial_inverse (n : ℕ) (gamma c : ℝ)
    (hne : (n : ℝ) - gamma ≠ 0) :
    dilationTransport gamma (fun q ↦ (c / ((n : ℝ) - gamma)) * q ^ n) =
      fun q ↦ c * q ^ n := by
  rw [dilationTransport_monomial]
  funext q
  field_simp

#print axioms iteratedDeriv_dilationTransport_zero
#print axioms nonzero_resonant_jet_excludes_smooth_solution
#print axioms nonresonant_jet_reconstruction
#print axioms resonant_monomial_preserves_source
#print axioms nonresonant_monomial_inverse

end Soma.Holonics.Millennium.NavierStokesDilationResonance
