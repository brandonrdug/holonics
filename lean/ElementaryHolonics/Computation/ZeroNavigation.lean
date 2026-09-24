import Mathlib

/-!
# Zero navigation: exact finite observations and generator travel

These are source-class constraints for a Holonic zero solver. A finite set of
point observations cannot decide zero existence over all analytic generators:
an explicit finite product agrees with the constant-one source on every
queried point and vanishes at an unqueried target. A finite propagation cone
does follow for an ordered generator word when every constituent has a
declared metric travel bound. Neither statement chooses a universal solver
policy or an intrinsic speed for every source.
-/

noncomputable section

namespace Soma.Holonics.Computation.ZeroNavigation

open scoped BigOperators

/-- A finite-product source that agrees with the constant-one source at
the queries and has a prescribed zero at the target when the target is
unqueried. The denominator is a source coefficient, not a sampled float. -/
def finiteQueryTwin (queries : Finset ℂ) (target : ℂ) (z : ℂ) : ℂ :=
  1 - (queries.prod fun q => z - q) / (queries.prod fun q => target - q)

/-- The adversarial twin is an entire finite-product source in its
variable, including when its target denominator happens to vanish. -/
theorem finiteQueryTwin_differentiable (queries : Finset ℂ) (target : ℂ) :
    Differentiable ℂ (finiteQueryTwin queries target) := by
  unfold finiteQueryTwin
  fun_prop

/-- Every queried value is exactly one, independently of the target. -/
theorem finiteQueryTwin_on_query (queries : Finset ℂ) (target q : ℂ)
    (hq : q ∈ queries) :
    finiteQueryTwin queries target q = 1 := by
  have hzero : (queries.prod fun x => q - x) = 0 :=
    Finset.prod_eq_zero hq (by simp)
  simp [finiteQueryTwin, hzero]

/-- An unqueried target is an exact zero of the twin source. -/
theorem finiteQueryTwin_target_zero (queries : Finset ℂ) (target : ℂ)
    (htarget : target ∉ queries) :
    finiteQueryTwin queries target target = 0 := by
  have hnonzero : (queries.prod fun q => target - q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    apply sub_ne_zero.mpr
    intro heq
    apply htarget
    simpa [heq] using hq
  simp [finiteQueryTwin, hnonzero]

/-- An ordered generator word; the rightmost entry is applied last. -/
def applyWord {X : Type*} : List (X → X) → X → X
  | [], x => x
  | generator :: rest, x => applyWord rest (generator x)

/-- An exact causal cone relative to a *declared* metric and per-generator
travel law. Without that locality hypothesis, an arbitrary generator can
jump any distance in one step. -/
theorem word_speed_cone {X : Type*} [PseudoMetricSpace X]
    (word : List (X → X)) (radius : (X → X) → ℝ)
    (hlocal : ∀ generator ∈ word, ∀ x, dist x (generator x) ≤ radius generator)
    (x : X) :
    dist x (applyWord word x) ≤ (word.map radius).sum := by
  induction word generalizing x with
  | nil =>
      simp [applyWord]
  | cons generator rest ih =>
      have hstep : dist x (generator x) ≤ radius generator :=
        hlocal generator (by simp) x
      have hrest : ∀ g ∈ rest, ∀ y, dist y (g y) ≤ radius g := by
        intro g hg y
        exact hlocal g (by simp [hg]) y
      have htail := ih hrest (generator x)
      calc
        dist x (applyWord (generator :: rest) x)
            = dist x (applyWord rest (generator x)) := rfl
        _ ≤ dist x (generator x) +
              dist (generator x) (applyWord rest (generator x)) := dist_triangle _ _ _
        _ ≤ radius generator + (rest.map radius).sum := add_le_add hstep htail
        _ = ((generator :: rest).map radius).sum := by simp

end Soma.Holonics.Computation.ZeroNavigation

section Audit
open Soma.Holonics.Computation.ZeroNavigation
#print axioms finiteQueryTwin_on_query
#print axioms finiteQueryTwin_differentiable
#print axioms finiteQueryTwin_target_zero
#print axioms word_speed_cone
end Audit
