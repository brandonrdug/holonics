import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A passage regenerated from the current law carries no new evidence

The record `research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md`
(atlas `probe.information-value`) prices a probe by the information it gives about the surviving
constitutions, and reads a passage regenerated from the current law as worthless in expectation:
`Σ_y P(y | h) P(θ | h, y) = P(θ | h)`. #410 owes that identity; this file proves it for a finite
fibre of constitutions `Θ` and finite readings `Y`, over any field.

[proved-standard; formal-checked] What is proved.

1. **The marginal times the posterior is the joint** (`marginal_mul_posterior`), wherever a reading
   of zero marginal has zero joint weight (`null_of_nonneg`: every nonnegative law).
2. **No new evidence from regeneration** (`regeneration_no_new_evidence`): the posterior averaged
   over readings drawn from the current law is the prior.
3. **The expected update is zero** (`expected_update_zero`): for a normalized law,
   `Σ_y P(y | h) (P(θ | h, y) − P(θ | h)) = 0`.

The computational object is the helical pair interaction: the joint is the pairing of the
constitution fibre with the readings, and the posterior is its section at one reading. Of the winding
guide's six general objects this touches faces and placement (the reading of a face); the helix,
the pair, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `probe.information-value`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.Regeneration

variable {Θ Y K : Type*} [Fintype Θ] [Fintype Y] [Field K]

/-- [definition] The marginal of a reading, `P(y | h) = Σ_θ P(θ, y | h)`. -/
def marginal (p : Θ → Y → K) (y : Y) : K := ∑ θ, p θ y

/-- [definition] The prior of a constitution, `P(θ | h) = Σ_y P(θ, y | h)`. -/
def prior (p : Θ → Y → K) (θ : Θ) : K := ∑ y, p θ y

/-- [definition] The posterior, `P(θ | h, y) = P(θ, y | h) / P(y | h)`. -/
def posterior (p : Θ → Y → K) (θ : Θ) (y : Y) : K := p θ y / marginal p y

omit [Fintype Y] in
/-- [proved-standard; formal-checked] **The marginal times the posterior is the joint**, where a
reading of zero marginal carries zero joint weight. -/
theorem marginal_mul_posterior (p : Θ → Y → K) (hp : ∀ θ y, marginal p y = 0 → p θ y = 0)
    (θ : Θ) (y : Y) : marginal p y * posterior p θ y = p θ y := by
  by_cases h : marginal p y = 0
  · rw [h, zero_mul, hp θ y h]
  · unfold posterior
    exact mul_div_cancel₀ _ h

/-- [proved-standard; formal-checked] **No new evidence from regeneration:**
`Σ_y P(y | h) P(θ | h, y) = P(θ | h)`. -/
theorem regeneration_no_new_evidence (p : Θ → Y → K)
    (hp : ∀ θ y, marginal p y = 0 → p θ y = 0) (θ : Θ) :
    ∑ y, marginal p y * posterior p θ y = prior p θ :=
  Finset.sum_congr rfl fun y _ => marginal_mul_posterior p hp θ y

/-- [proved-standard; formal-checked] **The expected update is zero** for a normalized law. -/
theorem expected_update_zero (p : Θ → Y → K) (hp : ∀ θ y, marginal p y = 0 → p θ y = 0)
    (htot : ∑ y, marginal p y = 1) (θ : Θ) :
    ∑ y, marginal p y * (posterior p θ y - prior p θ) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [regeneration_no_new_evidence p hp θ, ← Finset.sum_mul, htot, one_mul, sub_self]

omit [Fintype Y] in
/-- [proved-standard; formal-checked] A nonnegative law gives zero joint weight to a reading of zero
marginal. -/
theorem null_of_nonneg [LinearOrder K] [IsStrictOrderedRing K] (p : Θ → Y → K)
    (h0 : ∀ θ y, 0 ≤ p θ y) : ∀ θ y, marginal p y = 0 → p θ y = 0 :=
  fun θ y hm =>
    (Finset.sum_eq_zero_iff_of_nonneg fun θ' _ => h0 θ' y).mp hm θ (Finset.mem_univ θ)

end Holonics.Foundation.Regeneration
