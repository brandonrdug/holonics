import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Refs #62. An integral fibre sum; no averaging and no inverse/isometry claim.
The receiver's scale is the certified fibre count. -/
namespace Holonics.Epime.IntegralTrace
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [AddCommMonoid R]

def trace (π : A → B) (f : A → R) (b : B) : R :=
  ∑ a, if π a = b then f a else 0

def pullback (π : A → B) (f : B → R) : A → R := fun a => f (π a)

def action (σ : Equiv.Perm A) (f : A → R) : A → R := fun a => f (σ.symm a)

theorem trace_action (π : A → B) (σ : Equiv.Perm A) (τ : Equiv.Perm B)
    (h : ∀ a, π (σ a) = τ (π a)) (f : A → R) :
    trace π (action σ f) = action τ (trace π f) := by
  funext b
  change (∑ a, if π a=b then f (σ.symm a) else 0) =
    ∑ a, if π a=τ.symm b then f a else 0
  calc
    _ = ∑ a, if π (σ a)=b then f a else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        (σ.sum_comp Finset.univ (fun a => if π a=b then f (σ.symm a) else 0)
          (by intro a _; exact Finset.mem_univ a)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have hc : π (σ a)=b ↔ π a=τ.symm b := by
        rw [h a]
        exact (Equiv.eq_symm_apply τ).symm
      simp only [hc]

/-- The fibre chart itself provides the count; no cardinality assumption. -/
theorem trace_pullback_scale (k : ℕ) (e : Fin k × B ≃ A) (f : B → R) :
    trace (fun a => (e.symm a).2) (pullback (fun a => (e.symm a).2) f) =
      fun b => k • f b := by
  funext b
  change (∑ a, if (e.symm a).2=b then f (e.symm a).2 else 0) = k • f b
  calc
    _ = ∑ z : Fin k × B, if z.2=b then f z.2 else 0 := by
      exact Fintype.sum_equiv e.symm _ _ (fun a => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp

end Holonics.Epime.IntegralTrace

#print axioms Holonics.Epime.IntegralTrace.trace_action
#print axioms Holonics.Epime.IntegralTrace.trace_pullback_scale
