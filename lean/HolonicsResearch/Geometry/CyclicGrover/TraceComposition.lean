import HolonicsResearch.Geometry.CyclicGrover.TowerCover

/-! Refs #62. Integral fibre sums compose along the actual cover restrictions. -/
namespace Holonics.Epime.IntegralTrace
variable {A B C R : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq B] [DecidableEq C] [AddCommMonoid R]

theorem trace_comp (π : A → B) (ρ : B → C) (f : A → R) :
    trace ρ (trace π f) = trace (fun a => ρ (π a)) f := by
  funext c
  change (∑ b, if ρ b=c then (∑ a, if π a=b then f a else 0) else 0) =
    ∑ a, if ρ (π a)=c then f a else 0
  calc
    _ = ∑ b, ∑ a, if π a=b then (if ρ b=c then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : ρ b=c <;> simp [h]
    _ = ∑ a, ∑ b, if π a=b then (if ρ b=c then f a else 0) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp

end Holonics.Epime.IntegralTrace

namespace Holonics.Epime.GroverTower
theorem trace_composes {R : Type*} [CommRing R] {l m n : ℕ} (h : l ≤ m)
    (f : Dart n → R) : trace l m (trace m n f) = trace l n f := by
  change IntegralTrace.trace (restriction l m)
    (IntegralTrace.trace (restriction m n) f) = IntegralTrace.trace (restriction l n) f
  rw [IntegralTrace.trace_comp]
  congr 1
  funext d
  exact restriction_composes h d
end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.IntegralTrace.trace_comp
#print axioms Holonics.Epime.GroverTower.trace_composes
