import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! A restriction lemma for actual scheme graph diagrams. The monomorphisms
and projection squares are proved in each concrete application; no cycle,
Cartier or intersection claim is supplied as an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits
namespace Holonics.Hodge.CMGraphSource
universe u v

theorem graphChart_isPullback {C : Type u} [Category.{v} C]
    {A B X Y : C} (j : A ⟶ X) (k : B ⟶ Y) (r : B ⟶ A) (p : Y ⟶ X)
    (q : A ⟶ B) (g : X ⟶ Y) [Mono j] [Mono k]
    (hfirst : g ≫ p = 𝟙 X) (hchart : k ≫ p = r ≫ j)
    (hsquare : q ≫ k = j ≫ g) : IsPullback q j k g := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk q j hsquare)
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ r) ?_ ?_ ?_
  · intro s
    have h : (s.fst ≫ r) ≫ j = s.snd := by
      have he := congrArg (fun f => f ≫ p) s.condition
      simpa only [Category.assoc, hchart, hfirst, Category.comp_id] using he
    apply (cancel_mono k).mp
    rw [Category.assoc, hsquare, ← Category.assoc, h]
    exact s.condition.symm
  · intro s
    have he := congrArg (fun f => f ≫ p) s.condition
    simpa only [Category.assoc, hchart, hfirst, Category.comp_id] using he
  · intro s m _ hm
    apply (cancel_mono j).mp
    have he := congrArg (fun f => f ≫ p) s.condition
    have h : (s.fst ≫ r) ≫ j = s.snd := by
      simpa only [Category.assoc, hchart, hfirst, Category.comp_id] using he
    exact hm.trans h.symm

#print axioms graphChart_isPullback
end Holonics.Hodge.CMGraphSource
