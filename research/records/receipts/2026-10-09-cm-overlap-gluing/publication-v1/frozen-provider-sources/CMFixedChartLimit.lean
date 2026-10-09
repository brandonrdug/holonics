import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
A categorical chart restriction of a proved fixed equalizer. The only
chart hypothesis is the commuting inclusion square, which the concrete
source must prove. This theorem constructs the lift; it assumes none.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace Holonics.Hodge.CMGraphSource
universe v u
variable {C : Type u} [Category.{v} C]

def fixedChartFork {X : C} {f : X ⟶ X} (s : Fork f (𝟙 X)) {U : C}
    (j : U ⟶ X) [Mono j] (q : U ⟶ U) (hq : q ≫ j = j ≫ f)
    [HasPullback s.ι j] : Fork q (𝟙 U) :=
  Fork.ofι (pullback.snd s.ι j) (by
    apply (cancel_mono j).mp
    simp only [Category.assoc, Category.comp_id]
    rw [hq, ← Category.assoc, ← pullback.condition, Category.assoc,
      s.condition, Category.comp_id])

def fixedChartFork_isLimit {X : C} {f : X ⟶ X} (s : Fork f (𝟙 X))
    (hs : IsLimit s) {U : C} (j : U ⟶ X) [Mono j] (q : U ⟶ U)
    (hq : q ≫ j = j ≫ f) [HasPullback s.ι j] :
    IsLimit (fixedChartFork s j q hq) :=
  Fork.IsLimit.mk' _ fun t => by
    have ht : (t.ι ≫ j) ≫ f = (t.ι ≫ j) ≫ 𝟙 X := by
      rw [Category.assoc, ← hq, ← Category.assoc, t.condition]
      simp only [Category.comp_id]
    let k := Fork.ofι (t.ι ≫ j) ht
    let l := hs.lift k
    have hl : l ≫ s.ι = t.ι ≫ j := hs.fac k WalkingParallelPair.zero
    refine ⟨pullback.lift l t.ι hl, pullback.lift_snd _ _ _, ?_⟩
    intro m hm
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply Fork.IsLimit.hom_ext hs
      rw [Category.assoc, pullback.condition, ← Category.assoc, hl]
      exact congrArg (fun a => a ≫ j) hm
    · exact hm.trans (pullback.lift_snd _ _ _).symm

#print axioms fixedChartFork_isLimit
end Holonics.Hodge.CMGraphSource
