import CMComplexGraphCore
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
The actual relative graph--diagonal intersection of the reduced projective
cubic. Its universal property is the fixed-point equalizer of the constructed
CM automorphism. No identification with local coordinate quotients or with a
two-point finite scheme is assumed here.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

def cmComplexDiagonal : CMProjectiveCubic ⟶ pullback cmConcreteCubicBase cmConcreteCubicBase :=
  pullback.diagonal cmConcreteCubicBase

def CMProjectiveFixedScheme : Scheme := pullback cmConcreteComplexGraph cmComplexDiagonal

def cmFixedInclusion : CMProjectiveFixedScheme ⟶ CMProjectiveCubic :=
  pullback.fst cmConcreteComplexGraph cmComplexDiagonal

theorem cmFixed_projections_agree : cmFixedInclusion =
    pullback.snd cmConcreteComplexGraph cmComplexDiagonal := by
  have h := congrArg (fun k => k ≫ pullback.fst cmConcreteCubicBase cmConcreteCubicBase)
    (pullback.condition (f := cmConcreteComplexGraph) (g := cmComplexDiagonal))
  change pullback.fst cmConcreteComplexGraph cmComplexDiagonal =
    pullback.snd cmConcreteComplexGraph cmComplexDiagonal
  simpa only [Category.assoc, cmConcreteComplexGraph_first_projection,
    cmComplexDiagonal, pullback.diagonal_fst, Category.comp_id] using h

theorem cmFixed_equation : cmFixedInclusion ≫ cubicIota.hom = cmFixedInclusion := by
  have h := congrArg (fun k => k ≫ pullback.snd cmConcreteCubicBase cmConcreteCubicBase)
    (pullback.condition (f := cmConcreteComplexGraph) (g := cmComplexDiagonal))
  have hh : cmFixedInclusion ≫ cubicIota.hom =
      pullback.snd cmConcreteComplexGraph cmComplexDiagonal := by
    simpa only [Category.assoc, cmConcreteComplexGraph_second_projection,
      cmComplexDiagonal, pullback.diagonal_snd, Category.comp_id, cmFixedInclusion,
      CMProjectiveFixedScheme] using h
  exact hh.trans cmFixed_projections_agree.symm

def cmFixedFork : Fork cubicIota.hom (𝟙 CMProjectiveCubic) :=
  Fork.ofι cmFixedInclusion (by simpa using cmFixed_equation)

def cmFixedFork_isLimit : IsLimit cmFixedFork :=
  Fork.IsLimit.mk' _ fun s => by
    have hs : s.ι ≫ cmConcreteComplexGraph = s.ι ≫ cmComplexDiagonal := by
      apply pullback.hom_ext
      · simp only [Category.assoc, cmConcreteComplexGraph_first_projection,
          cmComplexDiagonal, pullback.diagonal_fst, Category.comp_id]
      · simpa only [Category.assoc, cmConcreteComplexGraph_second_projection,
          cmComplexDiagonal, pullback.diagonal_snd, Category.comp_id] using s.condition
    refine ⟨pullback.lift s.ι s.ι hs, ?_, ?_⟩
    · exact pullback.lift_fst _ _ _
    · intro m hm
      apply pullback.hom_ext
      · exact hm.trans (pullback.lift_fst _ _ _).symm
      · rw [pullback.lift_snd]
        change m ≫ pullback.snd cmConcreteComplexGraph cmComplexDiagonal = s.ι
        rw [← cmFixed_projections_agree]
        exact hm

#print axioms cmFixed_projections_agree
#print axioms cmFixed_equation
#print axioms cmFixedFork_isLimit
end Holonics.Hodge.CMGraphSource
