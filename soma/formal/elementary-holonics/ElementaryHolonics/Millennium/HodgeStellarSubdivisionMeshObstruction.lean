import ElementaryHolonics.Millennium.HodgeStellarSubdivisionHomotopy

/-!
# The exact mesh obstruction for three-cone stellar subdivision

The checked three-cone operator is an exact chain homotopy tool, but it is not a mesh-shrinking
subdivision.  Along the branch which repeatedly selects cone `0`, the complete edge joining source
vertices `1` and `2` survives pointwise at every depth.

This file returns that insufficiency through a concrete two-aperture open cover of the standard
triangle.  No member of the cover contains both retained vertices, hence the persistent branch is
never subordinate to the cover.  A cover-smallness proof must therefore refine edges as well as
cone faces; the present operator cannot be promoted by adding a hypothesis that contradicts this
receiver.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeStellarSubdivisionMeshObstruction

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision

/-- The descendant branch which always selects stellar cone `0`. -/
def zeroConeIterate : ℕ → C(Triangle, Triangle)
  | 0 => ContinuousMap.id Triangle
  | scale + 1 => (zeroConeIterate scale).comp (stellarConeMap 0)

/-- The first endpoint of the exterior edge survives every refinement on this branch. -/
@[simp]
theorem zeroConeIterate_vertex_one (scale : ℕ) :
    zeroConeIterate scale (stdSimplex.vertex 1) = stdSimplex.vertex 1 := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      have hcone : stellarConeMap 0 (stdSimplex.vertex 1) =
          stdSimplex.vertex 1 := by
        simpa using stellarConeMap_vertex_succ 0 (0 : Fin 2)
      rw [zeroConeIterate, ContinuousMap.comp_apply, hcone, inductionHypothesis]

/-- The second endpoint of the same exterior edge also survives every refinement. -/
@[simp]
theorem zeroConeIterate_vertex_two (scale : ℕ) :
    zeroConeIterate scale (stdSimplex.vertex 2) = stdSimplex.vertex 2 := by
  induction scale with
  | zero => rfl
  | succ scale inductionHypothesis =>
      have hcone : stellarConeMap 0 (stdSimplex.vertex 2) =
          stdSimplex.vertex 2 := by
        simpa using stellarConeMap_vertex_succ 0 (1 : Fin 2)
      rw [zeroConeIterate, ContinuousMap.comp_apply, hcone, inductionHypothesis]

/-- The lower coordinate aperture. -/
def lowerAperture : Set Triangle :=
  { point | point 1 < (2 : ℝ) / 3 }

/-- The upper coordinate aperture. -/
def upperAperture : Set Triangle :=
  { point | (1 : ℝ) / 3 < point 1 }

theorem isOpen_lowerAperture : IsOpen lowerAperture := by
  exact isOpen_lt
    ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val) continuous_const

theorem isOpen_upperAperture : IsOpen upperAperture := by
  exact isOpen_lt continuous_const
    ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val)

/-- The two exact apertures cover the entire triangle. -/
theorem lowerAperture_union_upperAperture :
    lowerAperture ∪ upperAperture = Set.univ := by
  ext point
  simp only [lowerAperture, upperAperture, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  by_cases hlower : point 1 < (2 : ℝ) / 3
  · exact Or.inl hlower
  · right
    linarith

/-- A map is subordinate to this cover only if its complete image lies in one declared aperture. -/
def SubordinateToSeparatingCover (map : C(Triangle, Triangle)) : Prop :=
  Set.range map ⊆ lowerAperture ∨ Set.range map ⊆ upperAperture

/-- Exact receiver insufficiency: the persistent edge prevents the branch from entering either
cover aperture at every finite scale. -/
theorem zeroConeIterate_not_subordinate (scale : ℕ) :
    ¬ SubordinateToSeparatingCover (zeroConeIterate scale) := by
  intro hsmall
  rcases hsmall with hlower | hupper
  · have hone : zeroConeIterate scale (stdSimplex.vertex 1) ∈ lowerAperture :=
      hlower ⟨stdSimplex.vertex 1, rfl⟩
    rw [zeroConeIterate_vertex_one] at hone
    change (stdSimplex.vertex (1 : Fin 3)) 1 < (2 : ℝ) / 3 at hone
    norm_num at hone
  · have htwo : zeroConeIterate scale (stdSimplex.vertex 2) ∈ upperAperture :=
      hupper ⟨stdSimplex.vertex 2, rfl⟩
    rw [zeroConeIterate_vertex_two] at htwo
    change (1 : ℝ) / 3 < (stdSimplex.vertex (2 : Fin 3)) 1 at htwo
    simp at htwo
    norm_num at htwo

/-- No finite scale can make every stellar descendant subordinate: the all-zero word supplies a
counterexample branch at that scale. -/
theorem no_uniform_cover_smallness_for_three_cone_stellar :
    ¬ ∃ scale : ℕ, SubordinateToSeparatingCover (zeroConeIterate scale) := by
  rintro ⟨scale, hsmall⟩
  exact zeroConeIterate_not_subordinate scale hsmall

section Audit

#print axioms zeroConeIterate_vertex_one
#print axioms lowerAperture_union_upperAperture
#print axioms zeroConeIterate_not_subordinate
#print axioms no_uniform_cover_smallness_for_three_cone_stellar

end Audit

end Soma.Holonics.Millennium.HodgeStellarSubdivisionMeshObstruction
