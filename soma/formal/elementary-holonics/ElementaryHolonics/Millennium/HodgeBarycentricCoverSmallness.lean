import ElementaryHolonics.Millennium.HodgeBarycentricTriangleSubdivision
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Exact cover-smallness of the edge-refining barycentric operator

The six-cell triangle successor contracts every addressed source word by `(4/9)^n` in squared
coordinate distance.  Compactness and the metric Lebesgue-number theorem now convert that uniform
law into a source-smallness theorem for every open cover.  Pulling a cover back along a singular
simplex then returns the source-specific small-simplex passage required by singular homology.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricCoverSmallness

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeStellarSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision

theorem triangleSquaredCoordinateDistance_le_three (left right : Triangle) :
    triangleSquaredCoordinateDistance left right ≤ 3 := by
  have hl0 := stdSimplex.zero_le left (0 : Fin 3)
  have hl1 := stdSimplex.zero_le left (1 : Fin 3)
  have hl2 := stdSimplex.zero_le left (2 : Fin 3)
  have hr0 := stdSimplex.zero_le right (0 : Fin 3)
  have hr1 := stdSimplex.zero_le right (1 : Fin 3)
  have hr2 := stdSimplex.zero_le right (2 : Fin 3)
  have hlsum := stdSimplex.sum_eq_one left
  have hrsum := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_three] at hlsum hrsum
  rw [triangleSquaredCoordinateDistance, Fin.sum_univ_three]
  have h0 : (left 0 - right 0) ^ 2 ≤ 1 := by nlinarith
  have h1 : (left 1 - right 1) ^ 2 ≤ 1 := by nlinarith
  have h2 : (left 2 - right 2) ^ 2 ≤ 1 := by nlinarith
  linarith

theorem dist_lt_of_triangleSquaredCoordinateDistance_lt_sq
    (left right : Triangle) {radius : ℝ} (hradius : 0 < radius)
    (hsquared : triangleSquaredCoordinateDistance left right < radius ^ 2) :
    dist left right < radius := by
  change dist (left : Fin 3 → ℝ) (right : Fin 3 → ℝ) < radius
  rw [dist_pi_lt_iff hradius]
  intro coordinate
  rw [Real.dist_eq]
  have hterm : (left coordinate - right coordinate) ^ 2 ≤
      triangleSquaredCoordinateDistance left right := by
    exact Finset.single_le_sum
      (fun other _ => sq_nonneg (left other - right other))
      (Finset.mem_univ coordinate)
  have habsSquare : |left coordinate - right coordinate| ^ 2 < radius ^ 2 := by
    rw [sq_abs]
    exact lt_of_le_of_lt hterm hsquared
  nlinarith [abs_nonneg (left coordinate - right coordinate)]

/-- Every open cover of the standard triangle receives all descendant images at one uniform
finite barycentric depth. -/
theorem exists_scale_all_barycentric_words_subordinate
    {ι : Type*} (cover : ι → Set Triangle)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTriangleAddress,
      word.length = scale → ∃ index,
        Set.range (barycentricTriangleWordMap word) ⊆ cover index := by
  obtain ⟨radius, hradius, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hopen hcovers
  obtain ⟨scale, hscale⟩ : ∃ scale : ℕ,
      ((4 : ℝ) / 9) ^ scale < radius ^ 2 / 3 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  refine ⟨scale, fun word hlength => ?_⟩
  obtain ⟨index, hindex⟩ :=
    hball (barycentricTriangleWordMap word triangleBarycenter) (Set.mem_univ _)
  refine ⟨index, fun point hpoint => ?_⟩
  rcases hpoint with ⟨source, rfl⟩
  apply hindex
  rw [Metric.mem_ball]
  apply dist_lt_of_triangleSquaredCoordinateDistance_lt_sq _ _ hradius
  calc
    triangleSquaredCoordinateDistance
        (barycentricTriangleWordMap word source)
        (barycentricTriangleWordMap word triangleBarycenter) ≤
      ((4 : ℝ) / 9) ^ word.length *
        triangleSquaredCoordinateDistance source triangleBarycenter :=
      triangleSquaredCoordinateDistance_barycentricTriangleWordMap word _ _
    _ ≤ ((4 : ℝ) / 9) ^ word.length * 3 := by
      exact mul_le_mul_of_nonneg_left
        (triangleSquaredCoordinateDistance_le_three source triangleBarycenter)
        (by positivity)
    _ < radius ^ 2 := by
      rw [hlength]
      nlinarith

/-- Pulling an open cover of `S²` back through a singular simplex gives one uniform finite depth
at which every addressed barycentric descendant of that simplex lies in one cover member. -/
theorem exists_scale_sphereSimplex_barycentric_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 2) (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTriangleAddress,
      word.length = scale → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 2)) simplex).comp
              (barycentricTriangleWordMap word)) ⊆ cover index := by
  let realized : C(Triangle, ↑sphereTopCat) :=
    TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2)) simplex
  have hpullOpen : ∀ index, IsOpen (realized ⁻¹' cover index) := fun index =>
    (hopen index).preimage realized.continuous
  have hpullCover : Set.univ ⊆ ⋃ index, realized ⁻¹' cover index := by
    intro point _
    have himage : realized point ∈ Set.univ := Set.mem_univ _
    have := hcovers himage
    simpa only [Set.mem_iUnion, Set.mem_preimage] using this
  obtain ⟨scale, hscale⟩ :=
    exists_scale_all_barycentric_words_subordinate
      (fun index => realized ⁻¹' cover index) hpullOpen hpullCover
  refine ⟨scale, fun word hlength => ?_⟩
  obtain ⟨index, hindex⟩ := hscale word hlength
  refine ⟨index, ?_⟩
  rintro point ⟨source, rfl⟩
  exact hindex ⟨source, rfl⟩

/-- Once the source image is small, every further addressed refinement remains small.  The
retained suffix is the already-small outer transport; the earlier part of the word only selects a
smaller source population inside it. -/
theorem exists_scale_sphereSimplex_all_deeper_barycentric_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 2) (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTriangleAddress,
      scale ≤ word.length → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 2)) simplex).comp
              (barycentricTriangleWordMap word)) ⊆ cover index := by
  obtain ⟨scale, hscale⟩ :=
    exists_scale_sphereSimplex_barycentric_descendants_subordinate
      simplex cover hopen hcovers
  refine ⟨scale, fun word hlength => ?_⟩
  let cut := word.length - scale
  let first := word.take cut
  let second := word.drop cut
  have hsecondLength : second.length = scale := by
    simp only [second, List.length_drop, cut]
    omega
  obtain ⟨index, hindex⟩ := hscale second hsecondLength
  refine ⟨index, fun point hpoint => ?_⟩
  rcases hpoint with ⟨source, rfl⟩
  apply hindex
  refine ⟨barycentricTriangleWordMap first source, ?_⟩
  simp only [ContinuousMap.comp_apply]
  have hsplit : first ++ second = word := by
    exact List.take_append_drop cut word
  rw [← hsplit, barycentricTriangleWordMap_append]
  rfl

/-- A finite addressed population of singular triangles admits one synchronized scale.  The
population is not collapsed to a count: every occurrence retains its source map and independently
returns the cover aperture containing each descendant. -/
theorem exists_scale_finite_sphereSimplex_family_barycentric_descendants_subordinate
    {κ ι : Type*} [Fintype κ]
    (simplex : κ → SphereSingularSimplex 2) (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ occurrence : κ,
      ∀ word : List BarycentricTriangleAddress,
        scale ≤ word.length → ∃ index,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 2)) (simplex occurrence)).comp
                (barycentricTriangleWordMap word)) ⊆ cover index := by
  choose localScale localLaw using fun occurrence =>
    exists_scale_sphereSimplex_all_deeper_barycentric_descendants_subordinate
      (simplex occurrence) cover hopen hcovers
  refine ⟨∑ occurrence : κ, localScale occurrence, fun occurrence word hlength => ?_⟩
  apply localLaw occurrence word
  apply le_trans ?_ hlength
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (localScale other))
    (Finset.mem_univ occurrence)

section Audit

#print axioms triangleSquaredCoordinateDistance_le_three
#print axioms exists_scale_all_barycentric_words_subordinate
#print axioms exists_scale_sphereSimplex_barycentric_descendants_subordinate
#print axioms exists_scale_sphereSimplex_all_deeper_barycentric_descendants_subordinate
#print axioms exists_scale_finite_sphereSimplex_family_barycentric_descendants_subordinate

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricCoverSmallness
