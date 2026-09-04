import ElementaryHolonics.Millennium.HodgeBarycentricTetrahedron
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Exact cover-smallness of the twenty-four-cell tetrahedron refinement

The degree-three barycentric carrier contracts every complete flag word by `(9/16)^n` in squared
coordinate distance.  Compactness and a Lebesgue number convert that exact rational law into a
uniform open-cover theorem, first on the standard tetrahedron and then through every singular
three-simplex.  A finite occurrence population receives one synchronized depth without erasing
its addresses.

Truth status: every theorem is `[proved-derived; formal-checked]` relative to the imported exact
contraction law and standard compact-metric cover theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricTetrahedronCoverSmallness

open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralStellarSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron

theorem tetrahedronSquaredCoordinateDistance_le_four
    (left right : Tetrahedron) :
    tetrahedronSquaredCoordinateDistance left right ≤ 4 := by
  have hl0 := stdSimplex.zero_le left (0 : Fin 4)
  have hl1 := stdSimplex.zero_le left (1 : Fin 4)
  have hl2 := stdSimplex.zero_le left (2 : Fin 4)
  have hl3 := stdSimplex.zero_le left (3 : Fin 4)
  have hr0 := stdSimplex.zero_le right (0 : Fin 4)
  have hr1 := stdSimplex.zero_le right (1 : Fin 4)
  have hr2 := stdSimplex.zero_le right (2 : Fin 4)
  have hr3 := stdSimplex.zero_le right (3 : Fin 4)
  have hleft := stdSimplex.sum_eq_one left
  have hright := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_four] at hleft hright
  rw [tetrahedronSquaredCoordinateDistance, Fin.sum_univ_four]
  have h0 : (left 0 - right 0) ^ 2 ≤ 1 := by nlinarith
  have h1 : (left 1 - right 1) ^ 2 ≤ 1 := by nlinarith
  have h2 : (left 2 - right 2) ^ 2 ≤ 1 := by nlinarith
  have h3 : (left 3 - right 3) ^ 2 ≤ 1 := by nlinarith
  linarith

theorem dist_lt_of_tetrahedronSquaredCoordinateDistance_lt_sq
    (left right : Tetrahedron) {radius : ℝ} (radiusPositive : 0 < radius)
    (squared : tetrahedronSquaredCoordinateDistance left right < radius ^ 2) :
    dist left right < radius := by
  change dist (left : Fin 4 → ℝ) (right : Fin 4 → ℝ) < radius
  rw [dist_pi_lt_iff radiusPositive]
  intro coordinate
  rw [Real.dist_eq]
  have termBound : (left coordinate - right coordinate) ^ 2 ≤
      tetrahedronSquaredCoordinateDistance left right := by
    exact Finset.single_le_sum
      (fun other _ => sq_nonneg (left other - right other))
      (Finset.mem_univ coordinate)
  have absSquared : |left coordinate - right coordinate| ^ 2 < radius ^ 2 := by
    rw [sq_abs]
    exact lt_of_le_of_lt termBound squared
  nlinarith [abs_nonneg (left coordinate - right coordinate)]

/-- Every open cover of the standard tetrahedron receives every descendant image at one uniform
barycentric depth. -/
theorem exists_scale_all_barycentricTetrahedron_words_subordinate
    {ι : Type*} (cover : ι → Set Tetrahedron)
    (openCover : ∀ index, IsOpen (cover index))
    (covers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTetrahedronAddress,
      word.length = scale → ∃ index,
        Set.range (barycentricTetrahedronWordMap word) ⊆ cover index := by
  obtain ⟨radius, radiusPositive, ballRefines⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ openCover covers
  obtain ⟨scale, scaleBound⟩ : ∃ scale : ℕ,
      ((9 : ℝ) / 16) ^ scale < radius ^ 2 / 4 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  refine ⟨scale, fun word wordLength => ?_⟩
  obtain ⟨index, centerBall⟩ :=
    ballRefines
      (barycentricTetrahedronWordMap word tetrahedronBarycenter) (Set.mem_univ _)
  refine ⟨index, fun point pointInRange => ?_⟩
  rcases pointInRange with ⟨source, rfl⟩
  apply centerBall
  rw [Metric.mem_ball]
  apply dist_lt_of_tetrahedronSquaredCoordinateDistance_lt_sq _ _ radiusPositive
  calc
    tetrahedronSquaredCoordinateDistance
        (barycentricTetrahedronWordMap word source)
        (barycentricTetrahedronWordMap word tetrahedronBarycenter) ≤
      ((9 : ℝ) / 16) ^ word.length *
        tetrahedronSquaredCoordinateDistance source tetrahedronBarycenter :=
      tetrahedronSquaredCoordinateDistance_barycentricTetrahedronWordMap word _ _
    _ ≤ ((9 : ℝ) / 16) ^ word.length * 4 := by
      exact mul_le_mul_of_nonneg_left
        (tetrahedronSquaredCoordinateDistance_le_four source tetrahedronBarycenter)
        (by positivity)
    _ < radius ^ 2 := by
      rw [wordLength]
      nlinarith

/-- Pulling an open cover of `S²` through a singular tetrahedron returns one exact depth at which
every addressed descendant lies in one cover member. -/
theorem exists_scale_sphereTetrahedron_barycentric_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 3)
    (cover : ι → Set ↑sphereTopCat)
    (openCover : ∀ index, IsOpen (cover index))
    (covers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTetrahedronAddress,
      word.length = scale → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 3)) simplex).comp
              (barycentricTetrahedronWordMap word)) ⊆ cover index := by
  let realized : C(Tetrahedron, ↑sphereTopCat) :=
    TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 3)) simplex
  have pullOpen : ∀ index, IsOpen (realized ⁻¹' cover index) := fun index =>
    (openCover index).preimage realized.continuous
  have pullCover : Set.univ ⊆ ⋃ index, realized ⁻¹' cover index := by
    intro point _
    have imageInCover := covers (Set.mem_univ (realized point))
    simpa only [Set.mem_iUnion, Set.mem_preimage] using imageInCover
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_all_barycentricTetrahedron_words_subordinate
      (fun index => realized ⁻¹' cover index) pullOpen pullCover
  refine ⟨scale, fun word wordLength => ?_⟩
  obtain ⟨index, imageLaw⟩ := scaleLaw word wordLength
  refine ⟨index, ?_⟩
  rintro point ⟨source, rfl⟩
  exact imageLaw ⟨source, rfl⟩

/-- Once a singular-tetrahedron descendant is small, every deeper addressed descendant remains
inside the same cover member through retained suffix factorization. -/
theorem exists_scale_sphereTetrahedron_all_deeper_barycentric_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 3)
    (cover : ι → Set ↑sphereTopCat)
    (openCover : ∀ index, IsOpen (cover index))
    (covers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List BarycentricTetrahedronAddress,
      scale ≤ word.length → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 3)) simplex).comp
              (barycentricTetrahedronWordMap word)) ⊆ cover index := by
  obtain ⟨scale, scaleLaw⟩ :=
    exists_scale_sphereTetrahedron_barycentric_descendants_subordinate
      simplex cover openCover covers
  refine ⟨scale, fun word lengthBound => ?_⟩
  let cut := word.length - scale
  let first := word.take cut
  let second := word.drop cut
  have secondLength : second.length = scale := by
    simp only [second, List.length_drop, cut]
    omega
  obtain ⟨index, imageLaw⟩ := scaleLaw second secondLength
  refine ⟨index, fun point pointInRange => ?_⟩
  rcases pointInRange with ⟨source, rfl⟩
  apply imageLaw
  refine ⟨barycentricTetrahedronWordMap first source, ?_⟩
  simp only [ContinuousMap.comp_apply]
  have split : first ++ second = word := List.take_append_drop cut word
  rw [← split, barycentricTetrahedronWordMap_append]
  rfl

/-- One synchronized depth works for every member of a finite addressed singular-tetrahedron
population. -/
theorem exists_scale_finite_sphereTetrahedron_family_barycentric_descendants_subordinate
    {κ ι : Type*} [Fintype κ]
    (simplex : κ → SphereSingularSimplex 3) (cover : ι → Set ↑sphereTopCat)
    (openCover : ∀ index, IsOpen (cover index))
    (covers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ occurrence : κ,
      ∀ word : List BarycentricTetrahedronAddress,
        scale ≤ word.length → ∃ index,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 3)) (simplex occurrence)).comp
                (barycentricTetrahedronWordMap word)) ⊆ cover index := by
  choose localScale localLaw using fun occurrence =>
    exists_scale_sphereTetrahedron_all_deeper_barycentric_descendants_subordinate
      (simplex occurrence) cover openCover covers
  refine ⟨∑ occurrence : κ, localScale occurrence,
    fun occurrence word lengthBound => ?_⟩
  apply localLaw occurrence word
  apply le_trans ?_ lengthBound
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (localScale other))
    (Finset.mem_univ occurrence)

section Audit

#print axioms tetrahedronSquaredCoordinateDistance_le_four
#print axioms exists_scale_all_barycentricTetrahedron_words_subordinate
#print axioms exists_scale_sphereTetrahedron_barycentric_descendants_subordinate
#print axioms exists_scale_sphereTetrahedron_all_deeper_barycentric_descendants_subordinate
#print axioms exists_scale_finite_sphereTetrahedron_family_barycentric_descendants_subordinate

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricTetrahedronCoverSmallness
