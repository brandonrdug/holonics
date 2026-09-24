import ElementaryHolonics.Millennium.HodgeRefinementWords
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Exact cover-smallness of fixed-length barycentric edge words

Each addressed edge refinement contracts source-parameter distance by exactly `1/2`.  The
contraction iterates over the serial edge-word map, and the metric Lebesgue-number theorem turns
the resulting uniform law into cover-smallness on `Segment`, through one sphere singular edge,
and for every deeper word.  A finite addressed family receives one synchronized depth.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeBarycentricEdgeCoverSmallness

open CategoryTheory
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeBarycentricEdgeSubdivision
open Soma.Holonics.Millennium.HodgeRefinementWords

theorem segmentParameterDistance_le_one (left right : Segment) :
    segmentParameterDistance left right ≤ 1 := by
  have hl0 := stdSimplex.zero_le left (0 : Fin 2)
  have hl1 := stdSimplex.zero_le left (1 : Fin 2)
  have hr0 := stdSimplex.zero_le right (0 : Fin 2)
  have hr1 := stdSimplex.zero_le right (1 : Fin 2)
  have hleft := stdSimplex.sum_eq_one left
  have hright := stdSimplex.sum_eq_one right
  rw [Fin.sum_univ_two] at hleft hright
  rw [segmentParameterDistance, abs_le]
  constructor <;> nlinarith

theorem dist_lt_of_segmentParameterDistance_lt
    (left right : Segment) {radius : ℝ} (hradius : 0 < radius)
    (hdistance : segmentParameterDistance left right < radius) :
    dist left right < radius := by
  change dist (left : Fin 2 → ℝ) (right : Fin 2 → ℝ) < radius
  rw [dist_pi_lt_iff hradius]
  intro coordinate
  rw [Real.dist_eq]
  fin_cases coordinate
  · change |left 0 - right 0| < radius
    exact hdistance
  · have hleft := stdSimplex.sum_eq_one left
    have hright := stdSimplex.sum_eq_one right
    rw [Fin.sum_univ_two] at hleft hright
    have hcoordinate : left 1 - right 1 = -(left 0 - right 0) := by
      linarith
    change |left 1 - right 1| < radius
    rw [hcoordinate, abs_neg]
    exact hdistance

theorem segmentParameterDistance_edgeWordMap
    (word : List (Fin 2)) (left right : Segment) :
    segmentParameterDistance
        (edgeWordMap word left) (edgeWordMap word right) =
      (2 : ℝ)⁻¹ ^ word.length * segmentParameterDistance left right := by
  induction word generalizing left right with
  | nil =>
      simp [edgeWordMap]
  | cons address tail inductionHypothesis =>
      rw [edgeWordMap, ContinuousMap.comp_apply]
      calc
        segmentParameterDistance
            (edgeWordMap tail (edgeConeMap address left))
            (edgeWordMap tail (edgeConeMap address right)) =
          (2 : ℝ)⁻¹ ^ tail.length *
            segmentParameterDistance (edgeConeMap address left)
              (edgeConeMap address right) :=
          inductionHypothesis _ _
        _ = (2 : ℝ)⁻¹ ^ tail.length *
            ((2 : ℝ)⁻¹ * segmentParameterDistance left right) := by
          rw [segmentParameterDistance_edgeConeMap]
        _ = (2 : ℝ)⁻¹ ^ (address :: tail).length *
            segmentParameterDistance left right := by
          simp only [List.length_cons, pow_succ]
          ring

theorem edgeWordMap_append (first second : List (Fin 2)) :
    edgeWordMap (first ++ second) =
      (edgeWordMap second).comp (edgeWordMap first) := by
  induction first with
  | nil =>
      apply ContinuousMap.ext
      intro point
      rfl
  | cons address tail inductionHypothesis =>
      simp only [List.cons_append, edgeWordMap, inductionHypothesis,
        ContinuousMap.comp_assoc]

theorem exists_scale_all_edge_words_subordinate
    {ι : Type*} (cover : ι → Set Segment)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List (Fin 2),
      word.length = scale → ∃ index,
        Set.range (edgeWordMap word) ⊆ cover index := by
  obtain ⟨radius, hradius, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hopen hcovers
  obtain ⟨scale, hscale⟩ : ∃ scale : ℕ,
      (2 : ℝ)⁻¹ ^ scale < radius :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  refine ⟨scale, fun word hlength => ?_⟩
  obtain ⟨index, hindex⟩ :=
    hball (edgeWordMap word segmentMidpoint) (Set.mem_univ _)
  refine ⟨index, fun point hpoint => ?_⟩
  rcases hpoint with ⟨source, rfl⟩
  apply hindex
  rw [Metric.mem_ball]
  apply dist_lt_of_segmentParameterDistance_lt _ _ hradius
  calc
    segmentParameterDistance
        (edgeWordMap word source)
        (edgeWordMap word segmentMidpoint) =
      (2 : ℝ)⁻¹ ^ word.length *
        segmentParameterDistance source segmentMidpoint :=
      segmentParameterDistance_edgeWordMap word _ _
    _ ≤ (2 : ℝ)⁻¹ ^ word.length * 1 := by
      exact mul_le_mul_of_nonneg_left
        (segmentParameterDistance_le_one source segmentMidpoint)
        (by positivity)
    _ < radius := by
      rw [hlength]
      nlinarith

theorem exists_scale_sphereSimplex_edge_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 1)
    (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List (Fin 2),
      word.length = scale → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 1)) simplex).comp
              (edgeWordMap word)) ⊆ cover index := by
  let realized : C(Segment, ↑sphereTopCat) :=
    TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 1)) simplex
  have hpullOpen : ∀ index, IsOpen (realized ⁻¹' cover index) := fun index =>
    (hopen index).preimage realized.continuous
  have hpullCover : Set.univ ⊆ ⋃ index, realized ⁻¹' cover index := by
    intro point _
    have himage : realized point ∈ Set.univ := Set.mem_univ _
    have := hcovers himage
    simpa only [Set.mem_iUnion, Set.mem_preimage] using this
  obtain ⟨scale, hscale⟩ :=
    exists_scale_all_edge_words_subordinate
      (fun index => realized ⁻¹' cover index) hpullOpen hpullCover
  refine ⟨scale, fun word hlength => ?_⟩
  obtain ⟨index, hindex⟩ := hscale word hlength
  refine ⟨index, ?_⟩
  rintro point ⟨source, rfl⟩
  exact hindex ⟨source, rfl⟩

theorem exists_scale_sphereSimplex_all_deeper_edge_descendants_subordinate
    {ι : Type*} (simplex : SphereSingularSimplex 1)
    (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ word : List (Fin 2),
      scale ≤ word.length → ∃ index,
        Set.range
          ((TopCat.toSSetObjEquiv sphereTopCat
            (Opposite.op (SimplexCategory.mk 1)) simplex).comp
              (edgeWordMap word)) ⊆ cover index := by
  obtain ⟨scale, hscale⟩ :=
    exists_scale_sphereSimplex_edge_descendants_subordinate
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
  refine ⟨edgeWordMap first source, ?_⟩
  simp only [ContinuousMap.comp_apply]
  have hsplit : first ++ second = word := by
    exact List.take_append_drop cut word
  rw [← hsplit, edgeWordMap_append]
  rfl

theorem exists_scale_finite_sphereSimplex_family_edge_descendants_subordinate
    {κ ι : Type*} [Fintype κ]
    (simplex : κ → SphereSingularSimplex 1)
    (cover : ι → Set ↑sphereTopCat)
    (hopen : ∀ index, IsOpen (cover index))
    (hcovers : Set.univ ⊆ ⋃ index, cover index) :
    ∃ scale : ℕ, ∀ occurrence : κ,
      ∀ word : List (Fin 2),
        scale ≤ word.length → ∃ index,
          Set.range
            ((TopCat.toSSetObjEquiv sphereTopCat
              (Opposite.op (SimplexCategory.mk 1)) (simplex occurrence)).comp
                (edgeWordMap word)) ⊆ cover index := by
  choose localScale localLaw using fun occurrence =>
    exists_scale_sphereSimplex_all_deeper_edge_descendants_subordinate
      (simplex occurrence) cover hopen hcovers
  refine ⟨∑ occurrence : κ, localScale occurrence,
    fun occurrence word hlength => ?_⟩
  apply localLaw occurrence word
  apply le_trans ?_ hlength
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (localScale other))
    (Finset.mem_univ occurrence)

section Audit

#print axioms segmentParameterDistance_le_one
#print axioms dist_lt_of_segmentParameterDistance_lt
#print axioms segmentParameterDistance_edgeWordMap
#print axioms edgeWordMap_append
#print axioms exists_scale_all_edge_words_subordinate
#print axioms exists_scale_sphereSimplex_edge_descendants_subordinate
#print axioms exists_scale_sphereSimplex_all_deeper_edge_descendants_subordinate
#print axioms exists_scale_finite_sphereSimplex_family_edge_descendants_subordinate

end Audit

end Soma.Holonics.Millennium.HodgeBarycentricEdgeCoverSmallness
