import ElementaryHolonics.Millennium.HodgeTetrahedralLabelCarry

/-!
# The tetrahedral open-star cover of the two-sphere

The radial tetrahedral boundary can be read directly on `S²` through four centered affine
coordinates.  The first three are the ambient coordinates and the fourth is their negative sum.
The open star of a tetrahedral vertex consists of directions for which that vertex coordinate is
strictly above at least one other coordinate.

These four stars cover the sphere, but their fourfold intersection is empty because a finite
coordinate population always has a minimum.  This is the geometric nerve law required by
`CompatibleTetrahedralLabeling`: a small simplex subordinate to one common star-intersection can
never receive all four labels.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralStarCover

open Set
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex

/-- The four centered tetrahedral coordinates of a direction on the sphere.  Their sum is zero. -/
def sphereTetraCoordinate (vertex : TetraVertex) (point : TwoSphere) : ℝ :=
  if vertex = 0 then point.1 0
  else if vertex = 1 then point.1 1
  else if vertex = 2 then point.1 2
  else -(point.1 0 + point.1 1 + point.1 2)

theorem sphereTetraCoordinate_sum_zero (point : TwoSphere) :
    ∑ vertex : TetraVertex, sphereTetraCoordinate vertex point = 0 := by
  rw [Fin.sum_univ_four]
  simp [sphereTetraCoordinate, Fin.ext_iff]

theorem continuous_sphereTetraCoordinate (vertex : TetraVertex) :
    Continuous (sphereTetraCoordinate vertex) := by
  have hAmbient : Continuous (fun point : TwoSphere => point.1) :=
    continuous_subtype_val
  have hcoordinate (coordinate : Fin 3) :
      Continuous (fun point : TwoSphere => point.1 coordinate) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).comp hAmbient
  fin_cases vertex
  · change Continuous (fun point : TwoSphere => point.1 (0 : Fin 3))
    exact hcoordinate 0
  · change Continuous (fun point : TwoSphere => point.1 (1 : Fin 3))
    exact hcoordinate 1
  · change Continuous (fun point : TwoSphere => point.1 (2 : Fin 3))
    exact hcoordinate 2
  · change Continuous (fun point : TwoSphere =>
      -(point.1 (0 : Fin 3) + point.1 (1 : Fin 3) + point.1 (2 : Fin 3)))
    exact ((hcoordinate 0).add (hcoordinate 1) |>.add (hcoordinate 2)).neg

/-- The open star of one tetrahedral vertex in the radial boundary receiver. -/
def vertexStar (vertex : TetraVertex) : Set TwoSphere :=
  {point | ∃ lower : TetraVertex,
    sphereTetraCoordinate lower point < sphereTetraCoordinate vertex point}

theorem isOpen_vertexStar (vertex : TetraVertex) : IsOpen (vertexStar vertex) := by
  rw [vertexStar]
  simp_rw [setOf_exists]
  exact isOpen_iUnion fun lower =>
    isOpen_lt (continuous_sphereTetraCoordinate lower)
      (continuous_sphereTetraCoordinate vertex)

/-- A sphere direction cannot have all four centered tetrahedral coordinates equal. -/
theorem not_all_sphereTetraCoordinate_equal (point : TwoSphere) :
    ¬ ∀ vertex : TetraVertex,
      sphereTetraCoordinate vertex point = sphereTetraCoordinate 0 point := by
  intro hall
  have h1 := hall (1 : TetraVertex)
  have h2 := hall (2 : TetraVertex)
  have h3 := hall (3 : TetraVertex)
  simp [sphereTetraCoordinate, Fin.ext_iff] at h1 h2 h3
  have hzero0 : point.1 0 = 0 := by linarith
  have hzero1 : point.1 1 = 0 := by linarith
  have hzero2 : point.1 2 = 0 := by linarith
  have hpointZero : point.1 = (0 : AmbientThree) := by
    ext coordinate
    fin_cases coordinate
    · exact hzero0
    · exact hzero1
    · exact hzero2
  have hnorm := mem_sphere_zero_iff_norm.mp point.2
  rw [hpointZero, norm_zero] at hnorm
  norm_num at hnorm

/-- The four vertex stars cover the whole radial sphere. -/
theorem vertexStar_cover : Set.univ ⊆ ⋃ vertex : TetraVertex, vertexStar vertex := by
  intro point _
  have hnot := not_all_sphereTetraCoordinate_equal point
  push_neg at hnot
  obtain ⟨vertex, hvertex⟩ := hnot
  rcases lt_or_gt_of_ne hvertex with hlower | hhigher
  · exact Set.mem_iUnion.2 ⟨0, ⟨vertex, hlower⟩⟩
  · exact Set.mem_iUnion.2 ⟨vertex, ⟨0, hhigher⟩⟩

/-- No direction belongs to all four open vertex stars.  The minimizing coordinate is the exact
obstruction. -/
theorem iInter_vertexStar_eq_empty :
    (⋂ vertex : TetraVertex, vertexStar vertex) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro point hpoint
  have hall : ∀ vertex : TetraVertex, point ∈ vertexStar vertex := by
    simpa only [Set.mem_iInter] using hpoint
  obtain ⟨minimum, _, hminimum⟩ :=
    Finset.exists_min_image (Finset.univ : Finset TetraVertex)
      (fun vertex => sphereTetraCoordinate vertex point) Finset.univ_nonempty
  obtain ⟨lower, hlower⟩ := hall minimum
  exact (not_lt_of_ge (hminimum lower (Finset.mem_univ lower))) hlower

/-- Membership in every star of a four-label word is impossible.  This is the cover-side form of
the degree-three admissibility receipt consumed by the finite label current. -/
theorem not_mem_all_labelStars (point : TwoSphere)
    (labels : Fin 4 → TetraVertex) (hsurjective : Function.Surjective labels) :
    ¬ ∀ index : Fin 4, point ∈ vertexStar (labels index) := by
  intro hall
  have hEvery : ∀ vertex : TetraVertex, point ∈ vertexStar vertex := by
    intro vertex
    obtain ⟨index, rfl⟩ := hsurjective vertex
    exact hall index
  have : point ∈ ⋂ vertex : TetraVertex, vertexStar vertex := by
    simpa only [Set.mem_iInter]
  rw [iInter_vertexStar_eq_empty] at this
  exact this

/-- [proved-derived; formal-checked] Four labels whose open stars share one actual sphere
occurrence are admissible for the tetrahedral face current.  If the labels were all distinct they
would bijectively enumerate the four stars, contradicting the empty fourfold intersection. -/
theorem fourLabelsAdmissible_of_commonStarPoint
    (labels : Fin 4 → TetraVertex) (point : TwoSphere)
    (common : ∀ index : Fin 4, point ∈ vertexStar (labels index)) :
    HodgeTetrahedralLabelCarry.FourLabelsAdmissible
      (labels 0) (labels 1) (labels 2) (labels 3) := by
  by_contra notAdmissible
  have injective : Function.Injective labels := by
    intro left right equalLabels
    fin_cases left <;> fin_cases right <;>
      simp_all [HodgeTetrahedralLabelCarry.FourLabelsAdmissible, Fin.ext_iff]
  have surjective : Function.Surjective labels :=
    ((Fintype.bijective_iff_injective_and_card labels).2 ⟨injective, rfl⟩).2
  exact not_mem_all_labelStars point labels surjective common

section Audit

#print axioms sphereTetraCoordinate_sum_zero
#print axioms isOpen_vertexStar
#print axioms not_all_sphereTetraCoordinate_equal
#print axioms vertexStar_cover
#print axioms iInter_vertexStar_eq_empty
#print axioms not_mem_all_labelStars
#print axioms fourLabelsAdmissible_of_commonStarPoint

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralStarCover
