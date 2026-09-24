import ElementaryHolonics.Millennium.HodgeProjectiveLineHolomorphicAtlas

/-!
# Cellular degree-two cohomology of the projective-line product

The actual projective-line quotient has one distinguished closed point and its complementary
affine chart.  We prove that complement is exactly the second standard chart and hence equivalent
to `ℂ`.  Taking products gives the four even cells of `ℙ¹_ℂ × ℙ¹_ℂ`; the two real-dimension-two
cell closures are precisely the two geometric ruling fibres.

Because the cell dimensions are `0`, `2`, and `4`, the incoming and outgoing degree-two cellular
coboundaries are both zero.  We therefore construct degree-two cellular cohomology as the kernel
of the outgoing map, prove the incoming range is bottom, and exhibit an exact linear equivalence
with the two-cell coordinate carrier.  This replaces the anonymous cohomology rebase in the
rank-two comparison by a constructed finite cochain calculation.

The remaining external edge is now sharply smaller: identify this constructed cellular theory
with rational singular cohomology and its Hodge `(1,1)` decomposition.  No such identification is
assumed below.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas

theorem coordinatePoint_not_in_second_chart : ¬ InChart .second coordinatePoint := by
  intro hsecond
  have hnonzero := coordinate_ne_zero_of_distinct_overlap (by decide)
    coordinatePoint coordinatePoint_in_first_chart hsecond
  exact hnonzero coordinate_coordinatePoint

/-- [proved-derived; formal-checked] The complement of the affine chart is exactly the addressed
closed point. -/
theorem not_in_second_chart_iff_eq_coordinatePoint (projectivePoint : ComplexProjectiveLine) :
    ¬ InChart .second projectivePoint ↔ projectivePoint = coordinatePoint := by
  constructor
  · intro hmissing
    have hfirst : InChart .first projectivePoint :=
      (chart_cover projectivePoint).resolve_right hmissing
    have hnumerator : projectivePoint.rep 1 = 0 := not_ne_iff.mp hmissing
    have hcoordinate :
        coordinate .first ⟨projectivePoint, hfirst⟩ = 0 := by
      simp [coordinate, AffineChart.other, AffineChart.pivot, hnumerator]
    calc
      projectivePoint = point .first
          (coordinate .first ⟨projectivePoint, hfirst⟩) :=
        (point_coordinate .first ⟨projectivePoint, hfirst⟩).symm
      _ = point .first 0 := by rw [hcoordinate]
      _ = coordinatePoint := coordinatePoint_eq_point_first_zero.symm
  · rintro rfl
    exact coordinatePoint_not_in_second_chart

theorem in_second_chart_iff_ne_coordinatePoint (projectivePoint : ComplexProjectiveLine) :
    InChart .second projectivePoint ↔ projectivePoint ≠ coordinatePoint := by
  simpa only [not_not] using
    not_congr (not_in_second_chart_iff_eq_coordinatePoint projectivePoint)

/-- [proved-derived; formal-checked] The open cell is exactly one complex affine line. -/
def affineCellEquiv :
    { point : ComplexProjectiveLine // point ≠ coordinatePoint } ≃ ℂ where
  toFun situated := coordinate .second
    ⟨situated.1, (in_second_chart_iff_ne_coordinatePoint situated.1).2 situated.2⟩
  invFun z :=
    ⟨point .second z, by
      intro hequal
      have hmem : InChart .second coordinatePoint := by
        rw [← hequal]
        exact point_mem .second z
      exact coordinatePoint_not_in_second_chart hmem⟩
  left_inv situated := by
    apply Subtype.ext
    exact point_coordinate .second
      ⟨situated.1, (in_second_chart_iff_ne_coordinatePoint situated.1).2 situated.2⟩
  right_inv z := coordinate_chartPoint .second z

/-- [definition] The two cells of `ℙ¹`: a closed point and its affine complement. -/
inductive ProjectiveLineCell
  | closedPoint
  | affineLine
  deriving DecidableEq

/-- [definition] The actual support of each cell. -/
def projectiveLineCellSupport : ProjectiveLineCell → Set ComplexProjectiveLine
  | .closedPoint => {coordinatePoint}
  | .affineLine => {point | point ≠ coordinatePoint}

/-- [proved-derived; formal-checked] The two cell supports are disjoint. -/
theorem projectiveLineCellSupport_disjoint :
    Disjoint (projectiveLineCellSupport .closedPoint)
      (projectiveLineCellSupport .affineLine) := by
  rw [Set.disjoint_left]
  intro point hclosed hopen
  exact hopen hclosed

/-- [proved-derived; formal-checked] The two cell supports cover the actual projective line. -/
theorem projectiveLineCellSupport_cover :
    projectiveLineCellSupport .closedPoint ∪
      projectiveLineCellSupport .affineLine = Set.univ := by
  ext point
  by_cases hequal : point = coordinatePoint <;>
    simp [projectiveLineCellSupport, hequal]

/-- [definition] Real cell dimensions: the closed point has dimension zero and the affine complex
line has dimension two. -/
def ProjectiveLineCell.realDimension : ProjectiveLineCell → ℕ
  | .closedPoint => 0
  | .affineLine => 2

/-- [definition] Product cells on the surface. -/
abbrev SurfaceCell := ProjectiveLineCell × ProjectiveLineCell

def surfaceCellSupport (cell : SurfaceCell) : Set Surface :=
  { point | point.1 ∈ projectiveLineCellSupport cell.1 ∧
      point.2 ∈ projectiveLineCellSupport cell.2 }

def SurfaceCell.realDimension (cell : SurfaceCell) : ℕ :=
  cell.1.realDimension + cell.2.realDimension

/-- [proved-derived; formal-checked] Every surface point belongs to an addressed product cell. -/
theorem surfaceCellSupport_cover (surfacePoint : Surface) :
    ∃ cell : SurfaceCell, surfacePoint ∈ surfaceCellSupport cell := by
  by_cases hfirst : surfacePoint.1 = coordinatePoint
  · by_cases hsecond : surfacePoint.2 = coordinatePoint
    · exact ⟨(.closedPoint, .closedPoint), hfirst, hsecond⟩
    · exact ⟨(.closedPoint, .affineLine), hfirst, hsecond⟩
  · by_cases hsecond : surfacePoint.2 = coordinatePoint
    · exact ⟨(.affineLine, .closedPoint), hfirst, hsecond⟩
    · exact ⟨(.affineLine, .affineLine), hfirst, hsecond⟩

/-- [definition] The two real-dimension-two cells. -/
inductive DegreeTwoCell
  | firstAffine
  | secondAffine
  deriving DecidableEq

/-- [definition] The open support of a degree-two cell. -/
def DegreeTwoCell.openSupport : DegreeTwoCell → Set Surface
  | .firstAffine => surfaceCellSupport (.affineLine, .closedPoint)
  | .secondAffine => surfaceCellSupport (.closedPoint, .affineLine)

/-- [definition] Its geometric closure is the corresponding ruling divisor. -/
def DegreeTwoCell.closureSupport : DegreeTwoCell → Set Surface
  | .firstAffine => rulingSupport .second
  | .secondAffine => rulingSupport .first

theorem firstAffine_openSupport_subset_closure :
    DegreeTwoCell.openSupport .firstAffine ⊆
      DegreeTwoCell.closureSupport .firstAffine := by
  intro point hpoint
  exact hpoint.2

theorem secondAffine_openSupport_subset_closure :
    DegreeTwoCell.openSupport .secondAffine ⊆
      DegreeTwoCell.closureSupport .secondAffine := by
  intro point hpoint
  exact hpoint.1

/-- [definition] Rational degree-two cellular cochains. -/
abbrev CellularTwoCochain := DegreeTwoCell → ℚ

/-- [definition] There are no real-dimension-three cells, so the outgoing coboundary is zero. -/
def outgoingCoboundary : CellularTwoCochain →ₗ[ℚ] (Empty → ℚ) := 0

/-- [definition] There are no real-dimension-one cells, so the incoming coboundary is zero. -/
def incomingCoboundary : (Empty → ℚ) →ₗ[ℚ] CellularTwoCochain := 0

theorem outgoingCoboundary_kernel : LinearMap.ker outgoingCoboundary = ⊤ := by
  ext cochain
  simp [outgoingCoboundary]

theorem incomingCoboundary_range : LinearMap.range incomingCoboundary = ⊥ := by
  ext cochain
  simp [incomingCoboundary]

/-- [definition] Degree-two cellular cohomology is the cocycle carrier; the preceding theorem
proves that the incoming boundary submodule is bottom. -/
abbrev CellularH2 := LinearMap.ker outgoingCoboundary

/-- [proved-derived; formal-checked] Every two-cochain is an exact cocycle coordinate. -/
def cochainCocycleEquiv : CellularTwoCochain ≃ₗ[ℚ] CellularH2 where
  toFun cochain := ⟨cochain, by simp [outgoingCoboundary]⟩
  invFun cocycle := cocycle.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- [definition] The two cellular generators are reindexed into the existing bidegree chart. -/
def cellularH2BidegreeEquiv : CellularH2 ≃ₗ[ℚ] Bidegree :=
  cochainCocycleEquiv.symm.trans
    { toFun := fun cochain index => if index = 0 then cochain .secondAffine else cochain .firstAffine
      invFun := fun bidegree cell =>
        match cell with
        | .firstAffine => bidegree 1
        | .secondAffine => bidegree 0
      left_inv := by intro cochain; funext cell; cases cell <;> simp
      right_inv := by intro bidegree; funext index; fin_cases index <;> simp
      map_add' := by intro x y; funext index; fin_cases index <;> simp
      map_smul' := by intro coefficient x; funext index; fin_cases index <;> simp }

/-- [definition] The cycle-class map from actual rational ruling divisors into constructed
degree-two cellular cohomology. -/
def cellularCycleClass : RationalRulingDivisor →ₗ[ℚ] CellularH2 :=
  cellularH2BidegreeEquiv.symm.toLinearMap.comp divisorBidegreeEquiv.toLinearMap

/-- [definition] The Hodge datum whose source and degree-two target are both constructed from the
actual projective-line product geometry. -/
def cellularDatum : Datum where
  Variety := Surface
  codimension := 1
  CycleSpace := ModuleCat.of ℚ RationalRulingDivisor
  Cohomology := ModuleCat.of ℚ CellularH2
  cycleClass := ModuleCat.ofHom cellularCycleClass
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

private def topCongr (equivalence : Bidegree ≃ₗ[ℚ] CellularH2) :
    (⊤ : Submodule ℚ Bidegree) ≃ₗ[ℚ] (⊤ : Submodule ℚ CellularH2) where
  toFun x := ⟨equivalence x.1, Submodule.mem_top⟩
  invFun x := ⟨equivalence.symm x.1, Submodule.mem_top⟩
  left_inv x := Subtype.ext (equivalence.symm_apply_apply x.1)
  right_inv x := Subtype.ext (equivalence.apply_symm_apply x.1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- [definition] Both the geometric divisor source and the finite cellular target now construct
the complete comparison into the rank-two model. -/
def cellularComparison : ProjectiveLineProductComparison cellularDatum where
  varietyEquiv := Equiv.refl Surface
  codimension_one := rfl
  cycleEquiv := divisorBidegreeEquiv.symm
  cohomologyEquiv := cellularH2BidegreeEquiv.symm
  hodgeEquiv := topCongr cellularH2BidegreeEquiv.symm
  cycleClass_commutes := by
    intro cycle
    change cellularCycleClass (divisorBidegreeEquiv.symm cycle) =
      cellularH2BidegreeEquiv.symm cycle
    change cellularH2BidegreeEquiv.symm
        (divisorBidegreeEquiv (divisorBidegreeEquiv.symm cycle)) =
      cellularH2BidegreeEquiv.symm cycle
    exact congrArg cellularH2BidegreeEquiv.symm
      (divisorBidegreeEquiv.apply_symm_apply cycle)
  hodgeClass_commutes := by
    intro hodgeClass
    rfl

/-- [proved-derived; formal-checked] The constructed divisor-to-cellular-cohomology realization
closes its entire degree-two Hodge receiver. -/
theorem cellularHodgeConclusion : cellularDatum.Conclusion :=
  cellularComparison.actualHodgeConclusion

/-- [proved-derived; formal-checked] Each cellular degree-two Hodge occurrence returns a rational
combination of actual ruling divisors. -/
noncomputable def cellularCycleLift
    (hodgeClass : cellularDatum.rationalHodgeClasses) :
    CycleLiftFibre cellularDatum hodgeClass :=
  cellularComparison.transportedCycleLift hodgeClass

section Audit

#print axioms affineCellEquiv
#print axioms projectiveLineCellSupport_cover
#print axioms surfaceCellSupport_cover
#print axioms outgoingCoboundary_kernel
#print axioms incomingCoboundary_range
#print axioms cochainCocycleEquiv
#print axioms cellularH2BidegreeEquiv
#print axioms cellularCycleClass
#print axioms cellularComparison
#print axioms cellularHodgeConclusion
#print axioms cellularCycleLift

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
