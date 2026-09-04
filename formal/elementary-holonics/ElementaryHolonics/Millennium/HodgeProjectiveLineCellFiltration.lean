import ElementaryHolonics.Millennium.HodgeProjectiveLineTopology
import ElementaryHolonics.Millennium.HodgeSphereProductFiniteComplex

/-!
# The actual `0 ⊂ 2 ⊂ 4` cell filtration of the projective-line product

This file constructs the geometric filtration that the singular-to-cellular proof must consume.
It is not a list of abstract cells.  Every stratum is a subset of the actual projectivization
carrier, every open cell has an explicit affine coordinate equivalence, and every closure/frontier
relation is proved in the transported topology.

The filtration is

`{(∞,∞)} ⊂ (ℙ¹ × {∞}) ∪ ({∞} × ℙ¹) ⊂ ℙ¹ × ℙ¹`.

Its strata have real dimensions `0`, `2 + 2`, and `4`.  The two middle cell closures are the
geometric ruling divisors already used by the cycle-class source.  The top-cell frontier is exactly
their union.  This supplies the actual attaching incidence needed by the forthcoming singular
chain reduction; none of these relations are postulated through a comparison field.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineCellFiltration

open Set
open scoped OnePoint
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology

/-- [definition] The unique zero-cell of the product. -/
def zeroSkeleton : Set Surface := {(coordinatePoint, coordinatePoint)}

/-- [definition] The two-skeleton is the union of the two geometric ruling divisors. -/
def twoSkeleton : Set Surface := rulingSupport .first ∪ rulingSupport .second

/-- [definition] The open four-cell is the simultaneous affine locus. -/
def fourCellOpen : Set Surface :=
  { surfacePoint | surfacePoint.1 ≠ coordinatePoint ∧ surfacePoint.2 ≠ coordinatePoint }

/-- [definition] The affine part of one projective line. -/
def affineLocus : Set ComplexProjectiveLine := { point | point ≠ coordinatePoint }

theorem affineLocus_eq_homeomorph_preimage_range :
    affineLocus = projectiveLineHomeomorphOnePoint ⁻¹'
      Set.range ((↑) : ℂ → OnePoint ℂ) := by
  ext projectivePoint
  by_cases hequal : projectivePoint = coordinatePoint
  · subst projectivePoint
    simp [affineLocus, projectiveLineHomeomorphOnePoint,
      projectiveLineEquivOnePoint, onePointEquivProjectiveLine]
  · simp [affineLocus, hequal, projectiveLineHomeomorphOnePoint,
      projectiveLineEquivOnePoint, onePointEquivProjectiveLine]

/-- [proved-derived; formal-checked] The affine cell is dense in the actual projective line. -/
theorem dense_affineLocus : Dense affineLocus := by
  rw [affineLocus_eq_homeomorph_preimage_range, dense_iff_closure_eq]
  rw [← projectiveLineHomeomorphOnePoint.preimage_closure]
  rw [OnePoint.denseRange_coe.closure_eq]
  simp

theorem affineLocus_isOpen : IsOpen affineLocus := by
  change IsOpen ({coordinatePoint}ᶜ : Set ComplexProjectiveLine)
  exact isClosed_singleton.isOpen_compl

theorem fourCellOpen_eq_prod :
    fourCellOpen = affineLocus ×ˢ affineLocus := by
  ext surfacePoint
  rfl

theorem fourCellOpen_isOpen : IsOpen fourCellOpen := by
  rw [fourCellOpen_eq_prod]
  exact affineLocus_isOpen.prod affineLocus_isOpen

/-- [proved-derived; formal-checked] The top cell is dense: its closure is the whole surface. -/
theorem closure_fourCellOpen : closure fourCellOpen = Set.univ := by
  rw [fourCellOpen_eq_prod, closure_prod_eq, dense_affineLocus.closure_eq]
  exact univ_prod_univ

/-- [proved-derived; formal-checked] What is not in the top affine cell is exactly one of the two
ruling divisors. -/
theorem fourCellOpen_compl : fourCellOpenᶜ = twoSkeleton := by
  ext surfacePoint
  simp [fourCellOpen, twoSkeleton, rulingSupport]
  tauto

/-- [proved-derived; formal-checked] The frontier of the four-cell is exactly the two-skeleton. -/
theorem frontier_fourCellOpen : frontier fourCellOpen = twoSkeleton := by
  rw [frontier, closure_fourCellOpen, fourCellOpen_isOpen.interior_eq]
  calc
    Set.univ \ fourCellOpen = fourCellOpenᶜ := by ext; simp
    _ = twoSkeleton := fourCellOpen_compl

/-- [definition] Coordinate equivalence for the actual top cell. -/
def fourCellEquiv : { point : Surface // point ∈ fourCellOpen } ≃ ℂ × ℂ where
  toFun point :=
    (affineCellEquiv ⟨point.1.1, point.2.1⟩,
      affineCellEquiv ⟨point.1.2, point.2.2⟩)
  invFun coordinate :=
    ⟨((affineCellEquiv.symm coordinate.1).1, (affineCellEquiv.symm coordinate.2).1),
      (affineCellEquiv.symm coordinate.1).2,
      (affineCellEquiv.symm coordinate.2).2⟩
  left_inv point := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (affineCellEquiv.left_inv ⟨point.1.1, point.2.1⟩)
    · exact congrArg Subtype.val (affineCellEquiv.left_inv ⟨point.1.2, point.2.2⟩)
  right_inv coordinate := by
    apply Prod.ext
    · exact affineCellEquiv.right_inv coordinate.1
    · exact affineCellEquiv.right_inv coordinate.2

/-- [definition] Coordinate equivalence for the first open two-cell. -/
def firstTwoCellEquiv :
    { point : Surface // point ∈ DegreeTwoCell.openSupport .firstAffine } ≃ ℂ where
  toFun point := affineCellEquiv ⟨point.1.1, point.2.1⟩
  invFun coordinate :=
    ⟨((affineCellEquiv.symm coordinate).1, coordinatePoint),
      (affineCellEquiv.symm coordinate).2, rfl⟩
  left_inv point := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (affineCellEquiv.left_inv ⟨point.1.1, point.2.1⟩)
    · exact point.2.2.symm
  right_inv coordinate := affineCellEquiv.right_inv coordinate

/-- [definition] Coordinate equivalence for the second open two-cell. -/
def secondTwoCellEquiv :
    { point : Surface // point ∈ DegreeTwoCell.openSupport .secondAffine } ≃ ℂ where
  toFun point := affineCellEquiv ⟨point.1.2, point.2.2⟩
  invFun coordinate :=
    ⟨(coordinatePoint, (affineCellEquiv.symm coordinate).1),
      rfl, (affineCellEquiv.symm coordinate).2⟩
  left_inv point := by
    apply Subtype.ext
    apply Prod.ext
    · exact point.2.1.symm
    · exact congrArg Subtype.val (affineCellEquiv.left_inv ⟨point.1.2, point.2.2⟩)
  right_inv coordinate := affineCellEquiv.right_inv coordinate

theorem firstTwoCellOpen_eq_prod :
    DegreeTwoCell.openSupport .firstAffine = affineLocus ×ˢ {coordinatePoint} := by
  ext point
  rfl

theorem secondTwoCellOpen_eq_prod :
    DegreeTwoCell.openSupport .secondAffine = {coordinatePoint} ×ˢ affineLocus := by
  ext point
  rfl

/-- [proved-derived; formal-checked] The closure of the first two-cell is its actual ruling
divisor. -/
theorem closure_firstTwoCell :
    closure (DegreeTwoCell.openSupport .firstAffine) = rulingSupport .second := by
  rw [firstTwoCellOpen_eq_prod, closure_prod_eq, dense_affineLocus.closure_eq,
    closure_singleton]
  ext point
  simp [rulingSupport]

/-- [proved-derived; formal-checked] The closure of the second two-cell is its actual ruling
divisor. -/
theorem closure_secondTwoCell :
    closure (DegreeTwoCell.openSupport .secondAffine) = rulingSupport .first := by
  rw [secondTwoCellOpen_eq_prod, closure_prod_eq, closure_singleton,
    dense_affineLocus.closure_eq]
  ext point
  simp [rulingSupport]

/-- [proved-derived; formal-checked] The two-skeleton is the disjoint-cell union of the zero-cell
and the two open degree-two cells. -/
theorem twoSkeleton_cell_decomposition :
    twoSkeleton = zeroSkeleton ∪ DegreeTwoCell.openSupport .firstAffine ∪
      DegreeTwoCell.openSupport .secondAffine := by
  ext point
  by_cases hfirst : point.1 = coordinatePoint <;>
    by_cases hsecond : point.2 = coordinatePoint <;>
      simp [twoSkeleton, zeroSkeleton, DegreeTwoCell.openSupport, surfaceCellSupport,
        projectiveLineCellSupport, rulingSupport, Prod.ext_iff, hfirst, hsecond]

/-- [proved-derived; formal-checked] All four strata cover the surface. -/
theorem cellFiltration_cover :
    zeroSkeleton ∪ DegreeTwoCell.openSupport .firstAffine ∪
      DegreeTwoCell.openSupport .secondAffine ∪ fourCellOpen = Set.univ := by
  rw [← twoSkeleton_cell_decomposition, ← fourCellOpen_compl]
  exact compl_union_self fourCellOpen

/-- [proved-derived; formal-checked] The frontier of either two-cell inside its ruling closure is
the unique zero-cell. -/
theorem firstTwoCell_closure_diff_open :
    closure (DegreeTwoCell.openSupport .firstAffine) \
      DegreeTwoCell.openSupport .firstAffine = zeroSkeleton := by
  rw [closure_firstTwoCell, firstTwoCellOpen_eq_prod]
  ext point
  by_cases hfirst : point.1 = coordinatePoint <;>
    by_cases hsecond : point.2 = coordinatePoint <;>
      simp [zeroSkeleton, affineLocus, rulingSupport, Prod.ext_iff, hfirst, hsecond]

theorem secondTwoCell_closure_diff_open :
    closure (DegreeTwoCell.openSupport .secondAffine) \
      DegreeTwoCell.openSupport .secondAffine = zeroSkeleton := by
  rw [closure_secondTwoCell, secondTwoCellOpen_eq_prod]
  ext point
  by_cases hfirst : point.1 = coordinatePoint <;>
    by_cases hsecond : point.2 = coordinatePoint <;>
      simp [zeroSkeleton, affineLocus, rulingSupport, Prod.ext_iff, hfirst, hsecond]

section Audit

#print axioms dense_affineLocus
#print axioms closure_fourCellOpen
#print axioms frontier_fourCellOpen
#print axioms fourCellEquiv
#print axioms firstTwoCellEquiv
#print axioms secondTwoCellEquiv
#print axioms closure_firstTwoCell
#print axioms closure_secondTwoCell
#print axioms twoSkeleton_cell_decomposition
#print axioms cellFiltration_cover
#print axioms firstTwoCell_closure_diff_open
#print axioms secondTwoCell_closure_diff_open

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineCellFiltration
