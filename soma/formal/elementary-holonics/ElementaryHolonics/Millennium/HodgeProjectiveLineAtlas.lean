import ElementaryHolonics.Millennium.HodgeProjectiveLineProduct

/-!
# The exact affine atlas of the complex projective line and its product

The projective-line product Hodge calculation already uses the actual carrier
`Projectivization ℂ ℂ² × Projectivization ℂ ℂ²`, but its geometric comparison port previously
began after the carrier had been collapsed to two rational coordinates.  This file constructs the
missing source-side atlas directly on the quotient carrier.

For each of the two homogeneous coordinates we define its nonvanishing chart, normalize that
coordinate to one, and retain the other coordinate.  We prove:

* the two charts cover every projective point;
* affine coordinate followed by homogeneous reconstruction returns the original projective point;
* homogeneous reconstruction followed by affine coordinate returns the original coordinate;
* on the overlap, the two coordinates are exact multiplicative inverses;
* the four product charts cover `ℙ¹_ℂ × ℙ¹_ℂ` and reconstruct both components exactly.

These are quotient-level theorems about the actual projectivization, not assumptions in a Hodge
datum.  They are the algebraic atlas skeleton on which the later topology/smoothness, cellular
cohomology, and divisor-cycle comparison must be built.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineAtlas

open scoped LinearAlgebra.Projectivization
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct

/-- [definition] The two standard affine charts of the complex projective line. -/
inductive AffineChart
  | first
  | second

instance : DecidableEq AffineChart := fun left right =>
  match left, right with
  | .first, .first => isTrue rfl
  | .first, .second => isFalse (by intro equality; cases equality)
  | .second, .first => isFalse (by intro equality; cases equality)
  | .second, .second => isTrue rfl

/-- [definition] The homogeneous coordinate normalized to one in a chart. -/
def AffineChart.pivot : AffineChart → Fin 2
  | .first => 0
  | .second => 1

/-- [definition] The homogeneous coordinate returned as the affine coordinate. -/
def AffineChart.other : AffineChart → Fin 2
  | .first => 1
  | .second => 0

/-- [definition] A point belongs to a chart precisely when its pivot coordinate is nonzero.
The chosen representative does not affect this predicate; scale covariance is proved below. -/
def InChart (chart : AffineChart) (point : ComplexProjectiveLine) : Prop :=
  point.rep chart.pivot ≠ 0

/-- [definition] The affine coordinate returned by a chart. -/
def coordinate (chart : AffineChart)
    (point : { point : ComplexProjectiveLine // InChart chart point }) : ℂ :=
  point.1.rep chart.other / point.1.rep chart.pivot

/-- [definition] The normalized homogeneous vector belonging to an affine coordinate. -/
def normalizedVector (chart : AffineChart) (z : ℂ) : Fin 2 → ℂ :=
  match chart with
  | .first => fun index => if index = 0 then 1 else z
  | .second => fun index => if index = 1 then 1 else z

theorem normalizedVector_pivot (chart : AffineChart) (z : ℂ) :
    normalizedVector chart z chart.pivot = 1 := by
  cases chart <;> simp [normalizedVector, AffineChart.pivot]

theorem normalizedVector_other (chart : AffineChart) (z : ℂ) :
    normalizedVector chart z chart.other = z := by
  cases chart <;> simp [normalizedVector, AffineChart.other]

theorem normalizedVector_ne_zero (chart : AffineChart) (z : ℂ) :
    normalizedVector chart z ≠ 0 := by
  intro hzero
  have hpivot := congrFun hzero chart.pivot
  simpa [normalizedVector_pivot] using hpivot

/-- [definition] Homogeneous reconstruction of an affine coordinate. -/
def point (chart : AffineChart) (z : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ (normalizedVector chart z) (normalizedVector_ne_zero chart z)

/-- [proved-derived; formal-checked] Ratios of coordinates are independent of the representative
chosen by the projectivization quotient. -/
theorem representative_ratio_mk
    (vector : Fin 2 → ℂ) (hvector : vector ≠ 0)
    (first second : Fin 2) (hsecond : vector second ≠ 0) :
    (Projectivization.mk ℂ vector hvector).rep first /
        (Projectivization.mk ℂ vector hvector).rep second =
      vector first / vector second := by
  obtain ⟨scale, hscale⟩ :=
    Projectivization.exists_smul_eq_mk_rep ℂ vector hvector
  have hfirst := congrFun hscale first
  have hsecondCoordinate := congrFun hscale second
  change (scale : ℂ) * vector first =
    (Projectivization.mk ℂ vector hvector).rep first at hfirst
  change (scale : ℂ) * vector second =
    (Projectivization.mk ℂ vector hvector).rep second at hsecondCoordinate
  rw [← hfirst, ← hsecondCoordinate]
  exact mul_div_mul_left _ _ (Units.ne_zero scale)

/-- [proved-derived; formal-checked] Every reconstructed point lies in its declared chart. -/
theorem point_mem (chart : AffineChart) (z : ℂ) : InChart chart (point chart z) := by
  obtain ⟨scale, hscale⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (normalizedVector chart z) (normalizedVector_ne_zero chart z)
  have hpivot := congrFun hscale chart.pivot
  change (scale : ℂ) * normalizedVector chart z chart.pivot =
    (Projectivization.mk ℂ (normalizedVector chart z)
      (normalizedVector_ne_zero chart z)).rep chart.pivot at hpivot
  rw [normalizedVector_pivot, mul_one] at hpivot
  change (Projectivization.mk ℂ (normalizedVector chart z)
    (normalizedVector_ne_zero chart z)).rep chart.pivot ≠ 0
  rw [← hpivot]
  exact Units.ne_zero scale

/-- [definition] The reconstructed point situated in its chart. -/
def chartPoint (chart : AffineChart) (z : ℂ) :
    { point : ComplexProjectiveLine // InChart chart point } :=
  ⟨point chart z, point_mem chart z⟩

/-- [proved-derived; formal-checked] Normalization followed by the affine receiver is exact. -/
theorem coordinate_chartPoint (chart : AffineChart) (z : ℂ) :
    coordinate chart (chartPoint chart z) = z := by
  change (Projectivization.mk ℂ (normalizedVector chart z)
      (normalizedVector_ne_zero chart z)).rep chart.other /
      (Projectivization.mk ℂ (normalizedVector chart z)
        (normalizedVector_ne_zero chart z)).rep chart.pivot = z
  rw [representative_ratio_mk]
  · rw [normalizedVector_other, normalizedVector_pivot]
    simp
  · exact normalizedVector_pivot chart z ▸ one_ne_zero

/-- [proved-derived; formal-checked] The affine coordinate reconstructs the original projective
point, including its quotient lineage. -/
theorem point_coordinate (chart : AffineChart)
    (situated : { point : ComplexProjectiveLine // InChart chart point }) :
    point chart (coordinate chart situated) = situated.1 := by
  rw [← Projectivization.mk_rep situated.1]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _
    (normalizedVector_ne_zero chart (coordinate chart situated))
    situated.1.rep_nonzero).2
  refine ⟨(situated.1.rep chart.pivot)⁻¹, ?_⟩
  funext index
  cases chart with
  | first =>
      have hpivot : situated.1.rep 0 ≠ 0 := situated.2
      fin_cases index
      · change (situated.1.rep 0)⁻¹ * situated.1.rep 0 = 1
        simpa [AffineChart.pivot] using inv_mul_cancel₀ hpivot
      · simp [normalizedVector, coordinate, AffineChart.pivot, AffineChart.other,
          div_eq_mul_inv, mul_comm]
  | second =>
      have hpivot : situated.1.rep 1 ≠ 0 := situated.2
      fin_cases index
      · simp [normalizedVector, coordinate, AffineChart.pivot, AffineChart.other,
          div_eq_mul_inv, mul_comm]
      · change (situated.1.rep 1)⁻¹ * situated.1.rep 1 = 1
        simpa [AffineChart.pivot] using inv_mul_cancel₀ hpivot

/-- [proved-derived; formal-checked] Each declared affine chart is genuinely equivalent to `ℂ`. -/
def chartEquiv (chart : AffineChart) :
    { point : ComplexProjectiveLine // InChart chart point } ≃ ℂ where
  toFun := coordinate chart
  invFun := chartPoint chart
  left_inv := by
    intro situated
    apply Subtype.ext
    exact point_coordinate chart situated
  right_inv := coordinate_chartPoint chart

/-- [proved-derived; formal-checked] The two affine charts cover the projective line. -/
theorem chart_cover (projectivePoint : ComplexProjectiveLine) :
    InChart .first projectivePoint ∨ InChart .second projectivePoint := by
  by_contra hmissing
  push_neg at hmissing
  apply projectivePoint.rep_nonzero
  funext index
  fin_cases index
  · exact not_ne_iff.mp hmissing.1
  · exact not_ne_iff.mp hmissing.2

/-- [proved-derived; formal-checked] On the overlap the two affine readings multiply to one. -/
theorem overlap_coordinates_mul
    (projectivePoint : ComplexProjectiveLine)
    (hfirst : InChart .first projectivePoint)
    (hsecond : InChart .second projectivePoint) :
    coordinate .first ⟨projectivePoint, hfirst⟩ *
        coordinate .second ⟨projectivePoint, hsecond⟩ = 1 := by
  simp only [coordinate, AffineChart.other, AffineChart.pivot]
  rw [div_mul_div_comm]
  rw [mul_comm (projectivePoint.rep 0) (projectivePoint.rep 1)]
  exact div_self (mul_ne_zero hsecond hfirst)

/-- [proved-derived; formal-checked] The transition function between the two charts is inversion. -/
theorem overlap_transition
    (projectivePoint : ComplexProjectiveLine)
    (hfirst : InChart .first projectivePoint)
    (hsecond : InChart .second projectivePoint) :
    coordinate .second ⟨projectivePoint, hsecond⟩ =
      (coordinate .first ⟨projectivePoint, hfirst⟩)⁻¹ := by
  simp only [coordinate, AffineChart.other, AffineChart.pivot]
  field_simp [hfirst, hsecond]

/-! ## The four-chart product atlas -/

/-- [definition] A product chart independently addresses each projective-line factor. -/
abbrev SurfaceChart := AffineChart × AffineChart

/-- [definition] Membership in a product chart retains both component memberships. -/
def InSurfaceChart (chart : SurfaceChart) (surfacePoint : Surface) : Prop :=
  InChart chart.1 surfacePoint.1 ∧ InChart chart.2 surfacePoint.2

/-- [definition] The two-dimensional complex coordinate returned by a product chart. -/
def surfaceCoordinate (chart : SurfaceChart)
    (surfacePoint : { point : Surface // InSurfaceChart chart point }) : ℂ × ℂ :=
  (coordinate chart.1 ⟨surfacePoint.1.1, surfacePoint.2.1⟩,
    coordinate chart.2 ⟨surfacePoint.1.2, surfacePoint.2.2⟩)

/-- [definition] Product reconstruction from two affine coordinates. -/
def surfacePoint (chart : SurfaceChart) (z : ℂ × ℂ) : Surface :=
  (point chart.1 z.1, point chart.2 z.2)

theorem surfacePoint_mem (chart : SurfaceChart) (z : ℂ × ℂ) :
    InSurfaceChart chart (surfacePoint chart z) :=
  ⟨point_mem chart.1 z.1, point_mem chart.2 z.2⟩

/-- [definition] Product reconstruction situated in the chosen chart. -/
def surfaceChartPoint (chart : SurfaceChart) (z : ℂ × ℂ) :
    { point : Surface // InSurfaceChart chart point } :=
  ⟨surfacePoint chart z, surfacePoint_mem chart z⟩

theorem surfaceCoordinate_surfaceChartPoint (chart : SurfaceChart) (z : ℂ × ℂ) :
    surfaceCoordinate chart (surfaceChartPoint chart z) = z := by
  apply Prod.ext
  · change coordinate chart.1 (chartPoint chart.1 z.1) = z.1
    exact coordinate_chartPoint chart.1 z.1
  · change coordinate chart.2 (chartPoint chart.2 z.2) = z.2
    exact coordinate_chartPoint chart.2 z.2

theorem surfacePoint_surfaceCoordinate (chart : SurfaceChart)
    (situated : { point : Surface // InSurfaceChart chart point }) :
    surfacePoint chart (surfaceCoordinate chart situated) = situated.1 := by
  apply Prod.ext
  · exact point_coordinate chart.1 ⟨situated.1.1, situated.2.1⟩
  · exact point_coordinate chart.2 ⟨situated.1.2, situated.2.2⟩

/-- [proved-derived; formal-checked] Every product chart is exactly equivalent to `ℂ²`. -/
def surfaceChartEquiv (chart : SurfaceChart) :
    { point : Surface // InSurfaceChart chart point } ≃ ℂ × ℂ where
  toFun := surfaceCoordinate chart
  invFun := surfaceChartPoint chart
  left_inv := by
    intro situated
    apply Subtype.ext
    exact surfacePoint_surfaceCoordinate chart situated
  right_inv := surfaceCoordinate_surfaceChartPoint chart

/-- [proved-derived; formal-checked] The four product charts cover the actual projective-line
product surface. -/
theorem surface_chart_cover (surfacePoint : Surface) :
    ∃ chart : SurfaceChart, InSurfaceChart chart surfacePoint := by
  obtain hfirst | hsecond := chart_cover surfacePoint.1
  · obtain hthird | hfourth := chart_cover surfacePoint.2
    · exact ⟨(.first, .first), hfirst, hthird⟩
    · exact ⟨(.first, .second), hfirst, hfourth⟩
  · obtain hthird | hfourth := chart_cover surfacePoint.2
    · exact ⟨(.second, .first), hsecond, hthird⟩
    · exact ⟨(.second, .second), hsecond, hfourth⟩

section Audit

#print axioms representative_ratio_mk
#print axioms point_mem
#print axioms coordinate_chartPoint
#print axioms point_coordinate
#print axioms chartEquiv
#print axioms chart_cover
#print axioms overlap_coordinates_mul
#print axioms overlap_transition
#print axioms surfaceChartEquiv
#print axioms surface_chart_cover

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
