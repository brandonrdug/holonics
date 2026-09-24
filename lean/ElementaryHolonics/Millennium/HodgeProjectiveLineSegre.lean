import ElementaryHolonics.Millennium.HodgeProjectiveLineTopology

/-!
# The Segre realization of the projective-line product

This file constructs the projective embedding required by the geometric Hodge source.  For actual
projective points represented by nonzero vectors `u,v : ℂ²`, their Segre coordinate at `(i,j)` is
`u i * v j`.  We prove directly on the quotient carrier that:

* the Segre vector is nonzero;
* its image satisfies the homogeneous quadric equation
  `X₀₀ X₁₁ - X₀₁ X₁₀ = 0`;
* equality of two Segre projective points reconstructs equality of both source projective points.

Thus the actual carrier `ℙ¹_ℂ × ℙ¹_ℂ` has an injective homogeneous quadratic realization in
`ℙ³_ℂ`.  The proof uses the full projectivization quotient relation and does not assume an
embedding field.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineSegre

open scoped LinearAlgebra.Projectivization
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct

/-- [definition] Four homogeneous coordinates indexed by the two source coordinates. -/
abbrev SegreCoordinate := Fin 2 × Fin 2

/-- [definition] Complex projective three-space in the four Segre coordinates. -/
abbrev ComplexProjectiveThreeSpace := Projectivization ℂ (SegreCoordinate → ℂ)

/-- [definition] The rank-one tensor of two homogeneous coordinate vectors. -/
def segreVector (left right : Fin 2 → ℂ) : SegreCoordinate → ℂ :=
  fun coordinate => left coordinate.1 * right coordinate.2

private theorem exists_coordinate_ne_zero
    {vector : Fin 2 → ℂ} (hvector : vector ≠ 0) :
    ∃ index : Fin 2, vector index ≠ 0 := by
  by_contra hmissing
  push_neg at hmissing
  apply hvector
  funext index
  exact hmissing index

theorem segreVector_ne_zero
    {left right : Fin 2 → ℂ} (hleft : left ≠ 0) (hright : right ≠ 0) :
    segreVector left right ≠ 0 := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  intro hzero
  have hatCoordinate := congrFun hzero (leftIndex, rightIndex)
  exact (mul_ne_zero hleftIndex hrightIndex) (by simpa [segreVector] using hatCoordinate)

/-- [definition] The projective point returned by two nonzero homogeneous vectors. -/
def segrePoint (left right : Fin 2 → ℂ) (hleft : left ≠ 0) (hright : right ≠ 0) :
    ComplexProjectiveThreeSpace :=
  Projectivization.mk ℂ (segreVector left right)
    (segreVector_ne_zero hleft hright)

/-- [definition] The Segre map on the actual projective-line product carrier. -/
def segre (surfacePoint : Surface) : ComplexProjectiveThreeSpace :=
  segrePoint surfacePoint.1.rep surfacePoint.2.rep
    surfacePoint.1.rep_nonzero surfacePoint.2.rep_nonzero

/-- [definition] The determinant cutting out the Segre quadric. -/
def quadricDeterminant (coordinate : SegreCoordinate → ℂ) : ℂ :=
  coordinate (0, 0) * coordinate (1, 1) -
    coordinate (0, 1) * coordinate (1, 0)

theorem quadricDeterminant_segreVector (left right : Fin 2 → ℂ) :
    quadricDeterminant (segreVector left right) = 0 := by
  simp [quadricDeterminant, segreVector]
  ring

theorem quadricDeterminant_smul (scale : ℂ) (coordinate : SegreCoordinate → ℂ) :
    quadricDeterminant (scale • coordinate) = scale ^ 2 * quadricDeterminant coordinate := by
  simp [quadricDeterminant]
  ring

/-- [definition] The homogeneous quadric locus in projective three-space. -/
def OnSegreQuadric (projectivePoint : ComplexProjectiveThreeSpace) : Prop :=
  quadricDeterminant projectivePoint.rep = 0

/-- [definition] The exact Jacobian row of the Segre quadric equation. -/
def quadricGradient (coordinate : SegreCoordinate → ℂ) : SegreCoordinate → ℂ
  | (0, 0) => coordinate (1, 1)
  | (0, 1) => -coordinate (1, 0)
  | (1, 0) => -coordinate (0, 1)
  | (1, 1) => coordinate (0, 0)

/-- [proved-derived; formal-checked] The quadric gradient vanishes only at the excluded zero
homogeneous vector. -/
theorem quadricGradient_eq_zero_iff (coordinate : SegreCoordinate → ℂ) :
    quadricGradient coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro hgradient
    funext coordinateIndex
    rcases coordinateIndex with ⟨firstIndex, secondIndex⟩
    fin_cases firstIndex <;> fin_cases secondIndex
    · have h := congrFun hgradient ((1 : Fin 2), (1 : Fin 2))
      simpa [quadricGradient] using h
    · have h := congrFun hgradient ((1 : Fin 2), (0 : Fin 2))
      simpa [quadricGradient] using congrArg Neg.neg h
    · have h := congrFun hgradient ((0 : Fin 2), (1 : Fin 2))
      simpa [quadricGradient] using congrArg Neg.neg h
    · have h := congrFun hgradient ((0 : Fin 2), (0 : Fin 2))
      simpa [quadricGradient] using h
  · rintro rfl
    funext coordinateIndex
    rcases coordinateIndex with ⟨firstIndex, secondIndex⟩
    fin_cases firstIndex <;> fin_cases secondIndex <;> simp [quadricGradient]

/-- [proved-derived; formal-checked] Every projective point has nonvanishing quadric Jacobian.
This is the source-level nonsingularity certificate for the projective quadric hypersurface. -/
theorem quadricGradient_rep_ne_zero (projectivePoint : ComplexProjectiveThreeSpace) :
    quadricGradient projectivePoint.rep ≠ 0 := by
  intro hgradient
  exact projectivePoint.rep_nonzero
    ((quadricGradient_eq_zero_iff projectivePoint.rep).1 hgradient)

/-- [definition] The smooth projective quadric locus, with its Jacobian witness retained. -/
def OnSmoothSegreQuadric (projectivePoint : ComplexProjectiveThreeSpace) : Prop :=
  OnSegreQuadric projectivePoint ∧ quadricGradient projectivePoint.rep ≠ 0

/-- [proved-derived; formal-checked] Every Segre image lies on the projective quadric. -/
theorem segre_mem_quadric (surfacePoint : Surface) : OnSegreQuadric (segre surfacePoint) := by
  obtain ⟨scale, hscale⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (segreVector surfacePoint.1.rep surfacePoint.2.rep)
    (segreVector_ne_zero surfacePoint.1.rep_nonzero surfacePoint.2.rep_nonzero)
  change quadricDeterminant
    (Projectivization.mk ℂ
      (segreVector surfacePoint.1.rep surfacePoint.2.rep)
      (segreVector_ne_zero surfacePoint.1.rep_nonzero
        surfacePoint.2.rep_nonzero)).rep = 0
  rw [← hscale]
  change quadricDeterminant
    ((scale : ℂ) • segreVector surfacePoint.1.rep surfacePoint.2.rep) = 0
  rw [quadricDeterminant_smul, quadricDeterminant_segreVector, mul_zero]

/-- [proved-derived; formal-checked] Every Segre image lies on the nonsingular projective
quadric, combining the homogeneous equation with its nonvanishing Jacobian. -/
theorem segre_mem_smooth_quadric (surfacePoint : Surface) :
    OnSmoothSegreQuadric (segre surfacePoint) :=
  ⟨segre_mem_quadric surfacePoint, quadricGradient_rep_ne_zero (segre surfacePoint)⟩

private theorem recover_left_from_scaled_segre
    {left right left' right' : Fin 2 → ℂ}
    (hleft : left ≠ 0) (hright : right ≠ 0)
    (scale : ℂ)
    (hscaled : scale • segreVector left' right' = segreVector left right) :
    ∃ coefficient : ℂ, coefficient • left' = left := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  have hcoordinate := congrFun hscaled (leftIndex, rightIndex)
  change scale * (left' leftIndex * right' rightIndex) =
    left leftIndex * right rightIndex at hcoordinate
  have hrightIndex' : right' rightIndex ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, mul_zero] at hcoordinate
    exact (mul_ne_zero hleftIndex hrightIndex) hcoordinate.symm
  refine ⟨scale * right' rightIndex / right rightIndex, ?_⟩
  funext index
  have hindex := congrFun hscaled (index, rightIndex)
  change scale * (left' index * right' rightIndex) =
    left index * right rightIndex at hindex
  change (scale * right' rightIndex / right rightIndex) * left' index = left index
  calc
    (scale * right' rightIndex / right rightIndex) * left' index =
        (scale * (left' index * right' rightIndex)) / right rightIndex := by ring
    _ = (left index * right rightIndex) / right rightIndex := by rw [hindex]
    _ = left index := by field_simp [hrightIndex]

private theorem recover_right_from_scaled_segre
    {left right left' right' : Fin 2 → ℂ}
    (hleft : left ≠ 0) (hright : right ≠ 0)
    (scale : ℂ)
    (hscaled : scale • segreVector left' right' = segreVector left right) :
    ∃ coefficient : ℂ, coefficient • right' = right := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  have hcoordinate := congrFun hscaled (leftIndex, rightIndex)
  change scale * (left' leftIndex * right' rightIndex) =
    left leftIndex * right rightIndex at hcoordinate
  have hleftIndex' : left' leftIndex ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, mul_zero] at hcoordinate
    exact (mul_ne_zero hleftIndex hrightIndex) hcoordinate.symm
  refine ⟨scale * left' leftIndex / left leftIndex, ?_⟩
  funext index
  have hindex := congrFun hscaled (leftIndex, index)
  change scale * (left' leftIndex * right' index) =
    left leftIndex * right index at hindex
  change (scale * left' leftIndex / left leftIndex) * right' index = right index
  calc
    (scale * left' leftIndex / left leftIndex) * right' index =
        (scale * (left' leftIndex * right' index)) / left leftIndex := by ring
    _ = (left leftIndex * right index) / left leftIndex := by rw [hindex]
    _ = right index := by field_simp [hleftIndex]

/-- [proved-derived; formal-checked] Equality in the Segre receiver reconstructs both source
projective points.  No coordinate chart or selected inverse is lost. -/
theorem segre_injective : Function.Injective segre := by
  rintro ⟨left, right⟩ ⟨left', right'⟩ hequal
  change segrePoint left.rep right.rep left.rep_nonzero right.rep_nonzero =
    segrePoint left'.rep right'.rep left'.rep_nonzero right'.rep_nonzero at hequal
  obtain ⟨scale, hscaled⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (segreVector left.rep right.rep)
      (segreVector left'.rep right'.rep)
      (segreVector_ne_zero left.rep_nonzero right.rep_nonzero)
      (segreVector_ne_zero left'.rep_nonzero right'.rep_nonzero)).1 hequal
  obtain ⟨leftScale, hleftScale⟩ := recover_left_from_scaled_segre
    left.rep_nonzero right.rep_nonzero scale hscaled
  obtain ⟨rightScale, hrightScale⟩ := recover_right_from_scaled_segre
    left.rep_nonzero right.rep_nonzero scale hscaled
  apply Prod.ext
  · rw [← Projectivization.mk_rep left, ← Projectivization.mk_rep left']
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ left.rep_nonzero left'.rep_nonzero).2
      ⟨leftScale, hleftScale⟩
  · rw [← Projectivization.mk_rep right, ← Projectivization.mk_rep right']
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ right.rep_nonzero right'.rep_nonzero).2
      ⟨rightScale, hrightScale⟩

/-- [definition] The actual surface realized as the image of its injective homogeneous quadratic
Segre map. -/
def segreImageEquiv : Surface ≃ { point : ComplexProjectiveThreeSpace // point ∈ Set.range segre } :=
  Equiv.ofInjective segre segre_injective

section Audit

#print axioms segreVector_ne_zero
#print axioms quadricDeterminant_segreVector
#print axioms quadricDeterminant_smul
#print axioms quadricGradient_eq_zero_iff
#print axioms quadricGradient_rep_ne_zero
#print axioms segre_mem_quadric
#print axioms segre_mem_smooth_quadric
#print axioms segre_injective
#print axioms segreImageEquiv

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineSegre
