import ElementaryHolonics.Millennium.HodgePowerComparison

/-!
# The finite Segre tensor embedding

The two-factor Segre construction is generalized here without duplicating a proof at every power.
First, one generic projective tensor-pair map is proved injective for arbitrary coordinate types.
It reconstructs both projective factors from equality of their rank-one tensor points.  The finite
projective-line power then enters recursively through this one map.

The resulting homogeneous coordinates are nested tensor addresses, and an exact equivalence
identifies them with binary factor words `Fin n → Fin 2`.  Thus the `2^n` coordinate population is
not an anonymous scalar count: every coordinate retains one binary choice at every projective-line
factor.  This file returns the embedding, its complete source reconstruction, and an equation-only
recursive homogeneous minor locus proved exactly equal to the global Segre range.  Closedness,
nonsingularity/global atlas transport, and coordinate-hyperplane pullback remain separate theorem
obligations for the smooth-projective admission certificate.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgePowerSegre

open scoped LinearAlgebra.Projectivization
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgePowerComparison

/-- [definition] The rank-one tensor of two addressed homogeneous vectors. -/
def tensorPairVector {I J : Type*} (left : I → ℂ) (right : J → ℂ) :
    I × J → ℂ := fun coordinate => left coordinate.1 * right coordinate.2

theorem exists_coordinate_ne_zero {I : Type*} {vector : I → ℂ}
    (hvector : vector ≠ 0) : ∃ index, vector index ≠ 0 := by
  by_contra hmissing
  apply hvector
  funext index
  by_contra hnonzero
  exact hmissing ⟨index, hnonzero⟩

/-- [proved-derived; formal-checked] Two nonzero vector occurrences have a nonzero rank-one tensor
product, with an explicit nonzero coordinate witness. -/
theorem tensorPairVector_ne_zero {I J : Type*}
    {left : I → ℂ} {right : J → ℂ} (hleft : left ≠ 0) (hright : right ≠ 0) :
    tensorPairVector left right ≠ 0 := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  intro hzero
  have hatCoordinate := congrFun hzero (leftIndex, rightIndex)
  exact (mul_ne_zero hleftIndex hrightIndex)
    (by simpa [tensorPairVector] using hatCoordinate)

abbrev TensorPairProjectiveSpace (I J : Type*) :=
  Projectivization ℂ (I × J → ℂ)

def tensorPairPoint {I J : Type*} (left : I → ℂ) (right : J → ℂ)
    (hleft : left ≠ 0) (hright : right ≠ 0) : TensorPairProjectiveSpace I J :=
  Projectivization.mk ℂ (tensorPairVector left right)
    (tensorPairVector_ne_zero hleft hright)

/-- [definition] The generic rank-one projective tensor passage. -/
def tensorPairSegre {I J : Type*}
    (pair : Projectivization ℂ (I → ℂ) × Projectivization ℂ (J → ℂ)) :
    TensorPairProjectiveSpace I J :=
  tensorPairPoint pair.1.rep pair.2.rep pair.1.rep_nonzero pair.2.rep_nonzero

/-! ## Homogeneous image equations -/

/-- [definition] The addressed `2 × 2` minor of a tensor-coordinate occurrence.  Its four
coordinates retain the two selected rows and columns rather than collapsing rank one to a scalar
dimension count. -/
def tensorPairMinor {I J : Type*} (tensor : I × J → ℂ)
    (firstRow secondRow : I) (firstColumn secondColumn : J) : ℂ :=
  tensor (firstRow, firstColumn) * tensor (secondRow, secondColumn) -
    tensor (firstRow, secondColumn) * tensor (secondRow, firstColumn)

/-- [proved-derived; formal-checked] Every addressed rank-one tensor has every homogeneous
`2 × 2` minor equal to zero. -/
theorem tensorPairMinor_tensorPairVector {I J : Type*}
    (left : I → ℂ) (right : J → ℂ)
    (firstRow secondRow : I) (firstColumn secondColumn : J) :
    tensorPairMinor (tensorPairVector left right)
      firstRow secondRow firstColumn secondColumn = 0 := by
  simp only [tensorPairMinor, tensorPairVector]
  ring

/-- [definition] A projective tensor point lies on the homogeneous rank-one minor locus when it
has a nonzero representative on which every addressed `2 × 2` minor vanishes.  The representative
and its reconstruction witness are retained explicitly. -/
def OnTensorPairMinorLocus {I J : Type*} (point : TensorPairProjectiveSpace I J) : Prop :=
  ∃ (tensor : I × J → ℂ) (htensor : tensor ≠ 0),
    point = Projectivization.mk ℂ tensor htensor ∧
      ∀ firstRow secondRow firstColumn secondColumn,
        tensorPairMinor tensor firstRow secondRow firstColumn secondColumn = 0

/-- [proved-derived; formal-checked] The generic Segre passage lands in the complete addressed
rank-one-minor locus.  This is the forward image equation; the converse factorization of an
arbitrary nonzero minor-zero representative is a separate theorem obligation. -/
theorem tensorPairSegre_onTensorPairMinorLocus {I J : Type*}
    (pair : Projectivization ℂ (I → ℂ) × Projectivization ℂ (J → ℂ)) :
    OnTensorPairMinorLocus (tensorPairSegre pair) := by
  refine ⟨tensorPairVector pair.1.rep pair.2.rep,
    tensorPairVector_ne_zero pair.1.rep_nonzero pair.2.rep_nonzero, rfl, ?_⟩
  exact tensorPairMinor_tensorPairVector pair.1.rep pair.2.rep

/-- [proved-derived; formal-checked] A nonzero tensor whose complete addressed `2 × 2` minor
population vanishes has an exact rank-one factorization.  The construction retains a nonzero pivot
coordinate: one factor is its column and the other is the corresponding normalized row. -/
theorem exists_tensorPair_of_minors_zero {I J : Type*} {tensor : I × J → ℂ}
    (htensor : tensor ≠ 0)
    (hminors : ∀ firstRow secondRow firstColumn secondColumn,
      tensorPairMinor tensor firstRow secondRow firstColumn secondColumn = 0) :
    ∃ (left : I → ℂ) (right : J → ℂ),
      left ≠ 0 ∧ right ≠ 0 ∧ tensorPairVector left right = tensor := by
  obtain ⟨pivot, hpivot⟩ := exists_coordinate_ne_zero htensor
  let left : I → ℂ := fun row => tensor (row, pivot.2)
  let right : J → ℂ := fun column => tensor (pivot.1, column) / tensor pivot
  have hleft : left ≠ 0 := by
    intro hzero
    have hatPivot := congrFun hzero pivot.1
    simp [left] at hatPivot
    exact hpivot hatPivot
  have hright : right ≠ 0 := by
    intro hzero
    have hatPivot := congrFun hzero pivot.2
    simp [right, hpivot] at hatPivot
  refine ⟨left, right, hleft, hright, ?_⟩
  funext coordinate
  have hminor := hminors coordinate.1 pivot.1 coordinate.2 pivot.2
  change tensor coordinate * tensor pivot -
      tensor (coordinate.1, pivot.2) * tensor (pivot.1, coordinate.2) = 0 at hminor
  have hcross : tensor coordinate * tensor pivot =
      tensor (coordinate.1, pivot.2) * tensor (pivot.1, coordinate.2) :=
    sub_eq_zero.mp hminor
  change left coordinate.1 * right coordinate.2 = tensor coordinate
  dsimp only [left, right]
  calc
    tensor (coordinate.1, pivot.2) *
          (tensor (pivot.1, coordinate.2) / tensor pivot) =
        (tensor (coordinate.1, pivot.2) * tensor (pivot.1, coordinate.2)) /
          tensor pivot := by ring
    _ = (tensor coordinate * tensor pivot) / tensor pivot := by rw [← hcross]
    _ = tensor coordinate := by field_simp [hpivot]

/-- [proved-derived; formal-checked] Applying the generic Segre map to projective classes made
from explicit representatives returns the projective class of their explicit tensor product. -/
theorem tensorPairSegre_mk_eq_tensorPairPoint {I J : Type*}
    (left : I → ℂ) (right : J → ℂ) (hleft : left ≠ 0) (hright : right ≠ 0) :
    tensorPairSegre
        (Projectivization.mk ℂ left hleft, Projectivization.mk ℂ right hright) =
      tensorPairPoint left right hleft hright := by
  obtain ⟨leftScale, hleftScale⟩ :=
    Projectivization.exists_smul_eq_mk_rep ℂ left hleft
  obtain ⟨rightScale, hrightScale⟩ :=
    Projectivization.exists_smul_eq_mk_rep ℂ right hright
  unfold tensorPairSegre tensorPairPoint
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
    ⟨(leftScale : ℂ) * (rightScale : ℂ), ?_⟩
  funext coordinate
  have hleftCoordinate := congrFun hleftScale coordinate.1
  have hrightCoordinate := congrFun hrightScale coordinate.2
  change (leftScale : ℂ) * left coordinate.1 =
    (Projectivization.mk ℂ left hleft).rep coordinate.1 at hleftCoordinate
  change (rightScale : ℂ) * right coordinate.2 =
    (Projectivization.mk ℂ right hright).rep coordinate.2 at hrightCoordinate
  change ((leftScale : ℂ) * (rightScale : ℂ)) *
      (left coordinate.1 * right coordinate.2) =
    (Projectivization.mk ℂ left hleft).rep coordinate.1 *
      (Projectivization.mk ℂ right hright).rep coordinate.2
  rw [← hleftCoordinate, ← hrightCoordinate]
  ring

/-- [proved-derived; formal-checked] The generic projective Segre image is exactly the common
zero locus of all addressed homogeneous rank-one minors. -/
theorem tensorPairSegre_range_eq_minorLocus {I J : Type*} :
    Set.range (tensorPairSegre (I := I) (J := J)) =
      { point | OnTensorPairMinorLocus point } := by
  ext point
  constructor
  · rintro ⟨pair, rfl⟩
    exact tensorPairSegre_onTensorPairMinorLocus pair
  · rintro ⟨tensor, htensor, hpoint, hminors⟩
    obtain ⟨left, right, hleft, hright, hfactor⟩ :=
      exists_tensorPair_of_minors_zero htensor hminors
    refine ⟨(Projectivization.mk ℂ left hleft,
      Projectivization.mk ℂ right hright), ?_⟩
    rw [tensorPairSegre_mk_eq_tensorPairPoint, hpoint]
    unfold tensorPairPoint
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨1, ?_⟩
    simpa using hfactor.symm

theorem recover_left_from_scaled_tensor {I J : Type*}
    {left : I → ℂ} {right : J → ℂ} {left' : I → ℂ} {right' : J → ℂ}
    (hleft : left ≠ 0) (hright : right ≠ 0) (scale : ℂ)
    (hscaled : scale • tensorPairVector left' right' =
      tensorPairVector left right) :
    ∃ coefficient : ℂ, coefficient • left' = left := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  have hcoordinate := congrFun hscaled (leftIndex, rightIndex)
  change scale * (left' leftIndex * right' rightIndex) =
    left leftIndex * right rightIndex at hcoordinate
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

theorem recover_right_from_scaled_tensor {I J : Type*}
    {left : I → ℂ} {right : J → ℂ} {left' : I → ℂ} {right' : J → ℂ}
    (hleft : left ≠ 0) (hright : right ≠ 0) (scale : ℂ)
    (hscaled : scale • tensorPairVector left' right' =
      tensorPairVector left right) :
    ∃ coefficient : ℂ, coefficient • right' = right := by
  obtain ⟨leftIndex, hleftIndex⟩ := exists_coordinate_ne_zero hleft
  obtain ⟨rightIndex, hrightIndex⟩ := exists_coordinate_ne_zero hright
  have hcoordinate := congrFun hscaled (leftIndex, rightIndex)
  change scale * (left' leftIndex * right' rightIndex) =
    left leftIndex * right rightIndex at hcoordinate
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

/-- [proved-derived; formal-checked] Equality of two rank-one projective tensor points
reconstructs equality of both source projective factors. -/
theorem tensorPairSegre_injective {I J : Type*} :
    Function.Injective (tensorPairSegre (I := I) (J := J)) := by
  rintro ⟨left, right⟩ ⟨left', right'⟩ hequal
  change tensorPairPoint left.rep right.rep left.rep_nonzero right.rep_nonzero =
    tensorPairPoint left'.rep right'.rep left'.rep_nonzero right'.rep_nonzero at hequal
  obtain ⟨scale, hscaled⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (tensorPairVector left.rep right.rep)
      (tensorPairVector left'.rep right'.rep)
      (tensorPairVector_ne_zero left.rep_nonzero right.rep_nonzero)
      (tensorPairVector_ne_zero left'.rep_nonzero right'.rep_nonzero)).1 hequal
  obtain ⟨leftScale, hleftScale⟩ := recover_left_from_scaled_tensor
    left.rep_nonzero right.rep_nonzero scale hscaled
  obtain ⟨rightScale, hrightScale⟩ := recover_right_from_scaled_tensor
    left.rep_nonzero right.rep_nonzero scale hscaled
  apply Prod.ext
  · rw [← Projectivization.mk_rep left, ← Projectivization.mk_rep left']
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ left.rep_nonzero left'.rep_nonzero).2
      ⟨leftScale, hleftScale⟩
  · rw [← Projectivization.mk_rep right, ← Projectivization.mk_rep right']
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ right.rep_nonzero right'.rep_nonzero).2
      ⟨rightScale, hrightScale⟩

/-! ## Recursive finite power and its binary-word coordinate chart -/

/-- [definition] The nested coordinate population of an ordered finite tensor power. -/
def PowerSegreCoordinate : ℕ → Type
  | 0 => PUnit
  | n + 1 => PowerSegreCoordinate n × Fin 2

/-- [proved-derived; formal-checked] Nested tensor coordinates are exactly binary factor words.
The equivalence retains the order and address of every factor. -/
def powerSegreCoordinateEquiv : ∀ factorCount,
    PowerSegreCoordinate factorCount ≃ (Fin factorCount → Fin 2)
  | 0 =>
      { toFun := fun _ index => Fin.elim0 index
        invFun := fun _ => PUnit.unit
        left_inv := by intro coordinate; cases coordinate; rfl
        right_inv := by intro word; funext index; exact Fin.elim0 index }
  | n + 1 =>
      { toFun := fun coordinate =>
          Fin.lastCases coordinate.2 (powerSegreCoordinateEquiv n coordinate.1)
        invFun := fun word =>
          ((powerSegreCoordinateEquiv n).symm
              (fun index => word index.castSucc),
            word (Fin.last n))
        left_inv := by
          intro coordinate
          apply Prod.ext
          · apply (powerSegreCoordinateEquiv n).injective
            funext index
            simp
          · simp
        right_inv := by
          intro word
          funext index
          cases index using Fin.lastCases <;> simp }

abbrev PowerSegreProjectiveSpace (factorCount : ℕ) :=
  Projectivization ℂ (PowerSegreCoordinate factorCount → ℂ)

def powerSegreZeroVector : PowerSegreCoordinate 0 → ℂ := fun _ => 1

theorem powerSegreZeroVector_ne_zero : powerSegreZeroVector ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero PUnit.unit
  change (1 : ℂ) = 0 at hcoordinate
  exact one_ne_zero hcoordinate

def powerSegreZeroPoint : PowerSegreProjectiveSpace 0 :=
  Projectivization.mk ℂ powerSegreZeroVector powerSegreZeroVector_ne_zero

/-- [definition] The finite Segre tensor map, built by serial composition of the one generic
projective tensor-pair passage. -/
def powerSegre : (factorCount : ℕ) →
    ProjectiveLinePower factorCount → PowerSegreProjectiveSpace factorCount
  | 0, _ => powerSegreZeroPoint
  | n + 1, point =>
      tensorPairSegre
        (powerSegre n (fun index => point index.castSucc), point (Fin.last n))

/-- [definition] The complete homogeneous equation population on an actual finite-power tensor
representative.  At a successor it requires every minor across the final binary cut to vanish and
recursively imposes the earlier-cut equations on each addressed final-coordinate section.  It
contains equations only; no factorization or range witness is stored in this predicate. -/
def PowerTensorMinorEquations : (factorCount : ℕ) →
    (PowerSegreCoordinate factorCount → ℂ) → Prop
  | 0, _ => True
  | n + 1, tensor =>
      (∀ firstRow secondRow firstColumn secondColumn,
        tensorPairMinor tensor firstRow secondRow firstColumn secondColumn = 0) ∧
      ∀ finalCoordinate,
        PowerTensorMinorEquations n (fun priorCoordinate =>
          tensor (priorCoordinate, finalCoordinate))

/-- [proved-derived; formal-checked] The complete recursive minor equation population is
homogeneous: multiplying a representative by any complex scale preserves every equation. -/
theorem powerTensorMinorEquations_smul : ∀ factorCount
    {tensor : PowerSegreCoordinate factorCount → ℂ},
    PowerTensorMinorEquations factorCount tensor →
      ∀ scale : ℂ, PowerTensorMinorEquations factorCount (scale • tensor)
  | 0, tensor, _, scale => by
      trivial
  | n + 1, tensor, hequations, scale => by
      refine ⟨?_, ?_⟩
      · intro firstRow secondRow firstColumn secondColumn
        have hminor := hequations.1 firstRow secondRow firstColumn secondColumn
        change (scale * tensor (firstRow, firstColumn)) *
              (scale * tensor (secondRow, secondColumn)) -
            (scale * tensor (firstRow, secondColumn)) *
              (scale * tensor (secondRow, firstColumn)) = 0
        calc
          (scale * tensor (firstRow, firstColumn)) *
                (scale * tensor (secondRow, secondColumn)) -
              (scale * tensor (firstRow, secondColumn)) *
                (scale * tensor (secondRow, firstColumn)) =
              scale ^ 2 * tensorPairMinor tensor
                firstRow secondRow firstColumn secondColumn := by
                  simp only [tensorPairMinor]
                  ring
          _ = 0 := by rw [hminor, mul_zero]
      · intro finalCoordinate
        have hsection := powerTensorMinorEquations_smul n
          (hequations.2 finalCoordinate) scale
        change PowerTensorMinorEquations n
          (fun priorCoordinate => scale * tensor (priorCoordinate, finalCoordinate))
        change PowerTensorMinorEquations n
          (fun priorCoordinate => scale * tensor (priorCoordinate, finalCoordinate)) at hsection
        exact hsection

/-- [definition] An explicit homogeneous tensor representative generated by an ordered family of
projective-line occurrences. -/
def powerSegreSourceVector : (factorCount : ℕ) →
    ProjectiveLinePower factorCount → PowerSegreCoordinate factorCount → ℂ
  | 0, _ => powerSegreZeroVector
  | n + 1, point =>
      tensorPairVector
        (powerSegreSourceVector n (fun index => point index.castSucc))
        (point (Fin.last n)).rep

theorem powerSegreSourceVector_ne_zero : ∀ factorCount
    (point : ProjectiveLinePower factorCount),
    powerSegreSourceVector factorCount point ≠ 0
  | 0, _ => powerSegreZeroVector_ne_zero
  | n + 1, point => tensorPairVector_ne_zero
      (powerSegreSourceVector_ne_zero n (fun index => point index.castSucc))
      (point (Fin.last n)).rep_nonzero

/-- [proved-derived; formal-checked] The explicit source tensor satisfies every recursive binary
minor equation. -/
theorem powerSegreSourceVector_minorEquations : ∀ factorCount
    (point : ProjectiveLinePower factorCount),
    PowerTensorMinorEquations factorCount (powerSegreSourceVector factorCount point)
  | 0, point => by
      trivial
  | n + 1, point => by
      refine ⟨tensorPairMinor_tensorPairVector _ _, ?_⟩
      intro finalCoordinate
      have hscaled := powerTensorMinorEquations_smul n
        (powerSegreSourceVector_minorEquations n (fun index => point index.castSucc))
        ((point (Fin.last n)).rep finalCoordinate)
      convert hscaled using 1
      funext priorCoordinate
      change powerSegreSourceVector n (fun index => point index.castSucc) priorCoordinate *
          (point (Fin.last n)).rep finalCoordinate =
        (point (Fin.last n)).rep finalCoordinate *
          powerSegreSourceVector n (fun index => point index.castSucc) priorCoordinate
      ring

/-- [proved-derived; formal-checked] The recursive Segre map is the projective class of its
explicit ordered source tensor. -/
theorem powerSegre_eq_mk_sourceVector : ∀ factorCount
    (point : ProjectiveLinePower factorCount),
    powerSegre factorCount point =
      Projectivization.mk ℂ (powerSegreSourceVector factorCount point)
        (powerSegreSourceVector_ne_zero factorCount point)
  | 0, point => by
      rfl
  | n + 1, point => by
      let priorSource : ProjectiveLinePower n := fun index => point index.castSucc
      let last := point (Fin.last n)
      have hprior := powerSegre_eq_mk_sourceVector n priorSource
      have hlast : last = Projectivization.mk ℂ last.rep last.rep_nonzero :=
        (Projectivization.mk_rep last).symm
      have hpair : (powerSegre n priorSource, last) =
          (Projectivization.mk ℂ (powerSegreSourceVector n priorSource)
              (powerSegreSourceVector_ne_zero n priorSource),
            Projectivization.mk ℂ last.rep last.rep_nonzero) :=
        Prod.ext hprior hlast
      change tensorPairSegre (powerSegre n priorSource, last) =
        Projectivization.mk ℂ
          (tensorPairVector (powerSegreSourceVector n priorSource) last.rep)
          (tensorPairVector_ne_zero
            (powerSegreSourceVector_ne_zero n priorSource) last.rep_nonzero)
      rw [hpair, tensorPairSegre_mk_eq_tensorPairPoint]
      rfl

/-- [definition] The genuine equation-only projective locus.  It retains a nonzero homogeneous
representative and the complete recursive minor ledger, but no Segre preimage. -/
def OnPowerSegreMinorLocus (factorCount : ℕ)
    (point : PowerSegreProjectiveSpace factorCount) : Prop :=
  ∃ (tensor : PowerSegreCoordinate factorCount → ℂ) (htensor : tensor ≠ 0),
    point = Projectivization.mk ℂ tensor htensor ∧
      PowerTensorMinorEquations factorCount tensor

/-- [proved-derived; formal-checked] Every finite Segre power lands in the equation-only recursive
minor locus. -/
theorem powerSegre_onPowerSegreMinorLocus (factorCount : ℕ)
    (point : ProjectiveLinePower factorCount) :
    OnPowerSegreMinorLocus factorCount (powerSegre factorCount point) := by
  refine ⟨powerSegreSourceVector factorCount point,
    powerSegreSourceVector_ne_zero factorCount point, ?_,
    powerSegreSourceVector_minorEquations factorCount point⟩
  exact powerSegre_eq_mk_sourceVector factorCount point

/-- [proved-derived; formal-checked] Every point satisfying only the complete recursive
homogeneous minor equations reconstructs a complete ordered projective-line factor family. -/
theorem exists_powerSegre_preimage_of_minorLocus : ∀ factorCount
    (point : PowerSegreProjectiveSpace factorCount),
    OnPowerSegreMinorLocus factorCount point →
      ∃ source : ProjectiveLinePower factorCount,
        powerSegre factorCount source = point
  | 0, point, hpoint => by
      obtain ⟨tensor, htensor, hpoint, _⟩ := hpoint
      obtain ⟨hpivot, hpivotNonzero⟩ := exists_coordinate_ne_zero htensor
      refine ⟨fun index => Fin.elim0 index, ?_⟩
      rw [hpoint]
      change Projectivization.mk ℂ powerSegreZeroVector powerSegreZeroVector_ne_zero =
        Projectivization.mk ℂ tensor htensor
      refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
        ⟨(tensor hpivot)⁻¹, ?_⟩
      funext coordinate
      cases coordinate
      cases hpivot
      change (tensor PUnit.unit)⁻¹ * tensor PUnit.unit = 1
      exact inv_mul_cancel₀ hpivotNonzero
  | n + 1, point, hpoint => by
      obtain ⟨tensor, htensor, hpoint, hequations⟩ := hpoint
      obtain ⟨left, right, hleft, hright, hfactor⟩ :=
        exists_tensorPair_of_minors_zero htensor hequations.1
      obtain ⟨finalCoordinate, hfinalCoordinate⟩ := exists_coordinate_ne_zero hright
      have hsection : PowerTensorMinorEquations n
          (fun priorCoordinate => tensor (priorCoordinate, finalCoordinate)) :=
        hequations.2 finalCoordinate
      have hsectionFactor :
          (fun priorCoordinate => tensor (priorCoordinate, finalCoordinate)) =
            (right finalCoordinate) • left := by
        funext priorCoordinate
        have hatCoordinate := congrFun hfactor (priorCoordinate, finalCoordinate)
        change left priorCoordinate * right finalCoordinate =
          tensor (priorCoordinate, finalCoordinate) at hatCoordinate
        change tensor (priorCoordinate, finalCoordinate) =
          right finalCoordinate * left priorCoordinate
        simpa [mul_comm] using hatCoordinate.symm
      rw [hsectionFactor] at hsection
      have hleftEquations := powerTensorMinorEquations_smul n hsection
        (right finalCoordinate)⁻¹
      have hleftEquations' : PowerTensorMinorEquations n left := by
        simpa [smul_smul, hfinalCoordinate] using hleftEquations
      let priorPoint : PowerSegreProjectiveSpace n :=
        Projectivization.mk ℂ left hleft
      obtain ⟨priorSource, hpriorSource⟩ :=
        exists_powerSegre_preimage_of_minorLocus n priorPoint
          ⟨left, hleft, rfl, hleftEquations'⟩
      let lastPoint : Projectivization ℂ (Fin 2 → ℂ) :=
        Projectivization.mk ℂ right hright
      let source : ProjectiveLinePower (n + 1) :=
        Fin.lastCases lastPoint priorSource
      refine ⟨source, ?_⟩
      change tensorPairSegre
        (powerSegre n (fun index => source index.castSucc), source (Fin.last n)) = point
      have hsourcePrior : (fun index : Fin n => source index.castSucc) = priorSource := by
        funext index
        simp [source]
      have hsourceLast : source (Fin.last n) = lastPoint := by
        simp [source]
      let tensorAtCut : PowerSegreCoordinate n × Fin 2 → ℂ :=
        fun coordinate => tensor coordinate
      have htensorAtCut : tensorAtCut ≠ 0 := by
        intro hzero
        apply htensor
        funext coordinate
        exact congrFun hzero coordinate
      have hfactorAtCut : tensorPairVector left right = tensorAtCut := by
        funext coordinate
        exact congrFun hfactor coordinate
      have hpointAtCut : point =
          Projectivization.mk ℂ tensorAtCut htensorAtCut := by
        rw [hpoint]
        refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨1, ?_⟩
        funext coordinate
        change (1 : ℂ) * tensor coordinate = tensor coordinate
        exact one_mul _
      rw [hsourcePrior, hsourceLast, hpriorSource]
      change tensorPairSegre
          (Projectivization.mk ℂ left hleft, Projectivization.mk ℂ right hright) = point
      rw [tensorPairSegre_mk_eq_tensorPairPoint, hpointAtCut]
      unfold tensorPairPoint
      refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨1, ?_⟩
      funext coordinate
      change (1 : ℂ) * tensorAtCut coordinate = tensorPairVector left right coordinate
      rw [one_mul]
      exact (congrFun hfactorAtCut coordinate).symm

/-- [proved-derived; formal-checked] For every finite factor count, the global Segre range is
exactly the common-zero population of the recursive homogeneous minor equations at every binary
factor cut.  Factor reconstruction is derived from those equations rather than stored in the
locus. -/
theorem powerSegre_range_eq_recursiveMinorLocus (factorCount : ℕ) :
    Set.range (powerSegre factorCount) =
      { point | OnPowerSegreMinorLocus factorCount point } := by
  ext point
  constructor
  · rintro ⟨source, rfl⟩
    exact powerSegre_onPowerSegreMinorLocus factorCount source
  · intro hpoint
    exact exists_powerSegre_preimage_of_minorLocus factorCount point hpoint

/-- [proved-derived; formal-checked] The finite Segre tensor map is injective at every factor
count.  The proof recursively reconstructs the prefix power and the final addressed factor. -/
theorem powerSegre_injective : ∀ factorCount,
    Function.Injective (powerSegre factorCount)
  | 0 => by
      intro left right _
      funext index
      exact Fin.elim0 index
  | n + 1 => by
      intro left right hequal
      change tensorPairSegre
          (powerSegre n (fun index => left index.castSucc), left (Fin.last n)) =
        tensorPairSegre
          (powerSegre n (fun index => right index.castSucc), right (Fin.last n)) at hequal
      have pairEqual := tensorPairSegre_injective hequal
      have prefixEqual :
          (fun index : Fin n => left index.castSucc) =
            (fun index : Fin n => right index.castSucc) :=
        powerSegre_injective n (congrArg Prod.fst pairEqual)
      have lastEqual : left (Fin.last n) = right (Fin.last n) :=
        congrArg Prod.snd pairEqual
      funext index
      cases index using Fin.lastCases with
      | last => exact lastEqual
      | cast previous => exact congrFun prefixEqual previous

/-- [proved-derived; formal-checked] The global projective power is equivalent to the complete
image of its injective finite Segre tensor realization. -/
def powerSegreImageEquiv (factorCount : ℕ) :
    ProjectiveLinePower factorCount ≃
      { point : PowerSegreProjectiveSpace factorCount //
        point ∈ Set.range (powerSegre factorCount) } :=
  Equiv.ofInjective (powerSegre factorCount) (powerSegre_injective factorCount)

section Audit

#print axioms tensorPairVector_ne_zero
#print axioms tensorPairMinor_tensorPairVector
#print axioms tensorPairSegre_onTensorPairMinorLocus
#print axioms exists_tensorPair_of_minors_zero
#print axioms tensorPairSegre_mk_eq_tensorPairPoint
#print axioms tensorPairSegre_range_eq_minorLocus
#print axioms tensorPairSegre_injective
#print axioms powerSegreCoordinateEquiv
#print axioms powerTensorMinorEquations_smul
#print axioms powerSegreSourceVector_minorEquations
#print axioms powerSegre_eq_mk_sourceVector
#print axioms powerSegre_onPowerSegreMinorLocus
#print axioms exists_powerSegre_preimage_of_minorLocus
#print axioms powerSegre_range_eq_recursiveMinorLocus
#print axioms powerSegre_injective
#print axioms powerSegreImageEquiv

end Audit

end Soma.Holonics.Millennium.HodgePowerSegre
