import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Millennium.NavierStokesVorticity

/-!
# Addressed alternating geometry from Swing to the Lamb interaction

The planar triangle and the three-dimensional cross interaction are two typed projections of one
alternating construction.  A triangle retains its three addressed boundary edges; their additive
sum closes, while the ordered pairing of two rays returns its hand.  In three dimensions the
exterior product first returns an antisymmetric bivector, and a separately declared positive
orientation then supplies the Hodge-dual chart.  Their composite is the existing cross product.

The final comparison cell keeps both routes: exchange the incoming rays before the cross
interaction, or apply the zero-anchored Swing after it.  Equality of their returned targets is a
theorem, not a constructor field.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicAlternatingGeometry

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.Swing
open Soma.Holonics.Millennium.SwingBridges
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## The addressed planar boundary and its surviving hand -/

/-- The three oriented boundary edges of the addressed triangle `(a,b,c)`. -/
def triangleBoundaryEdges (a b c : Site) : Fin 3 → Site :=
  ![b - a, c - b, a - c]

/-- The triangle's edge population closes at its additive boundary. -/
theorem triangleBoundaryEdges_sum_eq_zero (a b c : Site) :
    ∑ i, triangleBoundaryEdges a b c i = 0 := by
  simp [triangleBoundaryEdges, Fin.sum_univ_succ]

/-- The hand receiver pairs the first boundary edge with the composite of the first two. -/
def triangleBoundaryHand (a b c : Site) : ℤ :=
  WindingLedger.cross (triangleBoundaryEdges a b c 0)
    (triangleBoundaryEdges a b c 0 + triangleBoundaryEdges a b c 1)

/-- Closing the edge population does not erase its ordered alternating hand. -/
theorem triangleBoundaryHand_eq_orientedSpan (a b c : Site) :
    triangleBoundaryHand a b c = orientedSpan a b c := by
  rcases orientedSpan_eq_paying_eq_winding a b c with ⟨span, winding⟩
  rw [span, winding]
  simp [triangleBoundaryHand, triangleBoundaryEdges]

/-- The addressed graph retains the complete triangle occurrence before reading its hand. -/
def triangleHandPassage : AddressedPassage (Site × Site × Site) ℤ :=
  AddressedPassage.graph fun triangle =>
    triangleBoundaryHand triangle.1 triangle.2.1 triangle.2.2

/-- The occurrence carried by the hand passage is the addressed triangle itself. -/
theorem triangleHandPassage_retains_occurrence (a b c : Site) :
    Nonempty (triangleHandPassage.Fibre (a, b, c) (orientedSpan a b c)) := by
  exact ⟨⟨(a, b, c), rfl, triangleBoundaryHand_eq_orientedSpan a b c⟩⟩

/-! ## Exterior product, chosen orientation, and Hodge dual in three dimensions -/

/-- Bivectors are retained in the ambient two-index chart; alternation is proved for constructions. -/
abbrev Bivector3 := Matrix3

/-- The exterior product before an orientation or Hodge receiver is selected. -/
def exteriorProduct (u v : Space) : Bivector3 :=
  fun i j => u i * v j - u j * v i

theorem exteriorProduct_swap (u v : Space) :
    exteriorProduct v u = -exteriorProduct u v := by
  ext i j
  simp [exteriorProduct]
  ring

theorem exteriorProduct_self (u : Space) : exteriorProduct u u = 0 := by
  ext i j
  simp [exteriorProduct]
  ring

/-- The Hodge receiver determined by the standard positive orientation `(0,1,2)`. -/
def positiveHodgeDual (bivector : Bivector3) : Space :=
  vectorOfCoordinates ![bivector 1 2, bivector 2 0, bivector 0 1]

/-- The existing cross interaction factors through exterior product and oriented Hodge dual. -/
theorem cross_eq_positiveHodgeDual_exteriorProduct (u v : Space) :
    cross u v = positiveHodgeDual (exteriorProduct u v) := by
  ext i
  fin_cases i <;> simp [cross, positiveHodgeDual, exteriorProduct, crossProduct]

/-- The antisymmetric face of a Jacobian, oriented to match the deposited curl convention. -/
def jacobianExteriorFace (J : Matrix3) : Bivector3 :=
  fun i j => J j i - J i j

/-- Curl is the positive Hodge receiver of the Jacobian's exterior face. -/
theorem curlFromJacobian_eq_positiveHodgeDual_exteriorFace (J : Matrix3) :
    curlFromJacobian J = positiveHodgeDual (jacobianExteriorFace J) := by
  ext i
  fin_cases i <;> simp [curlFromJacobian, positiveHodgeDual, jacobianExteriorFace]

/-- The Lamb interaction now exposes its exterior-product and orientation factors. -/
theorem lambVector_eq_positiveHodgeDual_exteriorProduct (J : Matrix3) (u : Space) :
    lambVectorFromJacobian J u =
      positiveHodgeDual (exteriorProduct (curlFromJacobian J) u) := by
  exact cross_eq_positiveHodgeDual_exteriorProduct _ _

/-- The local Lamb identity rebased through the exterior/Hodge factorization. -/
theorem lambIdentity_through_exteriorHodge (J : Matrix3) (u : Space) :
    matrixAction J u = transposeAction J u +
      positiveHodgeDual (exteriorProduct (curlFromJacobian J) u) := by
  rw [← lambVector_eq_positiveHodgeDual_exteriorProduct]
  exact lambIdentity J u

/-! ## Input exchange as an addressed Swing comparison -/

/-- Exchange the two incoming rays before taking their cross interaction. -/
def exchangedCrossPassage : AddressedPassage (Space × Space) Space :=
  AddressedPassage.graph fun rays => cross rays.2 rays.1

/-- Take the cross interaction first, then Swing its returned vector about zero. -/
def swungCrossPassage : AddressedPassage (Space × Space) Space :=
  AddressedPassage.comp
    (AddressedPassage.graph (swing 0))
    (AddressedPassage.graph fun rays => cross rays.1 rays.2)

/-- Both route occurrences remain addressed at the same ordered incoming pair. -/
def crossExchangeSwingCell (u v : Space) :
    AddressedPassage.ComparisonCell exchangedCrossPassage swungCrossPassage where
  left := (u, v)
  right := ⟨(u, v), cross u v, rfl⟩
  source_exact := rfl

/-- Exchanging rays and swinging the returned cross vector are the same target route. -/
theorem crossExchangeSwingCell_commutes (u v : Space) :
    (crossExchangeSwingCell u v).Commutes := by
  exact cross_swap_is_zeroAnchoredSwing u v

/-- Both routes retain their own occurrence even after their returned vector agrees. -/
theorem crossExchangeSwingCell_retains_both_occurrences (u v : Space) :
    (crossExchangeSwingCell u v).left = (u, v) ∧
      (crossExchangeSwingCell u v).right.left = (u, v) := by
  exact ⟨rfl, rfl⟩

end Soma.Holonics.Millennium.HolonicAlternatingGeometry

section Audit
open Soma.Holonics.Millennium.HolonicAlternatingGeometry
#print axioms triangleBoundaryEdges_sum_eq_zero
#print axioms triangleBoundaryHand_eq_orientedSpan
#print axioms triangleHandPassage_retains_occurrence
#print axioms exteriorProduct_swap
#print axioms cross_eq_positiveHodgeDual_exteriorProduct
#print axioms curlFromJacobian_eq_positiveHodgeDual_exteriorFace
#print axioms lambIdentity_through_exteriorHodge
#print axioms crossExchangeSwingCell_commutes
end Audit
