import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Millennium.HolonicInteractionExterior
import ElementaryHolonics.Millennium.HolonicRankFourInteractionPlanes

/-!
# One four-cycle base, six interaction faces, and four dependent force sectors

**[proved-derived]** This file closes the exact kinematic part of the proposed four-force
unification carrier.  Two signed rank-four cycle populations meet through their alternating
product

`(x ∧ y)ᵢⱼ = xᵢ yⱼ - xⱼ yᵢ`,

which returns exactly six addressed plane coefficients.  The construction is alternating and is
natural under every integral rank-four transport through the already-defined exterior-square
action.  This is the rigorous `4 → 6` swing/interaction passage.

The four force names are then installed as a *dependent* family over that common cellular base.
Every sector owns its own internal fibre and base-dependent edge connection.  Its returned face
curvature is the ordered holonomy around the same addressed square face.  Consequently the base
directions and faces are shared while electromagnetic, weak, strong, and frame/gravity states are
not coerced into one untyped tensor.

**[open]** Physical `U(1)`, `SU(2)ₗ × U(1)ᵧ` with Higgs, `SU(3)`, and frame/Spin
realizations still owe their respective representation, action, constitutive/Hodge, source,
continuum, and calibration passages.  This file supplies the common incidence/holonomy type on
which those distinct instances can now be built.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicFourForceSectorCarrier

open Soma.Holonics
open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Millennium.HolonicComposition
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicInteractionExterior
open Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes

/-! ## The six addressed plane coordinates -/

/-- The existing plane names and the existing exterior-square coordinate order are exactly the
same six-element carrier: `01, 02, 03, 12, 13, 23`. -/
def interactionPlaneEquivFinSix : InteractionPlane ≃ Fin 6 where
  toFun
    | .gamma_u => 0
    | .gamma_w => 1
    | .gamma_delta => 2
    | .u_w => 3
    | .u_delta => 4
    | .w_delta => 5
  invFun index :=
    match index with
    | 0 => .gamma_u
    | 1 => .gamma_w
    | 2 => .gamma_delta
    | 3 => .u_w
    | 4 => .u_delta
    | 5 => .w_delta
  left_inv plane := by cases plane <;> rfl
  right_inv index := by fin_cases index <;> rfl

theorem interactionPlaneEquivFinSix_first (plane : InteractionPlane) :
    bladeFirst (interactionPlaneEquivFinSix plane) = plane.directions.1 := by
  cases plane <;> rfl

theorem interactionPlaneEquivFinSix_second (plane : InteractionPlane) :
    bladeSecond (interactionPlaneEquivFinSix plane) = plane.directions.2 := by
  cases plane <;> rfl

/-- The alternating interaction of two signed cycle populations. -/
def cycleWedge (left right : Lattice) : InteractionPlane → ℤ :=
  fun plane ↦
    left plane.directions.1 * right plane.directions.2 -
      left plane.directions.2 * right plane.directions.1

theorem cycleWedge_swap (left right : Lattice) :
    cycleWedge right left = -cycleWedge left right := by
  funext plane
  simp [cycleWedge]
  ring

theorem cycleWedge_self (cycle : Lattice) : cycleWedge cycle cycle = 0 := by
  funext plane
  change cycle plane.directions.1 * cycle plane.directions.2 -
      cycle plane.directions.2 * cycle plane.directions.1 = 0
  ring

theorem cycleWedge_basis (plane : InteractionPlane) :
    cycleWedge (basisDirection plane.directions.1)
        (basisDirection plane.directions.2) plane = 1 := by
  cases plane <;> decide

/-- The same wedge in the coordinate order consumed by `exteriorSquareAction`. -/
def cycleWedgeCoordinates (left right : Lattice) : FluxPlane :=
  fun index ↦ cycleWedge left right (interactionPlaneEquivFinSix.symm index)

/-- The complete naturality square: transport both signed cycle populations and then interact, or
interact first and transport the six-plane result by `Λ²`; the returned coefficients agree. -/
theorem cycleWedge_natural (transport : LatticeEnd) (left right : Lattice) :
    cycleWedgeCoordinates (transport.mulVec left) (transport.mulVec right) =
      (exteriorSquareAction transport).mulVec (cycleWedgeCoordinates left right) := by
  funext plane
  fin_cases plane <;>
    simp [cycleWedgeCoordinates, cycleWedge, interactionPlaneEquivFinSix,
      InteractionPlane.directions, exteriorSquareAction, bladeFirst, bladeSecond,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-! ## Four dependent sectors on the one addressed cellular base -/

inductive ForceSector where
  | electromagnetic
  | weak
  | strong
  | gravity
  deriving DecidableEq, Repr

instance : Fintype ForceSector :=
  Fintype.ofList [.electromagnetic, .weak, .strong, .gravity] <| by
    intro sector
    cases sector <;> simp

theorem forceSector_count : Fintype.card ForceSector = 4 := by decide

/-- One cellular edge is an addressed passage from its initial vertex to its swung vertex. -/
def cellularEdgePassage (grain : ℕ) :
    AddressedPassage (Vertex grain) (Vertex grain) where
  Occurrence := Edge grain
  source := Edge.base
  target edge := stepVertex edge.direction edge.base

/-- Each sector keeps its own internal state type.  A connection is attached to addressed edges,
not merely to four global direction labels, so even an abelian sector may have nonzero local
curvature. -/
structure FourForceCarrier (grain : ℕ) where
  InternalFibre : ForceSector → Type*
  connection : (sector : ForceSector) →
    AddressedConnection (InternalFibre sector) (cellularEdgePassage grain)

abbrev SixPlaneFace (grain : ℕ) := Vertex grain × InteractionPlane

def canonicalFace (address : SixPlaneFace grain) : Face grain where
  first := address.2.directions.1
  second := address.2.directions.2
  first_ne_second := address.2.directions_ne
  base := address.1

/-! ## The two retained routes across one square face -/

/-- Two elementary edge passages composed through their exact middle vertex. -/
abbrev faceRoutePassage (grain : ℕ) :
    AddressedPassage (Vertex grain) (Vertex grain) :=
  AddressedPassage.comp (cellularEdgePassage grain) (cellularEdgePassage grain)

/-- First swing in the first direction, then in the second direction. -/
def forwardFaceRoute (address : SixPlaneFace grain) : (faceRoutePassage grain).Occurrence :=
  let face := canonicalFace address
  ⟨⟨face.first, face.base⟩,
    ⟨face.second, stepVertex face.first face.base⟩,
    rfl⟩

/-- First swing in the second direction, then in the first direction. -/
def alternateFaceRoute (address : SixPlaneFace grain) : (faceRoutePassage grain).Occurrence :=
  let face := canonicalFace address
  ⟨⟨face.second, face.base⟩,
    ⟨face.first, stepVertex face.second face.base⟩,
    rfl⟩

/-- The face retains both route occurrences at their common source. -/
def faceRouteCell (address : SixPlaneFace grain) :
    AddressedPassage.ComparisonCell (faceRoutePassage grain) (faceRoutePassage grain) where
  left := alternateFaceRoute address
  right := forwardFaceRoute address
  source_exact := rfl

/-- The two cellular routes return to the same addressed vertex. -/
theorem faceRouteCell_commutes (address : SixPlaneFace grain) :
    (faceRouteCell address).Commutes := by
  simp only [AddressedPassage.ComparisonCell.Commutes, faceRouteCell,
    AddressedPassage.comp, forwardFaceRoute, alternateFaceRoute,
    canonicalFace]
  exact stepVertex_commute address.2.directions.1 address.2.directions.2 address.1
    address.2.directions_ne

/-- Serial connection on a two-edge route, retaining its joined occurrence. -/
def faceRouteConnection (carrier : FourForceCarrier grain) (sector : ForceSector) :
    AddressedConnection (carrier.InternalFibre sector) (faceRoutePassage grain) :=
  fun joined ↦ joinedConnectionTransport (carrier.connection sector)
    (carrier.connection sector) joined

/-- One sector's two addressed routes and their induced connection transports. -/
def sectorFaceComparison (carrier : FourForceCarrier grain) (sector : ForceSector)
    (address : SixPlaneFace grain) :
    AddressedConnectionComparison (carrier.InternalFibre sector)
      (faceRoutePassage grain) (faceRoutePassage grain) where
  cell := faceRouteCell address
  leftConnection := faceRouteConnection carrier sector
  rightConnection := faceRouteConnection carrier sector

/-- Ordered connection transports around one positively oriented cellular face.  The list is in
operator-composition order: successor before predecessor on each retained route. -/
def sectorFaceWord (carrier : FourForceCarrier grain) (sector : ForceSector)
    (address : SixPlaneFace grain) :
    List (Equiv.Perm (carrier.InternalFibre sector)) :=
  let face := canonicalFace address
  [ carrier.connection sector ⟨face.second, stepVertex face.first face.base⟩,
    carrier.connection sector ⟨face.first, face.base⟩,
    (carrier.connection sector ⟨face.second, face.base⟩)⁻¹,
    (carrier.connection sector
      ⟨face.first, stepVertex face.second face.base⟩)⁻¹ ]

/-- Curvature is returned as the ordered holonomy defect around the addressed face. -/
def returnedCurvature (carrier : FourForceCarrier grain) (sector : ForceSector)
    (address : SixPlaneFace grain) : Equiv.Perm (carrier.InternalFibre sector) :=
  parallelTransport (sectorFaceWord carrier sector address)

/-- The historical face word is exactly the common addressed two-route connection return. -/
theorem returnedCurvature_eq_addressedReturn (carrier : FourForceCarrier grain)
    (sector : ForceSector) (address : SixPlaneFace grain) :
    returnedCurvature carrier sector address =
      (sectorFaceComparison carrier sector address).returnedCurvature := by
  simp [returnedCurvature, sectorFaceWord, sectorFaceComparison,
    AddressedConnectionComparison.returnedCurvature,
    AddressedConnectionComparison.leftTransport,
    AddressedConnectionComparison.rightTransport,
    faceRouteConnection, faceRouteCell, forwardFaceRoute, alternateFaceRoute,
    joinedConnectionTransport, connectionTransport, routeComparisonReturn,
    parallelTransport, mul_assoc]

/-- Sector curvature vanishes exactly when the two complete addressed route transports agree. -/
theorem returnedCurvature_eq_one_iff_routeTransport (carrier : FourForceCarrier grain)
    (sector : ForceSector) (address : SixPlaneFace grain) :
    returnedCurvature carrier sector address = 1 ↔
      (sectorFaceComparison carrier sector address).rightTransport =
        (sectorFaceComparison carrier sector address).leftTransport := by
  rw [returnedCurvature_eq_addressedReturn]
  exact (sectorFaceComparison carrier sector address).returnedCurvature_eq_one_iff

/-- Reversing the addressed face route and every elementary orientation inverts its holonomy. -/
theorem reversedSectorFaceHolonomy (carrier : FourForceCarrier grain)
    (sector : ForceSector) (address : SixPlaneFace grain) :
    parallelTransport ((sectorFaceWord carrier sector address).reverse.map Inv.inv) =
      (returnedCurvature carrier sector address)⁻¹ := by
  exact reversal_holonomy (sectorFaceWord carrier sector address)

/-- Every sector uses the same six addressed base-plane species.  The dependent internal fibre is
what prevents this common base theorem from identifying the four physical interactions. -/
theorem everySector_has_six_base_planes (_sector : ForceSector) :
    Fintype.card InteractionPlane = 6 := interactionPlane_count

end Soma.Holonics.Millennium.HolonicFourForceSectorCarrier

section Audit
open Soma.Holonics.Millennium.HolonicFourForceSectorCarrier
#print axioms interactionPlaneEquivFinSix_first
#print axioms interactionPlaneEquivFinSix_second
#print axioms cycleWedge_swap
#print axioms cycleWedge_self
#print axioms cycleWedge_basis
#print axioms cycleWedge_natural
#print axioms forceSector_count
#print axioms faceRouteCell_commutes
#print axioms returnedCurvature_eq_addressedReturn
#print axioms returnedCurvature_eq_one_iff_routeTransport
#print axioms reversedSectorFaceHolonomy
#print axioms everySector_has_six_base_planes
end Audit
