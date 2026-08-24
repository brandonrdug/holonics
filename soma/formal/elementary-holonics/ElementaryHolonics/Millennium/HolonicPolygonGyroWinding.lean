import ElementaryHolonics.Millennium.HolonicAlternatingGeometry
import ElementaryHolonics.Millennium.NavierStokesMaterialPolygon

/-!
# Addressed material boundaries, winding fibres, and gyroparallelogram return

This file binds four already founded owners through addressed passages.  A material polygon returns
its complete edge population before the additive boundary receiver closes it.  A turn ledger
returns its interior-angle budget.  Flat gyroparallelogram and Swing completions are compared as
parallel routes.  Finally, winding is exhibited as a coarse returned face: two different crossing
populations travel through complete `polygon -> ledger -> net` passages and meet at one net.

A separate noncommuting connection control retains unequal route targets as a receiver defect.
It is not silently renamed curvature or gyration.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicPolygonGyroWinding

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.HolonicComposition
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesMaterialPolygon
open Soma.Holonics.Millennium.WindingLedger

/-! ## A material polygon returns its edge population before its zero boundary face -/

/-- The first route face retains every addressed material edge at one time. -/
def materialEdgePopulationPassage (extra : ℕ) (velocity : VelocityField) :
    AddressedPassage (MaterialPolygon extra velocity × ℝ) (PolygonIndex extra → Space) :=
  AddressedPassage.graph fun input i => input.1.edgeAt input.2 i

/-- The additive boundary receiver is applied only after the edge population is retained. -/
def materialBoundaryPassage (extra : ℕ) (velocity : VelocityField) :
    AddressedPassage (MaterialPolygon extra velocity × ℝ) Space :=
  AddressedPassage.comp
    (AddressedPassage.graph fun edges : PolygonIndex extra → Space => ∑ i, edges i)
    (materialEdgePopulationPassage extra velocity)

/-- The canonical joined occurrence carries polygon/time, every edge, and their joining equality. -/
def materialBoundaryOccurrence (polygon : MaterialPolygon extra velocity) (t : ℝ) :
    (materialBoundaryPassage extra velocity).Occurrence :=
  ⟨(polygon, t), fun i => polygon.edgeAt t i, rfl⟩

/-- The returned boundary is zero, derived from the material polygon's telescoping incidence. -/
theorem materialBoundaryPassage_target_eq_zero
    (polygon : MaterialPolygon extra velocity) (t : ℝ) :
    (materialBoundaryPassage extra velocity).target
      (materialBoundaryOccurrence polygon t) = 0 := by
  exact polygon.sum_edgesAt_eq_zero t

/-- The joined middle edge-population face cancels before the zero receiver is read. -/
theorem materialBoundaryPassage_middleBoundary_eq_zero
    (polygon : MaterialPolygon extra velocity) (t : ℝ) :
    AddressedPassage.joinedMiddleBoundary (materialEdgePopulationPassage extra velocity)
      (AddressedPassage.graph fun edges : PolygonIndex extra → Space => ∑ i, edges i)
      (materialBoundaryOccurrence polygon t) = 0 :=
  AddressedPassage.boundary_join _ _ _

/-! ## The angle ledger as a receiver of the retained turn population -/

/-- One addressed turn ledger returns its interior-angle receiver. -/
def turnBudgetPassage : AddressedPassage (PolygonTurnLedger extra) ℝ :=
  AddressedPassage.graph fun ledger => ∑ i, ledger.interior i

theorem turnBudgetPassage_target (ledger : PolygonTurnLedger extra) :
    turnBudgetPassage.target ledger = (extra + 1 : ℕ) * ledger.halfTurn :=
  ledger.sum_interior

/-! ## Flat Swing and gyroparallelogram routes -/

def swingCompletionPassage (G : Type*) [AddCommGroup G] :
    AddressedPassage (ReturnedQuadrilateral G) G :=
  AddressedPassage.graph ReturnedQuadrilateral.swingThenTransport

def gyroCompletionPassage (G : Type*) [AddCommGroup G] :
    AddressedPassage (ReturnedQuadrilateral G) G :=
  AddressedPassage.graph fun q =>
    Gyrogroup.gyroparallelogram (Gyrogroup.additive_gyrocommutative G)
      q.source q.left q.right

variable {G : Type*} [AddCommGroup G]

/-- Both flat completion routes retain the same quadrilateral occurrence. -/
def swingGyroCompletionCell (q : ReturnedQuadrilateral G) :
    AddressedPassage.ComparisonCell (swingCompletionPassage G) (gyroCompletionPassage G) where
  left := q
  right := q
  source_exact := rfl

/-- Zero-gyration additive transport makes the Swing and gyroparallelogram routes commute. -/
theorem swingGyroCompletionCell_commutes (q : ReturnedQuadrilateral G) :
    (swingGyroCompletionCell q).Commutes := by
  exact (q.additiveGyroparallelogram_eq_swingThenTransport).symm

def returnedVertexPassage (G : Type*) [AddCommGroup G] :
    AddressedPassage (ReturnedQuadrilateral G) G :=
  AddressedPassage.graph ReturnedQuadrilateral.returned

def flatCompletionPassage (G : Type*) [AddCommGroup G] :
    AddressedPassage (ReturnedQuadrilateral G) G :=
  AddressedPassage.graph ReturnedQuadrilateral.flatFourth

/-- The actual and flat-return routes remain comparable even when they do not close. -/
def returnedFlatCell (q : ReturnedQuadrilateral G) :
    AddressedPassage.ComparisonCell (returnedVertexPassage G) (flatCompletionPassage G) where
  left := q
  right := q
  source_exact := rfl

/-- Flat closure is exactly commutation of the returned and predicted routes. -/
theorem returnedFlatCell_commutes_iff (q : ReturnedQuadrilateral G) :
    (returnedFlatCell q).Commutes ↔ q.returnDefect = 0 := by
  change q.returned = q.flatFourth ↔ q.returnDefect = 0
  exact q.returnDefect_eq_zero_iff.symm

/-- Every nonzero return defect produces a route-separating identity receiver. -/
theorem returnedFlatCell_receiverDefect (q : ReturnedQuadrilateral G)
    (hdefect : q.returnDefect ≠ 0) :
    (returnedFlatCell q).ReceiverDefect G _root_.id := by
  refine ⟨?_⟩
  intro hclose
  exact hdefect (q.returnDefect_eq_zero_iff.mpr hclose)

/-! ## A noncommuting completion retains its route defect -/

def noncommutingLeftPassage : AddressedPassage (Fin 3) (Fin 3) :=
  AddressedPassage.graph (parallelTransport [swapZeroOne, swapOneTwo])

def noncommutingRightPassage : AddressedPassage (Fin 3) (Fin 3) :=
  AddressedPassage.graph (parallelTransport [swapOneTwo, swapZeroOne])

def noncommutingCompletionCell :
    AddressedPassage.ComparisonCell noncommutingLeftPassage noncommutingRightPassage where
  left := (0 : Fin 3)
  right := (0 : Fin 3)
  source_exact := rfl

/-- The route cell returns its unequal face before any geometric interpretation is attached. -/
theorem noncommutingCompletion_returns_receiverDefect :
    noncommutingCompletionCell.ReceiverDefect (Fin 3) _root_.id := by
  refine ⟨?_⟩
  change parallelTransport [swapZeroOne, swapOneTwo] 0 ≠
    parallelTransport [swapOneTwo, swapZeroOne] 0
  decide

/-! ## Winding net as a coarse face of complete addressed ledger routes -/

/-- A closed polygon is carried through its derived crossing ledger and only then through `net`. -/
def polygonLedgerNetPassage (polygon : List Pt) : AddressedPassage Unit ℤ :=
  AddressedPassage.comp (AddressedPassage.graph net)
    (AddressedPassage.comp (AddressedPassage.graph ledger)
      (AddressedPassage.graph fun _ : Unit => polygon))

/-- The complete canonical occurrence retains the polygon and the computed ledger. -/
def polygonLedgerNetOccurrence (polygon : List Pt) :
    (polygonLedgerNetPassage polygon).Occurrence :=
  ⟨⟨(), polygon, rfl⟩, ledger polygon, rfl⟩

/-- The enclosing and notched loops meet at one net while retaining separate route occurrences. -/
def equalNetDifferentLedgerCell :
    AddressedPassage.ComparisonCell
      (polygonLedgerNetPassage enclosingLoop)
      (polygonLedgerNetPassage notchedLoop) where
  left := polygonLedgerNetOccurrence enclosingLoop
  right := polygonLedgerNetOccurrence notchedLoop
  source_exact := rfl

theorem equalNetDifferentLedgerCell_commutes : equalNetDifferentLedgerCell.Commutes := by
  change net (ledger enclosingLoop) = net (ledger notchedLoop)
  exact theTwoPopulationsShareOneNet.1.trans theTwoPopulationsShareOneNet.2.1.symm

/-- The intermediate crossing populations remain unequal despite the commuting net face. -/
theorem equalNetDifferentLedgerCell_reopens_at_ledger :
    (equalNetDifferentLedgerCell.left.right : List Crossing) ≠
      equalNetDifferentLedgerCell.right.right := by
  change ledger enclosingLoop ≠ ledger notchedLoop
  exact theTwoPopulationsShareOneNet.2.2.2.2.2

/-- The richer population-count receiver separates those retained intermediate ledgers. -/
theorem equalNetDifferentLedgerCell_reopens_at_total :
    total equalNetDifferentLedgerCell.left.right ≠
      total equalNetDifferentLedgerCell.right.right := by
  change total (ledger enclosingLoop) ≠ total (ledger notchedLoop)
  rw [theTwoPopulationsShareOneNet.2.2.1, theTwoPopulationsShareOneNet.2.2.2.1]
  decide

end Soma.Holonics.Millennium.HolonicPolygonGyroWinding

section Audit
open Soma.Holonics.Millennium.HolonicPolygonGyroWinding
#print axioms materialBoundaryPassage_target_eq_zero
#print axioms materialBoundaryPassage_middleBoundary_eq_zero
#print axioms turnBudgetPassage_target
#print axioms swingGyroCompletionCell_commutes
#print axioms returnedFlatCell_commutes_iff
#print axioms returnedFlatCell_receiverDefect
#print axioms noncommutingCompletion_returns_receiverDefect
#print axioms equalNetDifferentLedgerCell_commutes
#print axioms equalNetDifferentLedgerCell_reopens_at_ledger
#print axioms equalNetDifferentLedgerCell_reopens_at_total
end Audit
