import Holonics.Foundation.Lineage
import Holonics.Foundation.ComparisonCell
import Mathlib.GroupTheory.Perm.Basic

/-!
# Connection transport along addressed lineage

A connection assigns invertible fibre transport to each retained occurrence of an addressed
passage. Comparing complete routes returns their curvature/holonomy defect. A fibre chart
rebase preserves that return; a noninvertible receiver or scale map is handled only by the
explicit intertwining hypotheses below, so a quotient may erase a defect. Noninvertible route
comparisons remain `AddressedPassage.ComparisonCell` receiver defects and are not promoted to
group actions.
-/

namespace Holonics.Foundation.ConnectionLineage

/-! ## Declared connection transport and loop return -/

/-- A connection assigns transport to the carrying occurrences of one addressed passage. -/
abbrev AddressedConnection (Fibre : Type*) {X Y : Type*} (P : AddressedPassage X Y) :=
  P.Occurrence → Equiv.Perm Fibre

/-- Connection transport is first defined on one addressed elementary occurrence. -/
def connectionTransport {X Y Fibre : Type*} {P : AddressedPassage X Y}
    (connection : AddressedConnection Fibre P) (carried : P.Occurrence) : Equiv.Perm Fibre :=
  connection carried

/-- A pullback join composes the successor transport after the predecessor transport. -/
def joinedConnectionTransport {X Y Z Fibre : Type*}
    {P : AddressedPassage X Y} {Q : AddressedPassage Y Z}
    (leftConnection : AddressedConnection Fibre P)
    (rightConnection : AddressedConnection Fibre Q)
    (joined : AddressedPassage.Join P Q) : Equiv.Perm Fibre :=
  connectionTransport rightConnection joined.right *
    connectionTransport leftConnection joined.left

theorem joinedConnectionTransport_is_serialComposition
    {X Y Z Fibre : Type*} {P : AddressedPassage X Y} {Q : AddressedPassage Y Z}
    (leftConnection : AddressedConnection Fibre P)
    (rightConnection : AddressedConnection Fibre Q)
    (joined : AddressedPassage.Join P Q) :
    joinedConnectionTransport leftConnection rightConnection joined =
      connectionTransport rightConnection joined.right *
        connectionTransport leftConnection joined.left := rfl

/-! ## Two addressed routes return one curvature defect -/

/-- Transport an invertible fibre action through an exact change of fibre chart. -/
def rebaseTransport {Fibre Fibre' : Type*} (chart : Fibre ≃ Fibre')
    (transport : Equiv.Perm Fibre) : Equiv.Perm Fibre' :=
  (chart.symm.trans transport).trans chart

@[simp] theorem rebaseTransport_apply {Fibre Fibre' : Type*} (chart : Fibre ≃ Fibre')
    (transport : Equiv.Perm Fibre) (state : Fibre') :
    rebaseTransport chart transport state = chart (transport (chart.symm state)) := rfl

/-- Exact chart transport respects serial composition of fibre actions. -/
theorem rebaseTransport_mul {Fibre Fibre' : Type*} (chart : Fibre ≃ Fibre')
    (left right : Equiv.Perm Fibre) :
    rebaseTransport chart (left * right) =
      rebaseTransport chart left * rebaseTransport chart right := by
  ext state
  simp [rebaseTransport]

/-- Exact chart transport respects reversal of a fibre action. -/
theorem rebaseTransport_inv {Fibre Fibre' : Type*} (chart : Fibre ≃ Fibre')
    (transport : Equiv.Perm Fibre) :
    rebaseTransport chart transport⁻¹ = (rebaseTransport chart transport)⁻¹ := by
  ext state
  simp [rebaseTransport]

/-- The returned connection defect between two routes: follow the right route and reverse the
left.  This is defined only after both route transports have been retained. -/
def routeComparisonReturn {Fibre : Type*}
    (left right : Equiv.Perm Fibre) : Equiv.Perm Fibre :=
  right * left⁻¹

/-- A route comparison is flat exactly when its two complete transports agree. -/
theorem routeComparisonReturn_eq_one_iff {Fibre : Type*}
    (left right : Equiv.Perm Fibre) :
    routeComparisonReturn left right = 1 ↔ right = left := by
  constructor
  · intro h
    have transported := congrArg (fun action : Equiv.Perm Fibre ↦ action * left) h
    simpa [routeComparisonReturn, mul_assoc] using transported
  · rintro rfl
    simp [routeComparisonReturn]

/-- A comparison of two addressed route occurrences together with the connection on each route.
The route occurrences remain available through `cell`; equal endpoints or equal transports do not
identify them. -/
structure AddressedConnectionComparison (Fibre : Type*) {X Y : Type*}
    (P Q : AddressedPassage X Y) where
  cell : AddressedPassage.ComparisonCell P Q
  leftConnection : AddressedConnection Fibre P
  rightConnection : AddressedConnection Fibre Q

namespace AddressedConnectionComparison

variable {Fibre X Y : Type*} {P Q : AddressedPassage X Y}

/-- The complete left occurrence in its addressed source/target fibre. -/
def leftFibre (comparison : AddressedConnectionComparison Fibre P Q) :
    P.Fibre (P.source comparison.cell.left) (P.target comparison.cell.left) :=
  ⟨comparison.cell.left, rfl, rfl⟩

/-- The complete right occurrence, rebased only at the common source proved by the comparison
cell.  Its target remains its own returned boundary face. -/
def rightFibre (comparison : AddressedConnectionComparison Fibre P Q) :
    Q.Fibre (P.source comparison.cell.left) (Q.target comparison.cell.right) :=
  ⟨comparison.cell.right, comparison.cell.source_exact.symm, rfl⟩

/-- The retained transport of the left route occurrence. -/
def leftTransport (comparison : AddressedConnectionComparison Fibre P Q) : Equiv.Perm Fibre :=
  connectionTransport comparison.leftConnection comparison.cell.left

/-- The retained transport of the right route occurrence. -/
def rightTransport (comparison : AddressedConnectionComparison Fibre P Q) : Equiv.Perm Fibre :=
  connectionTransport comparison.rightConnection comparison.cell.right

/-- Curvature/holonomy returned by the two addressed connection routes. -/
def returnedCurvature (comparison : AddressedConnectionComparison Fibre P Q) : Equiv.Perm Fibre :=
  routeComparisonReturn comparison.leftTransport comparison.rightTransport

/-- The addressed comparison is connection-flat exactly when its two route transports agree. -/
theorem returnedCurvature_eq_one_iff
    (comparison : AddressedConnectionComparison Fibre P Q) :
    comparison.returnedCurvature = 1 ↔
      comparison.rightTransport = comparison.leftTransport :=
  routeComparisonReturn_eq_one_iff comparison.leftTransport comparison.rightTransport

end AddressedConnectionComparison

/-- Fibre-chart rebase conjugates the complete route return; it cannot change whether the face is
flat. -/
theorem routeComparisonReturn_rebase {Fibre Fibre' : Type*} (chart : Fibre ≃ Fibre')
    (left right : Equiv.Perm Fibre) :
    routeComparisonReturn (rebaseTransport chart left) (rebaseTransport chart right) =
      rebaseTransport chart (routeComparisonReturn left right) := by
  rw [routeComparisonReturn, routeComparisonReturn, rebaseTransport_mul,
    rebaseTransport_inv]

/-! ## Receiver/scale descent of a two-route connection return -/

/-- A possibly noninvertible scale or receiver map which intertwines both complete route actions.
Unlike `rebaseTransport`, this passage permits a genuine quotient and therefore retains the
possibility that the coarse receiver loses curvature. -/
structure RouteScalePassage (Fine Coarse : Type*) where
  fibreMap : Fine → Coarse
  fineLeft : Equiv.Perm Fine
  fineRight : Equiv.Perm Fine
  coarseLeft : Equiv.Perm Coarse
  coarseRight : Equiv.Perm Coarse
  left_natural : ∀ state, fibreMap (fineLeft state) = coarseLeft (fibreMap state)
  right_natural : ∀ state, fibreMap (fineRight state) = coarseRight (fibreMap state)

namespace RouteScalePassage

variable {Fine Coarse : Type*} (passage : RouteScalePassage Fine Coarse)

/-- Intertwining an invertible route also intertwines its exact reversal. -/
theorem left_inv_natural (state : Fine) :
    passage.fibreMap (passage.fineLeft⁻¹ state) =
      passage.coarseLeft⁻¹ (passage.fibreMap state) := by
  have forward := passage.left_natural (passage.fineLeft⁻¹ state)
  have returned := congrArg passage.coarseLeft.symm forward
  simpa using returned.symm

/-- The complete curvature/holonomy return descends through every map which intertwines both
routes.  No injectivity, surjectivity, or choice of inverse is used. -/
theorem returnedCurvature_natural (state : Fine) :
    passage.fibreMap
        (routeComparisonReturn passage.fineLeft passage.fineRight state) =
      routeComparisonReturn passage.coarseLeft passage.coarseRight
        (passage.fibreMap state) := by
  change passage.fibreMap (passage.fineRight (passage.fineLeft⁻¹ state)) =
    passage.coarseRight (passage.coarseLeft⁻¹ (passage.fibreMap state))
  rw [passage.right_natural, passage.left_inv_natural]

/-- A coarse flat reading reconstructs fine flatness when the receiver retains all fine states. -/
theorem fineFlat_of_coarseFlat (hinjective : Function.Injective passage.fibreMap)
    (hcoarse : routeComparisonReturn passage.coarseLeft passage.coarseRight = 1) :
    routeComparisonReturn passage.fineLeft passage.fineRight = 1 := by
  ext state
  apply hinjective
  calc
    passage.fibreMap
        (routeComparisonReturn passage.fineLeft passage.fineRight state) =
      routeComparisonReturn passage.coarseLeft passage.coarseRight
        (passage.fibreMap state) := passage.returnedCurvature_natural state
    _ = passage.fibreMap state := by rw [hcoarse]; rfl

/-- Fine flatness fills the whole coarse receiver when every coarse state has a fine antecedent. -/
theorem coarseFlat_of_fineFlat (hsurjective : Function.Surjective passage.fibreMap)
    (hfine : routeComparisonReturn passage.fineLeft passage.fineRight = 1) :
    routeComparisonReturn passage.coarseLeft passage.coarseRight = 1 := by
  ext coarseState
  obtain ⟨fineState, rfl⟩ := hsurjective coarseState
  calc
    routeComparisonReturn passage.coarseLeft passage.coarseRight
        (passage.fibreMap fineState) =
      passage.fibreMap
        (routeComparisonReturn passage.fineLeft passage.fineRight fineState) :=
          (passage.returnedCurvature_natural fineState).symm
    _ = passage.fibreMap fineState := by rw [hfine]; rfl

/-- An exact fibre equivalence makes flatness invariant across scale; a quotient needs the stronger
one-way hypotheses above and may erase the defect. -/
theorem flat_iff_of_bijective (hbijective : Function.Bijective passage.fibreMap) :
    routeComparisonReturn passage.fineLeft passage.fineRight = 1 ↔
      routeComparisonReturn passage.coarseLeft passage.coarseRight = 1 := by
  exact ⟨passage.coarseFlat_of_fineFlat hbijective.2,
    passage.fineFlat_of_coarseFlat hbijective.1⟩

end RouteScalePassage

/-- The group commutator is the two-route return comparing the two orders around one addressed
two-direction face. -/
def commutatorRouteReturn {Fibre : Type*}
    (first second : Equiv.Perm Fibre) : Equiv.Perm Fibre :=
  routeComparisonReturn (second * first) (first * second)

/-- The commutator return is flat exactly when the two face directions commute. -/
theorem commutatorRouteReturn_eq_one_iff {Fibre : Type*}
    (first second : Equiv.Perm Fibre) :
    commutatorRouteReturn first second = 1 ↔ Commute first second := by
  rw [commutatorRouteReturn, routeComparisonReturn_eq_one_iff]
  rfl


end Holonics.Foundation.ConnectionLineage
