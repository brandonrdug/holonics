import ElementaryHolonics.Foundation.ComparisonCell
import ElementaryHolonics.Millennium.PhysicalRealization
import ElementaryHolonics.Millennium.SwingBridges

/-!
# Addressed transport words, route comparison, holonomy, and retained fibres

This theorem-only composition rotates the existing lineage, chronology, realization, receiver,
and Swing owners into contact.  It does not introduce a planner or a universal holon wrapper.
`wordPassage` is literally iterated pullback composition of generator graphs; its fibre therefore
retains every intermediate occurrence and joining equality.  Connection transport is declared
before loop holonomy, and noninvertible routes retain comparison defects without being promoted to
group commutators.
-/

namespace Soma.Holonics

open Soma.Holonics.Millennium.Chronology

universe u v w

namespace AddressedPassage

variable {X : Type u} {Y : Type v} {ι : Type w}

/-- The addressed graph of a function; its occurrence is its source, not its endpoint pair. -/
def graph (f : X → Y) : AddressedPassage X Y where
  Occurrence := X
  source := _root_.id
  target := f

/-- The canonical occurrence carried by one functional graph. -/
def graphFibre (f : X → Y) (x : X) : (graph f).Fibre x (f x) := ⟨x, rfl, rfl⟩

/-- An ordered word is serial pullback composition of its addressed generator graphs. -/
def wordPassage (T : ι → X → X) : List ι → AddressedPassage X X
  | [] => id X
  | i :: word => comp (graph (T i)) (wordPassage T word)

/-- The canonical carrying occurrence of a transport word from one source. -/
def wordOccurrence (T : ι → X → X) :
    (word : List ι) → (x : X) → (wordPassage T word).Occurrence
  | [], x => x
  | _ :: word, x =>
      let left := wordOccurrence T word x
      ⟨left, (wordPassage T word).target left, rfl⟩

@[simp] theorem wordOccurrence_source (T : ι → X → X)
    (word : List ι) (x : X) :
    (wordPassage T word).source (wordOccurrence T word x) = x := by
  induction word with
  | nil => rfl
  | cons i word ih => exact ih

@[simp] theorem wordOccurrence_target (T : ι → X → X)
    (word : List ι) (x : X) :
    (wordPassage T word).target (wordOccurrence T word x) = transportWord T word x := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change T i ((wordPassage T word).target (wordOccurrence T word x)) =
        T i (transportWord T word x)
      rw [ih]

/-- The complete addressed word fibre, including every intermediate state and joining equality. -/
def wordFibre (T : ι → X → X) (word : List ι) (x : X) :
    (wordPassage T word).Fibre x (transportWord T word x) :=
  ⟨wordOccurrence T word x, wordOccurrence_source T word x,
    wordOccurrence_target T word x⟩

/-- Naturality compares two routes without discarding either nested pullback occurrence. -/
def intertwinerWordCell (T : ι → X → X) (S : ι → Y → Y) (f : X → Y)
    (word : List ι) (x : X) :
    ComparisonCell
      (comp (graph f) (wordPassage T word))
      (comp (wordPassage S word) (graph f)) := by
  let left : (comp (graph f) (wordPassage T word)).Occurrence :=
    ⟨wordOccurrence T word x, transportWord T word x,
      wordOccurrence_target T word x⟩
  let right : (comp (wordPassage S word) (graph f)).Occurrence :=
    ⟨x, wordOccurrence S word (f x), (wordOccurrence_source S word (f x)).symm⟩
  exact
    { left := left
      right := right
      source_exact := wordOccurrence_source T word x }

/-- Generator-local intertwining derives exact target commutation for the two addressed words. -/
theorem intertwinerWordCell_commutes
    (T : ι → X → X) (S : ι → Y → Y) (f : X → Y)
    (generatorExact : ∀ i x, f (T i x) = S i (f x)) (word : List ι) (x : X) :
    (intertwinerWordCell T S f word x).Commutes := by
  simpa [ComparisonCell.Commutes, intertwinerWordCell, comp, graph] using
    generatorEquivarianceExtendsToEveryTransportWord T S f generatorExact word x

/-- A passage equivalence restricts to an equivalence of every complete addressed fibre. -/
def fibreEquivOfPassageEquiv {P Q : AddressedPassage X Y} (e : PassageEquiv P Q)
    (x : X) (y : Y) : P.Fibre x y ≃ Q.Fibre x y where
  toFun carried :=
    ⟨e.occurrence carried.1,
      (e.source_exact carried.1).trans carried.2.1,
      (e.target_exact carried.1).trans carried.2.2⟩
  invFun carried := by
    let predecessor := e.occurrence.symm carried.1
    have returns : e.occurrence predecessor = carried.1 :=
      e.occurrence.apply_symm_apply carried.1
    exact ⟨predecessor,
      (e.source_exact predecessor).symm.trans
        ((congrArg Q.source returns).trans carried.2.1),
      (e.target_exact predecessor).symm.trans
        ((congrArg Q.target returns).trans carried.2.2)⟩
  left_inv carried := by
    apply Subtype.ext
    exact e.occurrence.left_inv carried.1
  right_inv carried := by
    apply Subtype.ext
    exact e.occurrence.right_inv carried.1

end AddressedPassage

namespace Millennium.HolonicComposition

open Soma.Holonics.Millennium.Swing
open Soma.Holonics.Millennium.PhysicalRealization
open Soma.Holonics.Millennium.LineageCompression

/-! ## Swing as a concrete realization generator -/

/-- The affine Swing realization: receivers retain the exact site while generators are anchors. -/
def swingCore : PhysicalRealizationCore Site Unit Site Site where
  transport := swing
  receiver _ := _root_.id

/-- One affine Swing is an addressed generator occurrence. -/
def swingGeneratorPassage (anchor : Site) : AddressedPassage Site Site :=
  AddressedPassage.graph (swing anchor)

/-- A repeated-anchor chronology is exactly the corresponding function iterate. -/
theorem repeatedSwingWord_eq_iterate (anchor body : Site) (n : ℕ) :
    transportWord swing (List.replicate n anchor) body = (swing anchor)^[n] body := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, transportWord_cons, Function.iterate_succ_apply']
      rw [ih]

/-- Swing parity acts on orientation through the addressed ordered word. -/
theorem repeatedSwingWord_orientation (anchor body third : Site) (n : ℕ) :
    orientedSpan (transportWord swing (List.replicate n anchor) body) anchor third =
      (-1 : ℤ) ^ n * orientedSpan body anchor third := by
  rw [repeatedSwingWord_eq_iterate]
  exact Chronology.theHandIsTheParityOfTheWord body anchor third n

/-- Reversal of a repeated-anchor word retains the same addressed target and orientation. -/
theorem reverse_repeatedSwingWord (anchor body : Site) (n : ℕ) :
    transportWord swing (List.replicate n anchor).reverse body =
      transportWord swing (List.replicate n anchor) body := by
  rw [List.reverse_replicate]

/-- Every ordered Swing word has a complete inhabited addressed fibre. -/
theorem orderedSwingWord_retains_lineage (word : List Site) (body : Site) :
    Nonempty ((AddressedPassage.wordPassage swing word).Fibre body
      (transportWord swing word body)) :=
  ⟨AddressedPassage.wordFibre swing word body⟩

/-- Endpoint action is order-blind exactly for pairwise commuting transports.  The addressed word
and its occurrence fibre remain available even when this endpoint quotient applies. -/
theorem chronology_discard_iff_commuting {I X : Type*} (T : I → X → X) :
    OrderBlind T ↔ ∀ i j x, T i (T j x) = T j (T i x) :=
  orderBlind_iff_commute

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

/-! ## Additive connection specialization -/

/-- Exact translation of an additive fibre.  This is the abelian connection action used by
cellular circulation and phase transport; no metric or constitutive law is inserted. -/
def additiveTranslation {A : Type*} [AddGroup A] (increment : A) : Equiv.Perm A where
  toFun state := state + increment
  invFun state := state - increment
  left_inv state := by simp
  right_inv state := by simp

@[simp] theorem additiveTranslation_apply {A : Type*} [AddGroup A]
    (increment state : A) : additiveTranslation increment state = state + increment := rfl

/-- In an abelian fibre, serial translations add their oriented increments. -/
theorem additiveTranslation_mul {A : Type*} [AddCommGroup A] (left right : A) :
    additiveTranslation left * additiveTranslation right =
      additiveTranslation (left + right) := by
  ext state
  simp [add_comm, add_left_comm]

/-- Parallel transport composes the declared invertible elementary passages in word order. -/
def parallelTransport {X : Type*} : List (Equiv.Perm X) → Equiv.Perm X
  | [] => 1
  | transport :: word => transport * parallelTransport word

@[simp] theorem parallelTransport_nil {X : Type*} :
    parallelTransport ([] : List (Equiv.Perm X)) = 1 := rfl

/-- Abelian connection holonomy is translation by the exact sum of the retained increments. -/
theorem parallelTransport_additiveTranslation {A : Type*} [AddCommGroup A]
    (increments : List A) :
    parallelTransport (increments.map additiveTranslation) =
      additiveTranslation increments.sum := by
  induction increments with
  | nil => ext state; simp [additiveTranslation]
  | cons increment increments ih =>
      simp [parallelTransport, ih, additiveTranslation_mul]

theorem parallelTransport_append {X : Type*} (left right : List (Equiv.Perm X)) :
    parallelTransport (left ++ right) = parallelTransport left * parallelTransport right := by
  induction left with
  | nil => simp [parallelTransport]
  | cons transport left ih => simp [parallelTransport, ih, mul_assoc]

/-- The identity loop returns the identity transport. -/
theorem identityLoop_holonomy {X : Type*} :
    parallelTransport ([] : List (Equiv.Perm X)) = 1 := rfl

/-- Serial loop joining composes the two loop returns. -/
theorem serialLoop_holonomy {X : Type*} (left right : List (Equiv.Perm X)) :
    parallelTransport (left ++ right) = parallelTransport left * parallelTransport right :=
  parallelTransport_append left right

/-- Reversing a route and every elementary orientation inverts its parallel transport. -/
theorem reversal_holonomy {X : Type*} (word : List (Equiv.Perm X)) :
    parallelTransport (word.reverse.map Inv.inv) = (parallelTransport word)⁻¹ := by
  induction word with
  | nil => simp [parallelTransport]
  | cons transport word ih =>
      rw [List.reverse_cons, List.map_append, parallelTransport_append, ih]
      simp [parallelTransport]

/-- A basepoint route conjugates, rather than identifies, the returned loop transport. -/
def rebasedHolonomy {X : Type*} (route loop : List (Equiv.Perm X)) : Equiv.Perm X :=
  parallelTransport route * parallelTransport loop * (parallelTransport route)⁻¹

theorem changeOfBasepoint_holonomy {X : Type*} (route loop : List (Equiv.Perm X)) :
    rebasedHolonomy route loop =
      parallelTransport route * parallelTransport loop * (parallelTransport route)⁻¹ := rfl

/-! ## Commuting, noncommuting, and noninvertible controls -/

/-- A flat commuting control. -/
theorem flatIdentityLoop_is_trivial :
    parallelTransport ([1, 1] : List (Equiv.Perm Bool)) = 1 := by
  rfl

def swapZeroOne : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def swapOneTwo : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Two invertible noncommuting transports retain their word order. -/
theorem noncommutingTransport_is_wordSensitive :
    parallelTransport [swapZeroOne, swapOneTwo] ≠
      parallelTransport [swapOneTwo, swapZeroOne] := by
  decide

/-- Their commutator loop has a nontrivial returned holonomy. -/
theorem noncommutingTransport_has_nontrivialLoopReturn :
    parallelTransport [swapZeroOne, swapOneTwo, swapZeroOne⁻¹, swapOneTwo⁻¹] ≠ 1 := by
  decide

/-- The previous finite commutator control is exactly the generic two-route curvature return, not
merely a noncommuting word with no face comparison. -/
theorem noncommutingTransport_loop_eq_routeReturn :
    parallelTransport [swapZeroOne, swapOneTwo, swapZeroOne⁻¹, swapOneTwo⁻¹] =
      commutatorRouteReturn swapZeroOne swapOneTwo := by
  simp [parallelTransport, commutatorRouteReturn, routeComparisonReturn, mul_assoc]

/-- A finite receiver-insufficiency control: collapsing both fine states makes a nontrivial route
return look flat. -/
def boolToUnitRouteScale : RouteScalePassage Bool Unit where
  fibreMap _ := ()
  fineLeft := 1
  fineRight := Equiv.swap false true
  coarseLeft := 1
  coarseRight := 1
  left_natural _ := rfl
  right_natural _ := rfl

theorem boolToUnit_coarseReturn_is_flat :
    routeComparisonReturn boolToUnitRouteScale.coarseLeft
      boolToUnitRouteScale.coarseRight = 1 := by
  rfl

theorem boolToUnit_fineReturn_is_not_flat :
    routeComparisonReturn boolToUnitRouteScale.fineLeft
      boolToUnitRouteScale.fineRight ≠ 1 := by
  intro h
  have pointwise := DFunLike.congr_fun h false
  simp [boolToUnitRouteScale, routeComparisonReturn] at pointwise

/-- A noninvertible route remains a function and is refused as a connection element. -/
def collapsedBool (_ : Bool) : Bool := false

theorem collapsedBool_is_not_invertible : ¬ Function.Bijective collapsedBool := by
  intro h
  have impossible := h.1 (show collapsedBool false = collapsedBool true by rfl)
  exact Bool.false_ne_true impossible

/-- The refused group route still returns an exact addressed comparison defect. -/
def collapsedRouteCell :
    AddressedPassage.ComparisonCell
      (AddressedPassage.graph collapsedBool) (AddressedPassage.graph _root_.id) where
  left := true
  right := true
  source_exact := rfl

theorem collapsedRoute_returns_comparisonDefect :
    (collapsedRouteCell.ReceiverDefect Bool _root_.id) := by
  exact ⟨Bool.false_ne_true⟩

/-! ## A complete dynamic fibre and a richer exterior reopening -/

/-- A dynamic quotient exact for the declared first-coordinate receiver and identity histories. -/
def firstCoordinateHistoryCompression :
    ReceiverHistoryCompression Unit Unit (Bool × Bool) Bool Bool where
  present :=
    { quotient := Prod.fst
      receiver := fun _ => Prod.fst
      factor := fun _ => _root_.id
      exact := fun _ _ => rfl }
  sourceTransport := fun _ => _root_.id
  quotientTransport := fun _ => _root_.id
  generatorExact := fun _ _ => rfl

/-- Two distinct occurrences inhabit the complete retained quotient fibre. -/
theorem firstCoordinate_completeFibre_retains_collapsed_pair :
    ∃ left right : firstCoordinateHistoryCompression.preimageFibre false,
      left.1 = (false, false) ∧ right.1 = (false, true) := by
  exact ⟨⟨(false, false), rfl⟩, ⟨(false, true), rfl⟩, rfl, rfl⟩

/-- The exterior second-coordinate receiver constructively reopens that declared quotient fibre. -/
theorem richerReceiver_reopens_firstCoordinateFibre :
    (false, false).2 ≠ (false, true).2 := by decide

/-! ## Existing realization passages retain their own occurrences across word comparison -/

variable {Generator Receiver Face Source Target : Type*}
  {A : PhysicalRealizationCore Generator Receiver Source Face}
  {B : PhysicalRealizationCore Generator Receiver Target Face}

/-- The owned carrying occurrence selected from the passage's complete source/chart fibre. -/
noncomputable def ownedOccurrence (P : RealizationPassage A B) (source : Source) :
    P.span.addressed.Occurrence :=
  (Classical.choice (P.span.carries source)).1

@[simp] theorem ownedOccurrence_source (P : RealizationPassage A B) (source : Source) :
    P.span.addressed.source (ownedOccurrence P source) = source :=
  (Classical.choice (P.span.carries source)).2.1

@[simp] theorem ownedOccurrence_target (P : RealizationPassage A B) (source : Source) :
    P.span.addressed.target (ownedOccurrence P source) = P.span.chart source :=
  (Classical.choice (P.span.carries source)).2.2

/-- The naturality cell uses the passage's owned occurrence, not a replacement graph occurrence. -/
noncomputable def realizationWordCell (P : RealizationPassage A B)
    (word : List Generator) (source : Source) :
    AddressedPassage.ComparisonCell
      (AddressedPassage.comp P.span.addressed
        (AddressedPassage.wordPassage A.transport word))
      (AddressedPassage.comp (AddressedPassage.wordPassage B.transport word)
        P.span.addressed) where
  left :=
    ⟨AddressedPassage.wordOccurrence A.transport word source,
      ownedOccurrence P (transportWord A.transport word source),
      (AddressedPassage.wordOccurrence_target A.transport word source).trans
        (ownedOccurrence_source P _).symm⟩
  right :=
    ⟨ownedOccurrence P source,
      AddressedPassage.wordOccurrence B.transport word (P.span.chart source),
      (ownedOccurrence_target P source).trans
        (AddressedPassage.wordOccurrence_source B.transport word _).symm⟩
  source_exact :=
    (AddressedPassage.wordOccurrence_source A.transport word source).trans
      (ownedOccurrence_source P source).symm

/-- Generator exactness derives commutation of that owned-occurrence comparison cell. -/
theorem realizationWordCell_commutes (P : RealizationPassage A B)
    (word : List Generator) (source : Source) :
    (realizationWordCell P word source).Commutes := by
  simpa [AddressedPassage.ComparisonCell.Commutes, realizationWordCell,
    AddressedPassage.comp] using P.chartCommutesWithEveryOrderedWord word source

/-- Both serial routes expose and cancel their own joined middle boundary. -/
theorem realizationWordCell_middleBoundaries_cancel (P : RealizationPassage A B)
    (word : List Generator) (source : Source) :
    AddressedPassage.joinedMiddleBoundary
        (AddressedPassage.wordPassage A.transport word) P.span.addressed
        (realizationWordCell P word source).left = 0 ∧
      AddressedPassage.joinedMiddleBoundary P.span.addressed
        (AddressedPassage.wordPassage B.transport word)
        (realizationWordCell P word source).right = 0 := by
  exact ⟨AddressedPassage.boundary_join _ _ _, AddressedPassage.boundary_join _ _ _⟩

/-- One circulation theorem retains route comparison, additive cancellation, and future receiver. -/
theorem realizationWord_circulation_closes (P : RealizationPassage A B)
    (receiver : Receiver) (word : List Generator) (source : Source) :
    (realizationWordCell P word source).Commutes ∧
      AddressedPassage.joinedMiddleBoundary
          (AddressedPassage.wordPassage A.transport word) P.span.addressed
          (realizationWordCell P word source).left = 0 ∧
      AddressedPassage.joinedMiddleBoundary P.span.addressed
          (AddressedPassage.wordPassage B.transport word)
          (realizationWordCell P word source).right = 0 ∧
      futureFace B receiver word (P.span.chart source) =
        futureFace A receiver word source := by
  refine ⟨realizationWordCell_commutes P word source, ?_⟩
  rcases realizationWordCell_middleBoundaries_cancel P word source with ⟨left, right⟩
  exact ⟨left, right, P.everyFutureReceiverFactors receiver word source⟩

/-- The associator preserves complete fibres as well as exterior additive boundary. -/
def associator_preserves_complete_fibre
    {X Y Z W : Type*} (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (R : AddressedPassage Z W) (x : X) (w : W) :
    (AddressedPassage.comp R (AddressedPassage.comp Q P)).Fibre x w ≃
      (AddressedPassage.comp (AddressedPassage.comp R Q) P).Fibre x w :=
  AddressedPassage.fibreEquivOfPassageEquiv (AddressedPassage.compAssociator R Q P) x w

theorem associator_preserves_additive_boundary
    {X Y Z W : Type*} (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (R : AddressedPassage Z W)
    (carried : (AddressedPassage.comp R (AddressedPassage.comp Q P)).Occurrence) :
    (AddressedPassage.comp (AddressedPassage.comp R Q) P).additiveBoundary
        ((AddressedPassage.compAssociator R Q P).occurrence carried) =
      (AddressedPassage.comp R (AddressedPassage.comp Q P)).additiveBoundary carried :=
  AddressedPassage.boundary_compAssociator P Q R carried

end Millennium.HolonicComposition

end Soma.Holonics

section Audit
open Soma.Holonics
open Soma.Holonics.Millennium.HolonicComposition
#print axioms AddressedPassage.intertwinerWordCell_commutes
#print axioms repeatedSwingWord_orientation
#print axioms chronology_discard_iff_commuting
#print axioms reversal_holonomy
#print axioms joinedConnectionTransport_is_serialComposition
#print axioms routeComparisonReturn_eq_one_iff
#print axioms AddressedConnectionComparison.returnedCurvature_eq_one_iff
#print axioms routeComparisonReturn_rebase
#print axioms RouteScalePassage.returnedCurvature_natural
#print axioms RouteScalePassage.flat_iff_of_bijective
#print axioms boolToUnit_coarseReturn_is_flat
#print axioms boolToUnit_fineReturn_is_not_flat
#print axioms commutatorRouteReturn_eq_one_iff
#print axioms noncommutingTransport_loop_eq_routeReturn
#print axioms parallelTransport_additiveTranslation
#print axioms changeOfBasepoint_holonomy
#print axioms noncommutingTransport_is_wordSensitive
#print axioms collapsedBool_is_not_invertible
#print axioms collapsedRoute_returns_comparisonDefect
#print axioms firstCoordinate_completeFibre_retains_collapsed_pair
#print axioms richerReceiver_reopens_firstCoordinateFibre
#print axioms realizationWordCell_commutes
#print axioms realizationWord_circulation_closes
#print axioms associator_preserves_complete_fibre
#print axioms associator_preserves_additive_boundary
end Audit
