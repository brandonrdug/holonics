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
  | i :: word, x =>
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

/-- Chronology is discardable exactly for pairwise commuting transports. -/
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

/-- Parallel transport composes the declared invertible elementary passages in word order. -/
def parallelTransport {X : Type*} : List (Equiv.Perm X) → Equiv.Perm X
  | [] => 1
  | transport :: word => transport * parallelTransport word

@[simp] theorem parallelTransport_nil {X : Type*} :
    parallelTransport ([] : List (Equiv.Perm X)) = 1 := rfl

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
    ∃ left right : firstCoordinateHistoryCompression.reconstructionFibre false,
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
