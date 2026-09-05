import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite retained-row restriction and zero insertion

The retained-row chart is a compact resident presentation, not an assertion that omitted
foreign rows are zero.  Its decoder inserts zero outside the explicitly retained subset.  The
laws below concern only this declared restricted native matrix and its later additive overlays.
-/

namespace Soma.Holonics.Computation.HolonicResidentRestriction

open scoped BigOperators

universe uR uC uK uReceiver uFace

variable {Row : Type uR} {Col : Type uC} {K : Type uK}
  [Fintype Row] [Fintype Col] [DecidableEq Row]
  [CommSemiring K]

/-- The compact resident section contains exactly the rows admitted by `retained`. -/
def CompactRows (retained : Finset Row) := {row // row ∈ retained}

/-- Zero insertion is a declared restricted native matrix: omitted rows are zero. -/
def decode (retained : Finset Row)
    (compact : CompactRows retained → Col → K) : Row → Col → K :=
  fun row col => if h : row ∈ retained then compact ⟨row, h⟩ col else 0

/-- The named restricted matrix is definitionally the same zero-insertion decoder. -/
def restrictedMatrix (retained : Finset Row)
    (compact : CompactRows retained → Col → K) : Matrix Row Col K :=
  decode retained compact

theorem decode_eq_restrictedMatrix (retained : Finset Row)
    (compact : CompactRows retained → Col → K) :
    decode retained compact = restrictedMatrix retained compact := rfl

theorem decode_omitted_zero (retained : Finset Row)
    (compact : CompactRows retained → Col → K)
    {row : Row} (omitted : row ∉ retained) (col : Col) :
    decode retained compact row col = 0 := by
  simp [decode, omitted]

theorem decode_retained (retained : Finset Row)
    (compact : CompactRows retained → Col → K)
    {row : Row} (present : row ∈ retained) (col : Col) :
    decode retained compact row col = compact ⟨row, present⟩ col := by
  simp [decode, present]

/-- A contraction of a matrix row against a column carrier. -/
def contract (matrix : Matrix Row Col K) (carrier : Col → K) (row : Row) : K :=
  ∑ col, matrix row col * carrier col

theorem restricted_contract_eq_decoded_contract (retained : Finset Row)
    (compact : CompactRows retained → Col → K) (carrier : Col → K) (row : Row) :
    contract (restrictedMatrix retained compact) carrier row =
      contract (decode retained compact) carrier row := rfl

def addMatrix (left right : Matrix Row Col K) : Matrix Row Col K :=
  fun row col => left row col + right row col

/-- Adding an arbitrary learned overlay after decoding commutes with contraction. -/
theorem contract_decode_add_overlay (retained : Finset Row)
    (compact : CompactRows retained → Col → K)
    (overlay : Matrix Row Col K) (carrier : Col → K) (row : Row) :
    contract (addMatrix (decode retained compact) overlay) carrier row =
      contract (decode retained compact) carrier row + contract overlay carrier row := by
  simp only [contract, addMatrix]
  calc
    (∑ col, (decode retained compact row col + overlay row col) * carrier col) =
        ∑ col, (decode retained compact row col * carrier col +
          overlay row col * carrier col) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [add_mul]
    _ = _ := Finset.sum_add_distrib

theorem decoded_successor_with_overlay (retained : Finset Row)
    (compact : CompactRows retained → Col → K)
    (overlay : Matrix Row Col K) :
    addMatrix (restrictedMatrix retained compact) overlay =
      addMatrix (decode retained compact) overlay := by
  rw [decode_eq_restrictedMatrix]

/-! ## Equality through a declared receiver family -/

structure ReceiverFamily (Receiver : Type uReceiver) (Face : Type uFace) where
  observe : Receiver → (Row → K) → Face

variable {Receiver : Type uReceiver} {Face : Type uFace}

theorem receiver_family_successor_eq
    (family : ReceiverFamily (Row := Row) (K := K) Receiver Face)
    (left right : Matrix Row Col K) (overlay : Matrix Row Col K)
    (equal_successor : addMatrix left overlay = addMatrix right overlay)
    (receiver : Receiver) (carrier : Col → K) :
    family.observe receiver (fun row => contract (addMatrix left overlay) carrier row) =
      family.observe receiver (fun row => contract (addMatrix right overlay) carrier row) := by
  apply congrArg (family.observe receiver)
  funext row
  rw [show contract (addMatrix left overlay) carrier row =
      contract (addMatrix right overlay) carrier row by rw [equal_successor]]

/-! ## Packed native state and local additive recurrence -/

/-- A resident state keeps its compact base immutable in the chart and carries later full-width
overlays separately.  The overlay is the only field changed by the local generator below. -/
structure PackedState (Row : Type uR) (Col : Type uC) (K : Type uK)
    (retained : Finset Row) where
  base : CompactRows retained → Col → K
  overlay : Matrix Row Col K

abbrev ExpandedState (Row : Type uR) (Col : Type uC) (K : Type uK) := Matrix Row Col K

/-- Executable decoding of a packed state into its expanded native matrix. -/
def decodeState (state : PackedState Row Col K retained) : ExpandedState Row Col K :=
  addMatrix (decode retained state.base) state.overlay

/-- One local additive generator updates only the full overlay. -/
def packedSuccessor (delta : Matrix Row Col K)
    (state : PackedState Row Col K retained) : PackedState Row Col K retained :=
  { state with overlay := addMatrix state.overlay delta }

def expandedSuccessor (delta state : ExpandedState Row Col K) : ExpandedState Row Col K :=
  addMatrix state delta

theorem decodeState_packedSuccessor (delta : Matrix Row Col K)
    (state : PackedState Row Col K retained) :
    decodeState (packedSuccessor delta state) =
      expandedSuccessor delta (decodeState state) := by
  ext row col
  simp [decodeState, packedSuccessor, expandedSuccessor, addMatrix, add_assoc]

def runPacked (word : List (Matrix Row Col K))
    (state : PackedState Row Col K retained) : PackedState Row Col K retained :=
  word.foldl (fun current delta => packedSuccessor delta current) state

def runExpanded (word : List (Matrix Row Col K))
    (state : ExpandedState Row Col K) : ExpandedState Row Col K :=
  word.foldl (fun current delta => expandedSuccessor delta current) state

theorem decodeState_runPacked (word : List (Matrix Row Col K))
    (state : PackedState Row Col K retained) :
    decodeState (runPacked word state) = runExpanded word (decodeState state) := by
  induction word generalizing state with
  | nil => rfl
  | cons delta rest ih =>
      change decodeState (runPacked rest (packedSuccessor delta state)) =
        runExpanded rest (expandedSuccessor delta (decodeState state))
      rw [ih, decodeState_packedSuccessor]

/-! ## Nonvacuous controls -/

section Controls

abbrev TwoRows := Fin 2
abbrev OneCol := Fin 1
def controlKept : TwoRows := 0
def controlOmitted : TwoRows := 1
def controlOnly : OneCol := 0
def controlRetained : Finset TwoRows := {controlKept}

def controlCompact : CompactRows controlRetained → OneCol → ℤ := fun _ _ => 3

theorem omitted_control_is_zero :
    decode controlRetained controlCompact controlOmitted controlOnly = 0 := by
  exact decode_omitted_zero controlRetained controlCompact (row := controlOmitted)
    (by simp [controlRetained, controlOmitted, controlKept]) controlOnly

theorem retained_control_is_nonzero :
    decode controlRetained controlCompact controlKept controlOnly ≠ 0 := by
  have present : controlKept ∈ controlRetained := by simp [controlRetained]
  rw [decode_retained controlRetained controlCompact present]
  norm_num [controlCompact, CompactRows]

def controlOverlay : Matrix TwoRows OneCol ℤ
  | row, _ => if row = controlKept then 5 else 7

theorem overlay_control_is_retained_and_omitted :
    contract (addMatrix (decode controlRetained controlCompact) controlOverlay)
        (fun _ => 2) controlKept =
      contract (decode controlRetained controlCompact) (fun _ => 2) controlKept +
        contract controlOverlay (fun _ => 2) controlKept := by
  exact contract_decode_add_overlay controlRetained controlCompact controlOverlay (fun _ => 2)
    controlKept

def omittedDeposit : Matrix TwoRows OneCol ℤ
  | row, _ => if row = controlOmitted then 11 else 0

theorem omitted_deposit_survives_decode :
    decodeState (retained := controlRetained)
        { base := controlCompact, overlay := omittedDeposit }
        controlOmitted controlOnly = 11 := by
  simp [decodeState, decode, addMatrix, omittedDeposit, controlRetained, controlOmitted,
    controlKept, controlCompact]

def silentOmittedReduction : Matrix TwoRows OneCol ℤ
  | row, _ => if row = controlOmitted then 0 else 3

theorem silent_omitted_reduction_is_invalid :
    decodeState (retained := controlRetained)
        { base := controlCompact, overlay := omittedDeposit }
        controlOmitted controlOnly ≠ silentOmittedReduction controlOmitted controlOnly := by
  rw [omitted_deposit_survives_decode]
  simp [silentOmittedReduction, controlOmitted]

end Controls

end Soma.Holonics.Computation.HolonicResidentRestriction
