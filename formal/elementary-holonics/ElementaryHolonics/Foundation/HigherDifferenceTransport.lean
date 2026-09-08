import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Foundation.TransportWord
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

/-!
# Addressed higher-difference transport

This owner keeps the chronology of a finite word of local transports while repeatedly applying
the exact shifted Leibniz law.  Its primary return is a list of occurrence-level product faces;
commuting and binomial formulas are quotients of that list, not its definition.

The reciprocal theorem assumes an inverse only on the complete successor window actually visited
by the word.  Noncommuting words, chart rebase, and receiver preimage fibres remain visible.
Nothing in this file is specific to a fluid equation or a frequency lattice.
-/

noncomputable section

open scoped BigOperators fwdDiff

namespace Soma.Holonics.HigherDifferenceTransport

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology

universe u v w x

variable {Generator : Type u} {State : Type v} {R : Type w}

/-! ## One addressed change and its chronological word -/

/-- Pull a receiver section across one addressed transport. -/
def shift (transport : Generator → State → State) (generator : Generator)
    (observable : State → R) : State → R :=
  fun state ↦ observable (transport generator state)

/-- The oriented change returned by one addressed transport. -/
def difference [Sub R] (transport : Generator → State → State) (generator : Generator)
    (observable : State → R) : State → R :=
  fun state ↦ shift transport generator observable state - observable state

/-- Repeated differences retain the order in which the generator occurrences meet the section. -/
def differenceWord [Sub R] (transport : Generator → State → State) :
    List Generator → (State → R) → State → R
  | [], observable => observable
  | generator :: word, observable =>
      difference transport generator (differenceWord transport word observable)

@[simp] theorem differenceWord_nil [Sub R] (transport : Generator → State → State)
    (observable : State → R) : differenceWord transport [] observable = observable := rfl

@[simp] theorem differenceWord_cons [Sub R] (transport : Generator → State → State)
    (generator : Generator) (word : List Generator) (observable : State → R) :
    differenceWord transport (generator :: word) observable =
      difference transport generator (differenceWord transport word observable) := rfl

/-! ## The complete product-face ledger -/

/-- Which factor received the difference at one occurrence of the product rule. -/
inductive ProductHand
  | left
  | right
  deriving DecidableEq, Repr

/-- One occurrence-level leaf of the iterated shifted Leibniz tree. -/
structure ProductFace (Generator : Type u) (State : Type v) (R : Type w) where
  /-- Generator occurrences and their factor hands, in the original word order. -/
  trail : List (Generator × ProductHand)
  /-- The transported left section at this leaf. -/
  leftSection : State → R
  /-- The transported right section at this leaf. -/
  rightSection : State → R

namespace ProductFace

/-- The receiver value of one product face. -/
def value [Mul R] (face : ProductFace Generator State R) (state : State) : R :=
  face.leftSection state * face.rightSection state

end ProductFace

/-- The branch in which the new difference meets the right factor. -/
def rightBranch [Sub R] (transport : Generator → State → State) (generator : Generator)
    (face : ProductFace Generator State R) : ProductFace Generator State R where
  trail := (generator, .right) :: face.trail
  leftSection := face.leftSection
  rightSection := difference transport generator face.rightSection

/-- The branch in which the new difference meets the left factor and shifts the right factor. -/
def leftBranch [Sub R] (transport : Generator → State → State) (generator : Generator)
    (face : ProductFace Generator State R) : ProductFace Generator State R where
  trail := (generator, .left) :: face.trail
  leftSection := difference transport generator face.leftSection
  rightSection := shift transport generator face.rightSection

/-- The exact two children returned by one shifted Leibniz occurrence.  The right branch is first,
so the unique face carrying no left difference remains the ledger head. -/
def expandFace [Sub R] (transport : Generator → State → State) (generator : Generator)
    (face : ProductFace Generator State R) : List (ProductFace Generator State R) :=
  [rightBranch transport generator face, leftBranch transport generator face]

/-- The complete occurrence population of an iterated product difference. -/
def productLedger [Sub R] (transport : Generator → State → State) :
    List Generator → (State → R) → (State → R) → List (ProductFace Generator State R)
  | [], left, right => [{ trail := [], leftSection := left, rightSection := right }]
  | generator :: word, left, right =>
      (productLedger transport word left right).flatMap (expandFace transport generator)

/-- Sum every returned product face without quotienting its occurrence trail. -/
def ledgerSum [AddMonoid R] [Mul R]
    (ledger : List (ProductFace Generator State R)) : State → R :=
  fun state ↦ (ledger.map fun face ↦ face.value state).sum

@[simp] theorem ledgerSum_nil [AddMonoid R] [Mul R] :
    ledgerSum ([] : List (ProductFace Generator State R)) = 0 := rfl

@[simp] theorem ledgerSum_cons [AddMonoid R] [Mul R]
    (face : ProductFace Generator State R) (ledger : List (ProductFace Generator State R)) :
    ledgerSum (face :: ledger) = fun state ↦ face.value state + ledgerSum ledger state := by
  rfl

/-- One returned difference obeys the shifted Leibniz law exactly. -/
theorem difference_mul [CommRing R] (transport : Generator → State → State) (generator : Generator)
    (left right : State → R) :
    difference transport generator (fun state ↦ left state * right state) =
      fun state ↦
        left state * difference transport generator right state +
          difference transport generator left state * shift transport generator right state := by
  funext state
  simp only [difference, shift]
  ring

/-- Difference distributes over the sum of an occurrence ledger and expands each product face. -/
theorem difference_ledgerSum [CommRing R]
    (transport : Generator → State → State) (generator : Generator)
    (ledger : List (ProductFace Generator State R)) :
    difference transport generator (ledgerSum ledger) =
      ledgerSum (ledger.flatMap (expandFace transport generator)) := by
  induction ledger with
  | nil =>
      funext state
      simp [difference, shift, ledgerSum]
  | cons face ledger ih =>
      funext state
      have ihState := congrFun ih state
      simp only [ledgerSum, difference, shift, List.map_cons, List.sum_cons,
        List.flatMap_cons, expandFace, rightBranch, leftBranch, ProductFace.value,
        List.map_append, List.sum_append, List.map_nil, List.sum_nil] at ihState ⊢
      linear_combination ihState

/-- The iterated product difference is exactly the sum of its complete chronological face ledger. -/
theorem differenceWord_mul_eq_ledgerSum [CommRing R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) :
    differenceWord transport word (fun state ↦ left state * right state) =
      ledgerSum (productLedger transport word left right) := by
  induction word with
  | nil =>
      funext state
      simp [productLedger, ledgerSum, ProductFace.value]
  | cons generator word ih =>
      simp only [differenceWord_cons, productLedger]
      rw [ih]
      exact difference_ledgerSum transport generator _

/-- Every face retains exactly the generator-address population of the source word. -/
theorem productLedger_retains_word [Sub R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) (face : ProductFace Generator State R)
    (hface : face ∈ productLedger transport word left right) :
    face.trail.map Prod.fst = word := by
  induction word generalizing face with
  | nil =>
      simp only [productLedger, List.mem_singleton] at hface
      subst face
      rfl
  | cons generator word ih =>
      simp only [productLedger, List.mem_flatMap] at hface
      obtain ⟨predecessor, hpredecessor, hbranch⟩ := hface
      have hword := ih predecessor hpredecessor
      simp [expandFace] at hbranch
      rcases hbranch with rfl | rfl <;>
        simp [rightBranch, leftBranch, hword]

/-- A word of `n` occurrences returns exactly `2^n` occurrence-level product faces. -/
theorem productLedger_length [Sub R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) :
    (productLedger transport word left right).length = 2 ^ word.length := by
  induction word with
  | nil => simp [productLedger]
  | cons generator word ih =>
      simp [productLedger, expandFace, ih, pow_succ, Nat.mul_comm]

/-! ## Principal reciprocal face and complete remainder -/

/-- The unique product face in which every difference meets the right factor. -/
def principalFace [Sub R] (transport : Generator → State → State) :
    List Generator → (State → R) → (State → R) → ProductFace Generator State R
  | [], left, right => { trail := [], leftSection := left, rightSection := right }
  | generator :: word, left, right =>
      rightBranch transport generator (principalFace transport word left right)

/-- Every face except the principal all-right face, retained with its complete trail. -/
def reciprocalRemainderLedger [Sub R] (transport : Generator → State → State) :
    List Generator → (State → R) → (State → R) → List (ProductFace Generator State R)
  | [], _, _ => []
  | generator :: word, left, right =>
      leftBranch transport generator (principalFace transport word left right) ::
        (reciprocalRemainderLedger transport word left right).flatMap
          (expandFace transport generator)

/-- The principal face is first and every other occurrence remains in the reciprocal remainder. -/
theorem productLedger_eq_principal_cons_remainder [Sub R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) :
    productLedger transport word left right =
      principalFace transport word left right ::
        reciprocalRemainderLedger transport word left right := by
  induction word with
  | nil => rfl
  | cons generator word ih =>
      simp only [productLedger, ih, List.flatMap_cons, principalFace,
        reciprocalRemainderLedger, expandFace]
      rfl

@[simp] theorem principalFace_leftSection [Sub R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) :
    (principalFace transport word left right).leftSection = left := by
  induction word with
  | nil => rfl
  | cons generator word ih => simp [principalFace, rightBranch, ih]

@[simp] theorem principalFace_rightSection [Sub R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) :
    (principalFace transport word left right).rightSection =
      differenceWord transport word right := by
  induction word with
  | nil => rfl
  | cons generator word ih => simp [principalFace, rightBranch, ih]

/-- The product law with the reciprocal face isolated before any annihilator is applied. -/
theorem differenceWord_mul_eq_principal_add_remainder [CommRing R]
    (transport : Generator → State → State) (word : List Generator)
    (left right : State → R) (state : State) :
    differenceWord transport word (fun current ↦ left current * right current) state =
      left state * differenceWord transport word right state +
        ledgerSum (reciprocalRemainderLedger transport word left right) state := by
  rw [differenceWord_mul_eq_ledgerSum, productLedger_eq_principal_cons_remainder]
  simp [ProductFace.value]

/-! ## The exact successor window and local inverse recurrence -/

/-- The occurrence population at which a word evaluates its receiver section.  Multiplicity and
order are retained; this is not coerced to a set of endpoints. -/
def successorWindow (transport : Generator → State → State) : List Generator → State → List State
  | [], state => [state]
  | generator :: word, state =>
      successorWindow transport word (transport generator state) ++
        successorWindow transport word state

/-- Two sections are inverse on every occurrence visited by one addressed word. -/
def LocalInverse [Mul R] [One R] (transport : Generator → State → State)
    (word : List Generator) (left right : State → R) (state : State) : Prop :=
  ∀ current ∈ successorWindow transport word state, left current * right current = 1

/-- A nonempty difference word annihilates a section which is one on its complete successor
window. -/
theorem differenceWord_eq_zero_of_one_on_successorWindow [CommRing R]
    (transport : Generator → State → State) (word : List Generator)
    (observable : State → R) (state : State) (hword : word ≠ [])
    (hone : ∀ current ∈ successorWindow transport word state, observable current = 1) :
    differenceWord transport word observable state = 0 := by
  induction word generalizing state with
  | nil => exact (hword rfl).elim
  | cons generator word ih =>
      cases word with
      | nil =>
          have htransport : observable (transport generator state) = 1 := by
            apply hone
            simp [successorWindow]
          have hstate : observable state = 1 := by
            apply hone
            simp [successorWindow]
          simp [differenceWord, difference, shift, htransport, hstate]
      | cons next rest =>
          have honeTransport :
              ∀ current ∈ successorWindow transport (next :: rest)
                  (transport generator state), observable current = 1 := by
            intro current hcurrent
            exact hone current (List.mem_append_left _ hcurrent)
          have honeState :
              ∀ current ∈ successorWindow transport (next :: rest) state,
                observable current = 1 := by
            intro current hcurrent
            exact hone current (List.mem_append_right _ hcurrent)
          have hleft := ih (transport generator state) (by simp) honeTransport
          have hright := ih state (by simp) honeState
          change
            differenceWord transport (next :: rest) observable (transport generator state) -
                differenceWord transport (next :: rest) observable state = 0
          rw [hleft, hright]
          exact sub_self 0

/-- The local reciprocal recurrence: the principal all-right face is forced by the complete
nonempty-left remainder, with no inverse assumed outside the successor window. -/
theorem localReciprocal_recurrence [CommRing R]
    (transport : Generator → State → State) (word : List Generator)
    (denominator reciprocal : State → R) (state : State) (hword : word ≠ [])
    (hinverse : LocalInverse transport word denominator reciprocal state) :
    denominator state * differenceWord transport word reciprocal state =
      -ledgerSum (reciprocalRemainderLedger transport word denominator reciprocal) state := by
  have hzero :
      differenceWord transport word
        (fun current ↦ denominator current * reciprocal current) state = 0 :=
    differenceWord_eq_zero_of_one_on_successorWindow transport word _ state hword hinverse
  have hexpanded := differenceWord_mul_eq_principal_add_remainder
    transport word denominator reciprocal state
  have hsum :
      denominator state * differenceWord transport word reciprocal state +
          ledgerSum (reciprocalRemainderLedger transport word denominator reciprocal) state = 0 :=
    hexpanded.symm.trans hzero
  calc
    denominator state * differenceWord transport word reciprocal state =
        denominator state * differenceWord transport word reciprocal state +
            ledgerSum (reciprocalRemainderLedger transport word denominator reciprocal) state -
              ledgerSum (reciprocalRemainderLedger transport word denominator reciprocal) state := by
                ring
    _ = 0 - ledgerSum
          (reciprocalRemainderLedger transport word denominator reciprocal) state := by rw [hsum]
    _ = -ledgerSum
          (reciprocalRemainderLedger transport word denominator reciprocal) state := by ring

/-! ## Interchange is the chronology-forgetting quotient -/

/-- Exact interchange for every addressed generator pair. -/
def InterchangeReceipt (transport : Generator → State → State) : Prop :=
  ∀ first second state,
    transport first (transport second state) = transport second (transport first state)

/-- Exact interchange makes addressed difference operators commute. -/
theorem difference_commutes_of_interchange [CommRing R]
    (transport : Generator → State → State) (h : InterchangeReceipt transport)
    (first second : Generator) (observable : State → R) :
    difference transport first (difference transport second observable) =
      difference transport second (difference transport first observable) := by
  funext state
  simp only [difference, shift]
  rw [h first second state]
  ring

/-- Under exact interchange, a difference word depends only on its occurrence multiset. -/
theorem differenceWord_eq_of_perm [CommRing R]
    (transport : Generator → State → State) (h : InterchangeReceipt transport)
    {first second : List Generator} (permutation : first.Perm second) (observable : State → R) :
    differenceWord transport first observable = differenceWord transport second observable := by
  induction permutation with
  | nil => rfl
  | cons generator permutation ih => simp [differenceWord, ih]
  | swap first second word =>
      simp only [differenceWord]
      exact (difference_commutes_of_interchange (R := R) transport h first second
        (differenceWord transport word observable)).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The chronological ledger descends to the same total product face for permuted words only after
an interchange receipt is supplied. -/
theorem productLedgerSum_eq_of_perm [CommRing R]
    (transport : Generator → State → State) (h : InterchangeReceipt transport)
    {first second : List Generator} (permutation : first.Perm second)
    (left right : State → R) :
    ledgerSum (productLedger transport first left right) =
      ledgerSum (productLedger transport second left right) := by
  rw [← differenceWord_mul_eq_ledgerSum, ← differenceWord_mul_eq_ledgerSum]
  exact differenceWord_eq_of_perm transport h permutation _

/-! ## A finite noncommuting control -/

namespace NoncommutingControl

inductive ControlGenerator
  | flip
  | erase
  deriving DecidableEq, Repr

def transport : ControlGenerator → Bool → Bool
  | .flip, state => !state
  | .erase, _ => false

def receiver : Bool → ℤ
  | false => 0
  | true => 1

/-- The two generator orders return different second differences at the same addressed state. -/
theorem chronology_free_collapse_fails :
    differenceWord transport [.flip, .erase] receiver false = -1 ∧
      differenceWord transport [.erase, .flip] receiver false = 0 := by
  decide

/-- Consequently the control has no exact interchange receipt. -/
theorem no_interchange_receipt : ¬ InterchangeReceipt transport := by
  intro h
  have hs := differenceWord_eq_of_perm transport h
    (List.Perm.swap ControlGenerator.flip ControlGenerator.erase []) receiver
  have hvalue := congrFun hs false
  have hcontrol := chronology_free_collapse_fails
  omega

end NoncommutingControl

/-! ## Rebase and receiver fibres -/

/-- Generator-local chart conjugacy transports every higher-difference word naturally. -/
theorem differenceWord_rebase [CommRing R]
    {Rebased : Type x} (sourceTransport : Generator → State → State)
    (targetTransport : Generator → Rebased → Rebased) (chart : State ≃ Rebased)
    (generatorExact : ∀ generator state,
      chart (sourceTransport generator state) = targetTransport generator (chart state))
    (word : List Generator) (observable : Rebased → R) (state : State) :
    differenceWord sourceTransport word (fun current ↦ observable (chart current)) state =
      differenceWord targetTransport word observable (chart state) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word ih =>
      simp only [differenceWord, difference, shift]
      rw [ih (sourceTransport generator state), ih state,
        generatorExact generator state]

/-- The complete source population retained behind one quotient face. -/
def preimageFibre {Quotient : Type x}
    (compression : Compression (List Generator) State Quotient R) (quotient : Quotient) : Type _ :=
  { state : State // compression.quotient state = quotient }

/-- Equal quotient faces place both source occurrences in one retained preimage fibre. -/
theorem quotientEq_places_in_preimageFibre {Quotient : Type x}
    (compression : Compression (List Generator) State Quotient R) {left right : State}
    (h : compression.quotient left = compression.quotient right) :
    ∃ leftIn rightIn : preimageFibre compression (compression.quotient left),
      leftIn.1 = left ∧ rightIn.1 = right :=
  ⟨⟨left, rfl⟩, ⟨right, h.symm⟩, rfl, rfl⟩

/-- A richer higher-difference receiver word constructively reopens any proposed quotient which
would collapse two states it separates. -/
theorem separatingDifferenceWord_reopens_quotient [Sub R] {Quotient : Type x}
    (transport : Generator → State → State) (observable : State → R)
    (compression : Compression (List Generator) State Quotient R)
    (receiverExact : ∀ word state,
      compression.receiver word state = differenceWord transport word observable state)
    {left right : State} (word : List Generator)
    (separates : differenceWord transport word observable left ≠
      differenceWord transport word observable right) :
    compression.quotient left ≠ compression.quotient right := by
  intro hquotient
  have hreceiver := compression.receiver_eq_of_quotient_eq hquotient word
  rw [receiverExact word left, receiverExact word right] at hreceiver
  exact separates hreceiver

/-! ## The existing bounded one-path quotient -/

/-- The exact shifted binomial product formula through the presently required order six. -/
theorem fwdDiff_iter_mul_eq_sum_choose_through_six
    (left right : ℕ → ℂ) (order : ℕ) (horder : order ≤ 6) (start : ℕ) :
    (fwdDiff 1)^[order] (fun index ↦ left index * right index) start =
      ∑ derivative ∈ Finset.range (order + 1),
        (order.choose derivative : ℂ) *
          (fwdDiff 1)^[derivative] left start *
          (fwdDiff 1)^[order - derivative] right (start + derivative) := by
  interval_cases order <;>
    norm_num [Finset.sum_range_succ, Nat.choose, fwdDiff, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] <;> ring

/-- Local inverse sections make every positive product difference through order six vanish. -/
theorem fwdDiff_iter_mul_eq_zero_of_local_inverse_through_six
    (left right : ℕ → ℂ) (order : ℕ)
    (hpositive : 1 ≤ order) (horder : order ≤ 6) (start : ℕ)
    (hinverse : ∀ offset ≤ order,
      left (start + offset) * right (start + offset) = 1) :
    (fwdDiff 1)^[order] (fun index ↦ left index * right index) start = 0 := by
  have hbase : left start * right start = 1 := by
    simpa using hinverse 0 (Nat.zero_le order)
  interval_cases order <;>
    simp_all [fwdDiff, Nat.add_comm, Nat.add_left_comm]

/-- The bounded shifted-binomial reciprocal recurrence. -/
theorem reciprocalDifference_recurrence_through_six
    (denominator reciprocal : ℕ → ℂ) (order : ℕ)
    (hpositive : 1 ≤ order) (horder : order ≤ 6) (start : ℕ)
    (hinverse : ∀ offset ≤ order,
      denominator (start + offset) * reciprocal (start + offset) = 1) :
    denominator start * (fwdDiff 1)^[order] reciprocal start =
      -∑ derivative ∈ Finset.range order,
        (order.choose (derivative + 1) : ℂ) *
          (fwdDiff 1)^[derivative + 1] denominator start *
          (fwdDiff 1)^[order - (derivative + 1)] reciprocal
            (start + (derivative + 1)) := by
  have hproduct := fwdDiff_iter_mul_eq_sum_choose_through_six
    denominator reciprocal order horder start
  have hzero := fwdDiff_iter_mul_eq_zero_of_local_inverse_through_six
    denominator reciprocal order hpositive horder start hinverse
  rw [hproduct] at hzero
  interval_cases order <;>
    norm_num [Finset.sum_range_succ, Nat.choose] at hzero ⊢ <;>
    linear_combination hzero

/-- Once a path has zero third difference, its fourth through sixth differences vanish. -/
theorem higher_differences_eq_zero_of_third
    (denominator : ℕ → ℂ) (hthird : (fwdDiff 1)^[3] denominator = 0) :
    (fwdDiff 1)^[4] denominator = 0 ∧
      (fwdDiff 1)^[5] denominator = 0 ∧
      (fwdDiff 1)^[6] denominator = 0 := by
  have h4 : (fwdDiff 1)^[4] denominator = 0 := by
    rw [show 4 = 1 + 3 by norm_num, Function.iterate_add_apply, hthird]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  have h5 : (fwdDiff 1)^[5] denominator = 0 := by
    rw [show 5 = 1 + 4 by norm_num, Function.iterate_add_apply, h4]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  have h6 : (fwdDiff 1)^[6] denominator = 0 := by
    rw [show 6 = 1 + 5 by norm_num, Function.iterate_add_apply, h5]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  exact ⟨h4, h5, h6⟩

/-- A locally invertible quadratic denominator leaves exactly its first and second faces in the
sixth reciprocal recurrence. -/
theorem quadraticReciprocal_sixthDifference_recurrence
    (denominator reciprocal : ℕ → ℂ) (start : ℕ)
    (hinverse : ∀ offset ≤ 6,
      denominator (start + offset) * reciprocal (start + offset) = 1)
    (hthird : (fwdDiff 1)^[3] denominator = 0) :
    denominator start * (fwdDiff 1)^[6] reciprocal start =
      -(6 * fwdDiff 1 denominator start *
          (fwdDiff 1)^[5] reciprocal (start + 1) +
        15 * (fwdDiff 1)^[2] denominator start *
          (fwdDiff 1)^[4] reciprocal (start + 2)) := by
  have hrecurrence := reciprocalDifference_recurrence_through_six
    denominator reciprocal 6 (by norm_num) (by norm_num) start hinverse
  obtain ⟨h4, h5, h6⟩ := higher_differences_eq_zero_of_third denominator hthird
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, Function.iterate_zero_apply,
    Function.iterate_one, add_zero, zero_add] at hrecurrence
  rw [hthird, h4, h5, h6] at hrecurrence
  simpa only [Pi.zero_apply, mul_zero, zero_mul, add_zero] using hrecurrence

/-! ## The `(2,2,2)` commuting allocation receiver -/

/-- After quotienting two repeated differences on each of three commuting axes, each axis records
only whether zero, one, or two differences met the left factor. -/
abbrev ThreeAxisSecondOrderAllocation := Fin 3 → Fin 3

/-- Read one product-rule hand as the number of differences assigned to the left factor. -/
def ProductHand.leftOrder : ProductHand → ℕ
  | .left => 1
  | .right => 0

/-- Read one occurrence hand from a ledger trail.  The default is used only outside a declared
six-occurrence receiver aperture. -/
def ProductFace.handAt (face : ProductFace Generator State R) (index : ℕ) : ProductHand :=
  match face.trail[index]? with
  | some (_, hand) => hand
  | none => .right

/-- Two repeated occurrences on one commuting axis quotient to derivative order zero, one, or
two. -/
def pairedLeftOrder (first second : ProductHand) : Fin 3 := by
  refine ⟨first.leftOrder + second.leftOrder, ?_⟩
  cases first <;> cases second <;> decide

/-- The explicit receiver from a six-occurrence product face to the `(2,2,2)` multi-index.  Axis
`a` reads the two hands at positions `2a` and `2a+1`. -/
def secondOrderAllocationReceiver (face : ProductFace Generator State R) :
    ThreeAxisSecondOrderAllocation :=
  fun axis ↦ pairedLeftOrder (face.handAt (2 * axis.val)) (face.handAt (2 * axis.val + 1))

/-- The commuting `(2,2,2)` receiver has exactly `3^3 = 27` allocation faces. -/
theorem threeAxisSecondOrderAllocation_card :
    Fintype.card ThreeAxisSecondOrderAllocation = 27 := by
  native_decide

end Soma.Holonics.HigherDifferenceTransport

section Audit
open Soma.Holonics.HigherDifferenceTransport
#print axioms differenceWord_mul_eq_ledgerSum
#print axioms localReciprocal_recurrence
#print axioms differenceWord_eq_of_perm
#print axioms NoncommutingControl.no_interchange_receipt
#print axioms differenceWord_rebase
#print axioms separatingDifferenceWord_reopens_quotient
#print axioms quadraticReciprocal_sixthDifference_recurrence
#print axioms threeAxisSecondOrderAllocation_card
end Audit
