import ElementaryHolonics.Foundation.HigherDifferenceScaleDescent
import ElementaryHolonics.Millennium.NavierStokesQuadraticAnnihilatorLedger

/-!
# Three-axis scale descent for the quadratic Hodge reciprocal

HD1 retains nine nonzero occurrence faces in the six-letter word `(0,0,1,1,2,2)`.  This file
first groups those occurrences without forgetting their shifted receiver states.  The resulting
six-term recurrence is the top edge of the well-founded mixed-order descent
`11 -> 111 -> 112 -> 122 -> 222`.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.HigherDifferenceAnnihilator
open Soma.Holonics.HigherDifferenceScaleDescent
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesQuadraticAnnihilatorLedger

/-- Removing one occurrence of an axis from `(0,0,1,1,2,2)` leaves a word of strict order five. -/
def secondEachAxisRemoveOne : Fin 3 → List (Fin 3)
  := ![[0, 1, 1, 2, 2], [0, 0, 1, 2, 2], [0, 0, 1, 1, 2]]

/-- Removing both occurrences of one axis leaves a word of strict order four. -/
def secondEachAxisRemoveTwo : Fin 3 → List (Fin 3)
  := ![[1, 1, 2, 2], [0, 0, 2, 2], [0, 0, 1, 1]]

theorem secondEachAxisRemoveOne_length (axis : Fin 3) :
    (secondEachAxisRemoveOne axis).length = 5 := by
  fin_cases axis <;> rfl

theorem secondEachAxisRemoveTwo_length (axis : Fin 3) :
    (secondEachAxisRemoveTwo axis).length = 4 := by
  fin_cases axis <;> rfl

/-- The first genuinely three-axis predecessor word. -/
def oneEachAxisWord : List (Fin 3) := [0, 1, 2]

/-- One difference in every axis and a second occurrence in the addressed doubled axis. -/
def oneOneTwoWord : Fin 3 → List (Fin 3) :=
  ![[0, 0, 1, 2], [0, 1, 1, 2], [0, 1, 2, 2]]

/-- One occurrence in the addressed single axis and two in each transverse axis. -/
def oneTwoTwoWord : Fin 3 → List (Fin 3) :=
  ![[0, 1, 1, 2, 2], [0, 0, 1, 2, 2], [0, 0, 1, 1, 2]]

theorem oneEachAxisWord_length : oneEachAxisWord.length = 3 := by rfl

theorem oneOneTwoWord_length (axis : Fin 3) : (oneOneTwoWord axis).length = 4 := by
  fin_cases axis <;> rfl

theorem oneTwoTwoWord_length (axis : Fin 3) : (oneTwoTwoWord axis).length = 5 := by
  fin_cases axis <;> rfl

/-- The quadratic reciprocal remainder for any displayed predecessor word. -/
def hodgeQuadraticWordRemainderLedger (word : List (Fin 3)) :
    List (ProductFace (Fin 3) SpatialFrequency ℂ) :=
  reciprocalRemainderLedger coordinateTransport word
    (fun frequency ↦ (frequencySquared frequency : ℂ)) hodgeReciprocal

/-- The order-three word retains only its three first-denominator faces. -/
theorem hodgeOneEachRemainder_zero_of_inactive (frequency : SpatialFrequency) :
    ∀ face ∈ hodgeQuadraticWordRemainderLedger oneEachAxisWord,
      quadraticDenominatorActive face = false → face.value frequency = 0 := by
  simp [hodgeQuadraticWordRemainderLedger, oneEachAxisWord, reciprocalRemainderLedger,
    principalFace, expandFace, rightBranch, leftBranch, denominatorDifferenceAxes,
    quadraticDenominatorActive, ProductFace.value, difference, shift, coordinateTransport,
    coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- The order-four family retains four first faces and the one same-axis second face. -/
theorem hodgeOneOneTwoRemainder_zero_of_inactive
    (doubled : Fin 3) (frequency : SpatialFrequency) :
    ∀ face ∈ hodgeQuadraticWordRemainderLedger (oneOneTwoWord doubled),
      quadraticDenominatorActive face = false → face.value frequency = 0 := by
  fin_cases doubled <;>
    simp [hodgeQuadraticWordRemainderLedger, oneOneTwoWord, reciprocalRemainderLedger,
      principalFace, expandFace, rightBranch, leftBranch, denominatorDifferenceAxes,
      quadraticDenominatorActive, ProductFace.value, difference, shift, coordinateTransport,
      coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- The order-five family retains five first faces and the two same-axis second faces. -/
theorem hodgeOneTwoTwoRemainder_zero_of_inactive
    (single : Fin 3) (frequency : SpatialFrequency) :
    ∀ face ∈ hodgeQuadraticWordRemainderLedger (oneTwoTwoWord single),
      quadraticDenominatorActive face = false → face.value frequency = 0 := by
  fin_cases single <;>
    simp [hodgeQuadraticWordRemainderLedger, oneTwoTwoWord, reciprocalRemainderLedger,
      principalFace, expandFace, rightBranch, leftBranch, denominatorDifferenceAxes,
      quadraticDenominatorActive, ProductFace.value, difference, shift, coordinateTransport,
      coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- Proof-bearing active certificates for the three strict predecessor stages. -/
def hodgeOneEachAnnihilatorCertificate (frequency : SpatialFrequency) :
    AnnihilatorCertificate (hodgeQuadraticWordRemainderLedger oneEachAxisWord) frequency where
  active := quadraticDenominatorActive
  zero_of_inactive := hodgeOneEachRemainder_zero_of_inactive frequency

def hodgeOneOneTwoAnnihilatorCertificate
    (doubled : Fin 3) (frequency : SpatialFrequency) :
    AnnihilatorCertificate
      (hodgeQuadraticWordRemainderLedger (oneOneTwoWord doubled)) frequency where
  active := quadraticDenominatorActive
  zero_of_inactive := hodgeOneOneTwoRemainder_zero_of_inactive doubled frequency

def hodgeOneTwoTwoAnnihilatorCertificate
    (single : Fin 3) (frequency : SpatialFrequency) :
    AnnihilatorCertificate
      (hodgeQuadraticWordRemainderLedger (oneTwoTwoWord single)) frequency where
  active := quadraticDenominatorActive
  zero_of_inactive := hodgeOneTwoTwoRemainder_zero_of_inactive single frequency

theorem hodgeOneEach_activeLedger_length (frequency : SpatialFrequency) :
    (hodgeOneEachAnnihilatorCertificate frequency).activeLedger.length = 3 := by rfl

theorem hodgeOneOneTwo_activeLedger_length
    (doubled : Fin 3) (frequency : SpatialFrequency) :
    (hodgeOneOneTwoAnnihilatorCertificate doubled frequency).activeLedger.length = 5 := by
  fin_cases doubled <;> rfl

theorem hodgeOneTwoTwo_activeLedger_length
    (single : Fin 3) (frequency : SpatialFrequency) :
    (hodgeOneTwoTwoAnnihilatorCertificate single frequency).activeLedger.length = 7 := by
  fin_cases single <;> rfl

/-- Any proof-bearing quadratic word certificate feeds the local reciprocal recurrence on exactly
its declared successor population. -/
theorem hodgeReciprocal_word_activeRecurrence
    (word : List (Fin 3)) (hword : word ≠ [])
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport word frequency,
      frequencySquared current ≠ 0)
    (certificate : AnnihilatorCertificate
      (hodgeQuadraticWordRemainderLedger word) frequency) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport word hodgeReciprocal frequency =
      -ledgerSum certificate.activeLedger frequency := by
  rw [← ledgerSum_eq_activeLedger certificate]
  refine localReciprocal_recurrence coordinateTransport word
    (fun current ↦ (frequencySquared current : ℂ)) hodgeReciprocal frequency hword ?_
  intro current hcurrent
  have hcomplex : ((frequencySquared current : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hnonzero current hcurrent)
  simp only [hodgeReciprocal, one_div]
  exact mul_inv_cancel₀ hcomplex

theorem hodgeReciprocal_oneEach_activeRecurrence
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport oneEachAxisWord frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency =
      -ledgerSum (hodgeOneEachAnnihilatorCertificate frequency).activeLedger frequency :=
  hodgeReciprocal_word_activeRecurrence oneEachAxisWord (by decide) frequency hnonzero
    (hodgeOneEachAnnihilatorCertificate frequency)

theorem hodgeReciprocal_oneOneTwo_activeRecurrence
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneOneTwoWord doubled) frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneOneTwoWord doubled) hodgeReciprocal frequency =
      -ledgerSum
        (hodgeOneOneTwoAnnihilatorCertificate doubled frequency).activeLedger frequency := by
  apply hodgeReciprocal_word_activeRecurrence (oneOneTwoWord doubled)
  · intro hempty
    have hlength := oneOneTwoWord_length doubled
    rw [hempty] at hlength
    simp at hlength
  · exact hnonzero

theorem hodgeReciprocal_oneTwoTwo_activeRecurrence
    (single : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneTwoTwoWord single) frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneTwoTwoWord single) hodgeReciprocal frequency =
      -ledgerSum
        (hodgeOneTwoTwoAnnihilatorCertificate single frequency).activeLedger frequency := by
  apply hodgeReciprocal_word_activeRecurrence (oneTwoTwoWord single)
  · intro hempty
    have hlength := oneTwoTwoWord_length single
    rw [hempty] at hlength
    simp at hlength
  · exact hnonzero

/-- The six grouped active terms retain the translated receiver at which every lower reciprocal
word is read.  The coefficients `2,1` are occurrence multiplicities, not inserted binomial
shorthand. -/
def hodgeQuadraticGroupedActiveReturn (frequency : SpatialFrequency) : ℂ :=
  ∑ axis : Fin 3, (
    2 * differenceWord coordinateTransport [axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
          (coordinateTransport axis frequency) +
      differenceWord coordinateTransport [axis, axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
          (coordinateTransport axis (coordinateTransport axis frequency)))

/-- The nine active occurrence faces group exactly into six shifted lower-order terms. -/
theorem hodgeQuadratic_activeLedgerSum_eq_groupedReturn
    (frequency : SpatialFrequency) :
    ledgerSum (hodgeQuadraticAnnihilatorCertificate frequency).activeLedger frequency =
      hodgeQuadraticGroupedActiveReturn frequency := by
  simp [hodgeQuadraticAnnihilatorCertificate, AnnihilatorCertificate.activeLedger,
    hodgeQuadraticRemainderLedger, secondEachAxisWord, reciprocalRemainderLedger,
    principalFace, expandFace, rightBranch, leftBranch, quadraticDenominatorActive,
    denominatorDifferenceAxes, ledgerSum, ProductFace.value,
    hodgeQuadraticGroupedActiveReturn,
    secondEachAxisRemoveOne, secondEachAxisRemoveTwo, Fin.sum_univ_succ,
    difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
    shift]
  ring

/-- The two grouped predecessor faces owned by one coordinate axis. -/
def hodge222StrictOrderFaces (frequency : SpatialFrequency) (axis : Fin 3) :
    List (StrictOrderFace SpatialFrequency ℂ 6) :=
  [{ predecessor := ⟨5, by omega⟩
     successor := coordinateTransport axis frequency
     multiplicity := 2
     coefficient := 2 * differenceWord coordinateTransport [axis]
       (fun current ↦ (frequencySquared current : ℂ)) frequency
     lowerSection := differenceWord coordinateTransport (secondEachAxisRemoveOne axis)
       hodgeReciprocal },
   { predecessor := ⟨4, by omega⟩
     successor := coordinateTransport axis (coordinateTransport axis frequency)
     multiplicity := 1
     coefficient := differenceWord coordinateTransport [axis, axis]
       (fun current ↦ (frequencySquared current : ℂ)) frequency
     lowerSection := differenceWord coordinateTransport (secondEachAxisRemoveTwo axis)
       hodgeReciprocal }]

/-- The six grouped faces remain an addressed strict-order ledger; the nine-to-six passage groups
only equal occurrence returns and retains their multiplicities `2,1` on each axis. -/
def hodge222StrictOrderLedger (frequency : SpatialFrequency) :
    List (StrictOrderFace SpatialFrequency ℂ 6) :=
  hodge222StrictOrderFaces frequency 0 ++
    hodge222StrictOrderFaces frequency 1 ++
      hodge222StrictOrderFaces frequency 2

theorem hodge222StrictOrderLedger_length (frequency : SpatialFrequency) :
    (hodge222StrictOrderLedger frequency).length = 6 := by
  rfl

/-- The generic strict-order owner returns exactly the grouped active Hodge recurrence. -/
theorem hodge222StrictOrderReturn_eq_groupedActiveReturn
    (frequency : SpatialFrequency) :
    strictOrderReturn (hodge222StrictOrderLedger frequency) =
      hodgeQuadraticGroupedActiveReturn frequency := by
  simp [hodge222StrictOrderLedger, hodge222StrictOrderFaces, strictOrderReturn,
    StrictOrderFace.value, hodgeQuadraticGroupedActiveReturn,
    secondEachAxisRemoveOne, secondEachAxisRemoveTwo]
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  simp
  ring

/-- Exact top recurrence of the three-axis descent.  Every right-hand term has reciprocal order
four or five and is read on the shifted successor subwindow returned by its denominator face. -/
theorem hodgeReciprocal_secondEachAxis_groupedRecurrence
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport secondEachAxisWord frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency =
      -hodgeQuadraticGroupedActiveReturn frequency := by
  rw [hodgeReciprocal_secondEachAxis_activeRecurrence frequency hnonzero,
    hodgeQuadratic_activeLedgerSum_eq_groupedReturn]

/-! ## The strict lower-order envelope carried by the grouped return -/

/-- One certificate controls all three fifth-order and all three fourth-order shifted successors.
The word-length theorems above prove that both fields are strict predecessors of order six. -/
structure Hodge222LowerOrderEnvelope
    (frequency : SpatialFrequency) (fifthBound fourthBound : ℝ) : Prop where
  fifth : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
      (coordinateTransport axis frequency)‖ ≤ fifthBound
  fourth : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
      (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤ fourthBound

/-- A first difference of the quadratic denominator has the genuine linear coordinate envelope. -/
theorem norm_hodgeDenominator_singleDifference_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound) :
    ‖differenceWord coordinateTransport [axis]
      (fun current ↦ (frequencySquared current : ℂ)) frequency‖ ≤ 2 * bound + 1 := by
  simp only [differenceWord, difference, shift, coordinateTransport]
  rw [show frequency + coordinateStep axis =
      incrementFrequencyCoordinate axis frequency by
    exact add_coordinateStep_eq_increment axis frequency]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_frequencySquared_increment_sub_le hbound frequency hcoordinates axis

/-- Every same-axis second denominator face is exactly the constant two. -/
theorem hodgeDenominator_sameAxis_secondDifference_eq_two
    (axis : Fin 3) (frequency : SpatialFrequency) :
    differenceWord coordinateTransport [axis, axis]
      (fun current ↦ (frequencySquared current : ℂ)) frequency = 2 := by
  fin_cases axis <;>
    simp [differenceWord, difference, shift, coordinateTransport, coordinateStep,
      frequencySquared, Fin.sum_univ_succ] <;> ring

theorem norm_hodgeDenominator_sameAxis_secondDifference
    (axis : Fin 3) (frequency : SpatialFrequency) :
    ‖differenceWord coordinateTransport [axis, axis]
      (fun current ↦ (frequencySquared current : ℂ)) frequency‖ = 2 := by
  rw [hodgeDenominator_sameAxis_secondDifference_eq_two]
  norm_num

/-! ## A genuine three-axis successor aperture -/

/-- The addressed point in a finite three-axis forward stencil. -/
def threeAxisStencilPoint
    (first second third : Fin 3) (frequency : SpatialFrequency) (i j k : ℕ) :
    SpatialFrequency :=
  frequency + i • coordinateStep first + j • coordinateStep second +
    k • coordinateStep third

/-- Denominator and coordinate control on the complete addressed three-axis population. -/
def ThreeAxisStencilControlled
    (lower bound : ℝ) (first second third : Fin 3) (frequency : SpatialFrequency)
    (firstOrder secondOrder thirdOrder : ℕ) : Prop :=
  ∀ i ≤ firstOrder, ∀ j ≤ secondOrder, ∀ k ≤ thirdOrder,
    lower ≤ frequencySquared (threeAxisStencilPoint first second third frequency i j k) ∧
      ∀ other : Fin 3,
        ‖(threeAxisStencilPoint first second third frequency i j k other : ℂ)‖ ≤ bound

@[simp]
theorem threeAxisStencilPoint_zero_zero_zero
    (first second third : Fin 3) (frequency : SpatialFrequency) :
    threeAxisStencilPoint first second third frequency 0 0 0 = frequency := by
  simp [threeAxisStencilPoint]

/-- A translated sub-box inherits the exact aperture of its parent box. -/
theorem ThreeAxisStencilControlled.rebase
    {lower bound : ℝ} {first second third : Fin 3} {frequency : SpatialFrequency}
    {firstTotal secondTotal thirdTotal firstOffset secondOffset thirdOffset
      firstOrder secondOrder thirdOrder : ℕ}
    (hstencil : ThreeAxisStencilControlled lower bound first second third frequency
      firstTotal secondTotal thirdTotal)
    (hfirst : firstOffset + firstOrder ≤ firstTotal)
    (hsecond : secondOffset + secondOrder ≤ secondTotal)
    (hthird : thirdOffset + thirdOrder ≤ thirdTotal) :
    ThreeAxisStencilControlled lower bound first second third
      (threeAxisStencilPoint first second third frequency
        firstOffset secondOffset thirdOffset)
      firstOrder secondOrder thirdOrder := by
  intro i hi j hj k hk
  have hpoint :
      threeAxisStencilPoint first second third
          (threeAxisStencilPoint first second third frequency
            firstOffset secondOffset thirdOffset) i j k =
        threeAxisStencilPoint first second third frequency
          (firstOffset + i) (secondOffset + j) (thirdOffset + k) := by
    unfold threeAxisStencilPoint
    rw [add_nsmul, add_nsmul, add_nsmul]
    abel
  rw [hpoint]
  exact hstencil (firstOffset + i) (by omega)
    (secondOffset + j) (by omega) (thirdOffset + k) (by omega)

/-- Every occurrence in the successor window of a three-block word is an addressed point of the
corresponding finite stencil.  Multiplicity remains in the source list; this theorem only supplies
the receiver factorization needed by an aperture. -/
theorem mem_successorWindow_threeAxisBox
    (first second third : Fin 3) (firstOrder secondOrder thirdOrder : ℕ)
    (frequency current : SpatialFrequency)
    (hcurrent : current ∈ successorWindow coordinateTransport
      (List.replicate firstOrder first ++ List.replicate secondOrder second ++
        List.replicate thirdOrder third) frequency) :
    ∃ i ≤ firstOrder, ∃ j ≤ secondOrder, ∃ k ≤ thirdOrder,
      current = threeAxisStencilPoint first second third frequency i j k := by
  induction firstOrder generalizing frequency current with
  | zero =>
      simp only [List.replicate_zero, List.nil_append] at hcurrent
      induction secondOrder generalizing frequency current with
      | zero =>
          simp only [List.replicate_zero, List.nil_append] at hcurrent
          induction thirdOrder generalizing frequency current with
          | zero =>
              simp [successorWindow] at hcurrent
              subst current
              exact ⟨0, by omega, 0, by omega, 0, by omega, by
                simp [threeAxisStencilPoint]⟩
          | succ thirdOrder ih =>
              simp only [List.replicate_succ, successorWindow, List.mem_append] at hcurrent
              rcases hcurrent with hcurrent | hcurrent
              · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
                  ih (frequency := coordinateTransport third frequency)
                    (current := current) hcurrent
                refine ⟨i, by omega, j, by omega, k + 1, by omega, ?_⟩
                unfold threeAxisStencilPoint coordinateTransport
                rw [add_nsmul, one_nsmul]
                abel
              · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
                  ih (frequency := frequency) (current := current) hcurrent
                exact ⟨i, by omega, j, by omega, k, by omega, rfl⟩
      | succ secondOrder ih =>
          simp only [List.replicate_succ, List.cons_append, successorWindow,
            List.mem_append] at hcurrent
          rcases hcurrent with hcurrent | hcurrent
          · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
              ih (frequency := coordinateTransport second frequency)
                (current := current) hcurrent
            refine ⟨i, by omega, j + 1, by omega, k, by omega, ?_⟩
            unfold threeAxisStencilPoint coordinateTransport
            rw [add_nsmul, one_nsmul]
            abel
          · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
              ih (frequency := frequency) (current := current) hcurrent
            exact ⟨i, by omega, j, by omega, k, by omega, rfl⟩
  | succ firstOrder ih =>
      simp only [List.replicate_succ, List.cons_append, successorWindow,
        List.mem_append] at hcurrent
      rcases hcurrent with hcurrent | hcurrent
      · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
          ih (frequency := coordinateTransport first frequency)
            (current := current) hcurrent
        refine ⟨i + 1, by omega, j, by omega, k, by omega, ?_⟩
        unfold threeAxisStencilPoint coordinateTransport
        rw [add_nsmul, one_nsmul]
        abel
      · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
          ih (frequency := frequency) (current := current) hcurrent
        exact ⟨i, by omega, j, by omega, k, by omega, rfl⟩

/-- A positive controlled stencil makes the complete successor population of its block word
nonzero. -/
theorem ThreeAxisStencilControlled.successor_nonzero
    {lower bound : ℝ} (hlower : 0 < lower)
    {first second third : Fin 3} {frequency : SpatialFrequency}
    {firstOrder secondOrder thirdOrder : ℕ}
    (hstencil : ThreeAxisStencilControlled lower bound first second third frequency
      firstOrder secondOrder thirdOrder) :
    ∀ current ∈ successorWindow coordinateTransport
      (List.replicate firstOrder first ++ List.replicate secondOrder second ++
        List.replicate thirdOrder third) frequency,
      frequencySquared current ≠ 0 := by
  intro current hcurrent
  obtain ⟨i, hi, j, hj, k, hk, rfl⟩ :=
    mem_successorWindow_threeAxisBox first second third
      firstOrder secondOrder thirdOrder frequency current hcurrent
  exact (hlower.trans_le (hstencil i hi j hj k hk).1).ne'

/-- Fixing the first coordinate leaves the genuine second/third two-axis stencil. -/
theorem ThreeAxisStencilControlled.secondThird
    {lower bound : ℝ} {first second third : Fin 3} {frequency : SpatialFrequency}
    {firstOrder secondOrder thirdOrder firstOffset : ℕ}
    (hstencil : ThreeAxisStencilControlled lower bound first second third frequency
      firstOrder secondOrder thirdOrder)
    (hfirst : firstOffset ≤ firstOrder) :
    TwoAxisStencilControlled lower bound second third
      (threeAxisStencilPoint first second third frequency firstOffset 0 0)
      secondOrder thirdOrder := by
  intro j hj k hk
  have hpoint :
      twoAxisStencilPoint second third
          (threeAxisStencilPoint first second third frequency firstOffset 0 0) j k =
        threeAxisStencilPoint first second third frequency firstOffset j k := by
    unfold twoAxisStencilPoint threeAxisStencilPoint
    simp only [zero_nsmul, add_zero]
  rw [hpoint]
  exact hstencil firstOffset hfirst j hj k hk

/-- Fixing the second coordinate leaves the genuine first/third two-axis stencil. -/
theorem ThreeAxisStencilControlled.firstThird
    {lower bound : ℝ} {first second third : Fin 3} {frequency : SpatialFrequency}
    {firstOrder secondOrder thirdOrder secondOffset : ℕ}
    (hstencil : ThreeAxisStencilControlled lower bound first second third frequency
      firstOrder secondOrder thirdOrder)
    (hsecond : secondOffset ≤ secondOrder) :
    TwoAxisStencilControlled lower bound first third
      (threeAxisStencilPoint first second third frequency 0 secondOffset 0)
      firstOrder thirdOrder := by
  intro i hi k hk
  have hpoint :
      twoAxisStencilPoint first third
          (threeAxisStencilPoint first second third frequency 0 secondOffset 0) i k =
        threeAxisStencilPoint first second third frequency i secondOffset k := by
    unfold twoAxisStencilPoint threeAxisStencilPoint
    simp only [zero_nsmul, add_zero]
    abel
  rw [hpoint]
  exact hstencil i hi secondOffset hsecond k hk

/-- Fixing the third coordinate leaves the genuine first/second two-axis stencil. -/
theorem ThreeAxisStencilControlled.firstSecond
    {lower bound : ℝ} {first second third : Fin 3} {frequency : SpatialFrequency}
    {firstOrder secondOrder thirdOrder thirdOffset : ℕ}
    (hstencil : ThreeAxisStencilControlled lower bound first second third frequency
      firstOrder secondOrder thirdOrder)
    (hthird : thirdOffset ≤ thirdOrder) :
    TwoAxisStencilControlled lower bound first second
      (threeAxisStencilPoint first second third frequency 0 0 thirdOffset)
      firstOrder secondOrder := by
  intro i hi j hj
  have hpoint :
      twoAxisStencilPoint first second
          (threeAxisStencilPoint first second third frequency 0 0 thirdOffset) i j =
        threeAxisStencilPoint first second third frequency i j thirdOffset := by
    unfold twoAxisStencilPoint threeAxisStencilPoint
    simp only [zero_nsmul, add_zero]
    abel
  rw [hpoint]
  exact hstencil i hi j hj thirdOffset hthird

/-- The native difference word and the three-axis forward-difference chart are the same owner. -/
@[simp] theorem difference_coordinateTransport_eq_fwdDiff
    (axis : Fin 3) (observable : SpatialFrequency → ℂ) :
    difference coordinateTransport axis observable =
      fwdDiff (coordinateStep axis) observable := by
  rfl

theorem differenceWord_eq_threeAxisMixedForwardDifference
    (first second third : Fin 3) (firstOrder secondOrder thirdOrder : ℕ)
    (observable : SpatialFrequency → ℂ) :
    differenceWord coordinateTransport
        (List.replicate firstOrder first ++ List.replicate secondOrder second ++
          List.replicate thirdOrder third) observable =
      threeAxisMixedForwardDifference first second third
        firstOrder secondOrder thirdOrder observable := by
  induction firstOrder with
  | zero =>
      induction secondOrder with
      | zero =>
          induction thirdOrder with
          | zero => rfl
          | succ thirdOrder ih =>
              simpa [List.replicate_succ, threeAxisMixedForwardDifference,
                Function.iterate_succ_apply'] using
                congrArg (fwdDiff (coordinateStep third)) ih
      | succ secondOrder ih =>
          simpa [List.replicate_succ, threeAxisMixedForwardDifference,
            Function.iterate_succ_apply'] using
            congrArg (fwdDiff (coordinateStep second)) ih
  | succ firstOrder ih =>
      simpa [List.replicate_succ, threeAxisMixedForwardDifference,
        Function.iterate_succ_apply'] using
        congrArg (fwdDiff (coordinateStep first)) ih

/-- The two-axis forward-difference chart is the corresponding addressed replicate word. -/
theorem differenceWord_eq_mixedForwardDifference
    (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (observable : SpatialFrequency → ℂ) :
    differenceWord coordinateTransport
        (List.replicate firstOrder first ++ List.replicate secondOrder second) observable =
      mixedForwardDifference first second firstOrder secondOrder observable := by
  simpa [threeAxisMixedForwardDifference, mixedForwardDifference] using
    differenceWord_eq_threeAxisMixedForwardDifference
      first second 0 firstOrder secondOrder 0 observable

/-- The existing controlled `11` reciprocal envelope in addressed-word coordinates. -/
theorem norm_hodgeReciprocal_pairWord_one_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 1) :
    ‖differenceWord coordinateTransport [first, second] hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneOneEnvelope lower bound := by
  rw [show [first, second] =
      List.replicate 1 first ++ List.replicate 1 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
    hlower hbound first second haxes frequency hstencil

/-- The existing controlled `12` reciprocal envelope in addressed-word coordinates. -/
theorem norm_hodgeReciprocal_pairWord_one_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 2) :
    ‖differenceWord coordinateTransport [first, second, second] hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneTwoEnvelope lower bound := by
  rw [show [first, second, second] =
      List.replicate 1 first ++ List.replicate 2 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeReciprocal_mixedForwardDifference_one_two_le_of_controlled
    hlower hbound first second haxes frequency hstencil

/-- The transposed controlled `21` reciprocal envelope in addressed-word coordinates. -/
theorem norm_hodgeReciprocal_pairWord_two_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 1) :
    ‖differenceWord coordinateTransport [first, first, second] hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneTwoEnvelope lower bound := by
  rw [show [first, first, second] =
      List.replicate 2 first ++ List.replicate 1 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeReciprocal_mixedForwardDifference_two_one_le_of_controlled
    hlower hbound first second haxes frequency hstencil

/-- The existing controlled `22` reciprocal envelope in addressed-word coordinates. -/
theorem norm_hodgeReciprocal_pairWord_two_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 2) :
    ‖differenceWord coordinateTransport [first, first, second, second]
        hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
  rw [show [first, first, second, second] =
      List.replicate 2 first ++ List.replicate 2 second by simp,
    differenceWord_eq_mixedForwardDifference]
  exact norm_hodgeReciprocal_mixedForwardDifference_two_two_le_of_controlled
    hlower hbound first second haxes frequency hstencil

/-! ## Recursive order `111 -> 112 -> 122 -> 222` envelopes -/

/-- Removing one addressed axis from `111` leaves the two transverse first differences. -/
def oneEachAxisRemoveOne : Fin 3 → List (Fin 3) :=
  ![[1, 2], [0, 2], [0, 1]]

/-- The three active denominator occurrences of the order-three reciprocal word, with every
shifted lower receiver retained. -/
def hodge111GroupedActiveReturn (frequency : SpatialFrequency) : ℂ :=
  ∑ axis : Fin 3,
    differenceWord coordinateTransport [axis]
        (fun current ↦ (frequencySquared current : ℂ)) frequency *
      differenceWord coordinateTransport (oneEachAxisRemoveOne axis) hodgeReciprocal
        (coordinateTransport axis frequency)

/-- The order-three active occurrence ledger groups exactly by its differentiated axis. -/
theorem hodgeOneEach_activeLedgerSum_eq_groupedReturn
    (frequency : SpatialFrequency) :
    ledgerSum (hodgeOneEachAnnihilatorCertificate frequency).activeLedger frequency =
      hodge111GroupedActiveReturn frequency := by
  simp [hodgeOneEachAnnihilatorCertificate, AnnihilatorCertificate.activeLedger,
    hodgeQuadraticWordRemainderLedger, oneEachAxisWord, reciprocalRemainderLedger,
    principalFace, expandFace, rightBranch, leftBranch, quadraticDenominatorActive,
    denominatorDifferenceAxes, ledgerSum, ProductFace.value,
    hodge111GroupedActiveReturn, oneEachAxisRemoveOne, Fin.sum_univ_succ,
    difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
    shift]

/-- Exact first edge of the strict predecessor chain. -/
theorem hodgeReciprocal_oneEach_groupedRecurrence
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport oneEachAxisWord frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency =
      -hodge111GroupedActiveReturn frequency := by
  rw [hodgeReciprocal_oneEach_activeRecurrence frequency hnonzero,
    hodgeOneEach_activeLedgerSum_eq_groupedReturn]

/-- The order-three reciprocal envelope derived from the transverse order-two envelope. -/
def hodgeReciprocal111Envelope (lower bound : ℝ) : ℝ :=
  3 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound / lower

/-- The complete `111` successor population is contained in its controlled unit cube. -/
theorem ThreeAxisStencilControlled.oneEach_nonzero
    {lower bound : ℝ} (hlower : 0 < lower) (frequency : SpatialFrequency)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 1) :
    ∀ current ∈ successorWindow coordinateTransport oneEachAxisWord frequency,
      frequencySquared current ≠ 0 := by
  intro current hcurrent
  simp only [oneEachAxisWord, successorWindow, List.mem_append,
    List.mem_singleton] at hcurrent
  rcases hcurrent with ((hcurrent | hcurrent) | (hcurrent | hcurrent)) |
      ((hcurrent | hcurrent) | (hcurrent | hcurrent))
  · subst current
    have hpoint := (hstencil 1 (by omega) 1 (by omega) 1 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 1 (by omega) 1 (by omega) 0 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 1 (by omega) 0 (by omega) 1 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 1 (by omega) 0 (by omega) 0 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 0 (by omega) 1 (by omega) 1 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 0 (by omega) 1 (by omega) 0 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 0 (by omega) 0 (by omega) 1 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'
  · subst current
    have hpoint := (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).1
    simpa [threeAxisStencilPoint, coordinateTransport] using
      (hlower.trans_le hpoint).ne'

/-- The first three-axis envelope is derived from three shifted two-axis predecessor stencils. -/
theorem norm_hodgeReciprocal_oneEach_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 1) :
    ‖differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency‖ ≤
      hodgeReciprocal111Envelope lower bound := by
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).2
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).1
  have hgrouped : ‖hodge111GroupedActiveReturn frequency‖ ≤
      3 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    unfold hodge111GroupedActiveReturn
    calc
      ‖∑ axis : Fin 3,
          differenceWord coordinateTransport [axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (oneEachAxisRemoveOne axis) hodgeReciprocal
              (coordinateTransport axis frequency)‖ ≤
          ∑ axis : Fin 3,
            ‖differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneEachAxisRemoveOne axis) hodgeReciprocal
                (coordinateTransport axis frequency)‖ := norm_sum_le _ _
      _ ≤ ∑ _axis : Fin 3,
          (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
        apply Finset.sum_le_sum
        intro axis haxis
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_hodgeDenominator_singleDifference_le
            hbound axis frequency hcoordinates
        · fin_cases axis
          · have hraw :=
              norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
                hlower hbound 1 2 (by decide)
                (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
                (hstencil.secondThird (firstOffset := 1) (by omega))
            simpa [oneEachAxisRemoveOne, differenceWord, difference, shift,
              coordinateTransport, mixedForwardDifference, fwdDiff,
              threeAxisStencilPoint] using hraw
          · have hraw :=
              norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
                hlower hbound 0 2 (by decide)
                (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
                (hstencil.firstThird (secondOffset := 1) (by omega))
            simpa [oneEachAxisRemoveOne, differenceWord, difference, shift,
              coordinateTransport, mixedForwardDifference, fwdDiff,
              threeAxisStencilPoint] using hraw
          · have hraw :=
              norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
                hlower hbound 0 1 (by decide)
                (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
                (hstencil.firstSecond (thirdOffset := 1) (by omega))
            simpa [oneEachAxisRemoveOne, differenceWord, difference, shift,
              coordinateTransport, mixedForwardDifference, fwdDiff,
              threeAxisStencilPoint] using hraw
        · positivity
        · positivity
      _ = 3 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := by
        simp
        ring
  have hrecurrence := hodgeReciprocal_oneEach_groupedRecurrence frequency
    (hstencil.oneEach_nonzero hlower frequency)
  have hfrequencyPositive : 0 < frequencySquared frequency := hlower.trans_le hfrequency
  have hdenominatorNorm : ‖(frequencySquared frequency : ℂ)‖ =
      frequencySquared frequency := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfrequencyPositive]
  unfold hodgeReciprocal111Envelope
  rw [le_div_iff₀ hlower]
  calc
    ‖differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency‖ * lower ≤
        ‖differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency‖ *
          frequencySquared frequency :=
      mul_le_mul_of_nonneg_left hfrequency (norm_nonneg _)
    _ = ‖(frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport oneEachAxisWord hodgeReciprocal frequency‖ := by
      rw [norm_mul, hdenominatorNorm]
      ring
    _ = ‖hodge111GroupedActiveReturn frequency‖ := by rw [hrecurrence, norm_neg]
    _ ≤ 3 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound := hgrouped

/-- Removing one occurrence from the `112` word, indexed first by its doubled axis and then by
the differentiated axis. -/
def oneOneTwoRemoveOne : Fin 3 → Fin 3 → List (Fin 3) :=
  ![![[0, 1, 2], [0, 0, 2], [0, 0, 1]],
    ![[1, 1, 2], [0, 1, 2], [0, 1, 1]],
    ![[1, 2, 2], [0, 2, 2], [0, 1, 2]]]

/-- A first denominator difference occurs twice on the doubled axis and once transversely. -/
def oneOneTwoFirstMultiplicity (doubled axis : Fin 3) : ℕ :=
  if axis = doubled then 2 else 1

/-- The five active `112` occurrences grouped into three first-difference faces and one
same-axis second-difference face. -/
def hodge112GroupedActiveReturn (doubled : Fin 3) (frequency : SpatialFrequency) : ℂ :=
  (∑ axis : Fin 3,
    (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
      differenceWord coordinateTransport [axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) hodgeReciprocal
          (coordinateTransport axis frequency)) +
    differenceWord coordinateTransport [doubled, doubled]
        (fun current ↦ (frequencySquared current : ℂ)) frequency *
      differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) hodgeReciprocal
        (coordinateTransport doubled (coordinateTransport doubled frequency))

/-- The order-four active ledger groups with exact occurrence multiplicities `2,1,1,1`. -/
theorem hodgeOneOneTwo_activeLedgerSum_eq_groupedReturn
    (doubled : Fin 3) (frequency : SpatialFrequency) :
    ledgerSum (hodgeOneOneTwoAnnihilatorCertificate doubled frequency).activeLedger frequency =
      hodge112GroupedActiveReturn doubled frequency := by
  fin_cases doubled <;>
    simp [hodgeOneOneTwoAnnihilatorCertificate, AnnihilatorCertificate.activeLedger,
      hodgeQuadraticWordRemainderLedger, oneOneTwoWord, reciprocalRemainderLedger,
      principalFace, expandFace, rightBranch, leftBranch, quadraticDenominatorActive,
      denominatorDifferenceAxes, ledgerSum, ProductFace.value,
      hodge112GroupedActiveReturn, oneOneTwoRemoveOne, oneOneTwoFirstMultiplicity,
      oneEachAxisRemoveOne, Fin.sum_univ_succ,
      difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
      shift] <;> ring

/-- Exact second edge of the strict predecessor chain. -/
theorem hodgeReciprocal_oneOneTwo_groupedRecurrence
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneOneTwoWord doubled) frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneOneTwoWord doubled) hodgeReciprocal frequency =
      -hodge112GroupedActiveReturn doubled frequency := by
  rw [hodgeReciprocal_oneOneTwo_activeRecurrence doubled frequency hnonzero,
    hodgeOneOneTwo_activeLedgerSum_eq_groupedReturn]

/-- The order-four `112` envelope, with the doubled and transverse occurrence multiplicities
retained separately. -/
def hodgeReciprocal112Envelope (lower bound : ℝ) : ℝ :=
  (2 * (2 * bound + 1) * hodgeReciprocal111Envelope lower bound +
      2 * (2 * bound + 1) * hodgeReciprocalMixedOneTwoEnvelope lower bound +
      2 * hodgeReciprocalMixedOneOneEnvelope lower bound) / lower

/-- Heterogeneous strict predecessors of one `112` return. -/
structure Hodge112LowerOrderEnvelope
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (oneOneOneBound oneTwoBound oneOneBound : ℝ) : Prop where
  first : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis) hodgeReciprocal
      (coordinateTransport axis frequency)‖ ≤
        if axis = doubled then oneOneOneBound else oneTwoBound
  second :
    ‖differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) hodgeReciprocal
      (coordinateTransport doubled (coordinateTransport doubled frequency))‖ ≤ oneOneBound

/-- The five grouped occurrences return the exact `2+2+1` predecessor envelope. -/
theorem norm_hodge112GroupedActiveReturn_le
    {bound oneOneOneBound oneTwoBound oneOneBound : ℝ}
    (hbound : 0 ≤ bound) (doubled : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hlower : Hodge112LowerOrderEnvelope doubled frequency
      oneOneOneBound oneTwoBound oneOneBound)
    (h111 : 0 ≤ oneOneOneBound) (h12 : 0 ≤ oneTwoBound) (h11 : 0 ≤ oneOneBound) :
    ‖hodge112GroupedActiveReturn doubled frequency‖ ≤
      2 * (2 * bound + 1) * oneOneOneBound +
        2 * (2 * bound + 1) * oneTwoBound + 2 * oneOneBound := by
  unfold hodge112GroupedActiveReturn
  calc
    ‖(∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis)
                hodgeReciprocal (coordinateTransport axis frequency)) +
        differenceWord coordinateTransport [doubled, doubled]
            (fun current ↦ (frequencySquared current : ℂ)) frequency *
          differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) hodgeReciprocal
            (coordinateTransport doubled (coordinateTransport doubled frequency))‖ ≤
      ‖∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneOneTwoRemoveOne doubled axis)
                hodgeReciprocal (coordinateTransport axis frequency)‖ +
        ‖differenceWord coordinateTransport [doubled, doubled]
            (fun current ↦ (frequencySquared current : ℂ)) frequency *
          differenceWord coordinateTransport (oneEachAxisRemoveOne doubled) hodgeReciprocal
            (coordinateTransport doubled (coordinateTransport doubled frequency))‖ :=
      norm_add_le _ _
    _ ≤ (∑ axis : Fin 3,
          (oneOneTwoFirstMultiplicity doubled axis : ℝ) * (2 * bound + 1) *
            (if axis = doubled then oneOneOneBound else oneTwoBound)) +
        2 * oneOneBound := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis haxis
        simp only [norm_mul, Complex.norm_natCast]
        have hdenominator := norm_hodgeDenominator_singleDifference_le
          hbound axis frequency hcoordinates
        have hpredecessor := hlower.first axis
        have hmultiplicity : 0 ≤ (oneOneTwoFirstMultiplicity doubled axis : ℝ) := by positivity
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdenominator hmultiplicity)
          hpredecessor (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_hodgeDenominator_sameAxis_secondDifference]
        exact mul_le_mul_of_nonneg_left hlower.second (by norm_num)
    _ = 2 * (2 * bound + 1) * oneOneOneBound +
        2 * (2 * bound + 1) * oneTwoBound + 2 * oneOneBound := by
      fin_cases doubled <;>
        rw [Fin.sum_univ_succ, Fin.sum_univ_two] <;>
        simp [oneOneTwoFirstMultiplicity] <;> ring

/-- The axis multiplicity of the `112` word. -/
def oneOneTwoAxisOrder (doubled axis : Fin 3) : ℕ :=
  if axis = doubled then 2 else 1

/-- Division by the positive quadratic aperture, reusable at every strict predecessor stage. -/
theorem norm_differenceWord_le_div_of_frequencySquared_recurrence
    {lower envelope : ℝ} (hlower : 0 < lower)
    (word : List (Fin 3)) (frequency : SpatialFrequency) (returned : ℂ)
    (hfrequency : lower ≤ frequencySquared frequency)
    (hrecurrence : (frequencySquared frequency : ℂ) *
      differenceWord coordinateTransport word hodgeReciprocal frequency = -returned)
    (hreturn : ‖returned‖ ≤ envelope) :
    ‖differenceWord coordinateTransport word hodgeReciprocal frequency‖ ≤ envelope / lower := by
  have hfrequencyPositive : 0 < frequencySquared frequency := hlower.trans_le hfrequency
  have hdenominatorNorm : ‖(frequencySquared frequency : ℂ)‖ =
      frequencySquared frequency := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfrequencyPositive]
  rw [le_div_iff₀ hlower]
  calc
    ‖differenceWord coordinateTransport word hodgeReciprocal frequency‖ * lower ≤
        ‖differenceWord coordinateTransport word hodgeReciprocal frequency‖ *
          frequencySquared frequency :=
      mul_le_mul_of_nonneg_left hfrequency (norm_nonneg _)
    _ = ‖(frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport word hodgeReciprocal frequency‖ := by
      rw [norm_mul, hdenominatorNorm]
      ring
    _ = ‖returned‖ := by rw [hrecurrence, norm_neg]
    _ ≤ envelope := hreturn

/-- The complete controlled `112` word derives its heterogeneous predecessor certificate and hence
its order-four envelope; no active product-face bound is supplied. -/
theorem norm_hodgeReciprocal_oneOneTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (doubled : Fin 3) (frequency : SpatialFrequency)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneOneTwoAxisOrder doubled 0) (oneOneTwoAxisOrder doubled 1)
        (oneOneTwoAxisOrder doubled 2))
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneOneTwoWord doubled) frequency,
      frequencySquared current ≠ 0) :
    ‖differenceWord coordinateTransport (oneOneTwoWord doubled) hodgeReciprocal frequency‖ ≤
      hodgeReciprocal112Envelope lower bound := by
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by simp [oneOneTwoAxisOrder])
      0 (by simp [oneOneTwoAxisOrder]) 0 (by simp [oneOneTwoAxisOrder])).2
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by simp [oneOneTwoAxisOrder])
      0 (by simp [oneOneTwoAxisOrder]) 0 (by simp [oneOneTwoAxisOrder])).1
  have hlowerOrders : Hodge112LowerOrderEnvelope doubled frequency
      (hodgeReciprocal111Envelope lower bound)
      (hodgeReciprocalMixedOneTwoEnvelope lower bound)
      (hodgeReciprocalMixedOneOneEnvelope lower bound) := by
    fin_cases doubled
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 1 1 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeReciprocal_oneEach_le_of_controlled
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 1 0 0) hsub
          simpa [oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
      · have hraw := norm_hodgeReciprocal_pairWord_one_one_le
          hlower hbound 1 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
          (hstencil'.secondThird (firstOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
            coordinateTransport 0 (coordinateTransport 0 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [oneEachAxisRemoveOne] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 2 1 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeReciprocal_oneEach_le_of_controlled
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 0 1 0) hsub
          simpa [oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
      · have hraw := norm_hodgeReciprocal_pairWord_one_one_le
          hlower hbound 0 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
          (hstencil'.firstThird (secondOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
            coordinateTransport 1 (coordinateTransport 1 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [oneEachAxisRemoveOne] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 1 2 := by
        simpa [oneOneTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [oneOneTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hraw := norm_hodgeReciprocal_oneEach_le_of_controlled
            hlower hbound (threeAxisStencilPoint 0 1 2 frequency 0 0 1) hsub
          simpa [oneOneTwoRemoveOne, oneEachAxisWord, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · have hraw := norm_hodgeReciprocal_pairWord_one_one_le
          hlower hbound 0 1 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
          (hstencil'.firstSecond (thirdOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
            coordinateTransport 2 (coordinateTransport 2 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [oneEachAxisRemoveOne] using hraw
  have hgrouped := norm_hodge112GroupedActiveReturn_le hbound doubled frequency
    hcoordinates hlowerOrders (by
      unfold hodgeReciprocal111Envelope hodgeReciprocalMixedOneOneEnvelope
      positivity) (by
      unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
        hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      positivity) (by
      unfold hodgeReciprocalMixedOneOneEnvelope
      positivity)
  unfold hodgeReciprocal112Envelope
  exact norm_differenceWord_le_div_of_frequencySquared_recurrence
    hlower (oneOneTwoWord doubled) frequency (hodge112GroupedActiveReturn doubled frequency)
    hfrequency (hodgeReciprocal_oneOneTwo_groupedRecurrence doubled frequency hnonzero) hgrouped

/-! ### The `122` edge -/

/-- Removing one occurrence from a `122` word leaves either the transverse `22` word or a
shifted `112` word. -/
def oneTwoTwoRemoveOne : Fin 3 → Fin 3 → List (Fin 3) :=
  ![![[1, 1, 2, 2], [0, 1, 2, 2], [0, 1, 1, 2]],
    ![[0, 1, 2, 2], [0, 0, 2, 2], [0, 0, 1, 2]],
    ![[0, 1, 1, 2], [0, 0, 1, 2], [0, 0, 1, 1]]]

/-- Removing both occurrences of a doubled axis from `122` leaves a transverse `12` word.
The entry at the single axis is inert in the grouped return. -/
def oneTwoTwoRemoveTwo : Fin 3 → Fin 3 → List (Fin 3) :=
  ![![[1, 1, 2, 2], [0, 2, 2], [0, 1, 1]],
    ![[1, 2, 2], [0, 0, 2, 2], [0, 0, 1]],
    ![[1, 1, 2], [0, 0, 2], [0, 0, 1, 1]]]

/-- A first denominator difference occurs once on the single axis and twice on either doubled
axis. -/
def oneTwoTwoFirstMultiplicity (single axis : Fin 3) : ℕ :=
  if axis = single then 1 else 2

/-- The seven active `122` occurrences grouped without erasing their translated receivers. -/
def hodge122GroupedActiveReturn (single : Fin 3) (frequency : SpatialFrequency) : ℂ :=
  (∑ axis : Fin 3,
    (oneTwoTwoFirstMultiplicity single axis : ℂ) *
      differenceWord coordinateTransport [axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) hodgeReciprocal
          (coordinateTransport axis frequency)) +
    ∑ axis : Fin 3, if axis = single then 0 else
      differenceWord coordinateTransport [axis, axis]
          (fun current ↦ (frequencySquared current : ℂ)) frequency *
        differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) hodgeReciprocal
          (coordinateTransport axis (coordinateTransport axis frequency))

/-- The order-five active ledger groups with exact occurrence multiplicities
`1,2,2,1,1`. -/
theorem hodgeOneTwoTwo_activeLedgerSum_eq_groupedReturn
    (single : Fin 3) (frequency : SpatialFrequency) :
    ledgerSum (hodgeOneTwoTwoAnnihilatorCertificate single frequency).activeLedger frequency =
      hodge122GroupedActiveReturn single frequency := by
  fin_cases single <;>
    simp [hodgeOneTwoTwoAnnihilatorCertificate, AnnihilatorCertificate.activeLedger,
      hodgeQuadraticWordRemainderLedger, oneTwoTwoWord, reciprocalRemainderLedger,
      principalFace, expandFace, rightBranch, leftBranch, quadraticDenominatorActive,
      denominatorDifferenceAxes, ledgerSum, ProductFace.value,
      hodge122GroupedActiveReturn, oneTwoTwoRemoveOne, oneTwoTwoRemoveTwo,
      oneTwoTwoFirstMultiplicity, Fin.sum_univ_succ,
      difference_shift_of_interchange coordinateTransport coordinateTransport_interchange,
      shift] <;> ring

/-- Exact third edge of the strict predecessor chain. -/
theorem hodgeReciprocal_oneTwoTwo_groupedRecurrence
    (single : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneTwoTwoWord single) frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport (oneTwoTwoWord single) hodgeReciprocal frequency =
      -hodge122GroupedActiveReturn single frequency := by
  rw [hodgeReciprocal_oneTwoTwo_activeRecurrence single frequency hnonzero,
    hodgeOneTwoTwo_activeLedgerSum_eq_groupedReturn]

/-- The order-five `122` envelope forced by its seven retained occurrences. -/
def hodgeReciprocal122Envelope (lower bound : ℝ) : ℝ :=
  ((2 * bound + 1) * hodgeReciprocalMixedTwoTwoEnvelope lower bound +
      4 * (2 * bound + 1) * hodgeReciprocal112Envelope lower bound +
      4 * hodgeReciprocalMixedOneTwoEnvelope lower bound) / lower

/-- Heterogeneous strict predecessors of one `122` return. -/
structure Hodge122LowerOrderEnvelope
    (single : Fin 3) (frequency : SpatialFrequency)
    (twoTwoBound oneOneTwoBound oneTwoBound : ℝ) : Prop where
  first : ∀ axis : Fin 3,
    ‖differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis) hodgeReciprocal
      (coordinateTransport axis frequency)‖ ≤
        if axis = single then twoTwoBound else oneOneTwoBound
  second : ∀ axis : Fin 3, axis ≠ single →
    ‖differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis) hodgeReciprocal
      (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤ oneTwoBound

/-- The seven grouped occurrences return the exact `1+4+2` predecessor ledger, whose two
second-denominator faces each carry the constant coefficient two. -/
theorem norm_hodge122GroupedActiveReturn_le
    {bound twoTwoBound oneOneTwoBound oneTwoBound : ℝ}
    (hbound : 0 ≤ bound) (single : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hlower : Hodge122LowerOrderEnvelope single frequency
      twoTwoBound oneOneTwoBound oneTwoBound)
    (h22 : 0 ≤ twoTwoBound) (h112 : 0 ≤ oneOneTwoBound) (h12 : 0 ≤ oneTwoBound) :
    ‖hodge122GroupedActiveReturn single frequency‖ ≤
      (2 * bound + 1) * twoTwoBound +
        4 * (2 * bound + 1) * oneOneTwoBound + 4 * oneTwoBound := by
  unfold hodge122GroupedActiveReturn
  calc
    ‖(∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis)
                hodgeReciprocal (coordinateTransport axis frequency)) +
        ∑ axis : Fin 3, if axis = single then 0 else
          differenceWord coordinateTransport [axis, axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis)
              hodgeReciprocal
              (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤
      ‖∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℂ) *
            differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (oneTwoTwoRemoveOne single axis)
                hodgeReciprocal (coordinateTransport axis frequency)‖ +
        ‖∑ axis : Fin 3, if axis = single then 0 else
          differenceWord coordinateTransport [axis, axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (oneTwoTwoRemoveTwo single axis)
              hodgeReciprocal
              (coordinateTransport axis (coordinateTransport axis frequency))‖ :=
      norm_add_le _ _
    _ ≤ (∑ axis : Fin 3,
          (oneTwoTwoFirstMultiplicity single axis : ℝ) * (2 * bound + 1) *
            (if axis = single then twoTwoBound else oneOneTwoBound)) +
        ∑ axis : Fin 3, if axis = single then 0 else 2 * oneTwoBound := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis _
        simp only [norm_mul, Complex.norm_natCast]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_hodgeDenominator_singleDifference_le
              hbound axis frequency hcoordinates) (by positivity))
          (hlower.first axis) (norm_nonneg _) (by positivity)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro axis _
        split_ifs with haxis
        · simp
        · rw [norm_mul, norm_hodgeDenominator_sameAxis_secondDifference]
          exact mul_le_mul_of_nonneg_left (hlower.second axis haxis) (by norm_num)
    _ = (2 * bound + 1) * twoTwoBound +
        4 * (2 * bound + 1) * oneOneTwoBound + 4 * oneTwoBound := by
      fin_cases single <;>
        simp only [Fin.sum_univ_succ, Fin.sum_univ_two] <;>
        simp [oneTwoTwoFirstMultiplicity] <;> ring

/-- The axis multiplicity of the `122` word. -/
def oneTwoTwoAxisOrder (single axis : Fin 3) : ℕ :=
  if axis = single then 1 else 2

/-- The complete controlled `122` word derives its `22`, `112`, and `12` predecessor bounds.
The successor aperture is inherited from the same three-axis stencil. -/
theorem norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (single : Fin 3) (frequency : SpatialFrequency)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency
      (oneTwoTwoAxisOrder single 0) (oneTwoTwoAxisOrder single 1)
        (oneTwoTwoAxisOrder single 2))
    (hnonzero : ∀ current ∈
      successorWindow coordinateTransport (oneTwoTwoWord single) frequency,
      frequencySquared current ≠ 0) :
    ‖differenceWord coordinateTransport (oneTwoTwoWord single) hodgeReciprocal frequency‖ ≤
      hodgeReciprocal122Envelope lower bound := by
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by simp [oneTwoTwoAxisOrder])
      0 (by simp [oneTwoTwoAxisOrder]) 0 (by simp [oneTwoTwoAxisOrder])).2
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by simp [oneTwoTwoAxisOrder])
      0 (by simp [oneTwoTwoAxisOrder]) 0 (by simp [oneTwoTwoAxisOrder])).1
  have hlowerOrders : Hodge122LowerOrderEnvelope single frequency
      (hodgeReciprocalMixedTwoTwoEnvelope lower bound)
      (hodgeReciprocal112Envelope lower bound)
      (hodgeReciprocalMixedOneTwoEnvelope lower bound) := by
    fin_cases single
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 1 2 2 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 1 0 0)
            (hstencil'.secondThird (firstOffset := 1) (by omega))
          simpa [oneTwoTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 2)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 2)
                (threeAxisStencilPoint 0 1 2 frequency 0 1 0),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 0 1 0) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 1) (secondOrder := 2) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 1)
                (threeAxisStencilPoint 0 1 2 frequency 0 0 1),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 0 0 1) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · simp at haxis
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
            (hstencil'.firstThird (secondOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
              coordinateTransport 1 (coordinateTransport 1 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
            (hstencil'.firstSecond (thirdOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
              coordinateTransport 2 (coordinateTransport 2 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 1 2 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 1) (thirdOrder := 2)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 2)
                (threeAxisStencilPoint 0 1 2 frequency 1 0 0),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 1 0 0) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 1 0)
            (hstencil'.firstThird (secondOffset := 1) (by omega))
          simpa [oneTwoTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
              (firstOrder := 2) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 0)
                (threeAxisStencilPoint 0 1 2 frequency 0 0 1),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 0 0 1) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · have hraw := norm_hodgeReciprocal_pairWord_one_two_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
            (hstencil'.secondThird (firstOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
              coordinateTransport 0 (coordinateTransport 0 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
        · simp at haxis
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
            (hstencil'.firstSecond (thirdOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
              coordinateTransport 2 (coordinateTransport 2 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
    · have hstencil' : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 1 := by
        simpa [oneTwoTwoAxisOrder] using hstencil
      refine ⟨?_, ?_⟩
      · intro axis
        fin_cases axis
        · have hsub := hstencil'.rebase
              (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
              (firstOrder := 1) (secondOrder := 2) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 1)
                (threeAxisStencilPoint 0 1 2 frequency 1 0 0),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 1 0 0) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hsub := hstencil'.rebase
              (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
              (firstOrder := 2) (secondOrder := 1) (thirdOrder := 1)
              (by omega) (by omega) (by omega)
          have hsubNonzero : ∀ current ∈
              successorWindow coordinateTransport (oneOneTwoWord 0)
                (threeAxisStencilPoint 0 1 2 frequency 0 1 0),
              frequencySquared current ≠ 0 := by
            simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
          have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
            hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 0 1 0) hsub hsubNonzero
          simpa [oneOneTwoWord, oneTwoTwoRemoveOne, threeAxisStencilPoint,
            coordinateTransport] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
            hlower hbound 0 1 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 0 1)
            (hstencil'.firstSecond (thirdOffset := 1) (by omega))
          simpa [oneTwoTwoRemoveOne, threeAxisStencilPoint, coordinateTransport] using hraw
      · intro axis haxis
        fin_cases axis
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 1 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
            (hstencil'.secondThird (firstOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
              coordinateTransport 0 (coordinateTransport 0 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
        · have hraw := norm_hodgeReciprocal_pairWord_two_one_le
            hlower hbound 0 2 (by decide)
            (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
            (hstencil'.firstThird (secondOffset := 2) (by omega))
          have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
              coordinateTransport 1 (coordinateTransport 1 frequency) := by
            simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
            rw [two_nsmul]
            abel
          rw [hbase] at hraw
          simpa [oneTwoTwoRemoveTwo] using hraw
        · simp at haxis
  have hgrouped := norm_hodge122GroupedActiveReturn_le hbound single frequency
    hcoordinates hlowerOrders (by
      unfold hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalValueEnvelope
        hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      positivity) (by
      unfold hodgeReciprocal112Envelope hodgeReciprocal111Envelope
        hodgeReciprocalMixedOneOneEnvelope hodgeReciprocalMixedOneTwoEnvelope
        hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      positivity) (by
      unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
        hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      positivity)
  unfold hodgeReciprocal122Envelope
  exact norm_differenceWord_le_div_of_frequencySquared_recurrence
    hlower (oneTwoTwoWord single) frequency (hodge122GroupedActiveReturn single frequency)
    hfrequency (hodgeReciprocal_oneTwoTwo_groupedRecurrence single frequency hnonzero) hgrouped


/-- The complete nine-occurrence return is controlled by two strict predecessor envelopes.  This
is the scale ledger exposed by HD2: no bound for an individual active product face is assumed. -/
theorem norm_hodgeQuadraticGroupedActiveReturn_le
    {bound fifthBound fourthBound : ℝ}
    (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hlowerOrders : Hodge222LowerOrderEnvelope frequency fifthBound fourthBound) :
    ‖hodgeQuadraticGroupedActiveReturn frequency‖ ≤
      6 * (2 * bound + 1) * fifthBound + 6 * fourthBound := by
  unfold hodgeQuadraticGroupedActiveReturn
  calc
    ‖∑ axis : Fin 3,
        (2 * differenceWord coordinateTransport [axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
              (coordinateTransport axis frequency) +
          differenceWord coordinateTransport [axis, axis]
              (fun current ↦ (frequencySquared current : ℂ)) frequency *
            differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
              (coordinateTransport axis (coordinateTransport axis frequency)))‖ ≤
        ∑ axis : Fin 3,
          ‖2 * differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
                (coordinateTransport axis frequency) +
            differenceWord coordinateTransport [axis, axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
                (coordinateTransport axis (coordinateTransport axis frequency))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _axis : Fin 3,
        (2 * (2 * bound + 1) * fifthBound + 2 * fourthBound) := by
      apply Finset.sum_le_sum
      intro axis _
      calc
        ‖2 * differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
                (coordinateTransport axis frequency) +
            differenceWord coordinateTransport [axis, axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
                (coordinateTransport axis (coordinateTransport axis frequency))‖ ≤
            ‖2 * differenceWord coordinateTransport [axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveOne axis) hodgeReciprocal
                (coordinateTransport axis frequency)‖ +
            ‖differenceWord coordinateTransport [axis, axis]
                (fun current ↦ (frequencySquared current : ℂ)) frequency *
              differenceWord coordinateTransport (secondEachAxisRemoveTwo axis) hodgeReciprocal
                (coordinateTransport axis (coordinateTransport axis frequency))‖ :=
          norm_add_le _ _
        _ ≤ 2 * (2 * bound + 1) * fifthBound + 2 * fourthBound := by
          simp only [norm_mul]
          rw [show ‖(2 : ℂ)‖ = 2 by norm_num,
            norm_hodgeDenominator_sameAxis_secondDifference axis frequency]
          gcongr
          · exact norm_hodgeDenominator_singleDifference_le
              hbound axis frequency hcoordinates
          · exact hlowerOrders.fifth axis
          · exact hlowerOrders.fourth axis
    _ = 6 * (2 * bound + 1) * fifthBound + 6 * fourthBound := by
      simp
      ring

/-- Dividing the exact grouped recurrence by the positive quadratic aperture descends order six
to its uniform fifth- and fourth-order receiver envelopes. -/
theorem norm_hodgeReciprocal_secondEachAxis_le_of_lowerOrderEnvelope
    {lower bound fifthBound fourthBound : ℝ}
    (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : lower ≤ frequencySquared frequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport secondEachAxisWord frequency,
      frequencySquared current ≠ 0)
    (hlowerOrders : Hodge222LowerOrderEnvelope frequency fifthBound fourthBound) :
    ‖differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ ≤
      (6 * (2 * bound + 1) * fifthBound + 6 * fourthBound) / lower := by
  have hfrequencyPositive : 0 < frequencySquared frequency :=
    hlower.trans_le hfrequency
  have hdenominatorNorm : ‖(frequencySquared frequency : ℂ)‖ =
      frequencySquared frequency := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfrequencyPositive]
  have hrecurrenceNorm :
      ‖(frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ =
        ‖hodgeQuadraticGroupedActiveReturn frequency‖ := by
    rw [hodgeReciprocal_secondEachAxis_groupedRecurrence frequency hnonzero, norm_neg]
  rw [le_div_iff₀ hlower]
  calc
    ‖differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ * lower ≤
        ‖differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ *
          frequencySquared frequency :=
      mul_le_mul_of_nonneg_left hfrequency (norm_nonneg _)
    _ = ‖(frequencySquared frequency : ℂ) *
          differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ := by
      rw [norm_mul, hdenominatorNorm]
      ring
    _ = ‖hodgeQuadraticGroupedActiveReturn frequency‖ := hrecurrenceNorm
    _ ≤ 6 * (2 * bound + 1) * fifthBound + 6 * fourthBound :=
      norm_hodgeQuadraticGroupedActiveReturn_le hbound
        frequency hcoordinates hlowerOrders

/-! ### Closing the `222` edge -/

/-- The order-six reciprocal envelope obtained by the complete
`11 -> 111 -> 112 -> 122 -> 222` descent. -/
def hodgeReciprocal222Envelope (lower bound : ℝ) : ℝ :=
  (6 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound +
      6 * hodgeReciprocalMixedTwoTwoEnvelope lower bound) / lower

/-- The full controlled `222` cube supplies every fifth- and fourth-order shifted predecessor,
so the top recurrence closes without a facewise estimate. -/
theorem norm_hodgeReciprocal_secondEachAxis_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 2) :
    ‖differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency‖ ≤
      hodgeReciprocal222Envelope lower bound := by
  have hfrequency : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).1
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).2
  have hlowerOrders : Hodge222LowerOrderEnvelope frequency
      (hodgeReciprocal122Envelope lower bound)
      (hodgeReciprocalMixedTwoTwoEnvelope lower bound) := by
    refine ⟨?_, ?_⟩
    · intro axis
      fin_cases axis
      · have hsub := hstencil.rebase
            (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
            (firstOrder := 1) (secondOrder := 2) (thirdOrder := 2)
            (by omega) (by omega) (by omega)
        have hsubNonzero : ∀ current ∈
            successorWindow coordinateTransport (oneTwoTwoWord 0)
              (threeAxisStencilPoint 0 1 2 frequency 1 0 0),
            frequencySquared current ≠ 0 := by
          simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
        have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
          hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 1 0 0) hsub hsubNonzero
        simpa [secondEachAxisRemoveOne, oneTwoTwoWord, threeAxisStencilPoint,
          coordinateTransport] using hraw
      · have hsub := hstencil.rebase
            (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
            (firstOrder := 2) (secondOrder := 1) (thirdOrder := 2)
            (by omega) (by omega) (by omega)
        have hsubNonzero : ∀ current ∈
            successorWindow coordinateTransport (oneTwoTwoWord 1)
              (threeAxisStencilPoint 0 1 2 frequency 0 1 0),
            frequencySquared current ≠ 0 := by
          simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
        have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
          hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 0 1 0) hsub hsubNonzero
        simpa [secondEachAxisRemoveOne, oneTwoTwoWord, threeAxisStencilPoint,
          coordinateTransport] using hraw
      · have hsub := hstencil.rebase
            (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
            (firstOrder := 2) (secondOrder := 2) (thirdOrder := 1)
            (by omega) (by omega) (by omega)
        have hsubNonzero : ∀ current ∈
            successorWindow coordinateTransport (oneTwoTwoWord 2)
              (threeAxisStencilPoint 0 1 2 frequency 0 0 1),
            frequencySquared current ≠ 0 := by
          simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
        have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
          hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 0 0 1) hsub hsubNonzero
        simpa [secondEachAxisRemoveOne, oneTwoTwoWord, threeAxisStencilPoint,
          coordinateTransport] using hraw
    · intro axis
      fin_cases axis
      · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
          hlower hbound 1 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
          (hstencil.secondThird (firstOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
            coordinateTransport 0 (coordinateTransport 0 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [secondEachAxisRemoveTwo] using hraw
      · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
          hlower hbound 0 2 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
          (hstencil.firstThird (secondOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
            coordinateTransport 1 (coordinateTransport 1 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [secondEachAxisRemoveTwo] using hraw
      · have hraw := norm_hodgeReciprocal_pairWord_two_two_le
          hlower hbound 0 1 (by decide)
          (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
          (hstencil.firstSecond (thirdOffset := 2) (by omega))
        have hbase : threeAxisStencilPoint 0 1 2 frequency 0 0 2 =
            coordinateTransport 2 (coordinateTransport 2 frequency) := by
          simp only [threeAxisStencilPoint, coordinateTransport, zero_nsmul, add_zero]
          rw [two_nsmul]
          abel
        rw [hbase] at hraw
        simpa [secondEachAxisRemoveTwo] using hraw
  have hnonzero : ∀ current ∈
      successorWindow coordinateTransport secondEachAxisWord frequency,
      frequencySquared current ≠ 0 := by
    simpa [secondEachAxisWord] using hstencil.successor_nonzero hlower
  unfold hodgeReciprocal222Envelope
  exact norm_hodgeReciprocal_secondEachAxis_le_of_lowerOrderEnvelope
    hlower hbound frequency hfrequency hcoordinates hnonzero hlowerOrders

end Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

section Audit
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
#print axioms difference_coordinateTransport_eq_fwdDiff
#print axioms hodgeQuadratic_activeLedgerSum_eq_groupedReturn
#print axioms hodge222StrictOrderReturn_eq_groupedActiveReturn
#print axioms hodgeReciprocal_secondEachAxis_groupedRecurrence
#print axioms norm_hodgeQuadraticGroupedActiveReturn_le
#print axioms norm_hodgeReciprocal_secondEachAxis_le_of_lowerOrderEnvelope
end Audit
