import Mathlib.Tactic

/-!
# Finite fermionic occupation transport

**[proved-derived]** A finite linearly ordered mode population presents its fermionic carrier by
occupation subsets.  Creation and annihilation insert or remove one addressed mode with the Koszul
sign determined by the occupied modes preceding it.  The order is a presentation coordinate; the
operator laws below are the invariant return required before a lattice Hamiltonian is admitted.

This file owns only the finite occupation carrier and its canonical anticommutation relations.  It
does not introduce a Hamiltonian, dynamics, probability law, path integral, particle identity, or
apparatus backend.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicFermionicOccupation

open scoped BigOperators

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- [definition] One finite fermionic occupation occurrence. -/
abbrev Occupation (Mode : Type*) [DecidableEq Mode] := Finset Mode

/-- [definition] The finite occupation-basis complex carrier. -/
abbrev FockState (Mode : Type*) [DecidableEq Mode] := Occupation Mode → ℂ

/-- [definition] Occupied modes preceding the addressed mode in the presentation order. -/
def preceding (mode : Mode) (occupation : Occupation Mode) : Finset Mode :=
  occupation.filter fun candidate ↦ candidate < mode

/-- [definition] The number of occupied modes preceding one addressed mode. -/
def prefixCount (mode : Mode) (occupation : Occupation Mode) : ℕ :=
  (preceding mode occupation).card

/-- [definition] The Koszul sign of an addressed insertion/removal. -/
def koszulSign (mode : Mode) (occupation : Occupation Mode) : ℂ :=
  (-1 : ℂ) ^ prefixCount mode occupation

/-- The addressed mode itself never occurs in its preceding population. -/
theorem mode_not_mem_preceding (mode : Mode) (occupation : Occupation Mode) :
    mode ∉ preceding mode occupation := by
  simp [preceding]

/-- Erasing the addressed mode does not change its Koszul sign. -/
theorem preceding_erase_self (mode : Mode) (occupation : Occupation Mode) :
    preceding mode (occupation.erase mode) = preceding mode occupation := by
  ext candidate
  simp only [preceding, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_hne, hmem⟩, hlt⟩
    exact ⟨hmem, hlt⟩
  · rintro ⟨hmem, hlt⟩
    exact ⟨⟨ne_of_lt hlt, hmem⟩, hlt⟩

/-- Inserting the addressed mode does not change its Koszul sign. -/
theorem preceding_insert_self (mode : Mode) (occupation : Occupation Mode) :
    preceding mode (insert mode occupation) = preceding mode occupation := by
  ext candidate
  simp only [preceding, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hmode | hmem, hlt⟩
    · subst candidate
      exact (lt_irrefl mode hlt).elim
    · exact ⟨hmem, hlt⟩
  · rintro ⟨hmem, hlt⟩
    exact ⟨Or.inr hmem, hlt⟩

/-- Every Koszul sign is a unit of square one. -/
theorem koszulSign_mul_self (mode : Mode) (occupation : Occupation Mode) :
    koszulSign mode occupation * koszulSign mode occupation = 1 := by
  rw [koszulSign, ← pow_add]
  rw [show prefixCount mode occupation + prefixCount mode occupation =
      2 * prefixCount mode occupation by omega]
  rw [pow_mul]
  simp

/-- Inserting one unoccupied mode changes a later prefix count by exactly one and leaves every
earlier prefix count unchanged. -/
theorem prefixCount_insert (inserted addressed : Mode) (occupation : Occupation Mode)
    (absent : inserted ∉ occupation) :
    prefixCount addressed (insert inserted occupation) =
      prefixCount addressed occupation + if inserted < addressed then 1 else 0 := by
  unfold prefixCount preceding
  by_cases before : inserted < addressed <;>
    simp [Finset.filter_insert, absent, before]

/-- Inserting an earlier mode reverses the addressed Koszul sign. -/
theorem koszulSign_insert_of_lt (inserted addressed : Mode) (occupation : Occupation Mode)
    (absent : inserted ∉ occupation) (before : inserted < addressed) :
    koszulSign addressed (insert inserted occupation) = -koszulSign addressed occupation := by
  simp only [koszulSign]
  rw [prefixCount_insert inserted addressed occupation absent]
  simp [before, pow_succ]

/-- Inserting a mode which is not earlier leaves the addressed Koszul sign unchanged. -/
theorem koszulSign_insert_of_not_lt (inserted addressed : Mode)
    (occupation : Occupation Mode) (absent : inserted ∉ occupation)
    (notBefore : ¬ inserted < addressed) :
    koszulSign addressed (insert inserted occupation) = koszulSign addressed occupation := by
  simp only [koszulSign]
  rw [prefixCount_insert inserted addressed occupation absent]
  simp [notBefore]

/-- The two insertion orders carry opposite total sign. -/
theorem koszulSign_swap (first second : Mode) (occupation : Occupation Mode)
    (firstAbsent : first ∉ occupation) (secondAbsent : second ∉ occupation)
    (distinct : first ≠ second) :
    koszulSign first (insert second occupation) * koszulSign second occupation =
      -(koszulSign second (insert first occupation) * koszulSign first occupation) := by
  rcases lt_or_gt_of_ne distinct with before | after
  · rw [koszulSign_insert_of_not_lt second first occupation secondAbsent
          (not_lt_of_ge (le_of_lt before))]
    rw [koszulSign_insert_of_lt first second occupation firstAbsent before]
    simp [mul_comm]
  · rw [koszulSign_insert_of_lt second first occupation secondAbsent after]
    rw [koszulSign_insert_of_not_lt first second occupation firstAbsent
          (not_lt_of_ge (le_of_lt after))]
    simp [mul_comm]

/-- The annihilation-order sign is the same antisymmetric insertion law read from the target. -/
theorem koszulSign_cross (first second : Mode) (occupation : Occupation Mode)
    (firstAbsent : first ∉ occupation) (secondAbsent : second ∉ occupation)
    (distinct : first ≠ second) :
    koszulSign first occupation * koszulSign second (insert first occupation) =
      -(koszulSign second occupation * koszulSign first (insert second occupation)) := by
  have swapped := koszulSign_swap second first occupation secondAbsent firstAbsent distinct.symm
  simpa [mul_assoc, mul_comm, mul_left_comm] using swapped

/-- The mixed creation/annihilation order also reverses sign at distinct modes. -/
theorem koszulSign_double_insert (first second : Mode) (occupation : Occupation Mode)
    (firstAbsent : first ∉ occupation) (secondAbsent : second ∉ occupation)
    (distinct : first ≠ second) :
    koszulSign first (insert second occupation) *
        koszulSign second (insert first occupation) =
      -(koszulSign second occupation * koszulSign first occupation) := by
  rcases lt_or_gt_of_ne distinct with before | after
  · rw [koszulSign_insert_of_not_lt second first occupation secondAbsent
          (not_lt_of_ge (le_of_lt before))]
    rw [koszulSign_insert_of_lt first second occupation firstAbsent before]
    simp [mul_comm]
  · rw [koszulSign_insert_of_lt second first occupation secondAbsent after]
    rw [koszulSign_insert_of_not_lt first second occupation firstAbsent
          (not_lt_of_ge (le_of_lt after))]
    simp [mul_comm]

/-- [definition] Creation amplitude at a target occupation.  A target which already lacks the
addressed mode cannot have arisen by creating it. -/
def create (mode : Mode) (state : FockState Mode) : FockState Mode :=
  fun target ↦
    if mode ∈ target then
      koszulSign mode (target.erase mode) * state (target.erase mode)
    else
      0

/-- [definition] Annihilation amplitude at a target occupation.  The source is reconstructed by
inserting the removed mode into the target. -/
def annihilate (mode : Mode) (state : FockState Mode) : FockState Mode :=
  fun target ↦
    if mode ∈ target then
      0
    else
      koszulSign mode target * state (insert mode target)

/-- Creation is complex-linear on the finite occupation carrier. -/
def creation (mode : Mode) : FockState Mode →ₗ[ℂ] FockState Mode where
  toFun := create mode
  map_add' left right := by
    funext target
    simp only [create, Pi.add_apply]
    split <;> simp_all [mul_add]
  map_smul' scalar state := by
    funext target
    simp only [create, Pi.smul_apply, smul_eq_mul]
    split <;> simp_all
    ring

/-- Annihilation is complex-linear on the finite occupation carrier. -/
def annihilation (mode : Mode) : FockState Mode →ₗ[ℂ] FockState Mode where
  toFun := annihilate mode
  map_add' left right := by
    funext target
    simp only [annihilate, Pi.add_apply]
    split <;> simp_all [mul_add]
  map_smul' scalar state := by
    funext target
    simp only [annihilate, Pi.smul_apply, smul_eq_mul]
    split <;> simp_all
    ring

@[simp] theorem create_zero (mode : Mode) : create mode (0 : FockState Mode) = 0 := by
  funext occupation
  simp [create]

@[simp] theorem annihilate_zero (mode : Mode) : annihilate mode (0 : FockState Mode) = 0 := by
  funext occupation
  simp [annihilate]

/-- A target which lacks the addressed mode receives no creation amplitude. -/
theorem create_eq_zero_of_not_mem (mode : Mode) (state : FockState Mode)
    (occupation : Occupation Mode) (unoccupied : mode ∉ occupation) :
    create mode state occupation = 0 := by
  simp [create, unoccupied]

/-- A target which still contains the addressed mode receives no annihilation amplitude. -/
theorem annihilate_eq_zero_of_mem (mode : Mode) (state : FockState Mode)
    (occupation : Occupation Mode) (occupied : mode ∈ occupation) :
    annihilate mode state occupation = 0 := by
  simp [annihilate, occupied]

/-- Two creations at the same mode vanish. -/
theorem create_create_same (mode : Mode) (state : FockState Mode) :
    create mode (create mode state) = 0 := by
  funext occupation
  by_cases occupied : mode ∈ occupation
  · simp [create, occupied]
  · simp [create, occupied]

/-- Two annihilations at the same mode vanish. -/
theorem annihilate_annihilate_same (mode : Mode) (state : FockState Mode) :
    annihilate mode (annihilate mode state) = 0 := by
  funext occupation
  by_cases occupied : mode ∈ occupation
  · simp [annihilate, occupied]
  · simp [annihilate, occupied]

/-- The same-mode mixed anticommutator is the identity. -/
theorem annihilate_create_add_create_annihilate_same
    (mode : Mode) (state : FockState Mode) :
    annihilate mode (create mode state) + create mode (annihilate mode state) = state := by
  funext occupation
  by_cases occupied : mode ∈ occupation
  · simp [annihilate, create, occupied]
    have square := koszulSign_mul_self mode (occupation.erase mode)
    calc
      koszulSign mode (occupation.erase mode) *
          (koszulSign mode (occupation.erase mode) * state occupation) =
          (koszulSign mode (occupation.erase mode) *
            koszulSign mode (occupation.erase mode)) * state occupation := by ring
      _ = state occupation := by rw [square]; simp
  · simp [annihilate, create, occupied]
    have square := koszulSign_mul_self mode occupation
    calc
      koszulSign mode occupation * (koszulSign mode occupation * state occupation) =
          (koszulSign mode occupation * koszulSign mode occupation) * state occupation := by ring
      _ = state occupation := by rw [square]; simp

/-- Erasing two distinct addressed modes is independent of the presentation order of erasure. -/
theorem erase_erase_comm {EraseMode : Type*} [DecidableEq EraseMode]
    (occupation : Occupation EraseMode) (first second : EraseMode) :
    (occupation.erase first).erase second = (occupation.erase second).erase first := by
  ext mode
  simp only [Finset.mem_erase]
  aesop

/-- Creation operators at distinct modes anticommute. -/
theorem create_create_add_swap_of_ne (first second : Mode) (state : FockState Mode)
    (distinct : first ≠ second) :
    create first (create second state) + create second (create first state) = 0 := by
  funext occupation
  by_cases firstOccupied : first ∈ occupation
  · by_cases secondOccupied : second ∈ occupation
    · have secondAfterFirst : second ∈ occupation.erase first := by
        simp [secondOccupied, distinct.symm]
      have firstAfterSecond : first ∈ occupation.erase second := by
        simp [firstOccupied, distinct]
      simp only [Pi.add_apply]
      rw [create, create, create, create]
      simp only [firstOccupied, secondOccupied, secondAfterFirst, firstAfterSecond,
        ↓reduceIte]
      let base := (occupation.erase first).erase second
      have firstAbsent : first ∉ base := by
        simp [base]
      have secondAbsent : second ∉ base := by
        simp [base]
      have eraseFirst : occupation.erase first = insert second base := by
        exact (Finset.insert_erase secondAfterFirst).symm
      have eraseSecond : occupation.erase second = insert first base := by
        rw [show base = (occupation.erase second).erase first by
          exact erase_erase_comm occupation first second]
        exact (Finset.insert_erase firstAfterSecond).symm
      rw [eraseFirst, eraseSecond]
      simp only [Finset.erase_insert secondAbsent, Finset.erase_insert firstAbsent]
      have sign := koszulSign_swap first second base firstAbsent secondAbsent distinct
      calc
        koszulSign first (insert second base) *
              (koszulSign second base * state base) +
            koszulSign second (insert first base) *
              (koszulSign first base * state base) =
            (koszulSign first (insert second base) * koszulSign second base +
              koszulSign second (insert first base) * koszulSign first base) * state base := by
                ring
        _ = 0 := by rw [sign]; ring
    · simp [create, firstOccupied, secondOccupied]
  · simp [create, firstOccupied]

/-- The creation--creation CAR law, including its same-mode nilpotent branch. -/
theorem create_create_add_swap (first second : Mode) (state : FockState Mode) :
    create first (create second state) + create second (create first state) = 0 := by
  by_cases distinct : first ≠ second
  · exact create_create_add_swap_of_ne first second state distinct
  · have equal : first = second := not_ne_iff.mp distinct
    subst second
    simp [create_create_same]

/-- At distinct modes, reversing the order of two annihilations reverses the amplitude. -/
theorem annihilate_annihilate_eq_neg_swap_of_ne
    (first second : Mode) (state : FockState Mode) (distinct : first ≠ second) :
    annihilate first (annihilate second state) =
      -(annihilate second (annihilate first state)) := by
  funext occupation
  by_cases firstOccupied : first ∈ occupation
  · by_cases secondOccupied : second ∈ occupation
    · simp [annihilate, firstOccupied, secondOccupied]
    · simp [annihilate, firstOccupied, secondOccupied, distinct]
  · by_cases secondOccupied : second ∈ occupation
    · simp [annihilate, firstOccupied, secondOccupied, distinct.symm]
    · simp [annihilate, firstOccupied, secondOccupied, distinct, distinct.symm]
      have sign := koszulSign_cross first second occupation
        firstOccupied secondOccupied distinct
      calc
        koszulSign first occupation *
              (koszulSign second (insert first occupation) *
                state (insert second (insert first occupation))) =
            (koszulSign first occupation *
              koszulSign second (insert first occupation)) *
                state (insert second (insert first occupation)) := by ring
        _ = -(koszulSign second occupation *
              koszulSign first (insert second occupation)) *
                state (insert second (insert first occupation)) := by rw [sign]
        _ = -(koszulSign second occupation *
              (koszulSign first (insert second occupation) *
                state (insert first (insert second occupation)))) := by
          rw [Finset.insert_comm]
          ring

/-- The annihilation--annihilation CAR law, including its same-mode nilpotent branch. -/
theorem annihilate_annihilate_add_swap
    (first second : Mode) (state : FockState Mode) :
    annihilate first (annihilate second state) +
        annihilate second (annihilate first state) = 0 := by
  by_cases distinct : first ≠ second
  · rw [annihilate_annihilate_eq_neg_swap_of_ne first second state distinct]
    exact neg_add_cancel _
  · have equal : first = second := not_ne_iff.mp distinct
    subst second
    simp [annihilate_annihilate_same]

/-- At distinct modes, annihilation and creation anticommute. -/
theorem annihilate_create_eq_neg_create_annihilate_of_ne
    (first second : Mode) (state : FockState Mode) (distinct : first ≠ second) :
    annihilate first (create second state) =
      -(create second (annihilate first state)) := by
  funext occupation
  by_cases firstOccupied : first ∈ occupation
  · by_cases secondOccupied : second ∈ occupation <;>
      simp [annihilate, create, firstOccupied, secondOccupied, distinct]
  · by_cases secondOccupied : second ∈ occupation
    · simp [annihilate, create, firstOccupied, secondOccupied, distinct, distinct.symm]
      let base : Occupation Mode := occupation.erase second
      have firstAbsent : first ∉ base := by
        simp [base, Finset.mem_erase, firstOccupied]
      have secondAbsent : second ∉ base := by simp [base]
      have target : occupation = insert second base := by
        simpa [base] using (Finset.insert_erase secondOccupied).symm
      have transportedErase : (insert first (insert second base)).erase second =
          insert first base := by
        rw [Finset.erase_insert_of_ne distinct]
        rw [Finset.erase_insert secondAbsent]
      have sign := koszulSign_double_insert first second base
        firstAbsent secondAbsent distinct
      rw [target]
      rw [transportedErase]
      simp only [Finset.erase_insert secondAbsent]
      calc
        koszulSign first (insert second base) *
              (koszulSign second (insert first base) * state (insert first base)) =
            (koszulSign first (insert second base) *
              koszulSign second (insert first base)) * state (insert first base) := by ring
        _ = -(koszulSign second base * koszulSign first base) *
              state (insert first base) := by rw [sign]
        _ = -(koszulSign second base *
              (koszulSign first base * state (insert first base))) := by ring
    · simp [annihilate, create, firstOccupied, secondOccupied, distinct.symm]

/-- The complete mixed CAR law.  Equal modes return the identity; distinct modes cancel. -/
theorem annihilate_create_add_create_annihilate
    (first second : Mode) (state : FockState Mode) :
    annihilate first (create second state) + create second (annihilate first state) =
      if first = second then state else 0 := by
  by_cases distinct : first ≠ second
  · simp only [distinct, ↓reduceIte]
    rw [annihilate_create_eq_neg_create_annihilate_of_ne first second state distinct]
    exact neg_add_cancel _
  · have equal : first = second := not_ne_iff.mp distinct
    subst second
    simpa using annihilate_create_add_create_annihilate_same first state

/-! ## Vacuum, number grading, and the finite adjoint chart -/

/-- [definition] The empty occupation is the finite vacuum section. -/
def vacuum : FockState Mode :=
  fun occupation ↦ if occupation = ∅ then 1 else 0

/-- Every annihilation kills the vacuum. -/
theorem annihilate_vacuum (mode : Mode) : annihilate mode (vacuum (Mode := Mode)) = 0 := by
  funext occupation
  by_cases occupied : mode ∈ occupation
  · simp [annihilate, occupied]
  · simp [annihilate, vacuum, occupied]

/-- Creating one mode from vacuum returns unit amplitude at its singleton occupation. -/
theorem create_vacuum_singleton (mode : Mode) :
    create mode (vacuum (Mode := Mode)) {mode} = 1 := by
  simp [create, vacuum, koszulSign, prefixCount, preceding]

/-- [definition] The occupation-number grading. -/
def particleNumber (occupation : Occupation Mode) : ℕ := occupation.card

/-- A nonzero creation return comes from the immediately lower particle-number sector. -/
theorem particleNumber_create_source
    (mode : Mode) (state : FockState Mode) (target : Occupation Mode)
    (nonzero : create mode state target ≠ 0) :
    mode ∈ target ∧ particleNumber target = particleNumber (target.erase mode) + 1 := by
  by_cases occupied : mode ∈ target
  · refine ⟨occupied, ?_⟩
    simpa [particleNumber] using (Finset.card_erase_add_one occupied).symm
  · exact (nonzero (by simp [create, occupied])).elim

/-- A nonzero annihilation return comes from the immediately higher particle-number sector. -/
theorem particleNumber_annihilate_source
    (mode : Mode) (state : FockState Mode) (target : Occupation Mode)
    (nonzero : annihilate mode state target ≠ 0) :
    mode ∉ target ∧ particleNumber (insert mode target) = particleNumber target + 1 := by
  by_cases occupied : mode ∈ target
  · exact (nonzero (by simp [annihilate, occupied])).elim
  · refine ⟨occupied, ?_⟩
    simp [particleNumber, occupied]

/-- The finite occupation population has the expected power-set cardinality. -/
theorem card_occupation {FiniteMode : Type*} [DecidableEq FiniteMode] [Fintype FiniteMode] :
    Fintype.card (Occupation FiniteMode) = 2 ^ Fintype.card FiniteMode := by
  simp [Occupation]

/-- [definition] Creation coefficients in the occupation basis, with target as row and source as
column. -/
def creationMatrix (mode : Mode) : Matrix (Occupation Mode) (Occupation Mode) ℂ :=
  fun target source ↦
    if mode ∉ source ∧ target = insert mode source then koszulSign mode source else 0

/-- [definition] Annihilation coefficients in the same occupation basis. -/
def annihilationMatrix (mode : Mode) : Matrix (Occupation Mode) (Occupation Mode) ℂ :=
  fun target source ↦
    if mode ∈ source ∧ target = source.erase mode then koszulSign mode target else 0

/-- Complex conjugation fixes every real Koszul sign. -/
theorem conj_koszulSign (mode : Mode) (occupation : Occupation Mode) :
    starRingEnd ℂ (koszulSign mode occupation) = koszulSign mode occupation := by
  simp [koszulSign]

/-- In the finite occupation basis, annihilation is the conjugate transpose of creation. -/
theorem annihilationMatrix_eq_conjTranspose_creationMatrix (mode : Mode) :
    annihilationMatrix mode = (creationMatrix mode).conjTranspose := by
  ext target source
  by_cases sourceOccupied : mode ∈ source
  · by_cases targetEq : target = source.erase mode
    · subst target
      simp [annihilationMatrix, creationMatrix, Matrix.conjTranspose_apply,
        sourceOccupied, conj_koszulSign]
    · simp only [annihilationMatrix, sourceOccupied, targetEq, and_false, ↓reduceIte,
        Matrix.conjTranspose_apply, creationMatrix]
      by_cases targetAbsent : mode ∉ target
      · by_cases sourceEq : source = insert mode target
        · have : target = source.erase mode := by
            rw [sourceEq]
            exact (Finset.erase_insert targetAbsent).symm
          exact (targetEq this).elim
        · simp [targetAbsent, sourceEq]
      · simp [targetAbsent]
  · simp only [annihilationMatrix, sourceOccupied, false_and, ↓reduceIte,
      Matrix.conjTranspose_apply, creationMatrix]
    by_cases targetAbsent : mode ∉ target
    · by_cases sourceEq : source = insert mode target
      · have sourceHas : mode ∈ source := by simp [sourceEq]
        exact (sourceOccupied sourceHas).elim
      · simp [targetAbsent, sourceEq]
    · simp [targetAbsent]

/-- The creation--creation CAR law as equality of linear transports. -/
theorem creation_comp_creation_add_swap (first second : Mode) :
    (creation first).comp (creation second) +
        (creation second).comp (creation first) = 0 := by
  ext state occupation
  exact congrFun (create_create_add_swap first second state) occupation

/-- The annihilation--annihilation CAR law as equality of linear transports. -/
theorem annihilation_comp_annihilation_add_swap (first second : Mode) :
    (annihilation first).comp (annihilation second) +
        (annihilation second).comp (annihilation first) = 0 := by
  ext state occupation
  exact congrFun (annihilate_annihilate_add_swap first second state) occupation

/-- The mixed CAR law as equality of linear transports. -/
theorem annihilation_comp_creation_add_creation_comp_annihilation
    (first second : Mode) :
    (annihilation first).comp (creation second) +
        (creation second).comp (annihilation first) =
      if first = second then LinearMap.id else 0 := by
  by_cases distinct : first ≠ second
  · simp only [distinct, ↓reduceIte]
    ext state occupation
    change annihilate first (create second state) occupation +
      create second (annihilate first state) occupation = 0
    simpa [distinct] using congrFun
      (annihilate_create_add_create_annihilate first second state) occupation
  · have equal : first = second := not_ne_iff.mp distinct
    subst second
    simp only [if_pos]
    ext state occupation
    change annihilate first (create first state) occupation +
      create first (annihilate first state) occupation = state occupation
    exact congrFun (annihilate_create_add_create_annihilate_same first state) occupation

section SuperposedModes

variable [Fintype Mode]

/-- A one-particle mode may be any complex superposition of the presentation basis. -/
def superposedCreation (coefficients : Mode → ℂ) : Module.End ℂ (FockState Mode) :=
  ∑ mode, coefficients mode • creation mode

/-- Exchange antisymmetry is preserved for arbitrary superposed modes. -/
theorem superposedCreation_anticommute (left right : Mode → ℂ) :
    superposedCreation left * superposedCreation right +
      superposedCreation right * superposedCreation left = 0 := by
  unfold superposedCreation
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm (f := fun j i =>
    (right j * left i) • (creation j * creation i))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [mul_comm (right j) (left i), ← smul_add]
  have exchange : creation i * creation j + creation j * creation i = 0 :=
    creation_comp_creation_add_swap i j
  rw [exchange, smul_zero]

/-- Exclusion concerns the complete one-particle mode, not a chosen spatial/basis label. -/
theorem superposedCreation_square_zero (coefficients : Mode → ℂ) :
    superposedCreation coefficients * superposedCreation coefficients = 0 := by
  have exchange := superposedCreation_anticommute coefficients coefficients
  have doubled : (2 : ℂ) • (superposedCreation coefficients * superposedCreation coefficients) = 0 := by
    simpa only [two_smul ℂ] using exchange
  exact (smul_eq_zero.mp doubled).resolve_left (by norm_num)

end SuperposedModes

/-- A concrete two-mode control simultaneously exhibits exclusion and the distinct mixed CAR
return on the finite vacuum. -/
theorem twoMode_exclusion_and_mixed_control :
    create (0 : Fin 2) (create (0 : Fin 2) (vacuum (Mode := Fin 2))) = 0 ∧
      annihilate (0 : Fin 2) (create (1 : Fin 2) (vacuum (Mode := Fin 2))) +
        create (1 : Fin 2) (annihilate (0 : Fin 2) (vacuum (Mode := Fin 2))) = 0 := by
  constructor
  · exact create_create_same (0 : Fin 2) (vacuum (Mode := Fin 2))
  · simpa using annihilate_create_add_create_annihilate
      (0 : Fin 2) (1 : Fin 2) (vacuum (Mode := Fin 2))

section Audit

#print axioms mode_not_mem_preceding
#print axioms preceding_erase_self
#print axioms preceding_insert_self
#print axioms koszulSign_mul_self
#print axioms create_eq_zero_of_not_mem
#print axioms annihilate_eq_zero_of_mem
#print axioms create_zero
#print axioms annihilate_zero
#print axioms create_create_same
#print axioms annihilate_annihilate_same
#print axioms annihilate_create_add_create_annihilate_same
#print axioms erase_erase_comm
#print axioms create_create_add_swap
#print axioms annihilate_annihilate_add_swap
#print axioms annihilate_create_add_create_annihilate
#print axioms annihilate_vacuum
#print axioms create_vacuum_singleton
#print axioms particleNumber_create_source
#print axioms particleNumber_annihilate_source
#print axioms card_occupation
#print axioms annihilationMatrix_eq_conjTranspose_creationMatrix
#print axioms creation_comp_creation_add_swap
#print axioms superposedCreation_anticommute
#print axioms superposedCreation_square_zero
#print axioms annihilation_comp_annihilation_add_swap
#print axioms annihilation_comp_creation_add_creation_comp_annihilation
#print axioms twoMode_exclusion_and_mixed_control

end Audit

end Soma.Holonics.Computation.HolonicFermionicOccupation
