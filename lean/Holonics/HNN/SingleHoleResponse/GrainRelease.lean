import Holonics.Foundation.ReceiverRelease

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

section GrainAndRelease

variable {Completion Class : Type*} [Fintype Completion] [DecidableEq Completion]
  [Fintype Class] [DecidableEq Class]

/-- A completion's exact greatest face, supplied with its exact maximum value. This leaves the
receiving GrainCell chart explicit: callers must identify this rational ordered face with their
actual chart before using the theorem. -/
def exactLeaders (reading : Class → ℚ) (greatest : ℚ) : Finset Class :=
  Finset.univ.filter fun c => reading c = greatest

/-- The compatible completed-model leaders are the union of the exact leader faces of each
completion. -/
def exactLeaderUnion (reading : Completion → Class → ℚ) (greatest : Completion → ℚ)
    (compatible : Finset Completion) : Finset Class :=
  compatible.biUnion fun x => exactLeaders (reading x) (greatest x)

/-- Exact finite leader-union soundness: every published class is a greatest class for an admitted
completion, and every such greatest class is published. Ties are retained as a set. -/
theorem exactLeaderUnion_mem_iff (reading : Completion → Class → ℚ)
    (greatest : Completion → ℚ) (compatible : Finset Completion) (c : Class) :
    c ∈ exactLeaderUnion reading greatest compatible ↔
      ∃ x ∈ compatible, reading x c = greatest x := by
  simp [exactLeaderUnion, exactLeaders]

/-- With a certified exact maximum for each completed reading, the union contains precisely the
greatest classes for admitted completions. The certificate preserves tied leaders. -/
theorem exactLeaderUnion_sound (reading : Completion → Class → ℚ)
    (greatest : Completion → ℚ) (compatible : Finset Completion)
    (hmaximum : ∀ x ∈ compatible,
      (∀ c, reading x c ≤ greatest x) ∧ ∃ c, reading x c = greatest x) :
    ∀ c, c ∈ exactLeaderUnion reading greatest compatible ↔
      ∃ x ∈ compatible, (∀ j, reading x j ≤ greatest x) ∧ reading x c = greatest x := by
  intro c
  rw [exactLeaderUnion_mem_iff]
  constructor
  · rintro ⟨x, hx, hread⟩
    exact ⟨x, hx, (hmaximum x hx).1, hread⟩
  · rintro ⟨x, hx, _, hread⟩
    exact ⟨x, hx, hread⟩

/-- A constant exact scalar receiving face has zero width over its compatible finite family and is
releasable at tolerance zero under the existing receiver law. -/
theorem constant_face_released_at_zero
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → ℚ)
    (hconstant : ∀ x ∈ compatible, ∀ y ∈ compatible, reading x = reading y) :
    Holonics.Foundation.ReceiverRelease.Releasable compatible hcompat reading 0 := by
  change Holonics.Foundation.ReceiverRelease.width compatible hcompat reading ≤ 0
  have hz : Holonics.Foundation.ReceiverRelease.width compatible hcompat reading = 0 :=
    (Holonics.Foundation.ReceiverRelease.width_eq_zero_iff compatible hcompat reading).2 hconstant
  rw [hz]
  exact le_rfl

/-- The declared holding law actually releases this constant receiver face at tolerance zero. -/
theorem holdingLaw_releases_constant_face_at_zero
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → ℚ)
    (hconstant : ∀ x ∈ compatible, ∀ y ∈ compatible, reading x = reading y) :
    (Holonics.Foundation.ReceiverRelease.holdingLaw Completion Unit Unit 0).decide
      compatible hcompat reading =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  have hz : Holonics.Foundation.ReceiverRelease.width compatible hcompat reading = 0 :=
    (Holonics.Foundation.ReceiverRelease.width_eq_zero_iff compatible hcompat reading).2 hconstant
  simp [Holonics.Foundation.ReceiverRelease.holdingLaw, hz]

/-- If the union of exact completed-model leader faces is the singleton `{winner}`, every emitted
leader agrees with that same class. Its exact class reading is therefore released at tolerance
zero by the existing holding law. -/
theorem singletonLeader_holdingLaw_release
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → Class → ℚ) (greatest : Completion → ℚ)
    (winner : Class) (hunionsingle : exactLeaderUnion reading greatest compatible = {winner})
    (emit : Completion → Class)
    (hemits : ∀ x ∈ compatible, emit x ∈ exactLeaders (reading x) (greatest x))
    (classReading : Class → ℚ) :
    (Holonics.Foundation.ReceiverRelease.holdingLaw Completion Unit Unit 0).decide
      compatible hcompat (fun x => classReading (emit x)) =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  apply holdingLaw_releases_constant_face_at_zero
  intro x hx y hy
  have hxUnion : emit x ∈ exactLeaderUnion reading greatest compatible := by
    rw [exactLeaderUnion_mem_iff]
    exact ⟨x, hx, (Finset.mem_filter.mp (hemits x hx)).2⟩
  have hyUnion : emit y ∈ exactLeaderUnion reading greatest compatible := by
    rw [exactLeaderUnion_mem_iff]
    exact ⟨y, hy, (Finset.mem_filter.mp (hemits y hy)).2⟩
  have hxWinner : emit x = winner := by
    rw [hunionsingle] at hxUnion
    simpa using hxUnion
  have hyWinner : emit y = winner := by
    rw [hunionsingle] at hyUnion
    simpa using hyUnion
  rw [hxWinner, hyWinner]

end GrainAndRelease

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_mem_iff
#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_sound
#print axioms Holonics.HNN.SingleHoleResponse.constant_face_released_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.holdingLaw_releases_constant_face_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.singletonLeader_holdingLaw_release
