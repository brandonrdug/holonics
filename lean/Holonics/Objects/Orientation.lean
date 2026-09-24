import Holonics.Objects.Pairing

/-!
# Orientation of a reversing loop: the cycle theorem subsumes the Junction statement

[definition] Object 1 of `docs/ELEMENTARY_OBJECTS.md`: orientation exists only in the pairing, and
a cycle of cells whose `±1` joint relations multiply to `−1` admits no orientation
(`Objects/Pairing.no_orientation_of_reversing_cycle`). This module restates that theorem for
cycles of named faces on any carrier and derives from it the intended content of
`Transport/JunctionLaw.no_consistent_orientation_on_a_reversing_loop`.

[proved-derived; formal-checked] What is proved.

1. **Reversing closed walks.** For any face carrier and any closed walk `c : Fin (k+1) → Face`
   whose required joint relations `r` multiply to `−1`, no unit sign on the faces satisfies
   `sign (c i) · sign (c (i+1)) = r i` (`reversing_closed_walk_has_no_orientation`). The relation
   is data of the walk, so the statement has content whenever `k ≥ 1`.
2. **Preserving simple cycles are orientable** by a sign on the whole carrier
   (`preserving_simple_cycle_has_orientation`), extending `orientation_of_preserving_cycle`
   off the cycle by `+1`.
3. **The Junction statement is the one-face case.** With one face and the relation `−1` on its
   self-joint, (1) returns exactly the proposition of
   `JunctionLaw.no_consistent_orientation_on_a_reversing_loop`
   (`junction_statement_from_cycle`). That proposition carries no loop datum: the unit clause
   alone forces `s () · s () = 1` for every sign (`junction_hypothesis_is_refuted_by_unit_alone`),
   so its `−1` conjunct is refuted before any loop is read; it is subsumed, not strengthened.
4. **Witness with content.** The Möbius band cut into two faces with joint relations `(1, −1)`
   admits no orientation although each joint relation is separately satisfiable
   (`two_face_mobius_band`), while the annulus `(−1, −1)` is oriented by `(1, −1)`
   (`two_face_annulus`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Objects.Orientation

open Holonics.Objects.Pairing

variable {Face : Type*}

/-- [proved-derived; formal-checked] **A reversing closed walk of faces has no orientation**, for
any face carrier: compose the sign with the walk and apply
`Pairing.no_orientation_of_reversing_cycle`. -/
theorem reversing_closed_walk_has_no_orientation {k : ℕ} (c : Fin (k + 1) → Face)
    (r : Fin (k + 1) → ℤ) (reversing : ∏ i, r i = -1) :
    ¬ ∃ sign : Face → ℤ, (∀ f, sign f * sign f = 1) ∧
      ∀ i, sign (c i) * sign (c (i + 1)) = r i := by
  rintro ⟨sign, unit, rel⟩
  exact no_orientation_of_reversing_cycle r reversing ⟨sign ∘ c, fun i => unit (c i), rel⟩

open Classical in
/-- [proved-derived; formal-checked] **A preserving simple cycle is orientable on the whole
carrier**: the cycle's orientation from `Pairing.orientation_of_preserving_cycle`, extended by `+1`
off the cycle. -/
theorem preserving_simple_cycle_has_orientation {k : ℕ} (c : Fin (k + 1) → Face)
    (hc : Function.Injective c) (r : Fin (k + 1) → ℤ) (unitR : ∀ i, r i * r i = 1)
    (preserving : ∏ i, r i = 1) :
    ∃ sign : Face → ℤ, (∀ f, sign f * sign f = 1) ∧
      ∀ i, sign (c i) * sign (c (i + 1)) = r i := by
  obtain ⟨s, unit, rel⟩ := orientation_of_preserving_cycle r unitR preserving
  refine ⟨fun f => if h : ∃ i, c i = f then s h.choose else 1, ?_, ?_⟩
  · intro f
    by_cases h : ∃ i, c i = f
    · simp only [dif_pos h]; exact unit _
    · simp [dif_neg h]
  · have hsign : ∀ j, (if h : ∃ i, c i = c j then s h.choose else 1) = s j := by
      intro j
      have h : ∃ i, c i = c j := ⟨j, rfl⟩
      rw [dif_pos h, hc h.choose_spec]
    intro i
    simp only [hsign]
    exact rel i

/-- [proved-derived; formal-checked] **The Junction statement is the one-face case of the cycle
theorem**: one face, one self-joint, relation `−1`. -/
theorem junction_statement_from_cycle :
    ¬ ∃ sign : Unit → ℤ, (∀ f, sign f * sign f = 1) ∧ sign () * sign () = -1 := by
  rintro ⟨sign, unit, reversing⟩
  exact reversing_closed_walk_has_no_orientation (k := 0) (fun _ => ()) (fun _ => -1)
    (by simp) ⟨sign, unit, fun _ => reversing⟩

/-- [counterexample; formal-checked] **The Junction hypothesis carries no loop datum.** For every
sign, the unit clause alone gives `s () · s () = 1`, so the `−1` conjunct is refuted without
reading any loop or relation. -/
theorem junction_hypothesis_is_refuted_by_unit_alone (sign : Unit → ℤ)
    (unit : ∀ f, sign f * sign f = 1) : sign () * sign () = 1 ∧ sign () * sign () ≠ -1 :=
  ⟨unit (), by rw [unit ()]; decide⟩

/-- [proved-derived; formal-checked] **Witness with content: the two-face Möbius band.** The joint
relations `(1, −1)` multiply to `−1`, so no sign orients the band, although each joint relation is
satisfiable on its own (`(1, 1)` meets the first, `(1, −1)` the second). -/
theorem two_face_mobius_band :
    (¬ ∃ sign : Fin 2 → ℤ, (∀ f, sign f * sign f = 1) ∧
        ∀ i : Fin 2, sign (id i) * sign (id (i + 1)) = ![1, -1] i) ∧
      ((1 : ℤ) * 1 = ![(1 : ℤ), -1] 0) ∧ ((1 : ℤ) * -1 = ![(1 : ℤ), -1] 1) :=
  ⟨reversing_closed_walk_has_no_orientation id ![1, -1] (by simp [Fin.prod_univ_two]),
    by decide, by decide⟩

/-- [proved-derived; formal-checked] **Witness: the two-face annulus** `(−1, −1)` multiplies to
`+1` and is oriented by `(1, −1)`. -/
theorem two_face_annulus :
    ∃ sign : Fin 2 → ℤ, (∀ f, sign f * sign f = 1) ∧
      ∀ i : Fin 2, sign (id i) * sign (id (i + 1)) = ![-1, -1] i :=
  preserving_simple_cycle_has_orientation id Function.injective_id ![-1, -1] (by decide)
    (by simp [Fin.prod_univ_two])

section Audit
#print axioms reversing_closed_walk_has_no_orientation
#print axioms preserving_simple_cycle_has_orientation
#print axioms junction_statement_from_cycle
#print axioms junction_hypothesis_is_refuted_by_unit_alone
#print axioms two_face_mobius_band
#print axioms two_face_annulus
end Audit

end Holonics.Objects.Orientation
