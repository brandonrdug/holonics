import HolonicsResearch.Landmarks.CokernelCalculus
import HolonicsResearch.HNN.LoopPacking
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

/-!
# The grain of a class is a period: a class carried only in a multiple closes after that many turns

The record of November 20 on the integer failure of the Hodge relation (atlas
`hodge.failure-group-finite`, `coupling.grain-is-a-period`) reads a class that the carriers reach
only in a multiple as one object with a turn that has no fixed point: neither has a carrier at
grain one, and both close at the grain `k`. This file states the finite part.

`Landmarks/CokernelCalculus` holds the species (`ReachableOnlyInMultiple`: some nonzero multiple of
a class lies in the subgroup the carriers generate and the class does not), with Kollár's shape on
the Hodge side and the descent's on the side of Birch and Swinnerton-Dyer, and
`Landmarks/SmithCokernel` reads the cokernel by its invariants. `HNN/LoopPacking` holds the ring of
sign-reversing contacts (`odd_ring_breaks`, `even_ring_has_key`). What is added here:

1. **The grain.** The order of a class in the quotient by the carried classes is one number,
   `grain S b`: the multiples of `b` that are carried are the multiples of the grain
   (`nsmul_mem_iff_grain_dvd`). A class is carried when its grain is one (`mem_iff_grain_eq_one`),
   carried in some multiple when its grain is positive (`grain_pos_iff`), and two carried
   multiples give their greatest common divisor (`nsmul_mem_gcd`). A class reachable only in the
   multiple `m` has a grain above one that divides `m` (`grain_of_reachableOnlyInMultiple`), and
   `1` against the carried class `2` has grain `2` (`grain_one_mod_two`; the tree's
   `IntegralCokernel.kollar_witness` is the same class in `ℚ`).
2. **A reading with rational values that is blind to the carriers is blind to every class of
   positive grain** (`rational_reading_blind`): this is why no obstruction that such a reading
   carries survives a change to rational coefficients.
3. **The period.** A turn `h` of a group returns a state after `m` turns when the order of `h`
   divides `m` (`turns_close_iff`), a turn that is not the identity rests nowhere (`no_rest`), and
   every state moves on a cycle whose length is the order (`period_of_turn`). The half-turn
   `−1` and the flip of two digits have period two and no fixed point (`half_turn_period`,
   `half_turn_no_rest`, `flip_period`, `flip_no_rest`); the flip is the map of the diagonal
   argument (`Foundation/FiniteKey.two_digits_are_a_gap`).
4. **The cover.** An odd ring of sign-reversing contacts, unwrapped `m` times, has a key when `m`
   is even and at no odd `m` (`cover_of_odd_ring_has_key_iff`): the grain of its class is two.

Sources, `from training`: the order of an element and Lagrange's count are standard; the
integer failure of the Hodge relation is Atiyah and Hirzebruch 1962 and Kollár 1992, read in the
record and not stated here. The reading of a grain as the period of an alternation of carriers is
`agent-inferred` and stands in the record.

[proved-standard; formal-checked] What is proved: `nsmul_mem_iff_grain_dvd`,
`mem_iff_grain_eq_one`, `grain_pos_iff`, `nsmul_mem_gcd`, `grain_of_reachableOnlyInMultiple`,
`grain_one_mod_two`, `rational_reading_blind`, `turns_close_iff`, `no_rest`, `iterate_turn`,
`period_of_turn`, `orderOf_neg_one_units`, `half_turn_period`, `half_turn_no_rest`, `flip_period`,
`flip_no_rest`, `cover_of_odd_ring_has_key_iff`.

Not proved here: any statement about a variety. That the failure group of a polarized variety is
finite is the Hodge conjecture.
-/

namespace Holonics.Landmarks.GrainPeriod

open Holonics.Landmarks.CokernelCalculus Holonics.HNN.LoopPacking

/-! ## 1. The grain of a class -/

section Grain

variable {G : Type*} [AddCommGroup G]

/-- [definition] **The grain of a class** against the carried classes `S`: its order in the
quotient `G ⧸ S`. It is `0` when no positive multiple of the class is carried. -/
noncomputable def grain (S : AddSubgroup G) (b : G) : ℕ :=
  addOrderOf (QuotientAddGroup.mk b : G ⧸ S)

/-- [proved-standard; formal-checked] **The carried multiples of a class are the multiples of its
grain.** -/
theorem nsmul_mem_iff_grain_dvd (S : AddSubgroup G) (b : G) (k : ℕ) :
    k • b ∈ S ↔ grain S b ∣ k := by
  rw [grain, addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul,
    QuotientAddGroup.eq_zero_iff]

/-- [proved-standard; formal-checked] A class is carried when its grain is one. -/
theorem mem_iff_grain_eq_one (S : AddSubgroup G) (b : G) : b ∈ S ↔ grain S b = 1 := by
  rw [grain, AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff]

/-- [proved-standard; formal-checked] A class is carried in some positive multiple when its grain
is positive. -/
theorem grain_pos_iff (S : AddSubgroup G) (b : G) :
    0 < grain S b ↔ ∃ k : ℕ, 0 < k ∧ k • b ∈ S := by
  constructor
  · intro h
    exact ⟨grain S b, h, (nsmul_mem_iff_grain_dvd S b _).2 dvd_rfl⟩
  · rintro ⟨k, hk, hmem⟩
    exact Nat.pos_of_dvd_of_pos ((nsmul_mem_iff_grain_dvd S b k).1 hmem) hk

/-- [proved-standard; formal-checked] Two carried multiples give their greatest common divisor. -/
theorem nsmul_mem_gcd (S : AddSubgroup G) (b : G) {k l : ℕ} (hk : k • b ∈ S) (hl : l • b ∈ S) :
    Nat.gcd k l • b ∈ S :=
  (nsmul_mem_iff_grain_dvd S b _).2
    (Nat.dvd_gcd ((nsmul_mem_iff_grain_dvd S b k).1 hk) ((nsmul_mem_iff_grain_dvd S b l).1 hl))

/-- [proved-derived; formal-checked] **A class reachable only in the multiple `m` has a grain above
one that divides `m`.** -/
theorem grain_of_reachableOnlyInMultiple {S : Set G} {α : G} {m : ℤ}
    (h : ReachableOnlyInMultiple S α m) :
    grain (AddSubgroup.closure S) α ∣ m.natAbs ∧ 1 < grain (AddSubgroup.closure S) α := by
  obtain ⟨hm, hmul, hnot⟩ := h
  have hnat : m.natAbs • α ∈ AddSubgroup.closure S := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simpa using hmul
    · simpa using hmul
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  refine ⟨(nsmul_mem_iff_grain_dvd _ _ _).1 hnat, ?_⟩
  have h0 : 0 < grain (AddSubgroup.closure S) α := (grain_pos_iff _ _).2 ⟨_, hpos, hnat⟩
  have h1 : grain (AddSubgroup.closure S) α ≠ 1 := fun h =>
    hnot ((mem_iff_grain_eq_one _ _).2 h)
  omega

/-- [counterexample; formal-checked] **The smallest class of grain two**: `1` against the carried
class `2` in the integers. -/
theorem grain_one_mod_two : grain (AddSubgroup.zmultiples (2 : ℤ)) 1 = 2 := by
  have hd : grain (AddSubgroup.zmultiples (2 : ℤ)) 1 ∣ 2 :=
    (nsmul_mem_iff_grain_dvd _ _ _).1 (by
      rw [Int.mem_zmultiples_iff]
      norm_num)
  have hne : grain (AddSubgroup.zmultiples (2 : ℤ)) 1 ≠ 1 := fun h => by
    have h2 := (mem_iff_grain_eq_one (AddSubgroup.zmultiples (2 : ℤ)) 1).2 h
    rw [Int.mem_zmultiples_iff] at h2
    omega
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact absurd h hne
  · exact h

/-- [proved-derived; formal-checked] **A reading with rational values that vanishes on the carried
classes vanishes on every class of positive grain.** -/
theorem rational_reading_blind {V : Type*} [AddCommGroup V] [Module ℚ V] (S : AddSubgroup G)
    (φ : G →+ V) (hφ : ∀ s ∈ S, φ s = 0) (b : G) (hb : 0 < grain S b) : φ b = 0 := by
  have hmem : grain S b • b ∈ S := (nsmul_mem_iff_grain_dvd S b _).2 dvd_rfl
  have h : grain S b • φ b = 0 := by rw [← map_nsmul, hφ _ hmem]
  have h2 : ((grain S b : ℕ) : ℚ) • φ b = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Nat.cast_eq_zero.mp h3) hb.ne'
  · exact h3

end Grain

/-! ## 2. The period of a turn -/

section Period

variable {A : Type*} [Group A]

/-- [proved-standard; formal-checked] **A turn returns a state after `m` turns when its order
divides `m`.** -/
theorem turns_close_iff (h x : A) (m : ℕ) : h ^ m * x = x ↔ orderOf h ∣ m := by
  rw [mul_eq_right, orderOf_dvd_iff_pow_eq_one]

/-- [proved-standard; formal-checked] A turn that is not the identity rests nowhere. -/
theorem no_rest {h : A} (hh : h ≠ 1) (x : A) : h * x ≠ x := fun e => hh (mul_eq_right.mp e)

/-- [proved-standard; formal-checked] `m` turns are the `m`-th power of the turn. -/
theorem iterate_turn (h x : A) (m : ℕ) : (fun y => h * y)^[m] x = h ^ m * x := by
  rw [mul_left_iterate]

/-- [proved-standard; formal-checked] **Every state moves on a cycle whose length is the order of
the turn.** -/
theorem period_of_turn (h x : A) : Function.minimalPeriod (fun y => h * y) x = orderOf h := by
  apply Nat.dvd_antisymm
  · have hp : Function.IsPeriodicPt (fun y => h * y) (orderOf h) x := by
      show (fun y => h * y)^[orderOf h] x = x
      rw [iterate_turn]
      exact (turns_close_iff h x _).2 dvd_rfl
    exact hp.minimalPeriod_dvd
  · have hp : (fun y => h * y)^[Function.minimalPeriod (fun y => h * y) x] x = x :=
      Function.isPeriodicPt_minimalPeriod (fun y => h * y) x
    rw [iterate_turn] at hp
    exact (turns_close_iff h x _).1 hp

/-- [proved-standard; formal-checked] The half-turn has order two. -/
theorem orderOf_neg_one_units : orderOf (-1 : ℤˣ) = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- [proved-derived; formal-checked] **Under the half-turn every state has period two.** -/
theorem half_turn_period (x : ℤˣ) :
    Function.minimalPeriod (fun y => (-1 : ℤˣ) * y) x = 2 := by
  rw [period_of_turn, orderOf_neg_one_units]

/-- [proved-derived; formal-checked] The half-turn rests nowhere. -/
theorem half_turn_no_rest (x : ℤˣ) : (-1 : ℤˣ) * x ≠ x := no_rest (by decide) x

/-- [proved-standard; formal-checked] The flip of two digits rests nowhere: the map of the diagonal
argument. -/
theorem flip_no_rest (b : Bool) : (!b) ≠ b := Bool.not_ne_self b

/-- [proved-derived; formal-checked] **The flip of two digits has period two.** -/
theorem flip_period (b : Bool) : Function.minimalPeriod (fun c : Bool => !c) b = 2 := by
  have hp : Function.IsPeriodicPt (fun c : Bool => !c) 2 b := by
    show (fun c : Bool => !c)^[2] b = b
    simp
  rcases (Nat.dvd_prime Nat.prime_two).1 hp.minimalPeriod_dvd with h | h
  · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h) (flip_no_rest b)
  · exact h

end Period

/-! ## 3. The cover of a frustrated ring -/

/-- [proved-derived; formal-checked] **An odd ring of sign-reversing contacts, unwrapped `m` times,
has a key when `m` is even and at no odd `m`.** -/
theorem cover_of_odd_ring_has_key_iff {n : ℕ} (hn : Odd n) (m : ℕ) [NeZero (m * n)] :
    (∃ x : Fin (m * n) → ℤˣ,
        ∀ e, Holds (ringContacts (m * n)) (fun _ => (-1 : ℤˣ)) x e) ↔ Even m := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra hm
    have hodd : Odd (m * n) := (Nat.not_even_iff_odd.mp hm).mul hn
    obtain ⟨e, he⟩ := odd_ring_breaks (m * n) hodd x
    exact he (hx e)
  · intro hm
    exact even_ring_has_key (m * n) (hm.mul_right n)

end Holonics.Landmarks.GrainPeriod
