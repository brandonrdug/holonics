import ElementaryHolonics.Millennium.FamilyTunnellQuaternionicBridge

/-!
# The admissible Hamilton order for the Tunnell Brandt action

For the congruent-number representation at the class `[-1]`, the quaternionic
source is the order `R = Z[i] + 4 O_B`, where `O_B` is the Hurwitz maximal
order.  In integral Hamilton coordinates this order has the exact chart

`R = {(a,b,c,d) : d is even and c-d is divisible by 4}`.

This file constructs that chart as an actual noncommutative subring.  In
particular, closure under quaternion multiplication is proved from the retained
congruence witnesses; it is not inferred from the name of the order.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellAdmissibleOrder

open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge

/-- The exact integral-coordinate predicate for `Z[i] + 4 O_B`. -/
def InTunnellOrder (q : HamiltonInt) : Prop :=
  (2 : ℤ) ∣ q.imK ∧ (4 : ℤ) ∣ q.imJ - q.imK

theorem inTunnellOrder_iff_coordinates (q : HamiltonInt) :
    InTunnellOrder q ↔
      ∃ r u : ℤ, q.imK = 2 * r ∧ q.imJ = 2 * r + 4 * u := by
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨u, hu⟩⟩
    refine ⟨r, u, hr, ?_⟩
    linarith
  · rintro ⟨r, u, hk, hj⟩
    constructor
    · exact ⟨r, hk⟩
    · refine ⟨u, ?_⟩
      linarith

private theorem inTunnellOrder_zero : InTunnellOrder (0 : HamiltonInt) := by
  simp [InTunnellOrder]

private theorem inTunnellOrder_one : InTunnellOrder (1 : HamiltonInt) := by
  simp [InTunnellOrder]

private theorem inTunnellOrder_add {q r : HamiltonInt}
    (hq : InTunnellOrder q) (hr : InTunnellOrder r) :
    InTunnellOrder (q + r) := by
  rcases hq with ⟨hqk, hqd⟩
  rcases hr with ⟨hrk, hrd⟩
  constructor
  · simpa using dvd_add hqk hrk
  · have h := dvd_add hqd hrd
    have e : (q + r).imJ - (q + r).imK = (q.imJ - q.imK) + (r.imJ - r.imK) := by
      change (q.imJ + r.imJ) - (q.imK + r.imK) = _
      ring
    rw [e]
    exact h

private theorem inTunnellOrder_neg {q : HamiltonInt}
    (hq : InTunnellOrder q) : InTunnellOrder (-q) := by
  rcases hq with ⟨hqk, hqd⟩
  constructor
  · simpa using dvd_neg.mpr hqk
  · have h := dvd_neg.mpr hqd
    have e : (-q).imJ - (-q).imK = -(q.imJ - q.imK) := by
      change -q.imJ - -q.imK = _
      ring
    rw [e]
    exact h

/-- Closure under Hamilton multiplication.  The witness calculation is the
order's local holonomy law: the two congruent transverse coordinates remain
congruent after the noncommuting product. -/
private theorem inTunnellOrder_mul {q r : HamiltonInt}
    (hq : InTunnellOrder q) (hr : InTunnellOrder r) :
    InTunnellOrder (q * r) := by
  rcases (inTunnellOrder_iff_coordinates q).mp hq with
    ⟨qb, qu, hqk, hqj⟩
  rcases (inTunnellOrder_iff_coordinates r).mp hr with
    ⟨rb, ru, hrk, hrj⟩
  constructor
  · refine ⟨q.re * rb + q.imI * (rb + 2 * ru) -
        (qb + 2 * qu) * r.imI + qb * r.re, ?_⟩
    rw [Quaternion.imK_mul, hqk, hqj, hrk, hrj]
    ring
  · refine ⟨q.re * ru - q.imI * rb - q.imI * ru +
        qu * r.re + (qb + qu) * r.imI, ?_⟩
    rw [Quaternion.imJ_mul, Quaternion.imK_mul, hqk, hqj, hrk, hrj]
    ring

/-- The admissible order as an actual subring of the integral Hamilton algebra. -/
def tunnellAdmissibleOrder : Subring HamiltonInt where
  carrier := {q | InTunnellOrder q}
  zero_mem' := inTunnellOrder_zero
  one_mem' := inTunnellOrder_one
  add_mem' := inTunnellOrder_add
  neg_mem' := inTunnellOrder_neg
  mul_mem' := inTunnellOrder_mul

theorem mem_tunnellAdmissibleOrder_iff (q : HamiltonInt) :
    q ∈ tunnellAdmissibleOrder ↔ InTunnellOrder q := Iff.rfl

/-- An explicit four-coordinate occurrence chart for the order. -/
def tunnellOrderOccurrence (a b r u : ℤ) : HamiltonInt :=
  ⟨a, b, 2 * r + 4 * u, 2 * r⟩

theorem tunnellOrderOccurrence_mem (a b r u : ℤ) :
    tunnellOrderOccurrence a b r u ∈ tunnellAdmissibleOrder := by
  rw [mem_tunnellAdmissibleOrder_iff, inTunnellOrder_iff_coordinates]
  exact ⟨r, u, rfl, rfl⟩

/-- Every order occurrence has a complete coordinate predecessor. -/
theorem exists_tunnellOrderOccurrence_eq (q : tunnellAdmissibleOrder) :
    ∃ a b r u : ℤ, tunnellOrderOccurrence a b r u = q.1 := by
  rcases (inTunnellOrder_iff_coordinates q.1).mp q.2 with
    ⟨r, u, hk, hj⟩
  refine ⟨q.1.re, q.1.imI, r, u, ?_⟩
  apply Quaternion.ext
  · rfl
  · rfl
  · exact hj.symm
  · exact hk.symm

/-- The coordinate chart is injective; the order has no hidden quotient at this
stage. -/
theorem tunnellOrderOccurrence_injective :
    Function.Injective fun q : ℤ × ℤ × ℤ × ℤ =>
      tunnellOrderOccurrence q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  rintro ⟨a, b, r, u⟩ ⟨a', b', r', u'⟩ h
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  simp [tunnellOrderOccurrence] at hre hi hj hk
  congr <;> omega

#print axioms inTunnellOrder_iff_coordinates
#print axioms inTunnellOrder_mul
#print axioms tunnellOrderOccurrence_mem
#print axioms exists_tunnellOrderOccurrence_eq
#print axioms tunnellOrderOccurrence_injective

end Soma.Holonics.Millennium.FamilyTunnellAdmissibleOrder
