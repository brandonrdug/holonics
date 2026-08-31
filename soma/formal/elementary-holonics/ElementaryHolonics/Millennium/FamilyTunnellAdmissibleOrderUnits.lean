import ElementaryHolonics.Millennium.FamilyTunnellAdmissibleOrder

/-!
# Exact unit population of the constructed Tunnell order

The admissible quaternion order is already a concrete subring.  This file
classifies its actual unit group rather than borrowing the cardinality of a
ternary automorphism group.  Its units are exactly `±1, ±i`; the resulting
population has four addressed occurrences.  No claim about the right order of
the second ideal class is made here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellAdmissibleOrderUnits

open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellAdmissibleOrder

def hamiltonI : HamiltonInt := ⟨0, 1, 0, 0⟩

theorem hamiltonI_mem : hamiltonI ∈ tunnellAdmissibleOrder := by
  simp [hamiltonI, tunnellAdmissibleOrder, InTunnellOrder]

theorem neg_hamiltonI_mem : -hamiltonI ∈ tunnellAdmissibleOrder := by
  simp [hamiltonI, tunnellAdmissibleOrder, InTunnellOrder]

/-- The actual `i`-unit inside the constructed admissible order. -/
def admissibleI : Units tunnellAdmissibleOrder where
  val := ⟨hamiltonI, hamiltonI_mem⟩
  inv := ⟨-hamiltonI, neg_hamiltonI_mem⟩
  val_inv := by
    apply Subtype.ext
    apply Quaternion.ext <;> norm_num [hamiltonI]
  inv_val := by
    apply Subtype.ext
    apply Quaternion.ext <;> norm_num [hamiltonI]

/-- A norm-one occurrence of the admissible order has exactly one of the four
allowed signed axial coordinate forms. -/
theorem normSq_one_mem_admissibleOrder_iff (q : HamiltonInt) :
    Quaternion.normSq q = 1 ∧ q ∈ tunnellAdmissibleOrder ↔
      q = 1 ∨ q = -1 ∨ q = hamiltonI ∨ q = -hamiltonI := by
  constructor
  · rintro ⟨hnorm, hmem⟩
    rcases q with ⟨a, b, c, d⟩
    rw [Quaternion.normSq_def'] at hnorm
    change (2 : ℤ) ∣ d ∧ (4 : ℤ) ∣ c - d at hmem
    have ha0 : -1 ≤ a := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have ha1 : a ≤ 1 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb0 : -1 ≤ b := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb1 : b ≤ 1 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc0 : -1 ≤ c := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc1 : c ≤ 1 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd0 : -1 ≤ d := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd1 : d ≤ 1 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    rcases hmem.1 with ⟨kd, hkd⟩
    rcases hmem.2 with ⟨kc, hkc⟩
    have hkd0 : kd = 0 := by omega
    have hd : d = 0 := by omega
    have hkc0 : kc = 0 := by omega
    have hc : c = 0 := by omega
    subst kd
    subst kc
    subst d
    subst c
    have ha : a = -1 ∨ a = 0 ∨ a = 1 := by omega
    have hb : b = -1 ∨ b = 0 ∨ b = 1 := by omega
    rcases ha with ha | ha | ha <;>
      rcases hb with hb | hb | hb <;>
      subst a <;> subst b <;> norm_num at hnorm
    all_goals simp [hamiltonI]
    case mp.inl.inr.inl =>
      exact Or.inr (Or.inl (by apply Quaternion.ext <;> norm_num))
    case mp.inr.inl.inl =>
      exact Or.inr (Or.inr (Or.inr
        (by apply Quaternion.ext <;> norm_num [hamiltonI])))
    case mp.inr.inr.inr.inl =>
      exact Or.inl (by apply Quaternion.ext <;> norm_num)
  · rintro (rfl | rfl | rfl | rfl) <;>
      constructor <;>
      simp [hamiltonI, tunnellAdmissibleOrder, InTunnellOrder,
        Quaternion.normSq_def']

theorem admissibleUnit_normSq (u : Units tunnellAdmissibleOrder) :
    Quaternion.normSq (u.1.1 : HamiltonInt) = 1 := by
  have hmul : (u.1.1 : HamiltonInt) * ((u⁻¹).1.1 : HamiltonInt) = 1 := by
    exact congrArg Subtype.val u.val_inv
  have hnorm := congrArg Quaternion.normSq hmul
  rw [map_mul, map_one] at hnorm
  have hleft : 0 ≤ Quaternion.normSq (u.1.1 : HamiltonInt) := by
    simp
  have hright : 0 ≤ Quaternion.normSq ((u⁻¹).1.1 : HamiltonInt) := by
    simp
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hnorm with
    ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · omega

/-- The four addressed units of the actual admissible order. -/
def admissibleUnit : Fin 4 → Units tunnellAdmissibleOrder :=
  ![1, -1, admissibleI, -admissibleI]

def admissibleUnitSignature (i : Fin 4) : ℤ × ℤ :=
  (((admissibleUnit i).1.1 : HamiltonInt).re,
    ((admissibleUnit i).1.1 : HamiltonInt).imI)

private theorem admissibleUnitSignature_injective :
    Function.Injective admissibleUnitSignature := by
  decide

theorem admissibleUnit_injective : Function.Injective admissibleUnit := by
  intro i j h
  apply admissibleUnitSignature_injective
  exact congrArg
    (fun u : Units tunnellAdmissibleOrder => ((u.1.1 : HamiltonInt).re,
      (u.1.1 : HamiltonInt).imI)) h

theorem admissibleUnit_surjective : Function.Surjective admissibleUnit := by
  intro u
  have hclass := (normSq_one_mem_admissibleOrder_iff (u.1.1 : HamiltonInt)).mp
    ⟨admissibleUnit_normSq u, u.1.2⟩
  rcases hclass with h | h | h | h
  · refine ⟨0, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [admissibleUnit] using h.symm
  · refine ⟨1, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [admissibleUnit] using h.symm
  · refine ⟨2, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [admissibleUnit, admissibleI] using h.symm
  · refine ⟨3, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [admissibleUnit, admissibleI] using h.symm

def admissibleUnitEquiv : Fin 4 ≃ Units tunnellAdmissibleOrder :=
  Equiv.ofBijective admissibleUnit
    ⟨admissibleUnit_injective, admissibleUnit_surjective⟩

noncomputable instance : Fintype (Units tunnellAdmissibleOrder) :=
  Fintype.ofEquiv (Fin 4) admissibleUnitEquiv

theorem admissibleOrder_unit_card :
    Fintype.card (Units tunnellAdmissibleOrder) = 4 := by
  rw [← Fintype.card_congr admissibleUnitEquiv]
  simp

#print axioms normSq_one_mem_admissibleOrder_iff
#print axioms admissibleUnit_normSq
#print axioms admissibleUnit_injective
#print axioms admissibleUnit_surjective
#print axioms admissibleOrder_unit_card

end Soma.Holonics.Millennium.FamilyTunnellAdmissibleOrderUnits
