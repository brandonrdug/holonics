import ElementaryHolonics.Millennium.FamilyWaldspurgerGate

/-!
# FamilyThetaWaldspurgerBridge: the Poisson theta meets the ternary coefficient

`FamilyWaldspurgerGate` fixes the canonical signed ternary census and isolates the
remaining Waldspurger--Tunnell scalar defect.  This file makes one further exact
contact which was previously present only in prose:

* the full `2x² + y² + 8z² = p` population is the thin ternary theta coefficient;
* its even-`z` slice is the thick coefficient after the substitution `z = 2w`;
* the signed census is exactly `2 · thick - thin`;
* consequently, vanishing of the existing defect is equivalent to one displayed
  identity between the actual Poisson-transported family theta integral and the
  square of that finite ternary coefficient.

The last identity is the remaining analytic/arithmetic port.  It is characterized,
not proved, here; no Waldspurger theorem and no BSD conclusion are asserted.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge

open Complex MeasureTheory Set
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.FamilyThetaFE
open Soma.Holonics.Millennium.FamilyCentralRatio
open Soma.Holonics.Millennium.FamilyWaldspurgerGate
open Soma.Holonics.Millennium.LatticeCount

/-! ## 1. The two finite coefficient populations -/

/-- The complete thin ternary population on the proved-tight box. -/
def canonicalThinPopulation (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  SolFr p (Nat.sqrt p)

/-- The even-third-coordinate slice.  Under `z = 2w`, its form is
`2x² + y² + 32w²`; hence this is the thick coefficient inside the thin population. -/
def canonicalEvenSlicePopulation (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (canonicalThinPopulation p).filter fun t => t.2.2 % 2 = 0

/-- The complete thick ternary population on the same proved-sufficient box. -/
def canonicalThickPopulation (p : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((boxZ (Nat.sqrt p)) ×ˢ (boxZ (Nat.sqrt p)) ×ˢ (boxZ (Nat.sqrt p))).filter
    fun t => 2 * t.1 ^ 2 + t.2.1 ^ 2 + 32 * t.2.2 ^ 2 = (p : ℤ)

/-- The full (thin) ternary theta coefficient. -/
def thinThetaCoefficient (p : ℕ) : ℤ :=
  ((canonicalThinPopulation p).card : ℤ)

/-- The thick ternary theta coefficient. -/
def thickThetaCoefficient (p : ℕ) : ℤ :=
  ((canonicalThickPopulation p).card : ℤ)

/-- The oriented Tunnell coefficient `2 · thick - thin`. -/
def tunnellThetaCoefficient (p : ℕ) : ℤ :=
  2 * thickThetaCoefficient p - thinThetaCoefficient p

/-- Membership in the even slice records the complete tight-box incidence, the
thin ternary equation, and the parity condition—nothing is hidden in the name. -/
theorem mem_canonicalEvenSlicePopulation_iff (p : ℕ) (t : ℤ × ℤ × ℤ) :
    t ∈ canonicalEvenSlicePopulation p ↔
      ((t.1 ∈ boxZ (Nat.sqrt p) ∧ t.2.1 ∈ boxZ (Nat.sqrt p) ∧
          t.2.2 ∈ boxZ (Nat.sqrt p)) ∧
        2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ)) ∧
      t.2.2 % 2 = 0 := by
  simp [canonicalEvenSlicePopulation, canonicalThinPopulation, SolFr]

/-- Membership in the thick population is the corresponding tight-box incidence and
the `32z²` ternary equation. -/
theorem mem_canonicalThickPopulation_iff (p : ℕ) (t : ℤ × ℤ × ℤ) :
    t ∈ canonicalThickPopulation p ↔
      (t.1 ∈ boxZ (Nat.sqrt p) ∧ t.2.1 ∈ boxZ (Nat.sqrt p) ∧
        t.2.2 ∈ boxZ (Nat.sqrt p)) ∧
      2 * t.1 ^ 2 + t.2.1 ^ 2 + 32 * t.2.2 ^ 2 = (p : ℤ) := by
  simp [canonicalThickPopulation]

/-- On the even slice, division of the third coordinate exposes the thick form
without changing the represented modulus. -/
theorem evenSlice_exposes_thick_form {p : ℕ} {t : ℤ × ℤ × ℤ}
    (ht : t ∈ canonicalEvenSlicePopulation p) :
    2 * t.1 ^ 2 + t.2.1 ^ 2 + 32 * (t.2.2 / 2) ^ 2 = (p : ℤ) := by
  rw [mem_canonicalEvenSlicePopulation_iff] at ht
  have hz : t.2.2 = 2 * (t.2.2 / 2) := by omega
  rw [hz] at ht
  nlinarith

private def doubleThird (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1, t.2.1, 2 * t.2.2)

private def halveThird (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1, t.2.1, t.2.2 / 2)

/-- Doubling the third coordinate is an addressed bijection from the actual thick
population to the even slice of the thin population. -/
theorem canonicalThickPopulation_card_eq_evenSlicePopulation_card (p : ℕ) :
    (canonicalThickPopulation p).card = (canonicalEvenSlicePopulation p).card := by
  classical
  refine Finset.card_nbij' doubleThird halveThird ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ canonicalThickPopulation p at ht
    change doubleThird (x, y, z) ∈ canonicalEvenSlicePopulation p
    rw [mem_canonicalThickPopulation_iff] at ht
    rw [mem_canonicalEvenSlicePopulation_iff]
    simp only [doubleThird]
    have hthin : 2 * x ^ 2 + y ^ 2 + 8 * (2 * z) ^ 2 = (p : ℤ) := by
      nlinarith [ht.2]
    obtain ⟨hx, hy, hz⟩ := theSolutionsAreTightlyBounded hthin
    refine ⟨⟨⟨?_, ?_, ?_⟩, hthin⟩, by omega⟩
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hx
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hy
    · rw [theReducibleBoxIsTheInterval, Finset.mem_Icc, ← abs_le]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hz
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ canonicalEvenSlicePopulation p at ht
    change halveThird (x, y, z) ∈ canonicalThickPopulation p
    rw [mem_canonicalEvenSlicePopulation_iff] at ht
    rw [mem_canonicalThickPopulation_iff]
    simp only [halveThird]
    have hzmod : z % 2 = 0 := ht.2
    have hz : z = 2 * (z / 2) := by omega
    have hthick : 2 * x ^ 2 + y ^ 2 + 32 * (z / 2) ^ 2 = (p : ℤ) := by
      have hthin := ht.1.2
      rw [hz] at hthin
      nlinarith [hthin]
    refine ⟨⟨ht.1.1.1, ht.1.1.2.1, ?_⟩, hthick⟩
    change z / 2 ∈ boxZ (Nat.sqrt p)
    have hzbox : z ∈ boxZ (Nat.sqrt p) := by simpa using ht.1.1.2.2
    rw [theReducibleBoxIsTheInterval, Finset.mem_Icc] at hzbox ⊢
    omega
  · rintro ⟨x, y, z⟩ ht
    simp [doubleThird, halveThird]
  · rintro ⟨x, y, z⟩ ht
    change (x, y, z) ∈ canonicalEvenSlicePopulation p at ht
    rw [mem_canonicalEvenSlicePopulation_iff] at ht
    simp only [doubleThird, halveThird, Prod.mk.injEq, true_and]
    have hzmod : z % 2 = 0 := ht.2
    omega

/-! ## 2. The signed census is the coefficient difference -/

private theorem sign_of_third_coordinate (z : ℤ) :
    (-1 : ℤ) ^ z.natAbs = if z % 2 = 0 then 1 else -1 := by
  by_cases hz : z % 2 = 0
  · rw [if_pos hz]
    exact (Int.even_iff.mpr hz).natAbs.neg_one_pow
  · rw [if_neg hz]
    have hodd : Odd z := Int.odd_iff.mpr (by omega)
    exact hodd.natAbs.neg_one_pow

private theorem signedParitySum_eq_twice_even_card_sub_card
    {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℤ) :
    (∑ a ∈ s, (-1 : ℤ) ^ (z a).natAbs) =
      2 * (((s.filter fun a => z a % 2 = 0).card : ℕ) : ℤ) - (s.card : ℤ) := by
  let P : α → Prop := fun a => z a % 2 = 0
  let f : α → ℤ := fun a => (-1 : ℤ) ^ (z a).natAbs
  have heven :
      (∑ a ∈ s.filter P, f a) = (((s.filter P).card : ℕ) : ℤ) := by
    calc
      (∑ a ∈ s.filter P, f a) = ∑ _a ∈ s.filter P, (1 : ℤ) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        simp only [Finset.mem_filter] at ha
        exact (sign_of_third_coordinate (z a)).trans (if_pos ha.2)
      _ = (((s.filter P).card : ℕ) : ℤ) := by simp
  have hodd :
      (∑ a ∈ s.filter (fun a => ¬P a), f a) =
        -(((s.filter (fun a => ¬P a)).card : ℕ) : ℤ) := by
    calc
      (∑ a ∈ s.filter (fun a => ¬P a), f a) =
          ∑ _a ∈ s.filter (fun a => ¬P a), (-1 : ℤ) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        simp only [Finset.mem_filter] at ha
        exact (sign_of_third_coordinate (z a)).trans (if_neg ha.2)
      _ = -(((s.filter (fun a => ¬P a)).card : ℕ) : ℤ) := by simp
  have hcard :
      (((s.filter P).card : ℕ) : ℤ) +
          (((s.filter (fun a => ¬P a)).card : ℕ) : ℤ) = (s.card : ℤ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) P
  calc
    (∑ a ∈ s, (-1 : ℤ) ^ (z a).natAbs) = ∑ a ∈ s, f a := rfl
    _ = (∑ a ∈ s.filter P, f a) +
        ∑ a ∈ s.filter (fun a => ¬P a), f a :=
      (Finset.sum_filter_add_sum_filter_not s P f).symm
    _ = (((s.filter P).card : ℕ) : ℤ) -
        (((s.filter (fun a => ¬P a)).card : ℕ) : ℤ) := by rw [heven, hodd]; ring
    _ = 2 * (((s.filter fun a => z a % 2 = 0).card : ℕ) : ℤ) - (s.card : ℤ) := by
      change (((s.filter P).card : ℕ) : ℤ) -
          (((s.filter (fun a => ¬P a)).card : ℕ) : ℤ) =
        2 * (((s.filter P).card : ℕ) : ℤ) - (s.card : ℤ)
      omega

/-- **THE SIGNED CENSUS IS THE TUNNELL THETA COEFFICIENT.**
This is the exact finite-population identity `Σ(-1)^z = 2A_p - B_p`. -/
theorem canonicalSignedTernaryCount_eq_tunnellThetaCoefficient (p : ℕ) :
    canonicalSignedTernaryCount p = tunnellThetaCoefficient p := by
  have hsum := signedParitySum_eq_twice_even_card_sub_card
    (SolFr p (Nat.sqrt p)) (fun t : ℤ × ℤ × ℤ => t.2.2)
  have hcard := canonicalThickPopulation_card_eq_evenSlicePopulation_card p
  unfold canonicalSignedTernaryCount tunnellThetaCoefficient thickThetaCoefficient
    thinThetaCoefficient
  rw [hcard]
  simpa [canonicalThinPopulation, canonicalEvenSlicePopulation] using hsum

/-- The orbit-normalized branch count is the coefficient difference divided by four. -/
theorem canonicalBranchCount_eq_tunnellThetaCoefficient_div_four (p : ℕ) :
    canonicalBranchCount p = tunnellThetaCoefficient p / 4 := by
  unfold canonicalBranchCount
  rw [canonicalSignedTernaryCount_eq_tunnellThetaCoefficient]

/-! ## 3. The exact analytic/arithmetic contact -/

/-- **THE POISSON THETA / TERNARY COEFFICIENT GATE.**
On `p ≡ 3 (mod 8)`, vanishing of the already-isolated Waldspurger--Tunnell defect is
equivalent to one equality.  The left side is the integral of the actual family theta
whose inversion law was constructed by the Poisson/Gauss transport; the right side is
the square of the exact finite coefficient `2A_p-B_p`, orbit-normalized by four.

The theorem exposes the missing equality and does not prove either side equal. -/
theorem waldspurgerTunnellDefect_eq_zero_iff_theta_coefficient_identity
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    waldspurgerTunnellDefect p = 0 ↔
      (2 : ℂ) * ((∫ t in Ioi (0 : ℝ), thetaP p t : ℝ) : ℂ) =
        centralArchimedeanFactor p *
          (((((tunnellThetaCoefficient p / 4) ^ 2 : ℤ) : ℂ)) *
            ((BirchSwinnertonDyer.realPeriod p : ℝ) : ℂ)) := by
  rw [theCentralThetaIntegralIsTwiceTheExplicitLatticeSum hp8]
  rw [← canonicalBranchCount_eq_tunnellThetaCoefficient_div_four p]
  unfold waldspurgerTunnellDefect
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- The same contact without the quotient spelling: the canonical branch count is
already known to be integral and odd on this branch. -/
theorem waldspurgerTunnellDefect_eq_zero_iff_theta_branch_identity
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    waldspurgerTunnellDefect p = 0 ↔
      (2 : ℂ) * ((∫ t in Ioi (0 : ℝ), thetaP p t : ℝ) : ℂ) =
        centralArchimedeanFactor p *
          (((canonicalBranchCount p ^ 2 : ℤ) : ℂ) *
            ((BirchSwinnertonDyer.realPeriod p : ℝ) : ℂ)) := by
  rw [theCentralThetaIntegralIsTwiceTheExplicitLatticeSum hp8]
  unfold waldspurgerTunnellDefect
  push_cast
  constructor <;> intro h <;> linear_combination h

end Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
