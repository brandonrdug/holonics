import ElementaryHolonics.Millennium.FamilyTunnellBrandtPrimeResidual

/-!
# The Frobenius side as an exact cubic-residue population

The remaining odd-prime Brandt obstruction is expressed in the previous file
using the Frobenius trace of `E : y²=x³-x`.  Here that trace is opened back into
its finite receiver population.

The cubic has exactly the three zeroes `0,1,-1` at every odd prime.  Every other
quadratic-character reading is `+1` or `-1`.  Consequently the complete character
sum is

`p - 3 - 2 # {t | χ(t³-t)=-1}`.

This converts the primitive Tunnell census target into two oriented copies of a
concrete nonresidue population plus the exact `χ(-1)` boundary.  It is the finite
carrier on which the next source bijection must be constructed.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellCubicResidueCensus

open Finset
open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
open Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.GaussCoefficient

variable {p : ℕ} [Fact p.Prime]

def cubicSwingValue (t : ZMod p) : ZMod p := t ^ 3 - t

/-- The complete finite population of nonsquare, nonzero cubic swing values. -/
def cubicNonresiduePopulation : Finset (ZMod p) :=
  Finset.univ.filter fun t =>
    quadraticChar (ZMod p) (cubicSwingValue t) = -1

/-- The seam where the cubic receiver is zero. -/
def cubicZeroPopulation : Finset (ZMod p) :=
  Finset.univ.filter fun t => cubicSwingValue t = 0

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

/-- The cubic seam consists exactly of its three addressed linear factors. -/
theorem cubicZeroPopulation_eq_three :
    cubicZeroPopulation (p := p) = {0, 1, -1} := by
  ext t
  simp only [cubicZeroPopulation, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  have hfactor : cubicSwingValue t = t * (t - 1) * (t + 1) := by
    simp [cubicSwingValue]
    ring
  rw [hfactor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))
  · rintro (rfl | rfl | rfl) <;> ring

theorem cubicZeroPopulation_card (hp2 : p ≠ 2) :
    (cubicZeroPopulation (p := p)).card = 3 := by
  rw [cubicZeroPopulation_eq_three (p := p)]
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h0m : (0 : ZMod p) ≠ -1 :=
    Ne.symm (neg_ne_zero.mpr one_ne_zero)
  have h1m : (1 : ZMod p) ≠ -1 := by
    intro h
    apply two_ne_zero (p := p) hp2
    linear_combination h
  simp [h01, h0m, h1m]

private theorem cubicCharacter_pointwise_decomposition (t : ZMod p) :
    quadraticChar (ZMod p) (cubicSwingValue t) =
      1 - (if cubicSwingValue t = 0 then 1 else 0) -
        2 * (if quadraticChar (ZMod p) (cubicSwingValue t) = -1 then 1 else 0) := by
  by_cases hzero : cubicSwingValue t = 0
  · rw [hzero, (quadraticChar (ZMod p)).map_zero]
    norm_num
  · by_cases hneg : quadraticChar (ZMod p) (cubicSwingValue t) = -1
    · rw [if_neg hzero, if_pos hneg, hneg]
      ring
    · have hone : quadraticChar (ZMod p) (cubicSwingValue t) = 1 := by
        by_cases hsquare : IsSquare (cubicSwingValue t)
        · exact (quadraticChar_one_iff_isSquare hzero).mpr hsquare
        · exact False.elim (hneg
            (quadraticChar_neg_one_iff_not_isSquare.mpr hsquare))
      rw [if_neg hzero, if_neg hneg, hone]
      ring

/-- The exact character sum is the complete population, minus the three zero
seams, minus a second copy of every negative orientation. -/
theorem cubicCharacterSum_eq_nonresidue_card (hp2 : p ≠ 2) :
    (∑ t : ZMod p, quadraticChar (ZMod p) (cubicSwingValue t)) =
      (p : ℤ) - 3 - 2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) := by
  have hzeroSum :
      (∑ t : ZMod p, if cubicSwingValue t = 0 then (1 : ℤ) else 0) =
        ((cubicZeroPopulation (p := p)).card : ℤ) := by
    simpa [cubicZeroPopulation] using
      (Finset.sum_boole (R := ℤ) (fun t : ZMod p => cubicSwingValue t = 0)
        (Finset.univ : Finset (ZMod p)))
  have hnegativeSum :
      (∑ t : ZMod p,
        if quadraticChar (ZMod p) (cubicSwingValue t) = -1
          then (1 : ℤ) else 0) =
        ((cubicNonresiduePopulation (p := p)).card : ℤ) := by
    simpa [cubicNonresiduePopulation] using
      (Finset.sum_boole (R := ℤ)
        (fun t : ZMod p =>
          quadraticChar (ZMod p) (cubicSwingValue t) = -1)
        (Finset.univ : Finset (ZMod p)))
  calc
    (∑ t : ZMod p, quadraticChar (ZMod p) (cubicSwingValue t)) =
        ∑ t : ZMod p,
          (1 - (if cubicSwingValue t = 0 then 1 else 0) -
            2 * (if quadraticChar (ZMod p) (cubicSwingValue t) = -1
              then 1 else 0)) := by
                apply Finset.sum_congr rfl
                intro t ht
                exact cubicCharacter_pointwise_decomposition t
    _ = (p : ℤ) - ((cubicZeroPopulation (p := p)).card : ℤ) -
          2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hzeroSum, hnegativeSum]
      simp [Finset.card_univ, ZMod.card]
    _ = (p : ℤ) - 3 -
          2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) := by
      rw [cubicZeroPopulation_card (p := p) hp2]
      norm_num

/-- Frobenius trace as the returned difference between twice the nonresidue
population and the ambient prime aperture. -/
theorem traceOfFrobenius_eq_cubicNonresidue_card (hp2 : p ≠ 2) :
    traceOfFrobenius 1 p =
      2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) + 3 - (p : ℤ) := by
  rw [trace_eq_neg_charSum (p := p) hp2]
  change -(∑ t : ZMod p,
    quadraticChar (ZMod p) (cubicSwingValue t)) = _
  rw [cubicCharacterSum_eq_nonresidue_card (p := p) hp2]
  ring

/-- The primitive prime-square target is now a pure finite population identity. -/
theorem primitiveTraceDefect_eq_cubicPopulationDefect (hp2 : p ≠ 2) :
    primitiveTraceDefect (p := p) =
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) -
        (2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) +
          2 * (1 - quadraticChar (ZMod p) (-1))) := by
  unfold primitiveTraceDefect
  rw [traceOfFrobenius_eq_cubicNonresidue_card (p := p) hp2]
  ring

/-- Vanishing of the Brandt eigen-defect is equivalent to one explicit cardinal
identity between the integral prime-square carrier and the cubic nonresidue
carrier with its orientation boundary. -/
theorem brandtPrimeEigenDefect_eq_zero_iff_cubic_census (hp2 : p ≠ 2) :
    brandtPrimeEigenDefect (p := p) = 0 ↔
      ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
        2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) +
          2 * (1 - quadraticChar (ZMod p) (-1)) := by
  rw [brandtPrimeEigenDefect_eq_primitiveTraceDefect (p := p) hp2,
    primitiveTraceDefect_eq_cubicPopulationDefect (p := p) hp2]
  constructor <;> intro h <;> linarith

#print axioms cubicZeroPopulation_eq_three
#print axioms cubicZeroPopulation_card
#print axioms cubicCharacterSum_eq_nonresidue_card
#print axioms traceOfFrobenius_eq_cubicNonresidue_card
#print axioms primitiveTraceDefect_eq_cubicPopulationDefect
#print axioms brandtPrimeEigenDefect_eq_zero_iff_cubic_census

end Soma.Holonics.Millennium.FamilyTunnellCubicResidueCensus
