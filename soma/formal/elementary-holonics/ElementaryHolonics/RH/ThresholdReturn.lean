import Mathlib
import ElementaryHolonics.RH.LinePreservation

/-!
# FT6: the threshold, and the return of the campaign

The campaign's exact form of the target is `RH ⟺ Λ_DN = 0` with `Λ_DN = sInf seamTimes` from the
actual kernel. Two standing theorems of the literature are not returned by this line and are
carried here as named ports, neither of which is the target nor implies it: de Bruijn's bound
(`½` is a seam time) and Rodgers–Tao's `0 ≤ Λ_DN`. Given both, `RH ⟺ Λ_DN = 0`. The **first exact
missing inequality** of the line is therefore `Λ_DN ≤ 0` itself, whose falsifier is the null
falsifier of the conjecture: a zero of `ξ` off the seam. Every theorem is discharged with no
`sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.ThresholdReturn

open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.LinePreservation

/-- [open; project-postulate] **de Bruijn's bound**: `½` is a seam time (every zero of `H_{1/2}`
lies on the seam). Not the target and not an implication to it. -/
structure DeBruijnBound : Prop where
  half_mem : (1 / 2 : ℝ) ∈ seamTimes

/-- [open; project-postulate] **Rodgers–Tao**: the threshold is nonnegative. Not the target and
not an implication to it. -/
structure RodgersTaoNonneg : Prop where
  nonneg : 0 ≤ Λ_DN

/-- **Given de Bruijn's bound, `RH ⟺ Λ_DN ≤ 0`.** -/
theorem riemannHypothesis_iff_Λ_DN_le_of (h : DeBruijnBound) : RiemannHypothesis ↔ Λ_DN ≤ 0 :=
  riemannHypothesis_iff_Λ_DN_le ⟨1 / 2, h.half_mem⟩

/-- **Given de Bruijn's bound, `Λ_DN ≤ ½`.** -/
theorem Λ_DN_le_half (h : DeBruijnBound) : Λ_DN ≤ 1 / 2 := by
  by_cases hbdd : BddBelow seamTimes
  · exact csInf_le hbdd h.half_mem
  · unfold Λ_DN
    rw [Real.sInf_of_not_bddBelow hbdd]
    norm_num

/-- **The target's exact form**: given de Bruijn's bound and Rodgers–Tao's nonnegativity,
`RH ⟺ Λ_DN = 0`. The first exact missing inequality of the line is `Λ_DN ≤ 0`, with the null
falsifier of the conjecture. -/
theorem riemannHypothesis_iff_Λ_DN_eq (h₁ : DeBruijnBound) (h₂ : RodgersTaoNonneg) :
    RiemannHypothesis ↔ Λ_DN = 0 := by
  rw [riemannHypothesis_iff_Λ_DN_le_of h₁]
  constructor
  · intro hle
    exact le_antisymm hle h₂.nonneg
  · intro heq
    rw [heq]

end Soma.Holonics.RH.ThresholdReturn
