import Mathlib
import ElementaryHolonics.RH.LinePreservation
import ElementaryHolonics.RH.DescentZeros

/-!
# FT6 and RT6: the threshold, and the return of the campaign

The campaign's exact form of the target is `RH ⟺ Λ_DN = 0` with `Λ_DN = sInf seamTimes` from the
actual kernel. One standing theorem of the literature is not returned by this line and is
carried here as a named port, which is neither the target nor implies it: de Bruijn's bound
(`½` is a seam time). Rodgers–Tao's `0 ≤ Λ_DN` was a second port until the descent-route
campaign RT0–RT6 returned it as `DescentZeros.Λ_DN_nonneg`; it is now a theorem. Given de
Bruijn's bound alone, `RH ⟺ Λ_DN = 0`. The **first exact missing inequality** of the line is
therefore `Λ_DN ≤ 0` itself, whose falsifier is the null falsifier of the conjecture: a zero of
`ξ` off the seam. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.ThresholdReturn

open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.LinePreservation
open Soma.Holonics.RH.DescentZeros

/-- [open; project-postulate] **de Bruijn's bound**: `½` is a seam time (every zero of `H_{1/2}`
lies on the seam). Not the target and not an implication to it. -/
structure DeBruijnBound : Prop where
  half_mem : (1 / 2 : ℝ) ∈ seamTimes

/-- [proved-derived; formal-checked] **Rodgers–Tao**: the threshold is nonnegative. Formerly a
port; returned by the descent route (`DescentZeros.Λ_DN_nonneg`) and kept as a structure only so
that the earlier two-port statements still elaborate. -/
structure RodgersTaoNonneg : Prop where
  nonneg : 0 ≤ Λ_DN

/-- **The Rodgers–Tao port is discharged.** -/
theorem rodgersTaoNonneg : RodgersTaoNonneg := ⟨Λ_DN_nonneg⟩

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

/-- **The target's exact form with the single port**: given de Bruijn's bound,
`RH ⟺ Λ_DN = 0`. The nonnegativity `0 ≤ Λ_DN` is the descent route's theorem. -/
theorem riemannHypothesis_iff_Λ_DN_eq_of_deBruijn (h₁ : DeBruijnBound) :
    RiemannHypothesis ↔ Λ_DN = 0 :=
  riemannHypothesis_iff_Λ_DN_eq h₁ rodgersTaoNonneg

/-- **`Λ_DN ∈ [0, ½]` given de Bruijn's bound.** -/
theorem Λ_DN_mem_Icc (h : DeBruijnBound) : Λ_DN ∈ Set.Icc (0 : ℝ) (1 / 2) :=
  ⟨Λ_DN_nonneg, Λ_DN_le_half h⟩

end Soma.Holonics.RH.ThresholdReturn
