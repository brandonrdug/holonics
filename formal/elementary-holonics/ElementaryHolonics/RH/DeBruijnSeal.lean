import Mathlib
import ElementaryHolonics.RH.DeBruijnLimit
import ElementaryHolonics.RH.ThresholdReturn

/-!
# DB5 (i): the seal — the last port is discharged and `RH ⟺ Λ_DN = 0` with no port

`1/8 ∈ seamTimes` (DB4) and the up-set law give `½ ∈ seamTimes`, de Bruijn's bound as the
`ThresholdReturn` port stated it; with `0 ≤ Λ_DN` (RT6) the threshold lies in `[0, 1/8]` and the
target's exact form holds unconditionally.
-/

noncomputable section

namespace Soma.Holonics.RH.DeBruijnSeal

open Set
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.LinePreservation
open Soma.Holonics.RH.DescentZeros
open Soma.Holonics.RH.DeBruijnLimit
open Soma.Holonics.RH.ThresholdReturn

/-- `½` is a seam time, by the up-set law from `1/8`. -/
theorem half_mem_seamTimes : (1 / 2 : ℝ) ∈ seamTimes :=
  seamTimes_upset eighth_mem_seamTimes (by norm_num)

/-- **De Bruijn's port is discharged.** -/
theorem deBruijnBound : DeBruijnBound := ⟨half_mem_seamTimes⟩

theorem bddBelow_seamTimes : BddBelow seamTimes := ⟨0, fun τ hτ => seamTimes_subset_Ici hτ⟩

/-- **`Λ_DN ≤ 1/8`**, de Bruijn's bound in the tree's coordinate. -/
theorem Λ_DN_le_eighth : Λ_DN ≤ 1 / 8 := csInf_le bddBelow_seamTimes eighth_mem_seamTimes

/-- **`Λ_DN ∈ [0, 1/8]`.** -/
theorem Λ_DN_mem_Icc_eighth : Λ_DN ∈ Icc (0 : ℝ) (1 / 8) := ⟨Λ_DN_nonneg, Λ_DN_le_eighth⟩

/-- **The target's exact form, with no port: `RH ⟺ Λ_DN = 0`.** -/
theorem riemannHypothesis_iff_Λ_DN_eq : RiemannHypothesis ↔ Λ_DN = 0 :=
  riemannHypothesis_iff_Λ_DN_eq_of_deBruijn deBruijnBound

/-- **`RH ⟺ Λ_DN ≤ 0`, with no port.** -/
theorem riemannHypothesis_iff_Λ_DN_le : RiemannHypothesis ↔ Λ_DN ≤ 0 :=
  riemannHypothesis_iff_Λ_DN_le_of deBruijnBound

/-- The seam times are exactly the closed ray `[Λ_DN, ∞)`. -/
theorem seamTimes_eq_Ici : seamTimes = Ici Λ_DN := by
  ext τ
  constructor
  · intro hτ
    exact csInf_le bddBelow_seamTimes hτ
  · intro hτ
    have hmem : Λ_DN ∈ seamTimes :=
      isClosed_seamTimes.csInf_mem ⟨_, eighth_mem_seamTimes⟩ bddBelow_seamTimes
    exact seamTimes_upset hmem hτ

end Soma.Holonics.RH.DeBruijnSeal
