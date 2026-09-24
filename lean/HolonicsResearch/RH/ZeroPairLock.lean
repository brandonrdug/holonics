import HolonicsResearch.RH.FosterTanks
import Holonics.Transport.HelicalPairInteraction

/-!
# The reflected zero pair is locked exactly on the seam

[interpretation] A point `ρ = σ + iγ` of the strip is read as the generator
`(advance, angular) = (σ, γ)` of the one-parameter subgroup `u ↦ e^{ρu}` of `ℂ^×`, a helix on
the cylinder chart. The functional equation reflects it to `1 − ρ̄`, with generator
`(1 − σ, γ)`: a helical pair with equal angular rates.

[proved-derived; formal-checked] This module returns the first derivation target of that
correspondence. On the isotropic unit face of `Transport/HelicalPairInteraction`, the power read
by advancing both objects together is the squared advance defect `(2σ − 1)²`. It vanishes, that
is the pair is locked, exactly when `σ = ½`; and for `γ ≠ 0` that is exactly when the
`RH/FosterTanks` inductance of `ρ′ = ρ − ½` is a positive real. The lock of the helical pair and
Foster losslessness of the tank are therefore the same locus.

[established-bounded; formal-checked] Scope: rational generators and the algebraic locus only.
Nothing here concerns where the zeros of any function lie, and no operator carrying the zeros
as material is supplied. No `axiom`, no `sorry`.
-/

open Matrix

namespace Holonics.RH.ZeroPairLock

open Holonics.Geometry.ScrewGeometry
open Holonics.Transport.HolonicInteraction
open Holonics.Transport.HelicalPairInteraction

/-- [definition] The cylinder generator of `ρ = σ + iγ`: advance `σ`, angular rate `γ`. -/
def zeroGenerator (σ γ : ℚ) : Vec := ![σ, γ, 0]

/-- [definition] The generator of the reflected point `1 − ρ̄`: advance `1 − σ`, the same
angular rate. -/
def reflectedGenerator (σ γ : ℚ) : Vec := ![1 - σ, γ, 0]

/-- [definition] The power read on the isotropic unit face when both objects advance together. -/
def reflectedPairPower (σ γ : ℚ) : ℚ :=
  quad (faceForm 1 (pairSlip (zeroGenerator σ γ) (reflectedGenerator σ γ)) 1) ![1, 1]

/-- [proved-derived; formal-checked] **The pair's power is the squared advance defect.** -/
theorem reflectedPairPower_eq (σ γ : ℚ) : reflectedPairPower σ γ = (2 * σ - 1) ^ 2 := by
  unfold reflectedPairPower
  rw [pair_face_power]
  simp [zeroGenerator, reflectedGenerator, dotProduct, Fin.sum_univ_succ]
  ring

/-- [proved-derived; formal-checked] **The reflected pair is locked exactly on the seam.** -/
theorem reflected_pair_locked_iff_on_seam (σ γ : ℚ) :
    reflectedPairPower σ γ = 0 ↔ σ = 1 / 2 := by
  rw [reflectedPairPower_eq]
  constructor
  · intro h
    have : 2 * σ - 1 = 0 := by
      rcases pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h with h0
      exact h0
    linarith
  · intro h
    rw [h]
    norm_num

/-- [proved-derived; formal-checked] **Lock of the pair is Foster losslessness of the tank.**
For a nonzero angular rate, the reflected pair is locked exactly when the inductance of the tank
of `ρ′ = (σ − ½) + iγ` is a positive real. -/
theorem locked_iff_foster_inductance_positive (σ γ : ℚ) (hγ : γ ≠ 0) :
    reflectedPairPower σ γ = 0 ↔
      ∃ L : ℝ, 0 < L ∧
        Holonics.RH.FosterTanks.inductance
          (((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I) = (L : ℂ) := by
  rw [reflected_pair_locked_iff_on_seam, Holonics.RH.FosterTanks.inductance_pos_real_iff]
  have hre : ((((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I)).re = ((σ - 1 / 2 : ℚ) : ℝ) := by
    simp
  have him : ((((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I)).im = ((γ : ℚ) : ℝ) := by
    simp
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hre, h]
      norm_num
    · intro hzero
      have : ((γ : ℚ) : ℝ) = 0 := by
        rw [← him, hzero]
        simp
      exact hγ (by exact_mod_cast this)
  · rintro ⟨h, -⟩
    rw [hre] at h
    have : (σ - 1 / 2 : ℚ) = 0 := by exact_mod_cast h
    linarith

end Holonics.RH.ZeroPairLock
