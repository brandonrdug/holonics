import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The twisted cycle: its eigenvectors, the contact every section breaks, and the Fejér identity

The record `research/records/2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md`
(§0 statement 7; atlas `key.twisted-cycle-square-root`) reads the extreme case of the connection
Cheeger bound on the `n`-cycle carrying a `ℤ_k` turn `c ≢ 0` on one contact. #410 owes its
eigenvectors, the contact every section breaks, and the Fejér identity. This file proves those laws
on the universal cover of the cycle, where a section of the twisted cycle is a function on `ℤ` that
returns multiplied by the holonomy after one lap.

[proved-standard; formal-checked] What is proved.

1. **The powers are the eigenvectors** (`power_twisted`, `power_eigen`): for `z ≠ 0`, `u(x) = z^x`
   returns multiplied by `w = z^n` after a lap, and the connection Laplacian
   `(Lu)(x) = 2u(x) − u(x + 1) − u(x − 1)` reads `Lu = (1 − z)(1 − z⁻¹) u`. With `z = ζ_N^a`,
   `N = nk`, `a ≡ −c (mod k)`, the lap returns the turn and `u_a` is a section of the twisted cycle.
2. **On the unit circle the eigenvalue is `|1 − z|²`** (`eigenvalue_of_unit`).
3. **Every section of a frustrated cycle breaks a contact** (`defects_sum`,
   `frustrated_section_breaks`, `const_section_breaks_iff`): the defects
   `σ(x + 1) − σ(x) − c(x)` of a section sum to `−Σ c` round the cycle, so when `Σ c ≠ 0` some
   contact breaks; the constant section breaks exactly the turned contacts, so one turned contact
   gives `h₁ = 1/n` of the contacts.
4. **The Fejér identity** (`fejer_identity`): `|1 − z^n|² = |1 − z|² |Σ_(j<n) z^j|²`.

Still owed (#410): that `|1 − ζ^c|²` is the least eigenvalue, the limit `n² λ₁ → (2πc/k)²`, and a
section's Rayleigh quotient `λ₁ |Σ_(j<n) ζ^(cj)|²/n`.

The computational object is the helical pair interaction: the turn is carried by one pair contact,
and a section is a reading of the strand that must slip at some contact. Of the winding guide's six
general objects this touches the cell holonomy (the lap's turn) and the helix (the cover); the pair,
faces and placement, the tube and the tower thread stay attached.

Consumers: the atlas row `key.twisted-cycle-square-root`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.TwistedCycle

open Finset

/-! ## 1. The powers are the eigenvectors of the twisted cycle -/

section Eigen

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] The connection Laplacian on the cover of the cycle,
`(Lu)(x) = 2u(x) − u(x + 1) − u(x − 1)`. -/
def laplacian (u : ℤ → 𝕜) (x : ℤ) : 𝕜 := 2 * u x - u (x + 1) - u (x - 1)

/-- [proved-standard; formal-checked] **A power returns multiplied by its lap:**
`z^(x + n) = z^n z^x`, so `u(x) = z^x` is a section of the cycle twisted by `w = z^n`. -/
theorem power_twisted (z : 𝕜) (hz : z ≠ 0) (n : ℕ) (x : ℤ) :
    z ^ (x + (n : ℤ)) = z ^ n * z ^ x := by
  rw [zpow_add₀ hz, zpow_natCast, mul_comm]

/-- [proved-standard; formal-checked] **The powers are eigenvectors:**
`L(z^x) = (1 − z)(1 − z⁻¹) z^x`. -/
theorem power_eigen (z : 𝕜) (hz : z ≠ 0) (x : ℤ) :
    laplacian (fun y : ℤ => z ^ y) x = (1 - z) * (1 - z⁻¹) * z ^ x := by
  simp only [laplacian]
  rw [zpow_add₀ hz, zpow_sub₀ hz, zpow_one]
  have h1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  linear_combination (-(z ^ x)) * h1

end Eigen

/-- [proved-standard; formal-checked] **On the unit circle the eigenvalue is `|1 − z|²`.** -/
theorem eigenvalue_of_unit {z : ℂ} (hz : ‖z‖ = 1) :
    (1 - z) * (1 - z⁻¹) = ((‖1 - z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj hz, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub, map_one]

/-! ## 2. Every section of a frustrated cycle breaks a contact -/

section Sections

variable {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]

/-- [definition] The defect of a section `σ` on the contact `x → x + 1` carrying the turn `c x`. -/
def defect (c σ : ZMod n → G) (x : ZMod n) : G := σ (x + 1) - σ x - c x

/-- [proved-standard; formal-checked] **The defects sum to the turn round the cycle:**
`Σ_x (σ(x + 1) − σ(x) − c(x)) = −Σ_x c(x)`. -/
theorem defects_sum (c σ : ZMod n → G) : ∑ x, defect c σ x = -∑ x, c x := by
  have h : ∑ x, σ (x + 1) = ∑ x, σ x :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) (fun x => σ (x + 1)) σ fun x => by simp
  simp only [defect, Finset.sum_sub_distrib]
  rw [h]
  abel

/-- [proved-standard; formal-checked] **Every section of a frustrated cycle breaks a contact:** if
the turns do not sum to zero round the cycle, no section closes every contact. -/
theorem frustrated_section_breaks (c σ : ZMod n → G) (hc : ∑ x, c x ≠ 0) :
    ∃ x, σ (x + 1) ≠ σ x + c x := by
  by_contra h
  push_neg at h
  apply hc
  have hd : ∀ x, defect c σ x = 0 := fun x => by
    simp only [defect, h x]
    abel
  have hs := defects_sum c σ
  simp only [hd, Finset.sum_const_zero] at hs
  exact neg_eq_zero.mp hs.symm

omit [NeZero n] in
/-- [proved-standard; formal-checked] **The constant section breaks exactly the turned contacts**,
so a cycle with one turned contact has a section breaking one contact of `n`. -/
theorem const_section_breaks_iff (c : ZMod n → G) (g : G) (x : ZMod n) :
    g ≠ g + c x ↔ c x ≠ 0 := by
  simp

end Sections

/-! ## 3. The Fejér identity -/

/-- [proved-standard; formal-checked] **The Fejér identity:**
`|1 − z^n|² = |1 − z|² |Σ_(j<n) z^j|²`. -/
theorem fejer_identity {𝕜 : Type*} [NormedDivisionRing 𝕜] (z : 𝕜) (n : ℕ) :
    ‖1 - z ^ n‖ ^ 2 = ‖1 - z‖ ^ 2 * ‖∑ j ∈ range n, z ^ j‖ ^ 2 := by
  rw [← mul_neg_geom_sum, norm_mul, mul_pow]

end Holonics.Geometry.TwistedCycle
