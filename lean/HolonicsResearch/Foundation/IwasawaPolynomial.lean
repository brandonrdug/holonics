import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Refs #62. Existing finite-level Iwasawa polynomials and substitution laws,
moved unchanged to a narrow owner. Quotient, Selmer and growth laws stay in IwasawaTower. -/
noncomputable section
namespace Holonics.Foundation.IwasawaTower
variable (p : ℕ) [Fact p.Prime]

/-- [definition] `ω_n = (1 + T)^{p^n} − 1` as a **polynomial**, so that its distinguished shape and
the rank of its quotient are theorems rather than descriptions.

Retired Rust counterpart: `iwasawa_tower.rs::{omega, check_distinguished,
omega_divides_omega_succ}` ([history](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/iwasawa_tower.rs)). -/
def omegaPoly (n : ℕ) : Polynomial ℤ_[p] := (Polynomial.X + 1) ^ (p ^ n) - 1

variable {p}

/-- [definition] The group ring `ℤ_p[Γ/Γ_n] = ℤ_p[ℤ/p^n]` in its polynomial presentation
`ℤ_p[γ]/(γ^{p^n} − 1)`. -/
def groupRingPoly (p : ℕ) [Fact p.Prime] (n : ℕ) : Polynomial ℤ_[p] :=
  Polynomial.X ^ (p ^ n) - 1

/-- [proved-derived; formal-checked] The substitution `γ = 1 + T` carries `γ^{p^n} − 1` to `ω_n`,
as polynomials. -/
theorem omegaPoly_eq_groupRingPoly_comp (p : ℕ) [Fact p.Prime] (n : ℕ) :
    omegaPoly p n = (groupRingPoly p n).comp (Polynomial.X + 1) := by
  simp [omegaPoly, groupRingPoly]

/-- [proved-derived; formal-checked] And `T = γ − 1` carries it back. -/
theorem groupRingPoly_eq_omegaPoly_comp (p : ℕ) [Fact p.Prime] (n : ℕ) :
    groupRingPoly p n = (omegaPoly p n).comp (Polynomial.X - 1) := by
  simp [omegaPoly, groupRingPoly, sub_add_cancel]

end Holonics.Foundation.IwasawaTower
