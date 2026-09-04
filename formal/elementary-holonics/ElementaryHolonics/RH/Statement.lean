import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The actual Riemann Hypothesis

Mathlib already defines the analytic Riemann zeta function and the standard
nontrivial-zero proposition.  This project aliases that proposition; it does
not replace it with a finite model.
-/

namespace Soma.Holonics.RH

/-- The standard Mathlib proposition, with trivial zeros and the pole excluded. -/
abbrev Statement : Prop := RiemannHypothesis

theorem statement_def :
    Statement ↔
      ∀ (s : ℂ)
        (_ : riemannZeta s = 0)
        (_ : ¬ ∃ n : ℕ, s = -2 * (n + 1))
        (_ : s ≠ 1),
        s.re = 1 / 2 :=
  Iff.rfl

end Soma.Holonics.RH

