import Holonics.Mathematics.PolynomialReading
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Selected quadratic coefficient formulas for the Ratio object's exact root face

Generic contract for native selected-quadratic formulas, not a verification of Rust execution.
No scalar hierarchy: operands are ordinary rational coefficient pairs, read by
the existing `Holonics.Mathematics.Sturm.evalReal` owner. The root equation is an
explicit operand. Positivity and nonsquareness enter only the laws requiring them.

[agent-inferred] Keep the selected root and its source/decoder outside the pair:
the native `join` checks a common radicand before these formulas are consumed.
A zero coefficient is rational and requires no selected root. Width guards are
resource refusals, not mathematical hypotheses making division valid.
-/

noncomputable section

namespace Holonics.Objects.Ratio.SelectedQuadratic

open Holonics.Mathematics.Sturm

abbrev evaluate (s : ℝ) (x : ℚ × ℚ) : ℝ := evalReal s [x.1, x.2]

def add (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 + y.1, x.2 + y.2)
def multiply (D : ℚ) (x y : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 * y.1 + x.2 * y.2 * D, x.1 * y.2 + x.2 * y.1)
def conjugate (x : ℚ × ℚ) : ℚ × ℚ := (x.1, -x.2)
def norm (D : ℚ) (x : ℚ × ℚ) : ℚ := x.1 ^ 2 - x.2 ^ 2 * D
def inverse (D : ℚ) (x : ℚ × ℚ) : ℚ × ℚ :=
  (x.1 / norm D x, -x.2 / norm D x)
def Nonsquare (D : ℚ) : Prop := ∀ r : ℚ, r ^ 2 ≠ D

theorem evaluate_formula (s : ℝ) (u v : ℚ) :
    evaluate s (u, v) = (u : ℝ) + (v : ℝ) * s := by
  simp [evaluate, evalReal, mul_comm]

theorem evaluate_rational (s : ℝ) (u : ℚ) : evaluate s (u, 0) = u := by
  simp [evaluate_formula]

theorem evaluate_add (s : ℝ) (x y : ℚ × ℚ) :
    evaluate s (add x y) = evaluate s x + evaluate s y := by
  rcases x with ⟨u, v⟩; rcases y with ⟨a, b⟩
  simp only [add, evaluate_formula, Rat.cast_add]
  ring

theorem evaluate_multiply {D : ℚ} {s : ℝ} (hs : s ^ 2 = (D : ℝ))
    (x y : ℚ × ℚ) :
    evaluate s (multiply D x y) = evaluate s x * evaluate s y := by
  rcases x with ⟨u, v⟩; rcases y with ⟨a, b⟩
  simp only [multiply, evaluate_formula, Rat.cast_add, Rat.cast_mul]
  calc
    _ = (u : ℝ) * a + ((u : ℝ) * b + (v : ℝ) * a) * s +
        (v : ℝ) * b * s ^ 2 := by rw [hs]; ring
    _ = _ := by ring

theorem evaluate_conjugate (s : ℝ) (x : ℚ × ℚ) :
    evaluate s (conjugate x) = evaluate (-s) x := by
  rcases x with ⟨u, v⟩
  simp only [conjugate, evaluate_formula, Rat.cast_neg]
  ring

theorem conjugate_twice (x : ℚ × ℚ) : conjugate (conjugate x) = x := by
  rcases x with ⟨u, v⟩
  simp [conjugate]

theorem multiply_conjugate (D : ℚ) (x : ℚ × ℚ) :
    multiply D x (conjugate x) = (norm D x, 0) := by
  rcases x with ⟨u, v⟩
  simp only [multiply, conjugate, norm]
  congr 1 <;> ring

theorem norm_evaluation {D : ℚ} {s : ℝ} (hs : s ^ 2 = (D : ℝ))
    (x : ℚ × ℚ) :
    evaluate s x * evaluate s (conjugate x) = (norm D x : ℝ) := by
  rw [← evaluate_multiply hs, multiply_conjugate, evaluate_rational]

theorem norm_conjugate (D : ℚ) (x : ℚ × ℚ) :
    norm D (conjugate x) = norm D x := by
  rcases x with ⟨u, v⟩
  simp [norm, conjugate]

theorem norm_multiply (D : ℚ) (x y : ℚ × ℚ) :
    norm D (multiply D x y) = norm D x * norm D y := by
  rcases x with ⟨u, v⟩; rcases y with ⟨a, b⟩
  simp only [norm, multiply]
  ring

theorem norm_nonzero {D : ℚ} (hD : Nonsquare D) {x : ℚ × ℚ}
    (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) : norm D x ≠ 0 := by
  rcases x with ⟨u, v⟩
  intro hn
  have he : u ^ 2 = v ^ 2 * D := sub_eq_zero.mp hn
  by_cases hv : v = 0
  · simp only [hv, zero_pow (by decide : 2 ≠ 0), zero_mul] at he
    have hu : u = 0 := (sq_eq_zero_iff).mp he
    rcases hx with hu' | hv'
    · exact hu' hu
    · exact hv' hv
  · apply hD (u / v)
    field_simp
    exact he

theorem inverse_coefficients {D : ℚ} (x : ℚ × ℚ) (hn : norm D x ≠ 0) :
    multiply D x (inverse D x) = (1, 0) := by
  rcases x with ⟨u, v⟩
  simp only [multiply, inverse]
  apply Prod.ext
  · dsimp
    field_simp
    simp only [norm] at *
    ring
  · dsimp
    field_simp
    ring

theorem evaluation_nonzero {D : ℚ} {s : ℝ} (hs : s ^ 2 = (D : ℝ))
    (x : ℚ × ℚ) (hn : norm D x ≠ 0) : evaluate s x ≠ 0 := by
  intro he
  have hz := norm_evaluation hs x
  rw [he, zero_mul] at hz
  exact hn (Rat.cast_injective (hz.symm.trans (Rat.cast_zero).symm))

theorem evaluate_inverse {D : ℚ} {s : ℝ} (hs : s ^ 2 = (D : ℝ))
    (x : ℚ × ℚ) (hn : norm D x ≠ 0) :
    evaluate s (inverse D x) = (evaluate s x)⁻¹ := by
  have hi : evaluate s x * evaluate s (inverse D x) = 1 := by
    rw [← evaluate_multiply hs, inverse_coefficients x hn, evaluate_rational]
    simp
  exact (mul_eq_one_iff_eq_inv₀ (evaluation_nonzero hs x hn)).mp (by
    simpa [mul_comm] using hi)

theorem no_rational_root_iff_nonsquare (D : ℚ) :
    (∀ r : ℚ, evalAt r [-D, 0, 1] ≠ 0) ↔ Nonsquare D := by
  simp only [evalAt, mul_zero, add_zero, mul_one, zero_add]
  constructor
  · intro h r he
    apply h r
    nlinarith [he]
  · intro h r he
    apply h r
    nlinarith [he]

/-! Every exported law is audited; no `sorry`, added axioms or `native_decide`. -/
#print axioms evaluate_formula
#print axioms evaluate_rational
#print axioms evaluate_add
#print axioms evaluate_multiply
#print axioms evaluate_conjugate
#print axioms conjugate_twice
#print axioms multiply_conjugate
#print axioms norm_evaluation
#print axioms norm_conjugate
#print axioms norm_multiply
#print axioms norm_nonzero
#print axioms inverse_coefficients
#print axioms evaluation_nonzero
#print axioms evaluate_inverse
#print axioms no_rational_root_iff_nonsquare
end Holonics.Objects.Ratio.SelectedQuadratic
