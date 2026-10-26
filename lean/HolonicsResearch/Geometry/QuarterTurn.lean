import Holonics.Geometry.AffineSwing
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The half-turn is the square of an oriented quarter-turn

The atlas row `swing.square-of-quarter-turn` reads the half-turn `S_a x = 2a − x`
(`Holonics.Geometry.AffineSwing.swing`) as the square of an oriented quarter-turn built from a
polarity and an exchange (Kauffman's iterants): `D = diag(−1, 1)`, `S = [[0, 1], [1, 0]]`, `J = DS`.
#410 owes `J² = −I`, `Q_a² = S_a` and `Q_a⁴ = id`; this file proves them over any commutative ring,
so on the rational two-coordinate carrier the row names.

[proved-derived; formal-checked] What is proved.

1. **Polarity and exchange are involutions that anticommute** (`polarity_mul_self`,
   `exchange_mul_self`, `exchange_mul_polarity`): `D² = S² = I` and `SD = −DS`.
2. **Their product is a quarter-turn** (`quarter_eq`, `quarter_mul_self`, `quarter_pow_four`):
   `J = [[0, −1], [1, 0]]`, `J² = −I`, `J⁴ = I`.
3. **The half-turn is the square of the quarter-turn** (`quarterTurn_quarterTurn`,
   `quarterTurn_four`, `quarterTurn_anchor`): `Q_a x = a + J(x − a)` fixes its anchor,
   `Q_a(Q_a x) = S_a x = 2a − x`, and four quarter-turns return every point.

Re-entry through `J` gives the complex phase chart `i = e^(iπ/2)` of the notation guide; it is not
a parametron's storage law.

The computational object is the helical pair interaction: the half-turn is the pair's reflection
`U` of the dihedral group `⟨S, U | U² = 1, USU = S⁻¹⟩`, and the quarter-turn is its oriented square
root. Of the winding guide's six general objects this touches faces and placement (the polarity
reading) and the helix (the turn); the pair, the cell holonomy, the tube and the tower thread stay
attached.

Consumers: the atlas row `swing.square-of-quarter-turn`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.QuarterTurn

open Matrix Holonics.Geometry.AffineSwing

variable {R : Type*} [CommRing R]

/-- [definition] The polarity `D = diag(−1, 1)`. -/
def polarity : Matrix (Fin 2) (Fin 2) R := !![-1, 0; 0, 1]

/-- [definition] The exchange `S = [[0, 1], [1, 0]]`. -/
def exchange : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- [definition] The quarter-turn `J = D S`. -/
def quarter : Matrix (Fin 2) (Fin 2) R := polarity * exchange

/-- [proved-standard; formal-checked] The polarity is an involution. -/
theorem polarity_mul_self : (polarity : Matrix (Fin 2) (Fin 2) R) * polarity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polarity, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- [proved-standard; formal-checked] The exchange is an involution. -/
theorem exchange_mul_self : (exchange : Matrix (Fin 2) (Fin 2) R) * exchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchange, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- [proved-standard; formal-checked] **The quarter-turn** `J = DS = [[0, −1], [1, 0]]`. -/
theorem quarter_eq : (quarter : Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarter, polarity, exchange, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **Polarity and exchange anticommute:** `SD = −DS`. -/
theorem exchange_mul_polarity :
    (exchange : Matrix (Fin 2) (Fin 2) R) * polarity = -quarter := by
  rw [quarter_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exchange, polarity, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **`J² = −I`.** -/
theorem quarter_mul_self : (quarter : Matrix (Fin 2) (Fin 2) R) * quarter = -1 := by
  rw [quarter_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- [proved-derived; formal-checked] **`J⁴ = I`.** -/
theorem quarter_pow_four : (quarter : Matrix (Fin 2) (Fin 2) R) ^ 4 = 1 := by
  have h4 : (quarter : Matrix (Fin 2) (Fin 2) R) ^ 4 = (quarter * quarter) * (quarter * quarter) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [h4, quarter_mul_self, neg_mul_neg, one_mul]

/-- [definition] The quarter-turn about the anchor `a`: `Q_a x = a + J(x − a)`. -/
def quarterTurn (a x : Fin 2 → R) : Fin 2 → R := a + quarter *ᵥ (x - a)

/-- [proved-derived; formal-checked] The quarter-turn fixes its anchor. -/
theorem quarterTurn_anchor (a : Fin 2 → R) : quarterTurn a a = a := by
  simp [quarterTurn]

/-- [proved-derived; formal-checked] **The half-turn is the square of the quarter-turn:**
`Q_a(Q_a x) = S_a x = 2a − x` (`Geometry/AffineSwing.swing`). -/
theorem quarterTurn_quarterTurn (a x : Fin 2 → R) :
    quarterTurn a (quarterTurn a x) = swing a x := by
  simp only [quarterTurn, swing, add_sub_cancel_left, Matrix.mulVec_mulVec, quarter_mul_self,
    Matrix.neg_mulVec, Matrix.one_mulVec]
  abel

/-- [proved-derived; formal-checked] **Four quarter-turns return every point:** `Q_a⁴ = id`. -/
theorem quarterTurn_four (a x : Fin 2 → R) :
    quarterTurn a (quarterTurn a (quarterTurn a (quarterTurn a x))) = x := by
  rw [quarterTurn_quarterTurn, quarterTurn_quarterTurn]
  exact theSwingIsAnInvolution a x

end Holonics.Geometry.QuarterTurn
