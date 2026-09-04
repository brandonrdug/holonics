import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The exact lattice and twist arithmetic in the `(3,4,∞)` six-sphere construction

This file formalizes the finite algebraic entrance to the construction in
*A compact complex threefold fibred by tori over the projective line, and the six-sphere*.
It checks the integral monodromy matrices, their dual actions, the square-zero cusp
monodromy, the distinguished fixed lattice vectors, and the Seifert obstruction

```text
12ℓ₀ - 4ℓ₁ - 3ℓ₂.
```

Truth status: `[proved-derived]` for every theorem below, relative only to the displayed
integer matrices.  This is not a formalization of the period functions, toric or logarithmic
fillings, gluing, homology calculation, smooth recognition theorem, or integrable complex
structure on `S⁶`.  In particular, the arithmetic value `|p| = 1` is only the finite input to
the paper's fundamental-group calculation; it does not prove that calculation here.
-/

namespace Soma.Holonics.Geometry.SixSphereMonodromy

abbrev Lattice := Fin 4 → ℤ
abbrev LatticeEnd := Matrix (Fin 4) (Fin 4) ℤ

/-- The order-three monodromy on the rank-four lattice `V`. -/
def T1 : LatticeEnd :=
  !![1, 0, -6, 2;
     0, -1, 1, 1;
     0, -1, 0, 1;
     0, 0, 0, 1]

/-- The order-four monodromy on the rank-four lattice `V`. -/
def T2 : LatticeEnd :=
  !![1, 6, 0, -3;
     0, 0, -1, 1;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- The parabolic cusp monodromy `(T₁T₂)⁻¹`, exhibited integrally. -/
def T0 : LatticeEnd :=
  !![1, 0, 0, 1;
     0, 1, -1, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The square-zero logarithm of the cusp monodromy. -/
def N : LatticeEnd := T0 - 1

theorem T1_det : T1.det = 1 := by decide

theorem T2_det : T2.det = 1 := by decide

theorem T1_hasExactOrderThree : T1 ^ 3 = 1 ∧ T1 ≠ 1 := by decide

theorem T2_hasExactOrderFour : T2 ^ 4 = 1 ∧ T2 ^ 2 ≠ 1 := by decide

theorem T0_isTheIntegralInverse :
    (T1 * T2) * T0 = 1 ∧ T0 * (T1 * T2) = 1 := by decide

theorem T0_isUnipotent : T0 = 1 + N := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [T0, N]

theorem N_isSquareZero : N ^ 2 = 0 := by decide

theorem N_onTheBasis :
    N.mulVec ![1, 0, 0, 0] = 0 ∧
    N.mulVec ![0, 1, 0, 0] = 0 ∧
    N.mulVec ![0, 0, 1, 0] = ![0, -1, 0, 0] ∧
    N.mulVec ![0, 0, 0, 1] = ![1, 0, 0, 0] := by
  decide

/-! ## The dual lattice action -/

/-- The paper's explicit dual action `A₁ = (T₁⁻¹)ᵀ`. -/
def A1 : LatticeEnd :=
  !![1, 0, 0, 0;
     6, 0, 1, 0;
     -6, -1, -1, 0;
     -2, 1, 0, 1]

/-- The paper's explicit dual action `A₂ = (T₂⁻¹)ᵀ`. -/
def A2 : LatticeEnd :=
  !![1, 0, 0, 0;
     0, 0, -1, 0;
     -6, 1, 0, 0;
     3, 0, 1, 1]

/-- The paper's explicit dual cusp action `M₀ = (T₀⁻¹)ᵀ`. -/
def M0 : LatticeEnd :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 1, 1, 0;
     -1, 0, 0, 1]

theorem A1_isInverseTranspose :
    A1 * T1.transpose = 1 ∧ T1.transpose * A1 = 1 := by decide

theorem A2_isInverseTranspose :
    A2 * T2.transpose = 1 ∧ T2.transpose * A2 = 1 := by decide

theorem M0_isInverseTranspose :
    M0 * T0.transpose = 1 ∧ T0.transpose * M0 = 1 := by decide

theorem M0_isDualUnipotent : M0 = 1 - N.transpose := by decide

/-- The three displayed dual monodromies satisfy the triangle-group product relation. -/
theorem dualMonodromy_product : A1 * A2 * M0 = 1 := by decide

def epsilon : Lattice := ![1, 2, -4, 0]

def epsilon' : Lattice := ![1, 3, -3, 0]

def deltaHat : Lattice := ![0, 0, 0, 1]

theorem distinguishedVectors_areFixed :
    A1.mulVec epsilon = epsilon ∧
    A2.mulVec epsilon' = epsilon' ∧
    A1.mulVec deltaHat = deltaHat ∧
    A2.mulVec deltaHat = deltaHat := by
  decide

/-- The complete fixed lattice of `A₁`, not merely the two displayed fixed vectors. -/
theorem A1_fixedLattice (v : Lattice) :
    A1.mulVec v = v ↔ ∃ a d : ℤ, v = a • epsilon + d • deltaHat := by
  constructor
  · intro hv
    have h1 := congr_fun hv 1
    have h2 := congr_fun hv 2
    have h3 := congr_fun hv 3
    simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1 h2 h3
    refine ⟨v 0, v 3, ?_⟩
    ext i
    fin_cases i <;>
      simp [epsilon, deltaHat, h1, h2, h3] <;>
      omega
  · rintro ⟨a, d, rfl⟩
    ext i
    fin_cases i <;>
      simp [A1, epsilon, deltaHat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring

/-- The complete fixed lattice of `A₂`, not merely the two displayed fixed vectors. -/
theorem A2_fixedLattice (v : Lattice) :
    A2.mulVec v = v ↔ ∃ a d : ℤ, v = a • epsilon' + d • deltaHat := by
  constructor
  · intro hv
    have h1 := congr_fun hv 1
    have h2 := congr_fun hv 2
    have h3 := congr_fun hv 3
    simp [A2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1 h2 h3
    refine ⟨v 0, v 3, ?_⟩
    ext i
    fin_cases i <;>
      simp [epsilon', deltaHat, h1, h2, h3] <;>
      omega
  · rintro ⟨a, d, rfl⟩
    ext i
    fin_cases i <;>
      simp [A2, epsilon', deltaHat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring

/-- The surviving coinvariant coordinate: evaluation at the first lattice coordinate. -/
def gamma (v : Lattice) : ℤ := v 0

theorem monodromyDifferences_areInvisibleToGamma (v : Lattice) :
    gamma ((A1 - 1).mulVec v) = 0 ∧ gamma ((A2 - 1).mulVec v) = 0 := by
  constructor <;>
    simp [gamma, A1, A2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- All three dual monodromies preserve the surviving coinvariant coordinate. -/
theorem gamma_isMonodromyInvariant (v : Lattice) :
    gamma (A1.mulVec v) = gamma v ∧
      gamma (A2.mulVec v) = gamma v ∧
      gamma (M0.mulVec v) = gamma v := by
  simp [gamma, A1, A2, M0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The cusp map on the two-dimensional quotient/toric lattice, in the paper's bases. -/
def B0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

theorem B0_isUnimodular : B0.det = 1 := by
  norm_num [B0, Matrix.det_fin_two]

/-! ## The twist obstruction -/

/-- The integer controlling the cyclic fundamental-group presentation in the paper. -/
def seifertObstruction (ℓ0 ℓ1 ℓ2 : ℤ) : ℤ := 12 * ℓ0 - 4 * ℓ1 - 3 * ℓ2

/-- The coefficients are exactly the `(3,4)` Seifert denominators cleared by `lcm(3,4)=12`. -/
theorem seifertObstruction_clearsDenominators (ℓ0 ℓ1 ℓ2 : ℤ) :
    (seifertObstruction ℓ0 ℓ1 ℓ2 : ℚ) =
      12 * ((ℓ0 : ℚ) - (ℓ1 : ℚ) / 3 - (ℓ2 : ℚ) / 4) := by
  norm_num [seifertObstruction]
  ring

theorem chosenTwists : gamma epsilon = 1 ∧ gamma (-epsilon') = -1 := by
  norm_num [gamma, epsilon, epsilon']

theorem chosenObstruction_isNegativeOne : seifertObstruction 0 1 (-1) = -1 := by
  norm_num [seifertObstruction]

theorem chosenObstruction_hasUnitMagnitude :
    Int.natAbs (seifertObstruction 0 1 (-1)) = 1 := by
  norm_num [seifertObstruction]

/-- The orbifold Euler excess at `(3,4,∞)`.  This is a separate scalar from the
translation-weighted Seifert obstruction above; no geometric identification is asserted. -/
theorem orbifoldExcess_three_four_infinity :
    (1 / 3 : ℚ) + 1 / 4 - 1 = -5 / 12 := by norm_num

end Soma.Holonics.Geometry.SixSphereMonodromy
