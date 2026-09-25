import Holonics.Transport.HelicalPairInteraction
import Holonics.Geometry.LocalFactor
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Generator trace faces: what phase carriage conserves, and the machine's transfer determinant

[definition] A site's material is a matrix. Carrying it to another phase conjugates it, so every
class function of the material is a face conserved along the winding: its determinant, its
transfer determinant `det(1 − T·M)` and the whole trace sequence `tr(Mᵏ)`. For a two-by-two
site the existing `Geometry/LocalFactor` companion already reads these as the rotation–dilation
pair: trace `a` and determinant `q`, with `det(1 − T·M) = 1 − aT + qT²`. A machine of
independent sites is their block-diagonal material: its transfer determinant is the product of
the site factors and its closed-word count is the sum of the site trace sequences.

[established-bounded; formal-checked] Scope: matrices over a commutative ring and invertible
carriers. Coupled sites, convergence of a product over infinitely many sites and any statement
about where the zeros of such a product lie are outside this module. No `axiom`, no `sorry`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Holonics.Transport.GeneratorTraceFaces

open Holonics.Transport.HelicalPairInteraction
open Holonics.Geometry.LocalFactor

/-! ## 1. Powers of carried material are carried powers -/

/-- [proved-derived; formal-checked] Carrying commutes with repetition: the `k`-th power of
carried material is the carried `k`-th power. -/
theorem phaseTransport_pow {G : Type*} [Group G] (S P : G) (d : ℤ) (k : ℕ) :
    phaseTransport S P d ^ k = phaseTransport S (P ^ k) d := by
  induction k with
  | zero => simp [phaseTransport]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [phaseTransport]
    generalize P ^ k = X
    group

/-! ## 2. The faces conserved along the winding -/

section Conserved

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- [proved-derived; formal-checked] **Phase carriage conserves the determinant.** -/
theorem carried_material_conserves_determinant (S P : (Matrix ι ι R)ˣ) (d : ℤ) :
    ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R).det = (P : Matrix ι ι R).det := by
  have h : ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((S ^ d)⁻¹ : (Matrix ι ι R)ˣ) * (P : Matrix ι ι R) * ((S ^ d : (Matrix ι ι R)ˣ)) := by
    simp [phaseTransport, _root_.zpow_neg, Units.val_mul]
  rw [h, Matrix.det_units_conj']

/-- [proved-derived; formal-checked] **Phase carriage conserves the whole trace sequence.** The
count of closed words of every length is the same at every phase. -/
theorem carried_material_conserves_trace_sequence (S P : (Matrix ι ι R)ˣ) (d : ℤ) (k : ℕ) :
    (((phaseTransport S P d) ^ k : (Matrix ι ι R)ˣ) : Matrix ι ι R).trace
      = ((P ^ k : (Matrix ι ι R)ˣ) : Matrix ι ι R).trace := by
  rw [phaseTransport_pow]
  have h : ((phaseTransport S (P ^ k) d : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((S ^ d)⁻¹ : (Matrix ι ι R)ˣ) * ((P ^ k : (Matrix ι ι R)ˣ) : Matrix ι ι R)
          * ((S ^ d : (Matrix ι ι R)ˣ)) := by
    simp [phaseTransport, _root_.zpow_neg, Units.val_mul]
  rw [h, Matrix.trace_units_conj']

/-- [proved-derived; formal-checked] Conjugation by an invertible carrier conserves the transfer
determinant. -/
theorem units_conj_conserves_transfer_determinant (U P : (Matrix ι ι R)ˣ) (T : R) :
    ((1 : Matrix ι ι R) - T • ((U⁻¹ * P * U : (Matrix ι ι R)ˣ) : Matrix ι ι R)).det
      = ((1 : Matrix ι ι R) - T • (P : Matrix ι ι R)).det := by
  have h : (1 : Matrix ι ι R) - T • ((U⁻¹ * P * U : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = (↑U⁻¹ : Matrix ι ι R) * ((1 : Matrix ι ι R) - T • (P : Matrix ι ι R))
          * (U : Matrix ι ι R) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h, Matrix.det_units_conj']

/-- [proved-derived; formal-checked] **Phase carriage conserves the transfer determinant**
`det(1 − T·M)`, hence every coefficient of the site's factor. -/
theorem carried_material_conserves_transfer_determinant (S P : (Matrix ι ι R)ˣ) (d : ℤ) (T : R) :
    ((1 : Matrix ι ι R) - T • ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R)).det
      = ((1 : Matrix ι ι R) - T • (P : Matrix ι ι R)).det := by
  unfold phaseTransport
  rw [_root_.zpow_neg]
  exact units_conj_conserves_transfer_determinant (S ^ d) P T

end Conserved

/-! ## 3. A machine of independent sites -/

section Machine

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- [proved-derived; formal-checked] **The machine's transfer determinant is the product of the
site factors.** -/
theorem machine_transfer_determinant (M : σ → Matrix (Fin 2) (Fin 2) R) (T : R) :
    ((1 : Matrix (Fin 2 × σ) (Fin 2 × σ) R) - T • Matrix.blockDiagonal M).det
      = ∏ g, ((1 : Matrix (Fin 2) (Fin 2) R) - T • M g).det := by
  have h : (1 : Matrix (Fin 2 × σ) (Fin 2 × σ) R) - T • Matrix.blockDiagonal M
      = Matrix.blockDiagonal (fun g => (1 : Matrix (Fin 2) (Fin 2) R) - T • M g) := by
    rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_sub]
    rfl
  rw [h, Matrix.det_blockDiagonal]

/-- [proved-derived; formal-checked] For rotation–dilation sites with trace faces `a g` and
determinant faces `q g`, the machine's transfer determinant is `∏ (1 − a_g T + q_g T²)`. -/
theorem machine_factor_of_companions (a q : σ → R) (T : R) :
    ((1 : Matrix (Fin 2 × σ) (Fin 2 × σ) R)
        - T • Matrix.blockDiagonal (fun g => companion (a g) (q g))).det
      = ∏ g, (1 - a g * T + q g * T ^ 2) := by
  rw [machine_transfer_determinant]
  exact Finset.prod_congr rfl fun g _ => theLocalFactorIsTheTransferDeterminant (a g) (q g) T

/-- [proved-derived; formal-checked] **The machine's closed-word count is the sum of the site
trace sequences.** -/
theorem machine_trace_sequence (M : σ → Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    ((Matrix.blockDiagonal M) ^ k).trace = ∑ g, ((M g) ^ k).trace := by
  rw [← Matrix.blockDiagonal_pow, Matrix.trace_blockDiagonal]
  rfl

end Machine

/-! ## 4. Trace faces are invariants, not a complete action certificate -/

/-- [definition] The identity two-state action used by the separating witness below. -/
def identityTwo : Matrix (Fin 2) (Fin 2) ℚ := 1

/-- [definition] A nontrivial unipotent shear with the same trace and determinant faces as
`identityTwo`. -/
def unipotentTwo : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- [proved-derived; formal-checked] The shear's powers retain their nilpotent off-diagonal. -/
theorem unipotentTwo_pow (k : ℕ) :
    unipotentTwo ^ k = !![1, (k : ℚ); 0, 1] := by
  induction k with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipotentTwo]
  | succ k ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [unipotentTwo, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals ring

/-- [counterexample; formal-checked] The identity and unipotent actions have identical trace
sequences, so those faces alone do not certify equality of the transported action. -/
theorem identityTwo_trace_powers_eq_unipotentTwo (k : ℕ) :
    (identityTwo ^ k).trace = (unipotentTwo ^ k).trace := by
  rw [unipotentTwo_pow]
  norm_num [identityTwo, Matrix.trace_fin_two_of]

/-- [counterexample; formal-checked] The identity and unipotent actions also have the same
transfer determinant at every scalar `T`. -/
theorem identityTwo_transfer_determinant_eq_unipotentTwo (T : ℚ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) - T • identityTwo).det =
      ((1 : Matrix (Fin 2) (Fin 2) ℚ) - T • unipotentTwo).det := by
  simp only [identityTwo, unipotentTwo]
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-- [definition] The second basis state used as the source in the separating receiver. -/
def sourceE₂ : Fin 2 → ℚ := ![0, 1]

/-- [counterexample; formal-checked] A source/receiver face distinguishes the two actions in one
step: the first coordinate of `e₂` is zero after the identity and one after the shear. -/
theorem identityTwo_and_unipotentTwo_are_separated_by_source_receiver :
    (identityTwo *ᵥ sourceE₂) 0 ≠ (unipotentTwo *ᵥ sourceE₂) 0 := by
  norm_num [identityTwo, unipotentTwo, sourceE₂, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

end Holonics.Transport.GeneratorTraceFaces
