import Mathlib
import ElementaryHolonics.Mathematics.RatioSeriesTransport

/-!
# Exact finite generator factorisation certificates

This file records the elementary certificate used by a finite bilinear
generator search.  The certificate is an equality of maps, so its proof does
not depend on a search procedure or on a choice of inverse.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.GeneratorFactorization

open Soma.Holonics.Mathematics.RatioSeriesTransport

variable {R ι κ ρ ω : Type*} [CommRing R]
variable [Fintype ι] [Fintype κ] [Fintype ρ]

/-- A finite rank factorisation of a bilinear coefficient tensor gives the
corresponding bilinear map factorisation. -/
theorem bilinear_factorization
    (U : ρ → ι → R) (V : ρ → κ → R) (W : ω → ρ → R)
    (T : ω → ι → κ → R)
    (hT : ∀ o i j, T o i j = ∑ r, W o r * U r i * V r j)
    (o : ω) (x : ι → R) (y : κ → R) :
    ∑ r, W o r * (∑ i, U r i * x i) * (∑ j, V r j * y j) =
      ∑ i, ∑ j, T o i j * x i * y j := by
  classical
  calc
    (∑ r, W o r * (∑ i, U r i * x i) * (∑ j, V r j * y j)) =
        ∑ r, ∑ i, ∑ j, W o r * (U r i * x i) * (V r j * y j) := by
          congr 1
          funext r
          rw [show W o r * (∑ i, U r i * x i) * (∑ j, V r j * y j) =
            W o r * ((∑ i, U r i * x i) * (∑ j, V r j * y j)) by ring]
          rw [Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i, ∑ j, ∑ r, W o r * U r i * V r j * x i * y j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ i, ∑ j, T o i j * x i * y j := by
          simp [hT, Finset.sum_mul]

/-- Gauss's three-product formula for complex multiplication in real
coordinates.  The statement is deliberately over an arbitrary commutative
ring; it is an exact algebraic identity, not a numerical approximation. -/
theorem gauss_three_product
    (a b c d : R) :
    let p := (a + b) * c
    let q := a * (d - c)
    let r := b * (c + d)
    (p - r, p + q) = (a * c - b * d, a * d + b * c) := by
  dsimp
  ring

/-- The particular support selected by the exterior exact search. -/
theorem selected_three_product (a b c d : R) :
    let p := a * c
    let q := b * d
    let r := (a + b) * (c + d)
    (p - q, r - p - q) = (a * c - b * d, a * d + b * c) := by
  dsimp
  ring

/-- Shift and multiplication by the current coordinate form a noncommuting
operator chart. This rule must be retained when compiling Gamma shifts. -/
theorem shift_coordinate_commutator (f : R → R) (z : R) :
    (z + 1) * f (z + 1) - z * f (z + 1) = f (z + 1) := by
  ring

/-! ## The affine block bridge

The matrix records the two coefficient coordinates of a `Block`; its
chronological product is the reverse matrix product.  The length/clock field
is intentionally absent from this matrix bridge and remains part of `Block`.
-/

def blockMatrix (b : Block) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![b.alpha, 0; b.beta, 1]

theorem blockMatrix_compose (first second : Block) :
    blockMatrix (first.compose second) =
      blockMatrix second * blockMatrix first := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Block.compose, Matrix.mul_apply]
    <;> ring

/-! ## Exact first-jet transport

`jetAct` is the algebraic value/derivative transport rule.  This is a finite
product-rule certificate; it makes no analytic claim about Gamma or its
uniqueness.
-/

def jetAct (P dP g dg : R) : R × R :=
  (P * g, dP * g + P * dg)

theorem jetAct_compose (P dP Q dQ g dg : R) :
    jetAct Q dQ (jetAct P dP g dg).1 (jetAct P dP g dg).2 =
      jetAct (Q * P) (dQ * P + Q * dP) g dg := by
  simp [jetAct]
  constructor <;> ring

theorem jetAct_step (z g dg : R) :
    jetAct z 1 g dg = (z * g, g + z * dg) := by
  simp [jetAct]

end Soma.Holonics.Mathematics.GeneratorFactorization
