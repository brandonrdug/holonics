import ElementaryHolonics.Geometry.SixSphereMonodromy
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# The equivariant period entrance in the six-sphere construction

This file formalizes the pointwise algebra immediately following the finite monodromy layer of
`SixSphereMonodromy`.  For complex parameters `τ`, `μ`, and `β` it constructs the paper's period
matrix

```text
        [ 6μ  τ  1  0 ]
    Π = [ β   μ  0  1 ],
```

checks its three generator-equivariance identities against the already audited integral matrices
`T₁`, `T₂`, and `T₀`, computes its real determinant, and computes the determinant of the paper's
Hermitian Gram matrix.

Truth status: `[proved-derived] [formal-checked]` for every theorem, relative to the displayed
complex formulas and the integral matrices in `SixSphereMonodromy`.  The structures below are
pointwise algebraic period data.  They do not construct the paper's holomorphic functions on the
upper half-plane, prove their analytic existence or uniqueness, form a topological lattice quotient,
perform a toric/logarithmic filling or gluing, or identify any resulting manifold with `S⁶`.
-/

namespace Soma.Holonics.Geometry.SixSpherePeriods

open Soma.Holonics.Geometry.SixSphereMonodromy

noncomputable section

/-- One point of the paper's three-parameter period family. -/
structure PeriodPoint where
  τ : ℂ
  μ : ℂ
  β : ℂ

abbrev PeriodMatrix := Matrix (Fin 2) (Fin 4) ℂ
abbrev FibreMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev RealPeriodMatrix := Matrix (Fin 4) (Fin 4) ℝ
abbrev ComplexPeriodVector := Fin 4 → ℂ

/-! ## The invariant alternating form and period rows -/

/-- The primitive alternating form from Lemma 2.8, in the basis `(γ, u, w, δ)`. -/
def Q0 : LatticeEnd :=
  !![0, 0, 0, 1;
     0, 0, 6, 0;
     0, -6, 0, 0;
     -1, 0, 0, 0]

theorem Q0_isAlternating : Q0.transpose = -Q0 := by decide

theorem Q0_is_T1_invariant : T1.transpose * Q0 * T1 = Q0 := by decide

theorem Q0_is_T2_invariant : T2.transpose * Q0 * T2 = Q0 := by decide

theorem Q0_is_T0_invariant : T0.transpose * Q0 * T0 = Q0 := by decide

/-- Complexification of the invariant alternating form. -/
def Q0C : Matrix (Fin 4) (Fin 4) ℂ := Q0.map (Int.castRingHom ℂ)

/-- The complex-bilinear extension of `Q₀`. -/
def q0Pairing (v w : ComplexPeriodVector) : ℂ :=
  dotProduct v (Q0C.mulVec w)

/-- The first row `σ₁ = 6μγ + τu + w` of the period matrix. -/
def sigma1 (p : PeriodPoint) : ComplexPeriodVector := ![6 * p.μ, p.τ, 1, 0]

/-- The second row `σ₂ = βγ + μu + δ` of the period matrix. -/
def sigma2 (p : PeriodPoint) : ComplexPeriodVector := ![p.β, p.μ, 0, 1]

/-- The two period rows span an isotropic plane for `Q₀`. -/
theorem periodRows_q0_isotropic (p : PeriodPoint) :
    q0Pairing (sigma1 p) (sigma2 p) = 0 := by
  simp [q0Pairing, sigma1, sigma2, Q0C, Q0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The explicit `2 × 4` period matrix `Π = [Z | I]`, with columns indexed by
`(γ̂, û, ŵ, δ̂)`. -/
def periodMatrix (p : PeriodPoint) : PeriodMatrix :=
  !![6 * p.μ, p.τ, 1, 0;
     p.β, p.μ, 0, 1]

/-- The left `2 × 2` block of the period matrix. -/
def Z (p : PeriodPoint) : FibreMatrix :=
  !![6 * p.μ, p.τ;
     p.β, p.μ]

theorem periodMatrix_is_Z_with_identity (p : PeriodPoint) :
    periodMatrix p = !![Z p 0 0, Z p 0 1, 1, 0;
                        Z p 1 0, Z p 1 1, 0, 1] := by
  rfl

/-! ## The three pointwise period transformations -/

/-- The `(τ₁, μ₁, β₁)` transformation associated to the order-three generator. -/
def g1 (p : PeriodPoint) : PeriodPoint where
  τ := (p.τ - 1) / p.τ
  μ := (1 - p.μ) / p.τ
  β := p.β + 2 - 6 * (1 - p.μ) ^ 2 / p.τ

/-- The `(τ₂, μ₂, β₂)` transformation associated to the order-four generator. -/
def g2 (p : PeriodPoint) : PeriodPoint where
  τ := -1 / p.τ
  μ := 1 + p.μ / p.τ
  β := p.β - 3 - 6 * p.μ ^ 2 / p.τ

/-- The parabolic cusp transformation. -/
def g0 (p : PeriodPoint) : PeriodPoint where
  τ := p.τ - 1
  μ := p.μ
  β := p.β + 1

/-- The fibre-coordinate matrix for the order-three generator. -/
def R1 (p : PeriodPoint) : FibreMatrix :=
  !![-1 / p.τ, 0;
     (1 - p.μ) / p.τ, 1]

/-- The fibre-coordinate matrix for the order-four generator. -/
def R2 (p : PeriodPoint) : FibreMatrix :=
  !![1 / p.τ, 0;
     -p.μ / p.τ, 1]

/-- The cusp generator acts trivially on the fibre coordinates. -/
def R0 : FibreMatrix := 1

/-- Complexification of the transpose lattice action `M_g = T_gᵀ` used by the period formula. -/
def complexMonodromy (T : LatticeEnd) : Matrix (Fin 4) (Fin 4) ℂ :=
  T.transpose.map (Int.castRingHom ℂ)

def M1 : Matrix (Fin 4) (Fin 4) ℂ := complexMonodromy T1
def M2 : Matrix (Fin 4) (Fin 4) ℂ := complexMonodromy T2
def Mcusp : Matrix (Fin 4) (Fin 4) ℂ := complexMonodromy T0

/-- The period matrix is exactly equivariant for the order-three generator. -/
theorem periodMatrix_g1_equivariant (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    periodMatrix (g1 p) = R1 p * periodMatrix p * M1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, g1, R1, M1, complexMonodromy, T1,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- The period matrix is exactly equivariant for the order-four generator. -/
theorem periodMatrix_g2_equivariant (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    periodMatrix (g2 p) = R2 p * periodMatrix p * M2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, g2, R2, M2, complexMonodromy, T2,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- The period matrix is exactly equivariant for the parabolic cusp generator. -/
theorem periodMatrix_g0_equivariant (p : PeriodPoint) :
    periodMatrix (g0 p) = R0 * periodMatrix p * Mcusp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, g0, R0, Mcusp, complexMonodromy, T0,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem R1_det (p : PeriodPoint) : (R1 p).det = -1 / p.τ := by
  simp [R1, Matrix.det_fin_two]

theorem R2_det (p : PeriodPoint) : (R2 p).det = 1 / p.τ := by
  simp [R2, Matrix.det_fin_two]

theorem R0_det : R0.det = 1 := by
  simp [R0]

theorem R1_det_ne_zero (p : PeriodPoint) (hτ : p.τ ≠ 0) : (R1 p).det ≠ 0 := by
  simp [R1_det, hτ]

theorem R2_det_ne_zero (p : PeriodPoint) (hτ : p.τ ≠ 0) : (R2 p).det ≠ 0 := by
  simp [R2_det, hτ]

/-! ## The upper-half-plane and real determinant gates -/

/-- Both elliptic generators divide the imaginary part by `normSq τ`. -/
theorem g1_tau_im (p : PeriodPoint) :
    (g1 p).τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [g1, Complex.div_im, Complex.normSq]
  ring

theorem g2_tau_im (p : PeriodPoint) :
    (g2 p).τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [g2, Complex.div_im, Complex.normSq]
  ring

theorem g0_tau_im (p : PeriodPoint) : (g0 p).τ.im = p.τ.im := by
  simp [g0]

theorem g1_preserves_upperHalfPlane (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    0 < (g1 p).τ.im := by
  rw [g1_tau_im]
  have hne : p.τ ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
    exact hτ.ne' this
  exact div_pos hτ (Complex.normSq_pos.mpr hne)

theorem g2_preserves_upperHalfPlane (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    0 < (g2 p).τ.im := by
  rw [g2_tau_im]
  have hne : p.τ ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
    exact hτ.ne' this
  exact div_pos hτ (Complex.normSq_pos.mpr hne)

theorem g0_preserves_upperHalfPlane (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    0 < (g0 p).τ.im := by simpa [g0_tau_im] using hτ

/-- The real-coordinate matrix of `Π`, using row order
`(Re ζ₁, Im ζ₁, Re ζ₂, Im ζ₂)`. -/
def realPeriodMatrix (p : PeriodPoint) : RealPeriodMatrix :=
  !![6 * p.μ.re, p.τ.re, 1, 0;
     6 * p.μ.im, p.τ.im, 0, 0;
     p.β.re, p.μ.re, 0, 1;
     p.β.im, p.μ.im, 0, 0]

/-- The denominator-free determinant scalar `Im τ Im β - 6(Im μ)²`. -/
def determinantScalar (p : PeriodPoint) : ℝ :=
  p.τ.im * p.β.im - 6 * p.μ.im ^ 2

/-- The paper's defect `D = Im β - 6(Im μ)² / Im τ`. -/
def D (p : PeriodPoint) : ℝ :=
  p.β.im - 6 * p.μ.im ^ 2 / p.τ.im

/-- The real determinant of the four period columns is exactly the denominator-free scalar. -/
theorem realPeriodMatrix_det (p : PeriodPoint) :
    (realPeriodMatrix p).det = determinantScalar p := by
  rw [Matrix.det_succ_row_zero]
  simp [realPeriodMatrix, determinantScalar, Matrix.det_fin_three, Fin.sum_univ_succ,
    Fin.succAbove]
  ring

/-- When `Im τ` is nonzero, the denominator-free determinant is `Im τ · D`. -/
theorem determinantScalar_eq_tauIm_mul_D (p : PeriodPoint) (hτ : p.τ.im ≠ 0) :
    determinantScalar p = p.τ.im * D p := by
  simp only [determinantScalar, D, mul_sub]
  field_simp [hτ]

theorem realPeriodMatrix_det_eq_tauIm_mul_D (p : PeriodPoint) (hτ : p.τ.im ≠ 0) :
    (realPeriodMatrix p).det = p.τ.im * D p := by
  rw [realPeriodMatrix_det, determinantScalar_eq_tauIm_mul_D p hτ]

/-- The exact algebraic lattice prerequisite: strict upper-half-plane and `D < 0` force four
real-linearly independent period columns.  No discreteness/topological quotient claim is made here. -/
theorem realPeriodMatrix_det_negative (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    (realPeriodMatrix p).det < 0 := by
  rw [realPeriodMatrix_det_eq_tauIm_mul_D p hτ.ne']
  exact mul_neg_of_pos_of_neg hτ hD

theorem realPeriodMatrix_det_ne_zero (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    (realPeriodMatrix p).det ≠ 0 :=
  ne_of_lt (realPeriodMatrix_det_negative p hτ hD)

/-- With `τ` in the upper half-plane, `D ≠ 0` is exactly the nonvanishing real-determinant gate. -/
theorem realPeriodMatrix_det_ne_zero_iff (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    (realPeriodMatrix p).det ≠ 0 ↔ D p ≠ 0 := by
  rw [realPeriodMatrix_det_eq_tauIm_mul_D p hτ.ne']
  simp [hτ.ne']

/-- The four real period columns are linearly independent under the paper's strict choice `D < 0`. -/
theorem realPeriodColumns_linearIndependent (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    LinearIndependent ℝ (realPeriodMatrix p).col :=
  Matrix.linearIndependent_cols_of_det_ne_zero (realPeriodMatrix_det_ne_zero p hτ hD)

/-- The cusp shift leaves the defect unchanged. -/
theorem D_g0 (p : PeriodPoint) : D (g0 p) = D p := by
  simp [D, g0]

/-- The order-three period transformation leaves the paper's defect unchanged. -/
theorem D_g1 (p : PeriodPoint) (hτ : 0 < p.τ.im) : D (g1 p) = D p := by
  simp [D, g1, pow_two, Complex.div_im, Complex.normSq, Complex.mul_im, Complex.mul_re,
    Complex.sub_im, Complex.sub_re, Complex.add_im]
  field_simp [hτ.ne']
  ring

/-- The order-four period transformation leaves the paper's defect unchanged. -/
theorem D_g2 (p : PeriodPoint) (hτ : 0 < p.τ.im) : D (g2 p) = D p := by
  simp [D, g2, pow_two, Complex.div_im, Complex.normSq, Complex.mul_im, Complex.mul_re,
    Complex.sub_im, Complex.add_im]
  field_simp [hτ.ne']
  ring

/-! ## The negative Hermitian determinant -/

/-- The Gram matrix of `h(v,v') = i Q₀(v, overline v')` on the two displayed period rows,
with the sign convention of Remark 3.23. -/
def hodgeGram (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  - !![12 * p.τ.im, 12 * p.μ.im;
       12 * p.μ.im, 2 * p.β.im]

/-- The Hermitian form `i Q₀(v, conjugate w)` used in Remark 3.23. -/
def hodgePairing (v w : ComplexPeriodVector) : ℂ :=
  Complex.I * q0Pairing v (fun i => star (w i))

/-- The Gram matrix obtained from the two period rows and the invariant alternating form. -/
def derivedHodgeGram (p : PeriodPoint) : FibreMatrix :=
  fun i j => hodgePairing (![sigma1 p, sigma2 p] i) (![sigma1 p, sigma2 p] j)

/-- Direct derivation of the paper's displayed real Gram matrix from `Q₀`, rather than taking that
matrix as an independent input. -/
theorem derivedHodgeGram_eq_realGram (p : PeriodPoint) :
    derivedHodgeGram p = (hodgeGram p).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [derivedHodgeGram, hodgePairing, q0Pairing, sigma1, sigma2, Q0C, Q0,
      hodgeGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im] <;>
    ring

/-- The Hodge Gram determinant is `24` times the real period determinant scalar. -/
theorem hodgeGram_det (p : PeriodPoint) :
    (hodgeGram p).det = 24 * determinantScalar p := by
  simp [hodgeGram, determinantScalar, Matrix.det_fin_two]
  ring

theorem hodgeGram_det_eq_tauIm_mul_D (p : PeriodPoint) (hτ : p.τ.im ≠ 0) :
    (hodgeGram p).det = 24 * p.τ.im * D p := by
  rw [hodgeGram_det, determinantScalar_eq_tauIm_mul_D p hτ]
  ring

/-- Under the paper's nondegeneracy choice, the Hermitian determinant is negative.  This is the
finite algebraic obstruction to positive definiteness, not a construction of a Hodge structure. -/
theorem hodgeGram_det_negative (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    (hodgeGram p).det < 0 := by
  rw [hodgeGram_det_eq_tauIm_mul_D p hτ.ne']
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hτ) hD

theorem hodgeGram_is_not_positiveSemidefinite (p : PeriodPoint)
    (hτ : 0 < p.τ.im) :
    ¬ Matrix.PosSemidef (hodgeGram p) := by
  intro hpos
  have hdiag := hpos.diag_nonneg (i := (0 : Fin 2))
  simp [hodgeGram] at hdiag
  linarith

end

end Soma.Holonics.Geometry.SixSpherePeriods
