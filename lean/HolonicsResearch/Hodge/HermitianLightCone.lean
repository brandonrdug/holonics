import Mathlib
import HolonicsResearch.Hodge.HodgeEllipticProduct

/-!
# The Hodge index form of a torus of dimension two is the light cone of Hermitian matrices

**[definition]** The chart.  A Hermitian `2 × 2` matrix is `herm t x y z = !![t + z, x − y·i;
x + y·i, t − z]` for four real numbers, and every Hermitian `2 × 2` matrix is one, in one way
(`existsUnique_herm`).  Its determinant is `t² − x² − y² − z²` (`herm_det`).  `mink H K` is the
polarization of the determinant, `(det (H + K) − det H − det K) / 2`, which on two such matrices
reads `t t' − x x' − y y' − z z'` (`mink_herm`).  `quad H v` is the value `v† H v`.  `ray v` is the
rank-one matrix `v v†`.

**[proved-standard; formal-checked]** What is proved on the Hermitian matrices.

1. **The index theorem is the reversed Cauchy–Schwarz inequality** (`det_mul_det_le_mink_sq`,
   `det_mul_det_eq_mink_sq_iff`): for Hermitian `H`, `K` with `0 < det H`,
   `det H · det K ≤ (mink H K)²`, with equality precisely when `K` is a real multiple of `H`.
   So `mink H K = 0` gives `det K ≤ 0` (`det_nonpos_of_mink_eq_zero`), and `det K = 0` besides
   gives `K = 0` (`eq_zero_of_mink_eq_zero_of_det_eq_zero`): the form is negative definite on the
   complement of a class of positive square.  Signature `(1, 3)`.
2. **The cone** (`quad_pos_iff`, `herm_posDef_iff`, `lb_pos_of_future`, `mink_pos_of_posDef`): a
   Hermitian matrix is positive definite precisely when `0 < t` and `0 < det`; two such pair
   positively.  A rank-one matrix `v v†` is Hermitian of determinant zero and positive trace
   (`ray_isHermitian`, `ray_det`, `ray_trace_re_pos`), and two of them pair to
   `|v₀ w₁ − v₁ w₀|² / 2` (`mink_ray_ray`), which vanishes precisely when `w` is a multiple of `v`
   (`mink_ray_ray_eq_zero_iff`, `proportional_iff`).
3. **Moves** (`move_isHermitian`, `det_move`, `mink_move`, `mink_move_of_det_one`, `quad_move`,
   `move_posDef`): `H ↦ g H g†` keeps Hermitian matrices, multiplies the determinant and the
   pairing by `|det g|²`, and carries the value at `v` to the value at `g† v`.  A change of frame
   of determinant one keeps the form, and an invertible one keeps the future cone.  Three kinds, each written (`boostMove_herm`, `turnMove_herm`,
   `shearMove_herm`): the boost `diag(k, 1/k)` scales the two null coordinates `t + z`, `t − z` by
   `k²` and `1/k²`; the turn `diag(u, ū)`, `|u| = 1`, turns the plane `(x, y)` and fixes `t`, `z`;
   the shear `!![1, a; 0, 1]` fixes one null ray and `t − z`.  Their traces squared are `≥ 4`,
   `≤ 4` and `= 4` (`boostMove_trace_sq`, `turnMove_trace_sq`, `shearMove_trace_sq`).

**[proved-derived; formal-checked]** The join to the lattice chart of
`Hodge/HodgeEllipticProduct`.  The real classes of `E × E'` are `ClassR = Fin 6 → ℝ` with the same
period and intersection pairing (`periodR`, `interR`; `periodR_toReal`, `interR_toReal` say that
the integral classes sit inside with the built file's `period` and `inter`).  A real class is of
type `(1, 1)` when its period vanishes, two real equations (`isHodgeR_iff`).  With `τ = a + b i`,
`τ' = a' + b' i`,

`chart τ τ' c = !![b·c12, b'·conj (c14 + c24·τ); b'·(c14 + c24·τ), b'·c34]`

(`chart_eq`) is Hermitian, and on classes of type `(1, 1)`

`Im τ · Im τ' · inter c d = 2 · mink (chart c) (chart d)`  (`interR_eq_mink`).

For `Im τ, Im τ' ≠ 0` the chart is a bijection from the real classes of type `(1, 1)` onto the
Hermitian matrices (`chart_eq_zero`, `chart_injOn`, `chart_surjective`).  Under it
`[E × 0] ↦ Im τ · e₀e₀†`, `[0 × E'] ↦ Im τ' · e₁e₁†`, and the graph of a holomorphic `M` with
multiplier `μ` goes to `Im τ · v v†`, `v = (1, conj μ)` (`chart_fibreE`, `chart_fibreE'`,
`chart_graphClass`): three null rays, as their self-intersection zero says.
`[E × 0] + [0 × E']` goes to `diag(Im τ, Im τ')`, inside the cone when both are positive
(`chart_ample`, `chart_ample_posDef`).  The index theorem follows for every class of positive
square, not only the one the built file uses (`interR_reversed_cauchy_schwarz`,
`hodge_index_real`), and the built file's statement is derived again from it
(`hodge_index_again`).

**[interpretation]** On a torus of dimension two the real classes of type `(1, 1)` with the
intersection form are Minkowski space.  A curve of genus one is a light ray (`v v†`, a point `v`
of the projective line: here the graph of `μ` is the point `(1 : conj μ)`); the graphs of `μ` and
`ν` meet in `|μ − ν|² · Im τ / Im τ'` points (`inter_graphClass_graphClass_mul_im`, from
`mink_ray_ray`), zero precisely when they are the same ray.  The ample classes are the interior of the future cone, the Hodge index theorem is the
reversed Cauchy–Schwarz inequality of a timelike vector against any other, and a change of the
complex frame acts by a Lorentz move.  In the vocabulary of the Swing: a move of determinant one
is a turn (elliptic, trace² < 4), a boost (hyperbolic, trace² > 4) or a shear (parabolic,
trace² = 4, free fall), and here each acts on the classes as the Lorentz move of its kind.

**The tree's abstract form.**  `Hodge/HodgeIndex` builds, from a unit direction `e` of a real inner
product space, the form `v ↦ 2⟪e, v⟫² − ‖v‖²` of signature `(1, n − 1)`.  The determinant here is
its instance on `ℝ⁴` with `e` the `t` axis: `2t² − (t² + x² + y² + z²) = t² − x² − y² − z²`
(`lq_eq_hodge_reading`).  That module is not imported; the identity is stated on coordinates.

**What this does not state.**  The chart is linear algebra on `Λ²ℝ⁴` and on `2 × 2` matrices.  It
does not formalize that `ClassR` with `interR` is the second cohomology of the product with its cup
product, that the period's vanishing is the type `(1, 1)`, or that a class in the open cone is the
class of an ample divisor (Nakai–Moishezon and Lefschetz carry those).  It treats a product of two
tori of dimension one; for a general torus of dimension two the real `(1, 1)` classes are again
the Hermitian forms on `ℂ²` and the same four statements hold, and that case is not written here.
Nothing is said about the integral points of the cone (the Néron–Severi lattice inside it) beyond
the images of the three families of curves, nor about tori of higher dimension, where the index
form on `(1, 1)` classes is the polarization of a determinant of larger Hermitian matrices against
a fixed class and its cone is no longer a light cone.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Holonics.Hodge.HermitianLightCone

open Complex Matrix
open scoped ComplexOrder ComplexConjugate
open Holonics.Hodge.EllipticProduct

noncomputable section

/-! ## M1. The chart of Hermitian `2 × 2` matrices -/

/-- [definition] The Hermitian matrix with coordinates `(t, x, y, z)`. -/
def herm (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((t + z : ℝ) : ℂ), (x : ℂ) - y * I; (x : ℂ) + y * I, ((t - z : ℝ) : ℂ)]

@[simp] theorem herm_apply_zero_zero (t x y z : ℝ) : herm t x y z 0 0 = ((t + z : ℝ) : ℂ) := rfl
@[simp] theorem herm_apply_zero_one (t x y z : ℝ) : herm t x y z 0 1 = (x : ℂ) - y * I := rfl
@[simp] theorem herm_apply_one_zero (t x y z : ℝ) : herm t x y z 1 0 = (x : ℂ) + y * I := rfl
@[simp] theorem herm_apply_one_one (t x y z : ℝ) : herm t x y z 1 1 = ((t - z : ℝ) : ℂ) := rfl

/-- Two `2 × 2` matrices with the same four entries are equal. -/
theorem ext_fin_two {A B : Matrix (Fin 2) (Fin 2) ℂ} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- [definition] The four coordinates read off a matrix. -/
def tOf (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((H 0 0).re + (H 1 1).re) / 2
/-- [definition] -/
def xOf (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (H 1 0).re
/-- [definition] -/
def yOf (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (H 1 0).im
/-- [definition] -/
def zOf (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((H 0 0).re - (H 1 1).re) / 2

@[simp] theorem tOf_herm (t x y z : ℝ) : tOf (herm t x y z) = t := by simp [tOf]
@[simp] theorem xOf_herm (t x y z : ℝ) : xOf (herm t x y z) = x := by simp [xOf]
@[simp] theorem yOf_herm (t x y z : ℝ) : yOf (herm t x y z) = y := by simp [yOf]
@[simp] theorem zOf_herm (t x y z : ℝ) : zOf (herm t x y z) = z := by simp [zOf]

/-- [proved-standard; formal-checked] `herm t x y z` is Hermitian. -/
theorem herm_isHermitian (t x y z : ℝ) : (herm t x y z).IsHermitian := by
  apply ext_fin_two
  · simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply]
    ring
  · simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply]

/-- [proved-standard; formal-checked] A Hermitian `2 × 2` matrix is `herm` of its coordinates. -/
theorem eq_herm_of_isHermitian {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    H = herm (tOf H) (xOf H) (yOf H) (zOf H) := by
  have h00 : (H 0 0).im = 0 := by
    have := congrArg Complex.im (hH.apply 0 0)
    simp at this
    linarith
  have h11 : (H 1 1).im = 0 := by
    have := congrArg Complex.im (hH.apply 1 1)
    simp at this
    linarith
  have h01re : (H 0 1).re = (H 1 0).re := by
    have := congrArg Complex.re (hH.apply 0 1)
    simpa using this.symm
  have h01im : (H 0 1).im = -(H 1 0).im := by
    have := congrArg Complex.im (hH.apply 0 1)
    simpa using this.symm
  apply ext_fin_two
  · apply Complex.ext
    · simp only [herm_apply_zero_zero, Complex.ofReal_re, tOf, zOf]
      ring
    · simp [h00]
  · apply Complex.ext <;> simp [xOf, yOf, h01re, h01im]
  · apply Complex.ext <;> simp [xOf, yOf]
  · apply Complex.ext
    · simp only [herm_apply_one_one, Complex.ofReal_re, tOf, zOf]
      ring
    · simp [h11]

theorem exists_herm {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ t x y z : ℝ, H = herm t x y z :=
  ⟨_, _, _, _, eq_herm_of_isHermitian hH⟩

/-- [proved-standard; formal-checked] The coordinates are determined. -/
theorem herm_injective {t x y z t' x' y' z' : ℝ} (h : herm t x y z = herm t' x' y' z') :
    t = t' ∧ x = x' ∧ y = y' ∧ z = z' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg tOf h
  · simpa using congrArg xOf h
  · simpa using congrArg yOf h
  · simpa using congrArg zOf h

/-- [proved-standard; formal-checked] M1.  Every Hermitian `2 × 2` matrix is `herm` of exactly one
quadruple of real numbers. -/
theorem existsUnique_herm {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃! q : ℝ × ℝ × ℝ × ℝ, H = herm q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine ⟨(tOf H, xOf H, yOf H, zOf H), eq_herm_of_isHermitian hH, ?_⟩
  rintro ⟨t, x, y, z⟩ h
  simp only at h
  rw [h]
  simp

theorem herm_zero : herm 0 0 0 0 = 0 := by
  apply ext_fin_two <;> simp

theorem herm_add (t x y z t' x' y' z' : ℝ) :
    herm t x y z + herm t' x' y' z' = herm (t + t') (x + x') (y + y') (z + z') := by
  apply ext_fin_two <;> simp <;> ring

theorem herm_sub (t x y z t' x' y' z' : ℝ) :
    herm t x y z - herm t' x' y' z' = herm (t - t') (x - x') (y - y') (z - z') := by
  apply ext_fin_two <;> simp <;> ring

theorem herm_smul (c t x y z : ℝ) :
    (c : ℂ) • herm t x y z = herm (c * t) (c * x) (c * y) (c * z) := by
  apply ext_fin_two <;> simp <;> ring

/-- [definition] The Lorentz quadratic form on coordinates. -/
def lq (t x y z : ℝ) : ℝ := t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2

/-- [definition] The Lorentz pairing on coordinates. -/
def lb (t x y z t' x' y' z' : ℝ) : ℝ := t * t' - x * x' - y * y' - z * z'

/-- [proved-standard; formal-checked] M1.  The determinant is the Lorentz quadratic form. -/
theorem herm_det (t x y z : ℝ) :
    (herm t x y z).det = ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [herm_apply_zero_zero, herm_apply_zero_one, herm_apply_one_zero, herm_apply_one_one]
  push_cast
  linear_combination ((y : ℂ) ^ 2) * Complex.I_sq

theorem herm_det_re (t x y z : ℝ) : ((herm t x y z).det).re = lq t x y z := by
  rw [herm_det, Complex.ofReal_re, lq]

theorem herm_det_im (t x y z : ℝ) : ((herm t x y z).det).im = 0 := by
  rw [herm_det, Complex.ofReal_im]

/-- [proved-derived; formal-checked] The tree's abstract Hodge form `2⟪e, v⟫² − ‖v‖²`
(`Hodge/HodgeIndex.theHodgeReading`), at `e` the `t` axis of `ℝ⁴`, is this determinant. -/
theorem lq_eq_hodge_reading (t x y z : ℝ) :
    lq t x y z = 2 * (1 * t + 0 * x + 0 * y + 0 * z) ^ 2 - (t ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by
  unfold lq
  ring

/-! ## M2. The pairing -/

/-- [definition] The polarization of the determinant. -/
def mink (H K : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((H + K).det - H.det - K.det).re / 2

theorem mink_eq (H K : Matrix (Fin 2) (Fin 2) ℂ) :
    mink H K = (H 0 0 * K 1 1 + K 0 0 * H 1 1 - H 0 1 * K 1 0 - K 0 1 * H 1 0).re / 2 := by
  unfold mink
  congr 2
  simp only [Matrix.det_fin_two, Matrix.add_apply]
  ring

/-- [proved-standard; formal-checked] M2.  The pairing is symmetric. -/
theorem mink_comm (H K : Matrix (Fin 2) (Fin 2) ℂ) : mink H K = mink K H := by
  rw [mink_eq, mink_eq]
  congr 2
  ring

/-- [proved-standard; formal-checked] M2.  On the diagonal the pairing is the determinant. -/
theorem mink_self (H : Matrix (Fin 2) (Fin 2) ℂ) : mink H H = (H.det).re := by
  rw [mink_eq, Matrix.det_fin_two]
  have : H 0 0 * H 1 1 + H 0 0 * H 1 1 - H 0 1 * H 1 0 - H 0 1 * H 1 0
      = ((2 : ℝ) : ℂ) * (H 0 0 * H 1 1 - H 0 1 * H 1 0) := by
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul]
  ring

/-- [proved-standard; formal-checked] M2.  In coordinates the pairing is the Lorentz pairing. -/
theorem mink_herm (t x y z t' x' y' z' : ℝ) :
    mink (herm t x y z) (herm t' x' y' z') = lb t x y z t' x' y' z' := by
  unfold mink lb
  rw [herm_add, herm_det, herm_det, herm_det, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    Complex.ofReal_re]
  ring

/-- [proved-standard; formal-checked] The pairing is bilinear over the real numbers. -/
theorem mink_smul_smul (a b : ℝ) (H K : Matrix (Fin 2) (Fin 2) ℂ) :
    mink ((a : ℂ) • H) ((b : ℂ) • K) = a * b * mink H K := by
  rw [mink_eq, mink_eq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have : (a : ℂ) * H 0 0 * ((b : ℂ) * K 1 1) + (b : ℂ) * K 0 0 * ((a : ℂ) * H 1 1)
        - (a : ℂ) * H 0 1 * ((b : ℂ) * K 1 0) - (b : ℂ) * K 0 1 * ((a : ℂ) * H 1 0)
      = ((a * b : ℝ) : ℂ) * (H 0 0 * K 1 1 + K 0 0 * H 1 1 - H 0 1 * K 1 0 - K 0 1 * H 1 0) := by
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul]
  ring

/-! ## M3. The index theorem is the reversed Cauchy–Schwarz inequality -/

theorem cauchy3 (x y z x' y' z' : ℝ) :
    (x * x' + y * y' + z * z') ^ 2 ≤ (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
  nlinarith [sq_nonneg (x * y' - y * x'), sq_nonneg (x * z' - z * x'), sq_nonneg (y * z' - z * y')]

/-- [proved-standard; formal-checked] A vector orthogonal to a timelike one is not timelike. -/
theorem lq_nonpos_of_orth {t x y z t' x' y' z' : ℝ} (h : 0 < lq t x y z)
    (ho : lb t x y z t' x' y' z' = 0) : lq t' x' y' z' ≤ 0 := by
  unfold lq lb at *
  have hc := cauchy3 x y z x' y' z'
  have e : (t * t') ^ 2 = (x * x' + y * y' + z * z') ^ 2 := by
    rw [show t * t' = x * x' + y * y' + z * z' by linarith]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have h2 : 0 ≤ x' ^ 2 + y' ^ 2 + z' ^ 2 := by positivity
  have h3 : (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2) < t ^ 2 * t' ^ 2 := by
    calc (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2)
        ≤ (x ^ 2 + y ^ 2 + z ^ 2) * t' ^ 2 := mul_le_mul_of_nonneg_left (by linarith) h1
      _ < t ^ 2 * t' ^ 2 := mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have h4 : (t * t') ^ 2 = t ^ 2 * t' ^ 2 := mul_pow t t' 2
  linarith

/-- [proved-standard; formal-checked] A null vector orthogonal to a timelike one is zero. -/
theorem eq_zero_of_orth_of_null {t x y z t' x' y' z' : ℝ} (h : 0 < lq t x y z)
    (ho : lb t x y z t' x' y' z' = 0) (hz : lq t' x' y' z' = 0) :
    t' = 0 ∧ x' = 0 ∧ y' = 0 ∧ z' = 0 := by
  unfold lq lb at *
  have hc := cauchy3 x y z x' y' z'
  have e : (t * t') ^ 2 = (x * x' + y * y' + z * z') ^ 2 := by
    rw [show t * t' = x * x' + y * y' + z * z' by linarith]
  have e2 : (x ^ 2 + y ^ 2 + z ^ 2) * t' ^ 2 = (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
    rw [show t' ^ 2 = x' ^ 2 + y' ^ 2 + z' ^ 2 by linarith]
  have e3 : (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) * t' ^ 2
      = (t * t') ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) * t' ^ 2 := by ring
  have h3 : (t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) * t' ^ 2 ≤ 0 := by rw [e3]; linarith
  have ht2 : t' ^ 2 = 0 := by
    refine le_antisymm ?_ (sq_nonneg t')
    by_contra hh
    rw [not_le] at hh
    have := mul_pos h hh
    linarith
  have ht : t' = 0 := by simpa using ht2
  have hx2 : x' ^ 2 = 0 := by nlinarith [sq_nonneg x', sq_nonneg y', sq_nonneg z']
  have hy2 : y' ^ 2 = 0 := by nlinarith [sq_nonneg x', sq_nonneg y', sq_nonneg z']
  have hz2 : z' ^ 2 = 0 := by nlinarith [sq_nonneg x', sq_nonneg y', sq_nonneg z']
  exact ⟨ht, by simpa using hx2, by simpa using hy2, by simpa using hz2⟩

/-- [proved-standard; formal-checked] The reversed Cauchy–Schwarz inequality on coordinates. -/
theorem lq_mul_lq_le_lb_sq {t x y z t' x' y' z' : ℝ} (h : 0 < lq t x y z) :
    lq t x y z * lq t' x' y' z' ≤ (lb t x y z t' x' y' z') ^ 2 := by
  have ha : lq t x y z ≠ 0 := ne_of_gt h
  have ho : lb t x y z
      (t' - lb t x y z t' x' y' z' / lq t x y z * t) (x' - lb t x y z t' x' y' z' / lq t x y z * x)
      (y' - lb t x y z t' x' y' z' / lq t x y z * y) (z' - lb t x y z t' x' y' z' / lq t x y z * z)
      = 0 := by
    have : lb t x y z
        (t' - lb t x y z t' x' y' z' / lq t x y z * t)
        (x' - lb t x y z t' x' y' z' / lq t x y z * x)
        (y' - lb t x y z t' x' y' z' / lq t x y z * y)
        (z' - lb t x y z t' x' y' z' / lq t x y z * z)
        = lb t x y z t' x' y' z' - lb t x y z t' x' y' z' / lq t x y z * lq t x y z := by
      unfold lb lq
      ring
    rw [this]
    field_simp
    ring
  have h1 := lq_nonpos_of_orth h ho
  have key : lq t x y z * lq
      (t' - lb t x y z t' x' y' z' / lq t x y z * t) (x' - lb t x y z t' x' y' z' / lq t x y z * x)
      (y' - lb t x y z t' x' y' z' / lq t x y z * y) (z' - lb t x y z t' x' y' z' / lq t x y z * z)
      = lq t x y z * lq t' x' y' z' - (lb t x y z t' x' y' z') ^ 2 := by
    have e : ∀ a m : ℝ, a ≠ 0 → a = lq t x y z → m = lb t x y z t' x' y' z' →
        a * lq (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z)
          = a * lq t' x' y' z' - m ^ 2 := by
      intro a m ha0 haq hmq
      have expand : a * lq (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z)
          = a * lq t' x' y' z' - 2 * m * lb t x y z t' x' y' z' + m ^ 2 / a * lq t x y z := by
        unfold lq lb
        field_simp
        ring
      rw [expand, ← haq, ← hmq]
      field_simp
      ring
    exact e _ _ ha rfl rfl
  have h2 : lq t x y z * lq
      (t' - lb t x y z t' x' y' z' / lq t x y z * t) (x' - lb t x y z t' x' y' z' / lq t x y z * x)
      (y' - lb t x y z t' x' y' z' / lq t x y z * y) (z' - lb t x y z t' x' y' z' / lq t x y z * z)
      ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.le h1
  linarith

/-- [proved-standard; formal-checked] Equality in the reversed Cauchy–Schwarz inequality: the two
vectors are proportional. -/
theorem lq_mul_lq_eq_lb_sq_iff {t x y z t' x' y' z' : ℝ} (h : 0 < lq t x y z) :
    lq t x y z * lq t' x' y' z' = (lb t x y z t' x' y' z') ^ 2 ↔
      ∃ c : ℝ, t' = c * t ∧ x' = c * x ∧ y' = c * y ∧ z' = c * z := by
  constructor
  · intro heq
    have ha : lq t x y z ≠ 0 := ne_of_gt h
    have e : ∀ a m : ℝ, a ≠ 0 → a = lq t x y z → m = lb t x y z t' x' y' z' →
        lb t x y z (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z) = 0 ∧
        lq (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z) = 0 := by
      intro a m ha0 haq hmq
      have e1 : lb t x y z (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z)
          = lb t x y z t' x' y' z' - m / a * lq t x y z := by
        unfold lb lq
        ring
      have e2 : a * lq (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z)
          = a * lq t' x' y' z' - 2 * m * lb t x y z t' x' y' z' + m ^ 2 / a * lq t x y z := by
        unfold lq lb
        field_simp
        ring
      refine ⟨?_, ?_⟩
      · rw [e1, ← haq, ← hmq]
        field_simp
        ring
      · have : a * lq (t' - m / a * t) (x' - m / a * x) (y' - m / a * y) (z' - m / a * z) = 0 := by
          rw [e2, ← haq, ← hmq]
          have h5 : a * lq t' x' y' z' = m ^ 2 := by rw [haq, hmq]; exact heq
          rw [h5]
          field_simp
          ring
        exact (mul_eq_zero.mp this).resolve_left ha0
    obtain ⟨ho, hz⟩ := e _ _ ha rfl rfl
    obtain ⟨h1, h2, h3, h4⟩ := eq_zero_of_orth_of_null h ho hz
    exact ⟨lb t x y z t' x' y' z' / lq t x y z, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨c, rfl, rfl, rfl, rfl⟩
    unfold lq lb
    ring

/-- [proved-standard; formal-checked] M3.  The reversed Cauchy–Schwarz inequality: for Hermitian
`H`, `K` with `0 < det H`, `det H · det K ≤ (mink H K)²`. -/
theorem det_mul_det_le_mink_sq {H K : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian)
    (hK : K.IsHermitian) (hpos : 0 < (H.det).re) :
    (H.det).re * (K.det).re ≤ (mink H K) ^ 2 := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH
  obtain ⟨t', x', y', z', rfl⟩ := exists_herm hK
  rw [herm_det_re] at hpos ⊢
  rw [herm_det_re, mink_herm]
  exact lq_mul_lq_le_lb_sq hpos

/-- [proved-standard; formal-checked] M3.  Equality holds precisely when `K` is a real multiple of
`H`. -/
theorem det_mul_det_eq_mink_sq_iff {H K : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian)
    (hK : K.IsHermitian) (hpos : 0 < (H.det).re) :
    (H.det).re * (K.det).re = (mink H K) ^ 2 ↔ ∃ c : ℝ, K = (c : ℂ) • H := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH
  obtain ⟨t', x', y', z', rfl⟩ := exists_herm hK
  rw [herm_det_re] at hpos ⊢
  rw [herm_det_re, mink_herm, lq_mul_lq_eq_lb_sq_iff hpos]
  constructor
  · rintro ⟨c, rfl, rfl, rfl, rfl⟩
    exact ⟨c, (herm_smul c t x y z).symm⟩
  · rintro ⟨c, hc⟩
    rw [herm_smul] at hc
    obtain ⟨h1, h2, h3, h4⟩ := herm_injective hc
    exact ⟨c, h1, h2, h3, h4⟩

/-- [proved-standard; formal-checked] M3.  A Hermitian matrix orthogonal to one of positive
determinant has determinant `≤ 0`. -/
theorem det_nonpos_of_mink_eq_zero {H K : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian)
    (hK : K.IsHermitian) (hpos : 0 < (H.det).re) (h0 : mink H K = 0) : (K.det).re ≤ 0 := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH
  obtain ⟨t', x', y', z', rfl⟩ := exists_herm hK
  rw [herm_det_re] at hpos ⊢
  rw [mink_herm] at h0
  exact lq_nonpos_of_orth hpos h0

/-- [proved-standard; formal-checked] M3.  The form is negative definite on the complement of a
class of positive square: orthogonal and null is zero. -/
theorem eq_zero_of_mink_eq_zero_of_det_eq_zero {H K : Matrix (Fin 2) (Fin 2) ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (hpos : 0 < (H.det).re) (h0 : mink H K = 0)
    (hd : (K.det).re = 0) : K = 0 := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH
  obtain ⟨t', x', y', z', rfl⟩ := exists_herm hK
  rw [herm_det_re] at hpos hd
  rw [mink_herm] at h0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_zero_of_orth_of_null hpos h0 hd
  exact herm_zero

/-! ## M4. The cone -/

/-- [definition] The value `v† H v`, real part. -/
def quad (H : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℝ := (star v ⬝ᵥ (H *ᵥ v)).re

theorem star_dotProduct_herm_mulVec (t x y z : ℝ) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ (herm t x y z *ᵥ v)
      = (((t + z) * normSq (v 0) + (t - z) * normSq (v 1)
          + 2 * x * ((v 0).re * (v 1).re + (v 0).im * (v 1).im)
          + 2 * y * ((v 0).re * (v 1).im - (v 0).im * (v 1).re) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [dotProduct, mulVec, Fin.sum_univ_two, normSq_apply]
    ring
  · simp [dotProduct, mulVec, Fin.sum_univ_two, normSq_apply]
    ring

theorem quad_herm (t x y z : ℝ) (v : Fin 2 → ℂ) :
    quad (herm t x y z) v = (t + z) * normSq (v 0) + (t - z) * normSq (v 1)
      + 2 * x * ((v 0).re * (v 1).re + (v 0).im * (v 1).im)
      + 2 * y * ((v 0).re * (v 1).im - (v 0).im * (v 1).re) := by
  rw [quad, star_dotProduct_herm_mulVec, Complex.ofReal_re]

theorem add_pos_of_future {t x y z : ℝ} (ht : 0 < t) (hq : 0 < lq t x y z) : 0 < t + z := by
  unfold lq at hq
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : t ≤ -z := by linarith
  have h2 : t ^ 2 ≤ z ^ 2 := by nlinarith
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- [proved-standard; formal-checked] M4.  The value `v† H v` is positive at every nonzero `v`
precisely on the future cone `0 < t`, `0 < det`. -/
theorem quad_pos_iff (t x y z : ℝ) :
    (∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < quad (herm t x y z) v) ↔ 0 < t ∧ 0 < lq t x y z := by
  constructor
  · intro h
    have h1 : 0 < t + z := by
      have := h ![1, 0] (by intro h0; simpa using congrFun h0 0)
      rw [quad_herm] at this
      simpa using this
    have h2 : 0 < t - z := by
      have := h ![0, 1] (by intro h0; simpa using congrFun h0 1)
      rw [quad_herm] at this
      simpa using this
    have h3 : 0 < (t + z) * lq t x y z := by
      have := h ![-(x : ℂ) + y * I, ((t + z : ℝ) : ℂ)]
        (by intro h0; have := congrFun h0 1; simp at this; exact h1.ne' (by exact_mod_cast this))
      rw [quad_herm] at this
      simp [normSq_apply] at this
      unfold lq
      nlinarith
    exact ⟨by linarith, (mul_pos_iff_of_pos_left h1).mp h3⟩
  · rintro ⟨ht, hq⟩ v hv
    have htz := add_pos_of_future ht hq
    rw [quad_herm]
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        funext i
        fin_cases i
        · exact h0
        · exact hv1
      have := Complex.normSq_pos.mpr hv0
      simp [hv1]
      positivity
    · have hn : 0 < normSq (v 1) := Complex.normSq_pos.mpr hv1
      have key : (t + z) * ((t + z) * normSq (v 0) + (t - z) * normSq (v 1)
            + 2 * x * ((v 0).re * (v 1).re + (v 0).im * (v 1).im)
            + 2 * y * ((v 0).re * (v 1).im - (v 0).im * (v 1).re))
          = ((t + z) * (v 0).re + x * (v 1).re + y * (v 1).im) ^ 2
            + ((t + z) * (v 0).im + x * (v 1).im - y * (v 1).re) ^ 2
            + lq t x y z * normSq (v 1) := by
        simp only [normSq_apply, lq]
        ring
      have hpos : 0 < (t + z) * ((t + z) * normSq (v 0) + (t - z) * normSq (v 1)
            + 2 * x * ((v 0).re * (v 1).re + (v 0).im * (v 1).im)
            + 2 * y * ((v 0).re * (v 1).im - (v 0).im * (v 1).re)) := by
        rw [key]
        have := mul_pos hq hn
        positivity
      exact (mul_pos_iff_of_pos_left htz).mp hpos

/-- [proved-standard; formal-checked] M4.  Positive definite means inside the future cone. -/
theorem herm_posDef_iff (t x y z : ℝ) :
    (herm t x y z).PosDef ↔ 0 < t ∧ 0 < lq t x y z := by
  rw [← quad_pos_iff, Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ v hv
    exact (Complex.pos_iff.mp (h hv)).1
  · intro h
    refine ⟨herm_isHermitian t x y z, fun v hv => ?_⟩
    rw [Complex.pos_iff]
    refine ⟨h v hv, ?_⟩
    rw [star_dotProduct_herm_mulVec, Complex.ofReal_im]

/-- [proved-standard; formal-checked] Two vectors of the future cone pair positively. -/
theorem lb_pos_of_future {t x y z t' x' y' z' : ℝ} (ht : 0 < t) (hq : 0 < lq t x y z)
    (ht' : 0 < t') (hq' : 0 < lq t' x' y' z') : 0 < lb t x y z t' x' y' z' := by
  unfold lq lb at *
  have hc := cauchy3 x y z x' y' z'
  have h1 : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have h3 : (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2) < t ^ 2 * t' ^ 2 := by
    calc (x ^ 2 + y ^ 2 + z ^ 2) * (x' ^ 2 + y' ^ 2 + z' ^ 2)
        ≤ (x ^ 2 + y ^ 2 + z ^ 2) * t' ^ 2 := mul_le_mul_of_nonneg_left (by linarith) h1
      _ < t ^ 2 * t' ^ 2 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
  have h4 : (t * t') ^ 2 = t ^ 2 * t' ^ 2 := mul_pow t t' 2
  have h5 : 0 < t * t' := mul_pos ht ht'
  by_contra hcon
  rw [not_lt] at hcon
  have h6 : t * t' ≤ x * x' + y * y' + z * z' := by linarith
  have h7 : (t * t') ^ 2 ≤ (x * x' + y * y' + z * z') ^ 2 := by
    apply pow_le_pow_left₀ h5.le h6
  linarith

/-- [proved-standard; formal-checked] M4.  Two positive definite Hermitian matrices pair
positively. -/
theorem mink_pos_of_posDef {H K : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) (hK : K.PosDef) :
    0 < mink H K := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH.isHermitian
  obtain ⟨t', x', y', z', rfl⟩ := exists_herm hK.isHermitian
  rw [herm_posDef_iff] at hH hK
  rw [mink_herm]
  exact lb_pos_of_future hH.1 hH.2 hK.1 hK.2

/-- [definition] The rank-one matrix `v v†`: a null ray of the cone. -/
def ray (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => v i * conj (v j)

@[simp] theorem ray_apply (v : Fin 2 → ℂ) (i j : Fin 2) : ray v i j = v i * conj (v j) := rfl

theorem ray_eq_vecMulVec (v : Fin 2 → ℂ) : ray v = vecMulVec v (star v) := rfl

/-- [proved-standard; formal-checked] M4.  `v v†` is Hermitian. -/
theorem ray_isHermitian (v : Fin 2 → ℂ) : (ray v).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, mul_comm]

/-- [proved-standard; formal-checked] M4.  `v v†` has determinant zero: a null vector. -/
theorem ray_det (v : Fin 2 → ℂ) : (ray v).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [ray_apply]
  ring

theorem ray_trace (v : Fin 2 → ℂ) :
    (ray v).trace = ((normSq (v 0) + normSq (v 1) : ℝ) : ℂ) := by
  rw [Matrix.trace_fin_two]
  simp only [ray_apply, Complex.mul_conj]
  push_cast
  ring

/-- [proved-standard; formal-checked] M4.  For `v ≠ 0` the trace is positive: the ray points to
the future. -/
theorem ray_trace_re_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) : 0 < ((ray v).trace).re := by
  rw [ray_trace, Complex.ofReal_re]
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact hv0
      · exact h1
    have := Complex.normSq_pos.mpr hv1
    have := Complex.normSq_nonneg (v 0)
    linarith
  · have := Complex.normSq_pos.mpr hv0
    have := Complex.normSq_nonneg (v 1)
    linarith

/-- [proved-standard; formal-checked] `v v†` in coordinates: a null vector with `t > 0`. -/
theorem ray_eq_herm (v : Fin 2 → ℂ) :
    ray v = herm ((normSq (v 0) + normSq (v 1)) / 2) ((v 1 * conj (v 0)).re)
      ((v 1 * conj (v 0)).im) ((normSq (v 0) - normSq (v 1)) / 2) := by
  apply ext_fin_two <;> apply Complex.ext <;> simp [normSq_apply] <;> ring

/-- [proved-standard; formal-checked] M4.  Two rays pair to `|v₀ w₁ − v₁ w₀|² / 2`. -/
theorem mink_ray_ray (v w : Fin 2 → ℂ) :
    mink (ray v) (ray w) = normSq (v 0 * w 1 - v 1 * w 0) / 2 := by
  rw [mink_eq]
  congr 1
  have : ray v 0 0 * ray w 1 1 + ray w 0 0 * ray v 1 1 - ray v 0 1 * ray w 1 0
        - ray w 0 1 * ray v 1 0
      = (v 0 * w 1 - v 1 * w 0) * conj (v 0 * w 1 - v 1 * w 0) := by
    simp only [ray_apply, map_sub, map_mul]
    ring
  rw [this, Complex.mul_conj, Complex.ofReal_re]

/-- [proved-standard; formal-checked] M4.  Two rays are orthogonal precisely when
`v₀ w₁ = v₁ w₀`. -/
theorem mink_ray_ray_eq_zero_iff (v w : Fin 2 → ℂ) :
    mink (ray v) (ray w) = 0 ↔ v 0 * w 1 = v 1 * w 0 := by
  rw [mink_ray_ray]
  constructor
  · intro h
    have : normSq (v 0 * w 1 - v 1 * w 0) = 0 := by linarith
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp this)
  · intro h
    rw [sub_eq_zero.mpr h]
    simp

/-- [proved-standard; formal-checked] M4.  That is: `w` is a multiple of `v`, the same ray. -/
theorem proportional_iff {v : Fin 2 → ℂ} (hv : v ≠ 0) (w : Fin 2 → ℂ) :
    v 0 * w 1 = v 1 * w 0 ↔ ∃ c : ℂ, w = c • v := by
  constructor
  · intro h
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext i
        fin_cases i
        · exact hv0
        · exact h1
      have hw0 : w 0 = 0 := by
        rw [hv0, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hv1
      refine ⟨w 1 / v 1, ?_⟩
      funext i
      fin_cases i
      · simp [hw0, hv0]
      · simp
        field_simp
    · refine ⟨w 0 / v 0, ?_⟩
      funext i
      fin_cases i
      · simp
        field_simp
      · simp
        field_simp
        linear_combination h
  · rintro ⟨c, rfl⟩
    simp
    ring

/-! ## M5. Moves -/

/-- [proved-standard; formal-checked] M5.  `g H g†` is Hermitian. -/
theorem move_isHermitian (g : Matrix (Fin 2) (Fin 2) ℂ) {H : Matrix (Fin 2) (Fin 2) ℂ}
    (hH : H.IsHermitian) : (g * H * gᴴ).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose g hH

/-- [proved-standard; formal-checked] M5.  The determinant scales by `|det g|²`. -/
theorem det_move (g H : Matrix (Fin 2) (Fin 2) ℂ) :
    (g * H * gᴴ).det = (normSq g.det : ℂ) * H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

/-- [proved-standard; formal-checked] M5.  The pairing scales by `|det g|²`. -/
theorem mink_move (g H K : Matrix (Fin 2) (Fin 2) ℂ) :
    mink (g * H * gᴴ) (g * K * gᴴ) = normSq g.det * mink H K := by
  unfold mink
  have hadd : g * H * gᴴ + g * K * gᴴ = g * (H + K) * gᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [hadd, det_move, det_move, det_move]
  have : (normSq g.det : ℂ) * (H + K).det - (normSq g.det : ℂ) * H.det
        - (normSq g.det : ℂ) * K.det
      = (normSq g.det : ℂ) * ((H + K).det - H.det - K.det) := by ring
  rw [this, Complex.re_ofReal_mul]
  ring

/-- [proved-standard; formal-checked] M5.  A change of frame of determinant one keeps the form: a
Lorentz move. -/
theorem mink_move_of_det_one {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1)
    (H K : Matrix (Fin 2) (Fin 2) ℂ) : mink (g * H * gᴴ) (g * K * gᴴ) = mink H K := by
  rw [mink_move, hg]
  simp

/-- [proved-standard; formal-checked] M5.  The value at `v` of the moved matrix is the value of
the matrix at `g† v`. -/
theorem quad_move (g H : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    quad (g * H * gᴴ) v = quad H (gᴴ *ᵥ v) := by
  unfold quad
  congr 1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]

/-- [proved-standard; formal-checked] M5.  An invertible move keeps the future cone: time
orientation is kept. -/
theorem move_posDef {g H : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (hH : H.PosDef) :
    (g * H * gᴴ).PosDef := by
  have hinj : Function.Injective gᴴ.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hg)
  have := hH.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-- [definition] The boost `diag(k, 1/k)`. -/
def boostMove (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(k : ℂ), 0; 0, ((k⁻¹ : ℝ) : ℂ)]

/-- [definition] The turn `diag(u, conj u)`. -/
def turnMove (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![u, 0; 0, conj u]

/-- [definition] The shear `!![1, a; 0, 1]`. -/
def shearMove (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, (a : ℂ); 0, 1]

theorem boostMove_det {k : ℝ} (hk : k ≠ 0) : (boostMove k).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [boostMove, hk]

theorem turnMove_det {u : ℂ} (hu : normSq u = 1) : (turnMove u).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [turnMove, Complex.mul_conj, hu]

theorem shearMove_det (a : ℝ) : (shearMove a).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [shearMove]

theorem move_apply (g H : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (g * H * gᴴ) i j = (g i 0 * H 0 0 + g i 1 * H 1 0) * conj (g j 0)
      + (g i 0 * H 0 1 + g i 1 * H 1 1) * conj (g j 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def]

@[simp] theorem boostMove_apply_zero_zero (k : ℝ) : boostMove k 0 0 = (k : ℂ) := rfl
@[simp] theorem boostMove_apply_zero_one (k : ℝ) : boostMove k 0 1 = 0 := rfl
@[simp] theorem boostMove_apply_one_zero (k : ℝ) : boostMove k 1 0 = 0 := rfl
@[simp] theorem boostMove_apply_one_one (k : ℝ) : boostMove k 1 1 = ((k⁻¹ : ℝ) : ℂ) := rfl
@[simp] theorem turnMove_apply_zero_zero (u : ℂ) : turnMove u 0 0 = u := rfl
@[simp] theorem turnMove_apply_zero_one (u : ℂ) : turnMove u 0 1 = 0 := rfl
@[simp] theorem turnMove_apply_one_zero (u : ℂ) : turnMove u 1 0 = 0 := rfl
@[simp] theorem turnMove_apply_one_one (u : ℂ) : turnMove u 1 1 = conj u := rfl
@[simp] theorem shearMove_apply_zero_zero (a : ℝ) : shearMove a 0 0 = 1 := rfl
@[simp] theorem shearMove_apply_zero_one (a : ℝ) : shearMove a 0 1 = (a : ℂ) := rfl
@[simp] theorem shearMove_apply_one_zero (a : ℝ) : shearMove a 1 0 = 0 := rfl
@[simp] theorem shearMove_apply_one_one (a : ℝ) : shearMove a 1 1 = 1 := rfl

/-- [proved-standard; formal-checked] The boost scales the null coordinates `t + z`, `t − z` by
`k²`, `1/k²` and fixes `x`, `y`. -/
theorem boostMove_herm (k t x y z : ℝ) (hk : k ≠ 0) :
    boostMove k * herm t x y z * (boostMove k)ᴴ
      = herm ((k ^ 2 * (t + z) + (k⁻¹) ^ 2 * (t - z)) / 2) x y
          ((k ^ 2 * (t + z) - (k⁻¹) ^ 2 * (t - z)) / 2) := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  apply ext_fin_two
  · rw [move_apply]
    simp
    ring
  · rw [move_apply]
    simp
    field_simp
  · rw [move_apply]
    simp
    field_simp
  · rw [move_apply]
    simp
    ring

/-- [proved-standard; formal-checked] The turn fixes `t`, `z` and turns `x + y i` by `conj u²`. -/
theorem turnMove_herm (u : ℂ) (hu : normSq u = 1) (t x y z : ℝ) :
    turnMove u * herm t x y z * (turnMove u)ᴴ
      = herm t ((conj u ^ 2 * ((x : ℂ) + y * I)).re) ((conj u ^ 2 * ((x : ℂ) + y * I)).im) z := by
  have h1 : u * conj u = 1 := by rw [Complex.mul_conj, hu]; simp
  have hre : ∀ w : ℂ, ((w.re : ℂ) + (w.im : ℂ) * I) = w := fun w => Complex.re_add_im w
  have hconj : ∀ w : ℂ, ((w.re : ℂ) - (w.im : ℂ) * I) = conj w := by
    intro w
    apply Complex.ext <;> simp
  apply ext_fin_two
  · rw [move_apply]
    simp
    linear_combination ((t : ℂ) + z) * h1
  · rw [move_apply]
    simp only [herm_apply_zero_zero, herm_apply_zero_one, herm_apply_one_zero, herm_apply_one_one,
      hconj, turnMove_apply_zero_zero, turnMove_apply_zero_one, turnMove_apply_one_zero,
      turnMove_apply_one_one]
    simp
    ring
  · rw [move_apply]
    simp only [herm_apply_zero_zero, herm_apply_zero_one, herm_apply_one_zero, herm_apply_one_one,
      hre, turnMove_apply_zero_zero, turnMove_apply_zero_one, turnMove_apply_one_zero,
      turnMove_apply_one_one]
    simp
    ring
  · rw [move_apply]
    simp
    linear_combination ((t : ℂ) - z) * h1

/-- [proved-standard; formal-checked] The shear fixes `t − z`, `y` and the null ray of
`herm 1 0 0 1`. -/
theorem shearMove_herm (a t x y z : ℝ) :
    shearMove a * herm t x y z * (shearMove a)ᴴ
      = herm (t + a * x + a ^ 2 * (t - z) / 2) (x + a * (t - z)) y
          (z + a * x + a ^ 2 * (t - z) / 2) := by
  apply ext_fin_two
  · rw [move_apply]
    simp
    ring
  · rw [move_apply]
    simp
    ring
  · rw [move_apply]
    simp
    ring
  · rw [move_apply]
    simp

/-- [proved-standard; formal-checked] The three kinds by the trace: a boost has `tr² ≥ 4`. -/
theorem boostMove_trace_sq {k : ℝ} (hk : k ≠ 0) :
    ∃ r : ℝ, (boostMove k).trace = (r : ℂ) ∧ 4 ≤ r ^ 2 := by
  refine ⟨k + k⁻¹, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp [boostMove]
  · have h1 : k * k⁻¹ = 1 := mul_inv_cancel₀ hk
    nlinarith [sq_nonneg (k - k⁻¹)]

/-- [proved-standard; formal-checked] A turn has real trace with `tr² ≤ 4`. -/
theorem turnMove_trace_sq {u : ℂ} (hu : normSq u = 1) :
    ∃ r : ℝ, (turnMove u).trace = (r : ℂ) ∧ r ^ 2 ≤ 4 := by
  refine ⟨2 * u.re, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp only [turnMove]
    apply Complex.ext <;> simp
    ring
  · rw [Complex.normSq_apply] at hu
    nlinarith [mul_self_nonneg u.im]

/-- [proved-standard; formal-checked] A shear has `tr² = 4`. -/
theorem shearMove_trace_sq (a : ℝ) : (shearMove a).trace ^ 2 = 4 := by
  rw [Matrix.trace_fin_two]
  simp [shearMove]
  norm_num

/-! ## M6. The join to the lattice chart of `E × E'` -/

/-- [definition] Real classes: `Λ²ℝ⁴` in the built file's coordinates. -/
abbrev ClassR : Type := Fin 6 → ℝ

/-- [definition] An integral class read as a real one. -/
def toReal (c : Class2) : ClassR := fun i => (c i : ℝ)

/-- [definition] The period of a real class. -/
def periodR (τ τ' : ℂ) (c : ClassR) : ℂ := c 1 + c 2 * τ' + c 3 * τ + c 4 * τ * τ'

/-- [definition] The intersection pairing on real classes. -/
def interR (c c' : ClassR) : ℝ :=
  c 0 * c' 5 + c 5 * c' 0 - c 1 * c' 4 - c 4 * c' 1 + c 2 * c' 3 + c 3 * c' 2

/-- [definition] A real class of type `(1, 1)`. -/
def IsHodgeR (τ τ' : ℂ) (c : ClassR) : Prop := periodR τ τ' c = 0

theorem periodR_toReal (τ τ' : ℂ) (c : Class2) : periodR τ τ' (toReal c) = period τ τ' c := by
  simp [periodR, period, toReal]

theorem interR_toReal (c c' : Class2) : interR (toReal c) (toReal c') = (inter c c' : ℝ) := by
  simp [interR, inter, toReal]

theorem isHodgeR_toReal (τ τ' : ℂ) (c : Class2) : IsHodgeR τ τ' (toReal c) ↔ IsHodge τ τ' c := by
  unfold IsHodgeR IsHodge
  rw [periodR_toReal]

theorem interR_comm (c c' : ClassR) : interR c c' = interR c' c := by
  unfold interR
  ring

/-- [proved-derived; formal-checked] The type `(1, 1)` is two real equations. -/
theorem isHodgeR_iff (τ τ' : ℂ) (c : ClassR) :
    IsHodgeR τ τ' c ↔
      c 1 + c 2 * τ'.re + c 3 * τ.re + c 4 * (τ.re * τ'.re - τ.im * τ'.im) = 0 ∧
      c 2 * τ'.im + c 3 * τ.im + c 4 * (τ.re * τ'.im + τ.im * τ'.re) = 0 := by
  unfold IsHodgeR periodR
  rw [Complex.ext_iff]
  simp
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- [definition] The chart of the real classes in Hermitian matrices. -/
def chart (τ τ' : ℂ) (c : ClassR) : Matrix (Fin 2) (Fin 2) ℂ :=
  herm ((τ.im * c 0 + τ'.im * c 5) / 2) (τ'.im * (c 2 + c 4 * τ.re)) (τ'.im * (c 4 * τ.im))
    ((τ.im * c 0 - τ'.im * c 5) / 2)

theorem chart_isHermitian (τ τ' : ℂ) (c : ClassR) : (chart τ τ' c).IsHermitian :=
  herm_isHermitian _ _ _ _

/-- [proved-derived; formal-checked] The chart's four entries. -/
theorem chart_eq (τ τ' : ℂ) (c : ClassR) :
    chart τ τ' c = !![((τ.im * c 0 : ℝ) : ℂ), (τ'.im : ℂ) * conj ((c 2 : ℂ) + c 4 * τ);
      (τ'.im : ℂ) * ((c 2 : ℂ) + c 4 * τ), ((τ'.im * c 5 : ℝ) : ℂ)] := by
  apply ext_fin_two <;> apply Complex.ext <;> simp [chart] <;> ring

theorem chart_add (τ τ' : ℂ) (c d : ClassR) :
    chart τ τ' (c + d) = chart τ τ' c + chart τ τ' d := by
  unfold chart
  rw [herm_add]
  simp only [Pi.add_apply]
  congr 1 <;> ring

theorem chart_smul (τ τ' : ℂ) (r : ℝ) (c : ClassR) :
    chart τ τ' (r • c) = (r : ℂ) • chart τ τ' c := by
  unfold chart
  rw [herm_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- [proved-derived; formal-checked] M6.  On classes of type `(1, 1)` the intersection pairing is
the light cone's pairing: `Im τ · Im τ' · inter c d = 2 · mink (chart c) (chart d)`. -/
theorem interR_eq_mink {τ τ' : ℂ} {c d : ClassR} (hc : IsHodgeR τ τ' c) (hd : IsHodgeR τ τ' d) :
    τ.im * τ'.im * interR c d = 2 * mink (chart τ τ' c) (chart τ τ' d) := by
  obtain ⟨c_re, c_im⟩ := (isHodgeR_iff τ τ' c).mp hc
  obtain ⟨d_re, d_im⟩ := (isHodgeR_iff τ τ' d).mp hd
  unfold chart
  rw [mink_herm]
  unfold interR lb
  linear_combination (τ'.im * (-(τ.im) * c 4)) * d_re + (τ'.im * (-(τ.im) * d 4)) * c_re
    + (τ'.im * (c 2 + τ.re * c 4)) * d_im + (τ'.im * (d 2 + τ.re * d 4)) * c_im

/-- [proved-derived; formal-checked] M6.  The self-intersection is twice the determinant. -/
theorem interR_self_eq_det {τ τ' : ℂ} {c : ClassR} (hc : IsHodgeR τ τ' c) :
    τ.im * τ'.im * interR c c = 2 * ((chart τ τ' c).det).re := by
  rw [interR_eq_mink hc hc, mink_self]

/-- [proved-derived; formal-checked] M6.  The chart is injective on classes of type `(1, 1)`. -/
theorem chart_eq_zero {τ τ' : ℂ} (hτ : τ.im ≠ 0) (hτ' : τ'.im ≠ 0) {c : ClassR}
    (hc : IsHodgeR τ τ' c) (h : chart τ τ' c = 0) : c = 0 := by
  obtain ⟨c_re, c_im⟩ := (isHodgeR_iff τ τ' c).mp hc
  unfold chart at h
  rw [← herm_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := herm_injective h
  have e0 : τ.im * c 0 = 0 := by linarith
  have e5 : τ'.im * c 5 = 0 := by linarith
  have c0 : c 0 = 0 := (mul_eq_zero.mp e0).resolve_left hτ
  have c5 : c 5 = 0 := (mul_eq_zero.mp e5).resolve_left hτ'
  have c4 : c 4 = 0 := by
    have := (mul_eq_zero.mp h3).resolve_left hτ'
    exact (mul_eq_zero.mp this).resolve_right hτ
  have c2 : c 2 = 0 := by
    have := (mul_eq_zero.mp h2).resolve_left hτ'
    rw [c4] at this
    linarith
  have c3 : c 3 = 0 := by
    rw [c2, c4] at c_im
    have : c 3 * τ.im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hτ
  have c1 : c 1 = 0 := by
    rw [c2, c3, c4] at c_re
    linarith
  funext i
  fin_cases i <;> simp [c0, c1, c2, c3, c4, c5]

theorem isHodgeR_sub {τ τ' : ℂ} {c d : ClassR} (hc : IsHodgeR τ τ' c) (hd : IsHodgeR τ τ' d) :
    IsHodgeR τ τ' (c - d) := by
  unfold IsHodgeR periodR at *
  simp only [Pi.sub_apply]
  push_cast
  linear_combination hc - hd

theorem isHodgeR_add {τ τ' : ℂ} {c d : ClassR} (hc : IsHodgeR τ τ' c) (hd : IsHodgeR τ τ' d) :
    IsHodgeR τ τ' (c + d) := by
  unfold IsHodgeR periodR at *
  simp only [Pi.add_apply]
  push_cast
  linear_combination hc + hd

theorem chart_injOn {τ τ' : ℂ} (hτ : τ.im ≠ 0) (hτ' : τ'.im ≠ 0) {c d : ClassR}
    (hc : IsHodgeR τ τ' c) (hd : IsHodgeR τ τ' d) (h : chart τ τ' c = chart τ τ' d) : c = d := by
  have hsub : chart τ τ' (c - d) = 0 := by
    have : c - d = c + (-1 : ℝ) • d := by
      funext i
      simp [sub_eq_add_neg]
    rw [this, chart_add, chart_smul, h]
    simp
  exact sub_eq_zero.mp (chart_eq_zero hτ hτ' (isHodgeR_sub hc hd) hsub)

/-- [proved-derived; formal-checked] M6.  Every Hermitian matrix is the chart of a real class of
type `(1, 1)`: the classes of type `(1, 1)` are Minkowski space. -/
theorem chart_surjective {τ τ' : ℂ} (hτ : τ.im ≠ 0) (hτ' : τ'.im ≠ 0)
    {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ c : ClassR, IsHodgeR τ τ' c ∧ chart τ τ' c = H := by
  obtain ⟨t, x, y, z, rfl⟩ := exists_herm hH
  set c4 : ℝ := y / (τ.im * τ'.im) with hc4
  set c2 : ℝ := x / τ'.im - c4 * τ.re with hc2
  set c3 : ℝ := -(c2 * τ'.im + c4 * (τ.re * τ'.im + τ.im * τ'.re)) / τ.im with hc3
  set c1 : ℝ := -(c2 * τ'.re + c3 * τ.re + c4 * (τ.re * τ'.re - τ.im * τ'.im)) with hc1
  refine ⟨![(t + z) / τ.im, c1, c2, c3, c4, (t - z) / τ'.im], ?_, ?_⟩
  · rw [isHodgeR_iff]
    constructor
    · simp [hc1]
      ring
    · simp [hc3]
      field_simp
      ring
  · unfold chart
    simp
    congr 1
    · field_simp
      ring
    · rw [hc2]
      field_simp
      ring
    · rw [hc4]
      field_simp
    · field_simp
      ring

/-- [proved-derived; formal-checked] M6.  `[E × 0]` goes to a null ray. -/
theorem chart_fibreE (τ τ' : ℂ) : chart τ τ' (toReal fibreE) = (τ.im : ℂ) • ray ![1, 0] := by
  apply ext_fin_two <;> simp [chart, toReal, fibreE]

/-- [proved-derived; formal-checked] M6.  `[0 × E']` goes to a null ray. -/
theorem chart_fibreE' (τ τ' : ℂ) : chart τ τ' (toReal fibreE') = (τ'.im : ℂ) • ray ![0, 1] := by
  apply ext_fin_two
  · simp [chart, toReal, fibreE']
    ring
  · simp [chart, toReal, fibreE']
  · simp [chart, toReal, fibreE']
  · simp [chart, toReal, fibreE']
    ring

/-- [proved-derived; formal-checked] M6.  The graph of a holomorphic map with multiplier `μ` goes
to the null ray of `v = (1, conj μ)`. -/
theorem chart_graphClass (τ τ' : ℂ) (M : LatticeMap) (h : IsHolomorphic τ τ' M) :
    chart τ τ' (toReal (graphClass M)) = (τ.im : ℂ) • ray ![1, conj (multiplier τ' M)] := by
  have hdet := det_mul_im τ τ' M h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  rw [ray_eq_herm, herm_smul]
  unfold chart
  simp only [multiplier, Complex.normSq_apply, LatticeMap.det] at hdet ⊢
  simp [toReal, graphClass, LatticeMap.det] at hdet ⊢
  congr 1
  · linear_combination (1 / 2 : ℝ) * hdet
  · linear_combination him
  · ring
  · linear_combination (-1 / 2 : ℝ) * hdet

/-- [proved-derived; formal-checked] M6.  So the graph's image is null, as its self-intersection
zero says. -/
theorem chart_graphClass_det (τ τ' : ℂ) (M : LatticeMap) (h : IsHolomorphic τ τ' M) :
    (chart τ τ' (toReal (graphClass M))).det = 0 := by
  rw [chart_graphClass τ τ' M h, Matrix.det_smul, ray_det, mul_zero]

/-- [proved-derived; formal-checked] M6.  Two graphs meet as two light rays pair: the intersection
number of the graphs of `μ` and `ν` is `|μ − ν|²` times the ratio of the lattices' areas, and it
vanishes precisely when the multipliers agree. -/
theorem inter_graphClass_graphClass_mul_im (τ τ' : ℂ) (hτ : τ.im ≠ 0) (M N : LatticeMap)
    (hM : IsHolomorphic τ τ' M) (hN : IsHolomorphic τ τ' N) :
    (inter (graphClass M) (graphClass N) : ℝ) * τ'.im
      = normSq (multiplier τ' M - multiplier τ' N) * τ.im := by
  have hMR : IsHodgeR τ τ' (toReal (graphClass M)) :=
    (isHodgeR_toReal τ τ' _).mpr ((isHodge_graphClass_iff τ τ' M).mpr hM)
  have hNR : IsHodgeR τ τ' (toReal (graphClass N)) :=
    (isHodgeR_toReal τ τ' _).mpr ((isHodge_graphClass_iff τ τ' N).mpr hN)
  have h := interR_eq_mink hMR hNR
  rw [interR_toReal, chart_graphClass τ τ' M hM, chart_graphClass τ τ' N hN, mink_smul_smul,
    mink_ray_ray] at h
  have key : normSq ((![1, conj (multiplier τ' M)] : Fin 2 → ℂ) 0
        * (![1, conj (multiplier τ' N)] : Fin 2 → ℂ) 1
        - (![1, conj (multiplier τ' M)] : Fin 2 → ℂ) 1
        * (![1, conj (multiplier τ' N)] : Fin 2 → ℂ) 0)
      = normSq (multiplier τ' M - multiplier τ' N) := by
    have e : (![1, conj (multiplier τ' M)] : Fin 2 → ℂ) 0
        * (![1, conj (multiplier τ' N)] : Fin 2 → ℂ) 1
        - (![1, conj (multiplier τ' M)] : Fin 2 → ℂ) 1
        * (![1, conj (multiplier τ' N)] : Fin 2 → ℂ) 0
        = conj (-(multiplier τ' M - multiplier τ' N)) := by
      simp
    rw [e, Complex.normSq_conj, Complex.normSq_neg]
  rw [key] at h
  apply mul_left_cancel₀ hτ
  linear_combination h

/-- [proved-derived; formal-checked] M6.  `[E × 0] + [0 × E']` goes to `diag(Im τ, Im τ')`. -/
theorem chart_ample (τ τ' : ℂ) :
    chart τ τ' (toReal (fibreE + fibreE')) = herm ((τ.im + τ'.im) / 2) 0 0 ((τ.im - τ'.im) / 2) := by
  unfold chart
  simp [toReal, fibreE, fibreE']

/-- [proved-derived; formal-checked] M6.  It lies inside the future cone. -/
theorem chart_ample_posDef {τ τ' : ℂ} (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) :
    (chart τ τ' (toReal (fibreE + fibreE'))).PosDef := by
  rw [chart_ample, herm_posDef_iff]
  refine ⟨by linarith, ?_⟩
  unfold lq
  nlinarith [mul_pos hτ hτ']

/-- [proved-derived; formal-checked] M6.  The reversed Cauchy–Schwarz inequality of the
intersection form, against any class of type `(1, 1)` of positive square. -/
theorem interR_reversed_cauchy_schwarz {τ τ' : ℂ} (hτ : 0 < τ.im) (hτ' : 0 < τ'.im)
    {h c : ClassR} (hh : IsHodgeR τ τ' h) (hc : IsHodgeR τ τ' c) (hpos : 0 < interR h h) :
    interR h h * interR c c ≤ (interR h c) ^ 2 := by
  have hk : 0 < τ.im * τ'.im := mul_pos hτ hτ'
  have eA : ((chart τ τ' h).det).re = τ.im * τ'.im * interR h h / 2 := by
    linarith [interR_self_eq_det hh]
  have eB : ((chart τ τ' c).det).re = τ.im * τ'.im * interR c c / 2 := by
    linarith [interR_self_eq_det hc]
  have eM : mink (chart τ τ' h) (chart τ τ' c) = τ.im * τ'.im * interR h c / 2 := by
    linarith [interR_eq_mink hh hc]
  have hle := det_mul_det_le_mink_sq (chart_isHermitian τ τ' h) (chart_isHermitian τ τ' c)
    (by rw [eA]; positivity)
  rw [eA, eB, eM] at hle
  have hk2 : 0 < (τ.im * τ'.im) ^ 2 / 4 := by positivity
  have : (τ.im * τ'.im) ^ 2 / 4 * (interR h h * interR c c)
      ≤ (τ.im * τ'.im) ^ 2 / 4 * (interR h c) ^ 2 := by
    have e1 : τ.im * τ'.im * interR h h / 2 * (τ.im * τ'.im * interR c c / 2)
        = (τ.im * τ'.im) ^ 2 / 4 * (interR h h * interR c c) := by ring
    have e2 : (τ.im * τ'.im * interR h c / 2) ^ 2
        = (τ.im * τ'.im) ^ 2 / 4 * (interR h c) ^ 2 := by ring
    linarith
  exact le_of_mul_le_mul_left this hk2

/-- [proved-derived; formal-checked] M6.  The Hodge index theorem on the real classes of type
`(1, 1)`: the intersection form is negative definite on the complement of any class of positive
square. -/
theorem hodge_index_real {τ τ' : ℂ} (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) {h c : ClassR}
    (hh : IsHodgeR τ τ' h) (hc : IsHodgeR τ τ' c) (hpos : 0 < interR h h)
    (horth : interR h c = 0) : interR c c ≤ 0 ∧ (interR c c = 0 → c = 0) := by
  have hk : 0 < τ.im * τ'.im := mul_pos hτ hτ'
  have hcs := interR_reversed_cauchy_schwarz hτ hτ' hh hc hpos
  rw [horth] at hcs
  have hle : interR c c ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_pos hpos hcon
    nlinarith
  refine ⟨hle, fun h0 => ?_⟩
  have eA : 0 < ((chart τ τ' h).det).re := by
    have := interR_self_eq_det hh
    nlinarith [mul_pos hk hpos]
  have eB : ((chart τ τ' c).det).re = 0 := by
    have := interR_self_eq_det hc
    rw [h0] at this
    linarith
  have eM : mink (chart τ τ' h) (chart τ τ' c) = 0 := by
    have := interR_eq_mink hh hc
    rw [horth] at this
    linarith
  exact chart_eq_zero hτ.ne' hτ'.ne' hc
    (eq_zero_of_mink_eq_zero_of_det_eq_zero (chart_isHermitian τ τ' h) (chart_isHermitian τ τ' c)
      eA eM eB)

/-- [proved-derived; formal-checked] M6.  The built file's `hodge_index`, derived again from the
reversed Cauchy–Schwarz inequality of the light cone. -/
theorem hodge_index_again (τ τ' : ℂ) (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) (c : Class2)
    (hc : IsHodge τ τ' c) (horth : inter c (fibreE + fibreE') = 0) :
    inter c c ≤ 0 ∧ (inter c c = 0 → c = 0) := by
  have hamp : IsHodgeR τ τ' (toReal (fibreE + fibreE')) := by
    rw [isHodgeR_toReal]
    unfold IsHodge
    rw [period_add, isHodge_fibreE τ τ', isHodge_fibreE' τ τ', add_zero]
  have hcR : IsHodgeR τ τ' (toReal c) := (isHodgeR_toReal τ τ' c).mpr hc
  have hpos : 0 < interR (toReal (fibreE + fibreE')) (toReal (fibreE + fibreE')) := by
    rw [interR_toReal, inter_ample_self]
    norm_num
  have horthR : interR (toReal (fibreE + fibreE')) (toReal c) = 0 := by
    rw [interR_toReal, inter_comm, horth]
    simp
  obtain ⟨h1, h2⟩ := hodge_index_real hτ hτ' hamp hcR hpos horthR
  rw [interR_toReal] at h1 h2
  refine ⟨by exact_mod_cast h1, fun h0 => ?_⟩
  have := h2 (by exact_mod_cast h0)
  funext i
  have hi := congrFun this i
  simpa [toReal] using hi

section Audit

#print axioms existsUnique_herm
#print axioms herm_det
#print axioms mink_herm
#print axioms det_mul_det_le_mink_sq
#print axioms det_mul_det_eq_mink_sq_iff
#print axioms eq_zero_of_mink_eq_zero_of_det_eq_zero
#print axioms herm_posDef_iff
#print axioms mink_pos_of_posDef
#print axioms mink_ray_ray
#print axioms proportional_iff
#print axioms mink_move
#print axioms quad_move
#print axioms boostMove_herm
#print axioms turnMove_herm
#print axioms shearMove_herm
#print axioms interR_eq_mink
#print axioms chart_injOn
#print axioms chart_surjective
#print axioms chart_graphClass
#print axioms inter_graphClass_graphClass_mul_im
#print axioms move_posDef
#print axioms chart_ample_posDef
#print axioms interR_reversed_cauchy_schwarz
#print axioms hodge_index_real
#print axioms hodge_index_again

end Audit

end

end Holonics.Hodge.HermitianLightCone
