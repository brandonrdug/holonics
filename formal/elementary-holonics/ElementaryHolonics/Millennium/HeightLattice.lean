import Mathlib.Tactic

/-!
# HeightLattice: the height form pays on the remainder, and the cutoff direction is isotropic

The second installment of the rank-N investigation (`RealizerSupply.lean` is the first): the
Mordell–Weil height lattice of the rational elliptic surface, handed to this development's
positivity discipline as an exact object.  The Néron–Severi lattice of a rational elliptic
surface with no reducible fibres is `U ⊕ E₈(−1)`: a hyperbolic plane spanned by the zero section
and the fibre, and the `E₈` root lattice with reversed sign.  **The height pairing of
Mordell–Weil theory is the negative of the intersection form on the hyperbolic pair's
complement** — so the height form *is* `E₈`, and its positivity is exactly the
positivity-on-the-perp shape of the index equivalence: it pays on the remainder and fails on the
cutoff.

What is proved, all exact over `ℚ`:

* **the height form is a sum of squares with the `E₈` pivots**:
  `Q(x) = 2·L₀² + (3/2)·L₁² + (4/3)·L₂² + (5/4)·L₃² + (4/5)·L₄² + (3/4)·L₅² + (2/3)·L₆² +
  (1/2)·L₇²`, an exact polynomial identity (`ring`); the pivots' product is `1`, the
  determinant-one signature of `E₈`, stated as an identity;
* **the form pays**: `0 ≤ Q x`, riding the sum of squares;
* **the form is anisotropic**: `Q x = 0` forces `x = 0`, by draining the squares from the tail
  of the elimination back to its head — the radical is trivial on the remainder, which is what
  makes the height Gram determinant (the regulator) a genuine volume;
* **the cutoff pair is hyperbolic and its direction is isotropic**: on the hyperbolic plane
  `Q_U(a, b) = 2ab`, the zero-section direction has `Q_U(1, 0) = 0` — the positivity belongs to
  the remainder and **not** to the lattice, which is the can-fail control the tautology rule
  demands, in exactly the shape of the flipped-stress witnesses of `Rigidity.lean`.

The decomposition was computed exactly (integer/rational arithmetic, no floats) and verified as
a polynomial identity on exact rational sample points before this file was written; the kernel
then checks it symbolically.  The `E₈` Gram here is the `T(2,3,5)` tree: a branch node carrying
arms of one, two, and four nodes.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on
the Birch–Swinnerton-Dyer conjecture; no Néron–Tate height, elliptic surface, or specialization
argument appears — the file owns the exact linear algebra those imports would land on.
-/

namespace Soma.Holonics.Millennium.HeightLattice

/-- The `E₈` height form on eight rational coordinates: the `T(2,3,5)` tree with `2` on the
diagonal and `−1` across each edge — center `x₀`, arms `x₁`; `x₂, x₃`; `x₄, x₅, x₆, x₇`. -/
def Q (x : Fin 8 → ℚ) : ℚ :=
  2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2)
    - 2 * (x 0 * x 1 + x 0 * x 2 + x 2 * x 3 + x 0 * x 4 + x 4 * x 5 + x 5 * x 6 + x 6 * x 7)

/-- The eight elimination forms of the exact decomposition. -/
def L0 (x : Fin 8 → ℚ) : ℚ := x 0 - (1/2) * x 1 - (1/2) * x 2 - (1/2) * x 4
def L1 (x : Fin 8 → ℚ) : ℚ := x 1 - (1/3) * x 2 - (1/3) * x 4
def L2 (x : Fin 8 → ℚ) : ℚ := x 2 - (3/4) * x 3 - (1/2) * x 4
def L3 (x : Fin 8 → ℚ) : ℚ := x 3 - (2/5) * x 4
def L4 (x : Fin 8 → ℚ) : ℚ := x 4 - (5/4) * x 5
def L5 (x : Fin 8 → ℚ) : ℚ := x 5 - (4/3) * x 6
def L6 (x : Fin 8 → ℚ) : ℚ := x 6 - (3/2) * x 7
def L7 (x : Fin 8 → ℚ) : ℚ := x 7

/-- **The height form is a sum of squares with the `E₈` pivots** — an exact polynomial
identity. -/
theorem theHeightFormIsASumOfSquares (x : Fin 8 → ℚ) :
    Q x = 2 * L0 x ^ 2 + (3/2) * L1 x ^ 2 + (4/3) * L2 x ^ 2 + (5/4) * L3 x ^ 2
        + (4/5) * L4 x ^ 2 + (3/4) * L5 x ^ 2 + (2/3) * L6 x ^ 2 + (1/2) * L7 x ^ 2 := by
  simp only [Q, L0, L1, L2, L3, L4, L5, L6, L7]
  ring

/-- **The pivots' product is one** — the determinant-one signature of `E₈`, the unimodularity
the regulator story rides on.  *The proof is `norm_num`; the content is the identity.* -/
theorem thePivotProductIsOne :
    (2 : ℚ) * (3/2) * (4/3) * (5/4) * (4/5) * (3/4) * (2/3) * (1/2) = 1 := by norm_num

/-- **The height form pays**: it is non-negative everywhere, riding the sum of squares. -/
theorem theHeightFormPays (x : Fin 8 → ℚ) : 0 ≤ Q x := by
  rw [theHeightFormIsASumOfSquares]
  have s0 := sq_nonneg (L0 x); have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x); have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x); have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x); have s7 := sq_nonneg (L7 x)
  linarith

/-- **The height form is anisotropic**: a vector of height zero is the zero vector.  The squares
drain from the tail of the elimination back to its head. -/
theorem theHeightFormIsAnisotropic (x : Fin 8 → ℚ) (h : Q x = 0) : x = 0 := by
  rw [theHeightFormIsASumOfSquares] at h
  have s0 := sq_nonneg (L0 x); have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x); have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x); have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x); have s7 := sq_nonneg (L7 x)
  have h7 : L7 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h6 : L6 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h5 : L5 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h4 : L4 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h3 : L3 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h2 : L2 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h1 : L1 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h0 : L0 x = 0 := sq_eq_zero_iff.mp (by linarith)
  simp only [L0, L1, L2, L3, L4, L5, L6, L7] at h0 h1 h2 h3 h4 h5 h6 h7
  have c7 : x 7 = 0 := by linarith
  have c6 : x 6 = 0 := by linarith
  have c5 : x 5 = 0 := by linarith
  have c4 : x 4 = 0 := by linarith
  have c3 : x 3 = 0 := by linarith
  have c2 : x 2 = 0 := by linarith
  have c1 : x 1 = 0 := by linarith
  have c0 : x 0 = 0 := by linarith
  funext i
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

/-- The hyperbolic pairing of the cutoff pair — zero section against fibre: `Q_U(a, b) = 2ab`,
whose Gram on the standard pair is `[[0, 1], [1, 0]]`. -/
def QU (a b : ℚ) : ℚ := 2 * a * b

/-- **The cutoff direction is isotropic**: the zero-section direction pairs to nothing with
itself — the positivity belongs to the remainder and not to the lattice.  This is the can-fail
control: a form that paid everywhere would carry no evidence. -/
theorem theCutoffDirectionIsIsotropic : QU 1 0 = 0 ∧ QU 0 1 = 0 ∧ QU 1 1 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [QU]

end Soma.Holonics.Millennium.HeightLattice
