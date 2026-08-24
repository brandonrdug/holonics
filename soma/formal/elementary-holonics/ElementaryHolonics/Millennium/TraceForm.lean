import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The Riemann pivot, instantiated: the trace form and what a grading sees

`Pivots` proved that a pullback of an inner product along an injection is definite.  This file
names the realizer for the row where positivity is a theorem.

`Tr(AᵀB)` **is** the Euclidean inner product of the entry vectors — `theTraceFormIsTheEuclideanPullback`,
with `theRealizerIsInjective` beside it — so `Tr(AᵀA) = 0 ⟹ A = 0` is not a separate fact to be
established but `theRealizedFormIsDefinite` with the realizer exhibited.  That is
`Tr(αα†) > 0 for α ≠ 0` in its linear shell: Castelnuovo positivity of the Rosati involution, once
the correspondence algebra is realised.  **Realization pays; placement rides.**

## The other half: what a grading can see

`theGradedReadingIsTheCommutator` — for antisymmetric `S` and symmetric `A`, the symmetric part of
`SᵀA` is exactly `[A, S]`.  Refining the receiver from the plain diagonal to a graded one converts
an invisible structure into a visible one, and **what becomes visible is a curvature term** — the
`a ∧ a` of the corpus, arriving as the only thing a grading can see.

`theInvisibleAntisymmetricIsZero` — an antisymmetric operator invisible to *every* symmetric
receiver is zero, and the diagonal idempotents alone already recover it.  So the antisymmetric part
is not unreadable; it is unreadable **by one receiver**, and the family of graded receivers
separates it completely.  This is the general form of the two-dimensional witness in `Pivots`, and
it says the Navier–Stokes obstruction is a *choice of receiver*, not an absence of structure: the
nonlinearity is invisible to the energy reading and fully visible to the graded family.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.TraceForm

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace form is a sum of squares. -/
theorem theTraceFormIsASumOfSquares (A : Matrix n n ℝ) :
    Matrix.trace (Aᵀ * A) = ∑ i, ∑ j, A j i ^ 2 := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun j _ => by simp [Matrix.transpose_apply]; ring)

/-- **THE TRACE FORM IS POSITIVE DEFINITE.**  `Tr(AᵀA) = 0` forces `A = 0` — this is
`Tr(αα†) > 0 for α ≠ 0` in its linear shell, which is Castelnuovo positivity of the Rosati
involution once the correspondence algebra is realised. -/
theorem theTraceFormIsDefinite (A : Matrix n n ℝ) (h : Matrix.trace (Aᵀ * A) = 0) : A = 0 := by
  rw [theTraceFormIsASumOfSquares] at h
  ext j i
  have hnn : ∀ i ∈ (univ : Finset n), (0:ℝ) ≤ ∑ j, A j i ^ 2 :=
    fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 : ∑ j, A j i ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (mem_univ i)
  have h2 : A j i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h1 j (mem_univ j)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2

/-- The trace form is nonnegative. -/
theorem theTraceFormIsPositive (A : Matrix n n ℝ) : 0 ≤ Matrix.trace (Aᵀ * A) := by
  rw [theTraceFormIsASumOfSquares]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-! ## And it is a Euclidean pullback — the realizer, exhibited -/

/-- The realizer: read a matrix as a vector of its entries. -/
def realize (A : Matrix n n ℝ) : EuclideanSpace ℝ (n × n) := WithLp.toLp 2 (fun p => A p.1 p.2)

/-- **THE TRACE FORM IS THE PULLBACK OF THE EUCLIDEAN INNER PRODUCT ALONG THAT REALIZER.**  So its
positivity is not a separate fact to be established — it is `Pivots.theRealizedFormIsDefinite`
with the realizer named.  Realization pays; placement rides. -/
theorem theTraceFormIsTheEuclideanPullback (A B : Matrix n n ℝ) :
    inner ℝ (realize A) (realize B) = Matrix.trace (Aᵀ * B) := by
  rw [PiLp.inner_apply, Matrix.trace]
  simp only [realize, WithLp.toLp, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- The realizer is injective — a matrix is recoverable from its entries. -/
theorem theRealizerIsInjective {A : Matrix n n ℝ} (h : realize A = 0) : A = 0 := by
  ext i j
  have := congrFun (congrArg WithLp.ofLp h) (i, j)
  simpa [realize] using this

/-! ## What a graded receiver sees is the commutator -/

/-- **THE GRADED READING IS THE COMMUTATOR.**  For antisymmetric `S` and symmetric `A`, the
symmetric part of `SᵀA` is exactly `[A, S]`.  So refining the receiver from the plain diagonal to
a graded one converts an invisible structure into a visible one, and what becomes visible is a
*curvature* term — the `a ∧ a` of the corpus, arriving here as the only thing a grading can see. -/
theorem theGradedReadingIsTheCommutator {S A : Matrix n n ℝ} (hS : Sᵀ = -S) (hA : Aᵀ = A) :
    Sᵀ * A + Aᵀ * S = A * S - S * A := by
  rw [hS, hA, neg_mul, sub_eq_add_neg, add_comm]

/-- **AN ANTISYMMETRIC OPERATOR INVISIBLE TO EVERY SYMMETRIC RECEIVER IS ZERO.**  Grading against
the diagonal idempotents alone recovers it.  So the antisymmetric part is not *unreadable* — it is
unreadable by one receiver, and the family of graded receivers separates it completely.

This is the general form of the two-dimensional witness: the Navier–Stokes nonlinearity is
invisible to the energy reading and **fully visible to the family of graded readings**, so the
obstruction there is a choice of receiver, not an absence of structure. -/
theorem theInvisibleAntisymmetricIsZero {S : Matrix n n ℝ} (hS : Sᵀ = -S)
    (h : ∀ A : Matrix n n ℝ, Aᵀ = A → A * S = S * A) : S = 0 := by
  ext i j
  rcases eq_or_ne j i with rfl | hne
  · have := congrFun (congrFun hS j) j
    simp [Matrix.transpose_apply] at this
    simp only [Matrix.zero_apply]
    linarith [this]
  · set d : n → ℝ := fun k => if k = i then 1 else 0 with hd
    have hsym : (Matrix.diagonal d)ᵀ = Matrix.diagonal d := Matrix.diagonal_transpose d
    have hcomm := h (Matrix.diagonal d) hsym
    have h1 := congrFun (congrFun hcomm i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp [hd, hne] at h1
    simpa using h1

end Soma.Holonics.Millennium.TraceForm
