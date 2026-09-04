import Mathlib.Tactic

/-!
# MestreHeightLattice: the rank-12 height form of the Mestre K3 family, realized and definite

The Shioda height form of a Mestre rank-12 family (leaderboards #159, #161, #280 — all three
return the same lattice) was computed exactly over `ℚ[T]` by
`crates/holonic-engine/examples/the_height_form_of_the_surface_is_exact.rs`
(`.local/artifacts/the_height_form_of_the_surface_is_exact/159.txt`, 2026-08-28): the globally minimal
short model has `χ = 2` (a K3 surface), fibre `I₄` at infinity and twenty `I₁` fibres, and on the
twelve independent sections `a₁−T, a₂±T, …, a₆±T, L₀⁺` the Gram matrix `Q` below.  This file hands
that exact object to the positivity discipline of `HeightLattice.lean`:

* **the height form is a sum of squares with twelve positive pivots** — an exact polynomial
  identity checked by `ring`;
* **the pivots' product is `6804 = 2²·3⁵·7`** — the regulator of the twelve sections (the `ℤ`-span
  of all twenty-three sections contains them with index `6`, regulator `189 = 3³·7`);
* **the form pays** (`0 ≤ Q x`) and **is anisotropic** (`Q x = 0 → x = 0`): the radical is
  trivial, which is what makes the regulator a genuine volume — the Néron–Tate height on
  `MW ⊗ ℚ` is positive definite modulo torsion, here realized on an explicit rank-12 instance.

The Gram entries are exterior input (an exact computation, not a Lean derivation of Shioda's
formula); the identity, positivity, anisotropy and determinant are kernel-checked.  Nothing here
claims movement on the Birch–Swinnerton-Dyer conjecture: this is the *form* row of the coupling
table realized at rank twelve, not the rank/`L` equality.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.MestreHeightLattice

/-- The height form on the twelve independent sections, `⟨P,P⟩ = 2χ + 2(P·O) − Σ contr_v` and
`⟨P,Q⟩` by polarization, read off the exact Gram matrix. -/
def Q (x : Fin 12 → ℚ) : ℚ :=
  (3) * x 0 * x 0 + (1) * x 0 * x 1 + (2) * x 0 * x 2 + (1) * x 0 * x 3 + (2) * x 0 * x 4 + (1) * x 0 * x 5 + (2) * x 0 * x 6 + (1) * x 0 * x 7 + (2) * x 0 * x 8 + (1) * x 0 * x 9 + (2) * x 0 * x 10 + (3/2) * x 0 * x 11 + (1) * x 1 * x 0 + (4) * x 1 * x 1 + (3) * x 1 * x 2 + (2) * x 1 * x 3 + (2) * x 1 * x 4 + (2) * x 1 * x 5 + (2) * x 1 * x 6 + (2) * x 1 * x 7 + (2) * x 1 * x 8 + (2) * x 1 * x 9 + (2) * x 1 * x 10 + (2) * x 1 * x 11 + (2) * x 2 * x 0 + (3) * x 2 * x 1 + (5) * x 2 * x 2 + (2) * x 2 * x 3 + (3) * x 2 * x 4 + (2) * x 2 * x 5 + (3) * x 2 * x 6 + (2) * x 2 * x 7 + (3) * x 2 * x 8 + (2) * x 2 * x 9 + (3) * x 2 * x 10 + (3/2) * x 2 * x 11 + (1) * x 3 * x 0 + (2) * x 3 * x 1 + (2) * x 3 * x 2 + (4) * x 3 * x 3 + (3) * x 3 * x 4 + (2) * x 3 * x 5 + (2) * x 3 * x 6 + (2) * x 3 * x 7 + (2) * x 3 * x 8 + (2) * x 3 * x 9 + (2) * x 3 * x 10 + (1) * x 3 * x 11 + (2) * x 4 * x 0 + (2) * x 4 * x 1 + (3) * x 4 * x 2 + (3) * x 4 * x 3 + (5) * x 4 * x 4 + (2) * x 4 * x 5 + (3) * x 4 * x 6 + (2) * x 4 * x 7 + (3) * x 4 * x 8 + (2) * x 4 * x 9 + (3) * x 4 * x 10 + (3/2) * x 4 * x 11 + (1) * x 5 * x 0 + (2) * x 5 * x 1 + (2) * x 5 * x 2 + (2) * x 5 * x 3 + (2) * x 5 * x 4 + (4) * x 5 * x 5 + (3) * x 5 * x 6 + (2) * x 5 * x 7 + (2) * x 5 * x 8 + (2) * x 5 * x 9 + (2) * x 5 * x 10 + (2) * x 5 * x 11 + (2) * x 6 * x 0 + (2) * x 6 * x 1 + (3) * x 6 * x 2 + (2) * x 6 * x 3 + (3) * x 6 * x 4 + (3) * x 6 * x 5 + (5) * x 6 * x 6 + (2) * x 6 * x 7 + (3) * x 6 * x 8 + (2) * x 6 * x 9 + (3) * x 6 * x 10 + (5/2) * x 6 * x 11 + (1) * x 7 * x 0 + (2) * x 7 * x 1 + (2) * x 7 * x 2 + (2) * x 7 * x 3 + (2) * x 7 * x 4 + (2) * x 7 * x 5 + (2) * x 7 * x 6 + (4) * x 7 * x 7 + (3) * x 7 * x 8 + (2) * x 7 * x 9 + (2) * x 7 * x 10 + (1) * x 7 * x 11 + (2) * x 8 * x 0 + (2) * x 8 * x 1 + (3) * x 8 * x 2 + (2) * x 8 * x 3 + (3) * x 8 * x 4 + (2) * x 8 * x 5 + (3) * x 8 * x 6 + (3) * x 8 * x 7 + (5) * x 8 * x 8 + (2) * x 8 * x 9 + (3) * x 8 * x 10 + (3/2) * x 8 * x 11 + (1) * x 9 * x 0 + (2) * x 9 * x 1 + (2) * x 9 * x 2 + (2) * x 9 * x 3 + (2) * x 9 * x 4 + (2) * x 9 * x 5 + (2) * x 9 * x 6 + (2) * x 9 * x 7 + (2) * x 9 * x 8 + (4) * x 9 * x 9 + (3) * x 9 * x 10 + (1) * x 9 * x 11 + (2) * x 10 * x 0 + (2) * x 10 * x 1 + (3) * x 10 * x 2 + (2) * x 10 * x 3 + (3) * x 10 * x 4 + (2) * x 10 * x 5 + (3) * x 10 * x 6 + (2) * x 10 * x 7 + (3) * x 10 * x 8 + (3) * x 10 * x 9 + (5) * x 10 * x 10 + (5/2) * x 10 * x 11 + (3/2) * x 11 * x 0 + (2) * x 11 * x 1 + (3/2) * x 11 * x 2 + (1) * x 11 * x 3 + (3/2) * x 11 * x 4 + (2) * x 11 * x 5 + (5/2) * x 11 * x 6 + (1) * x 11 * x 7 + (3/2) * x 11 * x 8 + (1) * x 11 * x 9 + (5/2) * x 11 * x 10 + (13/4) * x 11 * x 11

def L0 (x : Fin 12 → ℚ) : ℚ := x 0 + (1/3) * x 1 + (2/3) * x 2 + (1/3) * x 3 + (2/3) * x 4 + (1/3) * x 5 + (2/3) * x 6 + (1/3) * x 7 + (2/3) * x 8 + (1/3) * x 9 + (2/3) * x 10 + (1/2) * x 11
def L1 (x : Fin 12 → ℚ) : ℚ := x 1 + (7/11) * x 2 + (5/11) * x 3 + (4/11) * x 4 + (5/11) * x 5 + (4/11) * x 6 + (5/11) * x 7 + (4/11) * x 8 + (5/11) * x 9 + (4/11) * x 10 + (9/22) * x 11
def L2 (x : Fin 12 → ℚ) : ℚ := x 2 + (1/8) * x 3 + (3/8) * x 4 + (1/8) * x 5 + (3/8) * x 6 + (1/8) * x 7 + (3/8) * x 8 + (1/8) * x 9 + (3/8) * x 10 + (-5/24) * x 11
def L3 (x : Fin 12 → ℚ) : ℚ := x 3 + (13/23) * x 4 + (7/23) * x 5 + (5/23) * x 6 + (7/23) * x 7 + (5/23) * x 8 + (7/23) * x 9 + (5/23) * x 10 + (-1/23) * x 11
def L4 (x : Fin 12 → ℚ) : ℚ := x 4 + (1/15) * x 5 + (4/15) * x 6 + (1/15) * x 7 + (4/15) * x 8 + (1/15) * x 9 + (4/15) * x 10 + (1/10) * x 11
def L5 (x : Fin 12 → ℚ) : ℚ := x 5 + (7/13) * x 6 + (3/13) * x 7 + (2/13) * x 8 + (3/13) * x 9 + (2/13) * x 10 + (9/26) * x 11
def L6 (x : Fin 12 → ℚ) : ℚ := x 6 + (1/24) * x 7 + (5/24) * x 8 + (1/24) * x 9 + (5/24) * x 10 + (1/3) * x 11
def L7 (x : Fin 12 → ℚ) : ℚ := x 7 + (31/59) * x 8 + (11/59) * x 9 + (7/59) * x 10 + (-8/59) * x 11
def L8 (x : Fin 12 → ℚ) : ℚ := x 8 + (1/35) * x 9 + (6/35) * x 10 + (1/210) * x 11
def L9 (x : Fin 12 → ℚ) : ℚ := x 9 + (43/83) * x 10 + (-19/166) * x 11
def L10 (x : Fin 12 → ℚ) : ℚ := x 10 + (7/12) * x 11
def L11 (x : Fin 12 → ℚ) : ℚ := x 11

set_option maxHeartbeats 4000000 in
/-- **The height form is a sum of squares with twelve positive pivots** — an exact polynomial
identity. -/
theorem theHeightFormIsASumOfSquares (x : Fin 12 → ℚ) :
    Q x = (3) * L0 x ^ 2 + (11/3) * L1 x ^ 2 + (24/11) * L2 x ^ 2 + (23/8) * L3 x ^ 2 + (45/23) * L4 x ^ 2 + (13/5) * L5 x ^ 2 + (24/13) * L6 x ^ 2 + (59/24) * L7 x ^ 2 + (105/59) * L8 x ^ 2 + (83/35) * L9 x ^ 2 + (144/83) * L10 x ^ 2 + (7/12) * L11 x ^ 2 := by
  simp only [Q, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

/-- **The pivots' product is 6804** — the regulator of the twelve sections. -/
theorem thePivotProductIsTheRegulator :
    (3) * (11/3) * (24/11) * (23/8) * (45/23) * (13/5) * (24/13) * (59/24) * (105/59) * (83/35) * (144/83) * (7/12) = (6804 : ℚ) := by norm_num

/-- **The height form pays**: non-negative everywhere, riding the sum of squares. -/
theorem theHeightFormPays (x : Fin 12 → ℚ) : 0 ≤ Q x := by
  rw [theHeightFormIsASumOfSquares]
  have s0 := sq_nonneg (L0 x)
  have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x)
  have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x)
  have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x)
  have s7 := sq_nonneg (L7 x)
  have s8 := sq_nonneg (L8 x)
  have s9 := sq_nonneg (L9 x)
  have s10 := sq_nonneg (L10 x)
  have s11 := sq_nonneg (L11 x)
  linarith

set_option maxHeartbeats 4000000 in
/-- **The height form is anisotropic**: a section combination of height zero is zero.  The squares
drain from the tail of the elimination back to its head. -/
theorem theHeightFormIsAnisotropic (x : Fin 12 → ℚ) (h : Q x = 0) : x = 0 := by
  rw [theHeightFormIsASumOfSquares] at h
  have s0 := sq_nonneg (L0 x)
  have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x)
  have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x)
  have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x)
  have s7 := sq_nonneg (L7 x)
  have s8 := sq_nonneg (L8 x)
  have s9 := sq_nonneg (L9 x)
  have s10 := sq_nonneg (L10 x)
  have s11 := sq_nonneg (L11 x)
  have h11 : L11 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h10 : L10 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h9 : L9 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h8 : L8 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h7 : L7 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h6 : L6 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h5 : L5 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h4 : L4 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h3 : L3 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h2 : L2 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h1 : L1 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h0 : L0 x = 0 := sq_eq_zero_iff.mp (by linarith)
  unfold L0 at h0
  unfold L1 at h1
  unfold L2 at h2
  unfold L3 at h3
  unfold L4 at h4
  unfold L5 at h5
  unfold L6 at h6
  unfold L7 at h7
  unfold L8 at h8
  unfold L9 at h9
  unfold L10 at h10
  unfold L11 at h11
  have c11 : x 11 = 0 := by linarith
  have c10 : x 10 = 0 := by linarith
  have c9 : x 9 = 0 := by linarith
  have c8 : x 8 = 0 := by linarith
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

section Audit

#print axioms theHeightFormIsASumOfSquares
#print axioms thePivotProductIsTheRegulator
#print axioms theHeightFormPays
#print axioms theHeightFormIsAnisotropic

end Audit

end Soma.Holonics.Millennium.MestreHeightLattice
